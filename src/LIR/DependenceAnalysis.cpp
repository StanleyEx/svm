#include "DependenceAnalysis.h"
#include "SCEVLinearizer.h"
#include "Utils.h"

#include <algorithm>
#include <limits>
#include <numeric>

namespace svm::ir {
namespace {

struct AccessBuildState {
  const SCEV &scev;                                     // 标量演化事实源
  const std::vector<const Loop *> &space;               // 可作为变量的循环
  BasicBlock *context = nullptr;                        // 路径事实上下文
  u32 nodesLeft = 0;                                    // 剩余SCEV节点预算
  AccessBuildStatus failure = AccessBuildStatus::Exact; // 首个失败原因
  MathBounds byteBounds; // pointer-width字节偏移前缀
};

bool containsLoop(const std::vector<const Loop *> &space,
                  const Loop *loop) noexcept {
  return std::find(space.begin(), space.end(), loop) != space.end();
}

bool addLoopTerm(std::vector<LoopCoefficient> &terms, const Loop *loop,
                 i64 coefficient) noexcept {
  if (coefficient == 0)
    return true;
  for (auto iterator = terms.begin(); iterator != terms.end(); ++iterator) {
    if (iterator->loop != loop)
      continue;
    i64 sum = 0;
    if (!checkedAdd(iterator->coefficient, coefficient, sum))
      return false;
    if (sum == 0)
      terms.erase(iterator);
    else
      iterator->coefficient = sum;
    return true;
  }
  terms.push_back({loop, coefficient});
  return true;
}

bool addInvariant(std::vector<InvariantAtom> &terms, const SCEVExpr *expression,
                  i64 coefficient) noexcept {
  if (coefficient == 0)
    return true;
  for (auto iterator = terms.begin(); iterator != terms.end(); ++iterator) {
    if (iterator->type != expression->ty || iterator->expression != expression)
      continue;
    i64 sum = 0;
    if (!checkedAdd(iterator->coefficient, coefficient, sum))
      return false;
    if (sum == 0)
      terms.erase(iterator);
    else
      iterator->coefficient = sum;
    return true;
  }
  terms.push_back({expression, expression->ty, coefficient});
  return true;
}

bool isInvariantForSpace(const SCEVExpr *expression,
                         const std::vector<const Loop *> &space) {
  if (!expression)
    return false;
  for (const Loop *loop : space)
    if (!expression->isLoopInvariant(loop))
      return false;
  return true;
}

bool linearizeAccessExpr(SCEVExpr *expression, i64 scale, AffineExpr &result,
                         AccessBuildState &state) {
  if (!expression || state.nodesLeft == 0) {
    state.failure = expression ? AccessBuildStatus::BudgetExceeded
                               : AccessBuildStatus::NonAffine;
    return false;
  }

  const SCEVLinearForm form = SCEVLinearizer(state.nodesLeft, state.nodesLeft)
                                  .linearize(expression, scale);
  state.nodesLeft -= std::min(state.nodesLeft, form.nodesVisited);
  if (form.status == SCEVLinearizeStatus::BudgetExceeded) {
    state.failure = AccessBuildStatus::BudgetExceeded;
    return false;
  }
  if (form.status == SCEVLinearizeStatus::ArithmeticOverflow) {
    state.failure = AccessBuildStatus::ArithmeticOverflow;
    return false;
  }
  if (!form.exact()) {
    state.failure = AccessBuildStatus::NonAffine;
    return false;
  }
  if (!checkedAdd(result.constant, form.constant, result.constant)) {
    state.failure = AccessBuildStatus::ArithmeticOverflow;
    return false;
  }

  for (const SCEVLinearTerm &term : form.terms) {
    SCEVExpr *atom = term.atom;
    if (atom && atom->kind == SCEVExpr::K_ADDREC &&
        containsLoop(state.space, atom->addRec.loop)) {
      i64 coefficient = 0;
      if (!atom->addRec.step || !atom->addRec.step->isConstant()) {
        state.failure = AccessBuildStatus::NonAffine;
        return false;
      }
      if (!checkedMul(term.coefficient, atom->addRec.step->cst.v,
                      coefficient) ||
          !addLoopTerm(result.loops, atom->addRec.loop, coefficient)) {
        state.failure = AccessBuildStatus::ArithmeticOverflow;
        return false;
      }
      if (!linearizeAccessExpr(atom->addRec.base, term.coefficient, result,
                               state))
        return false;
      continue;
    }
    if (!isInvariantForSpace(atom, state.space)) {
      state.failure = AccessBuildStatus::NonAffine;
      return false;
    }
    if (!addInvariant(result.symbols, atom, term.coefficient)) {
      state.failure = AccessBuildStatus::ArithmeticOverflow;
      return false;
    }
  }
  return true;
}

MathBounds accessMathBounds(const SCEV &scev, SCEVExpr *expression,
                            BasicBlock *context) {
  MathQuery query;
  query.contextBlock = context;
  return scev.getSignedDeltaBounds(expression, scev.getConstant(0, TY_I32),
                                   query);
}

bool appendOffsetTerm(SCEVExpr *index, i64 stride, AffineExpr &bytes,
                      AccessBuildState &state) {
  if (!index || index->ty != TY_I32 || stride <= 0) {
    state.failure = AccessBuildStatus::NonAffine;
    return false;
  }
  const MathBounds indexBounds =
      accessMathBounds(state.scev, index, state.context);
  if (!indexBounds.valid || !indexBounds.proof.proven()) {
    state.failure = AccessBuildStatus::MissingNoWrap;
    return false;
  }

  i64 termMin = 0;
  i64 termMax = 0;
  i64 prefixMin = 0;
  i64 prefixMax = 0;
  if (!checkedMul(indexBounds.min, stride, termMin) ||
      !checkedMul(indexBounds.max, stride, termMax) ||
      !checkedAdd(state.byteBounds.min, termMin, prefixMin) ||
      !checkedAdd(state.byteBounds.max, termMax, prefixMax)) {
    state.failure = AccessBuildStatus::ArithmeticOverflow;
    return false;
  }
  if (!linearizeAccessExpr(index, stride, bytes, state))
    return false;
  state.byteBounds = MathBounds::of(
      prefixMin, prefixMax,
      NoWrapInfo{NoWrapKind::PointerSigned, NoWrapSource::RangeProof});
  bytes.bounds = state.byteBounds;
  return true;
}

bool extractAddress(Inst *address, Inst *root, AffineExpr &bytes,
                    AccessBuildState &state, u32 depth) {
  if (!address || depth == 0) {
    state.failure = depth == 0 ? AccessBuildStatus::BudgetExceeded
                               : AccessBuildStatus::UnknownRoot;
    return false;
  }
  if (address == root)
    return true;

  if (address->getOp() == OP_GETPTR) {
    if (address->getOperandCount() != 2 || address->getStride() <= 0 ||
        !extractAddress(address->getArg(0), root, bytes, state, depth - 1)) {
      if (state.failure == AccessBuildStatus::Exact)
        state.failure = AccessBuildStatus::UnknownRoot;
      return false;
    }
    return appendOffsetTerm(state.scev.getSCEV(address->getArg(1)),
                            address->getStride(), bytes, state);
  }

  if (address->getOp() == OP_ARRAYIDX) {
    if (!extractAddress(address->getArg(0), root, bytes, state, depth - 1)) {
      if (state.failure == AccessBuildStatus::Exact)
        state.failure = AccessBuildStatus::UnknownRoot;
      return false;
    }
    const u32 indexCount = address->getOperandCount() - 1;
    for (u32 index = 0; index < indexCount; ++index) {
      Inst *subscript = address->getArg(index + 1);
      if (subscript->getOp() == OP_ICONST && !subscript->isUndefValue() &&
          subscript->getImm() == 0)
        continue;
      u64 rawStride = 0;
      if (!arrayIndexStrideBytes(address, index, rawStride) ||
          rawStride > static_cast<u64>(std::numeric_limits<i64>::max()) ||
          !appendOffsetTerm(state.scev.getSCEV(subscript),
                            static_cast<i64>(rawStride), bytes, state))
        return false;
    }
    return true;
  }

  state.failure = AccessBuildStatus::UnknownRoot;
  return false;
}

std::optional<StructuredSubscripts>
buildShape(Inst *address, const std::vector<const Loop *> &space,
           const SCEV &scev, u32 maxNodes) {
  if (!address || address->getOp() != OP_ARRAYIDX)
    return std::nullopt;

  const ArrayPayload &array = address->getArray();
  const u32 indexCount = address->getOperandCount() - 1;
  if (array.rank == 0 || indexCount != static_cast<u32>(array.rank) + 1)
    return std::nullopt;
  Inst *leading = address->getArg(1);
  const bool hasLeadingZero = leading && !leading->isUndefValue() &&
                              leading->getOp() == OP_ICONST &&
                              leading->getImm() == 0;
  const u32 coordinateCount =
      static_cast<u32>(array.rank) + (hasLeadingZero ? 0U : 1U);
  const u32 firstGepIndex = hasLeadingZero ? 1U : 0U;

  StructuredSubscripts shape;
  shape.elementType = array.elementType;
  shape.dims.reserve(coordinateCount);
  if (!hasLeadingZero)
    shape.dims.push_back(0); // 未知的形参首维
  shape.dims.insert(shape.dims.end(), array.dims, array.dims + array.rank);
  shape.strides.reserve(coordinateCount);
  shape.indices.reserve(coordinateCount);
  for (u32 coordinate = 0; coordinate < coordinateCount; ++coordinate) {
    const u32 gepIndex = firstGepIndex + coordinate;
    u64 rawStride = 0;
    if (!arrayIndexStrideBytes(address, gepIndex, rawStride) ||
        rawStride > static_cast<u64>(std::numeric_limits<u32>::max()))
      return std::nullopt;
    shape.strides.push_back(static_cast<u32>(rawStride));
    SCEVExpr *subscript = scev.getSCEV(address->getArg(gepIndex + 1));
    AccessBuildState state{
        scev, space, address->parentBlock(), maxNodes, AccessBuildStatus::Exact,
        {}};
    AffineExpr expression;
    expression.bounds =
        accessMathBounds(scev, subscript, address->parentBlock());
    const bool unknownDimension = !hasLeadingZero && coordinate == 0;
    const u32 dimension =
        unknownDimension ? 0 : coordinate - (hasLeadingZero ? 0U : 1U);
    if (!expression.bounds.valid || !expression.bounds.proof.proven() ||
        expression.bounds.min < 0 ||
        (!unknownDimension &&
         static_cast<u64>(expression.bounds.max) >= array.dims[dimension]) ||
        !linearizeAccessExpr(subscript, 1, expression, state))
      return std::nullopt;
    shape.indices.push_back(std::move(expression));
  }
  return shape;
}

u32 accessWidth(Inst *memoryInst) noexcept {
  const MemPayload &memory = memoryInst->getMem();
  if (memory.totalSizeBytes != 0)
    return memory.totalSizeBytes;
  const i32 fallback = typeSizeBytes(memory.elementType);
  return fallback > 0 ? static_cast<u32>(fallback) : 0;
}

AffineAccess
buildAffineAccess(const SCEV &scev, const AliasInfo &alias,
                  AffineAccessBudget budget, Inst *memoryInst,
                  const std::vector<const Loop *> &iterationSpace) {
  AffineAccess result;
  result.memoryInst = memoryInst;
  if (!memoryInst ||
      (memoryInst->getOp() != OP_LOAD && memoryInst->getOp() != OP_STORE) ||
      memoryInst->getOperandCount() == 0) {
    result.status = AccessBuildStatus::NonAffine;
    return result;
  }
  result.address = memoryInst->getArg(0);
  result.kind = memoryInst->getOp() == OP_STORE ? MemoryAccessKind::Write
                                                : MemoryAccessKind::Read;
  result.widthBytes = accessWidth(memoryInst);
  if (result.widthBytes == 0) {
    result.status = AccessBuildStatus::UnsupportedWidth;
    return result;
  }

  const PointerInfo pointer = alias.info(result.address);
  if (!pointer.root || pointer.kind == PointerKind::Opaque) {
    result.status = AccessBuildStatus::UnknownRoot;
    return result;
  }
  result.bytes.root = pointer.root;

  AccessBuildState state{scev,
                         iterationSpace,
                         memoryInst->parentBlock(),
                         budget.maxExpressionNodes,
                         AccessBuildStatus::Exact,
                         MathBounds::of(0, 0,
                                        NoWrapInfo{NoWrapKind::PointerSigned,
                                                   NoWrapSource::RangeProof})};
  AffineExpr bytes;
  bytes.bounds = state.byteBounds;
  if (!extractAddress(result.address, result.bytes.root, bytes, state,
                      budget.maxAddressDepth)) {
    result.status = state.failure;
    return result;
  }

  result.bytes.constant = bytes.constant;
  result.bytes.loops = std::move(bytes.loops);
  result.bytes.symbols = std::move(bytes.symbols);
  result.bytes.noWrap = bytes.bounds.proof;
  if (!result.bytes.noWrap.proven()) {
    result.status = AccessBuildStatus::MissingNoWrap;
    return result;
  }
  result.shape = buildShape(result.address, iterationSpace, scev,
                            budget.maxExpressionNodes);
  result.status = AccessBuildStatus::Exact;
  return result;
}

DependenceKind dependenceKind(const AffineAccess &source,
                              const AffineAccess &sink) noexcept {
  if (source.kind == MemoryAccessKind::Write)
    return sink.kind == MemoryAccessKind::Read ? DependenceKind::Flow
                                               : DependenceKind::Output;
  return sink.kind == MemoryAccessKind::Write ? DependenceKind::Anti
                                              : DependenceKind::Input;
}

DependenceRejectReason accessReject(AccessBuildStatus status) noexcept {
  switch (status) {
  case AccessBuildStatus::Exact:
    return DependenceRejectReason::None;
  case AccessBuildStatus::UnknownRoot:
    return DependenceRejectReason::UnknownRoot;
  case AccessBuildStatus::NonAffine:
    return DependenceRejectReason::NonAffine;
  case AccessBuildStatus::MissingNoWrap:
    return DependenceRejectReason::MissingNoWrap;
  case AccessBuildStatus::UnsupportedWidth:
    return DependenceRejectReason::UnsupportedWidth;
  case AccessBuildStatus::BudgetExceeded:
    return DependenceRejectReason::ExpressionBudgetExceeded;
  case AccessBuildStatus::ArithmeticOverflow:
    return DependenceRejectReason::ArithmeticOverflow;
  }
  return DependenceRejectReason::NonAffine;
}

DependenceProofKind solverProof(DependenceProof proof) noexcept {
  switch (proof) {
  case DependenceProof::None:
    return DependenceProofKind::None;
  case DependenceProof::ZIV:
    return DependenceProofKind::ZIV;
  case DependenceProof::SIV:
    return DependenceProofKind::SIV;
  case DependenceProof::GCD:
    return DependenceProofKind::GCD;
  case DependenceProof::Banerjee:
    return DependenceProofKind::Banerjee;
  }
  return DependenceProofKind::None;
}

DependenceRejectReason solverReject(DependenceSolverFailure failure) noexcept {
  switch (failure) {
  case DependenceSolverFailure::None:
    return DependenceRejectReason::None;
  case DependenceSolverFailure::InvalidProblem:
    return DependenceRejectReason::SolverInvalid;
  case DependenceSolverFailure::ArithmeticOverflow:
    return DependenceRejectReason::ArithmeticOverflow;
  case DependenceSolverFailure::DirectionBudgetExceeded:
    return DependenceRejectReason::DirectionBudgetExceeded;
  }
  return DependenceRejectReason::SolverInvalid;
}

bool sameRoot(const LinearByteFunction &left,
              const LinearByteFunction &right) noexcept {
  if (!left.root || !right.root)
    return false;
  if (left.root == right.root)
    return true;
  return left.root->getOp() == OP_GETGLOBAL &&
         right.root->getOp() == OP_GETGLOBAL &&
         left.root->getGlobal() == right.root->getGlobal();
}

bool sameAtom(const InvariantAtom &left, const InvariantAtom &right) noexcept {
  return left.type == right.type && left.expression == right.expression;
}

bool symbolsCancel(const std::vector<InvariantAtom> &left,
                   const std::vector<InvariantAtom> &right) noexcept {
  std::vector<bool> consumed(right.size(), false);
  for (const InvariantAtom &term : left) {
    bool found = false;
    for (usize index = 0; index < right.size(); ++index) {
      if (!consumed[index] && term.coefficient == right[index].coefficient &&
          sameAtom(term, right[index])) {
        consumed[index] = true;
        found = true;
        break;
      }
    }
    if (!found)
      return false;
  }
  return left.size() == right.size();
}

bool findCoefficient(const std::vector<LoopCoefficient> &terms,
                     const Loop *loop, i64 &coefficient) noexcept {
  coefficient = 0;
  for (const LoopCoefficient &term : terms) {
    if (term.loop != loop)
      continue;
    if (!checkedAdd(coefficient, term.coefficient, coefficient))
      return false;
  }
  return true;
}

bool projectExpression(const AffineExpr &source, const AffineExpr &sink,
                       const std::vector<const Loop *> &nest,
                       AffineEquationSide &sourceSide,
                       AffineEquationSide &sinkSide,
                       std::vector<i64> &locals) noexcept {
  sourceSide.constant = source.constant;
  sinkSide.constant = sink.constant;
  locals.clear();
  sourceSide.coefficients.reserve(nest.size());
  sinkSide.coefficients.reserve(nest.size());
  for (const Loop *loop : nest) {
    i64 sourceCoefficient = 0;
    i64 sinkCoefficient = 0;
    if (!findCoefficient(source.loops, loop, sourceCoefficient) ||
        !findCoefficient(sink.loops, loop, sinkCoefficient))
      return false;
    sourceSide.coefficients.push_back(sourceCoefficient);
    sinkSide.coefficients.push_back(sinkCoefficient);
  }

  for (const LoopCoefficient &term : source.loops) {
    if (std::find(nest.begin(), nest.end(), term.loop) != nest.end())
      continue;
    i64 other = 0;
    if (!findCoefficient(sink.loops, term.loop, other))
      return false;
    if (other == term.coefficient)
      continue;
    if (term.coefficient != 0)
      locals.push_back(term.coefficient);
    i64 negative = 0;
    if (other != 0 && !checkedSub(i64{0}, other, negative))
      return false;
    if (other != 0)
      locals.push_back(negative);
  }
  for (const LoopCoefficient &term : sink.loops) {
    if (std::find(nest.begin(), nest.end(), term.loop) != nest.end())
      continue;
    const bool handled = std::any_of(source.loops.begin(), source.loops.end(),
                                     [&](const LoopCoefficient &sourceTerm) {
                                       return sourceTerm.loop == term.loop;
                                     });
    i64 negative = 0;
    if (!handled && term.coefficient != 0 &&
        !checkedSub(i64{0}, term.coefficient, negative))
      return false;
    if (!handled && term.coefficient != 0)
      locals.push_back(negative);
  }
  if (!symbolsCancel(source.symbols, sink.symbols)) {
    if (locals.empty())
      return false;
    for (const InvariantAtom &term : source.symbols)
      if (term.coefficient != 0)
        locals.push_back(term.coefficient);
    for (const InvariantAtom &term : sink.symbols) {
      i64 negative = 0;
      if (term.coefficient != 0 &&
          !checkedSub(i64{0}, term.coefficient, negative))
        return false;
      if (term.coefficient != 0)
        locals.push_back(negative);
    }
  }
  return true;
}

AffineExpr asAffineExpr(const LinearByteFunction &bytes) {
  AffineExpr result;
  result.constant = bytes.constant;
  result.loops = bytes.loops;
  result.symbols = bytes.symbols;
  return result;
}

bool sameShapeOrigin(const AffineAccess &source, const AffineAccess &sink,
                     const AliasInfo &alias) {
  if (!source.address || !sink.address ||
      source.address->getOp() != OP_ARRAYIDX ||
      sink.address->getOp() != OP_ARRAYIDX)
    return false;
  Inst *sourceBase = source.address->getArg(0);
  Inst *sinkBase = sink.address->getArg(0);
  if (sourceBase == sinkBase)
    return true;
  const PointerInfo sourceInfo = alias.info(sourceBase);
  const PointerInfo sinkInfo = alias.info(sinkBase);
  if (!sourceInfo.root || !sinkInfo.root || !sourceInfo.constantOffset ||
      !sinkInfo.constantOffset ||
      sourceInfo.constantOffset != sinkInfo.constantOffset)
    return false;
  LinearByteFunction sourceRoot;
  sourceRoot.root = sourceInfo.root;
  LinearByteFunction sinkRoot;
  sinkRoot.root = sinkInfo.root;
  return sameRoot(sourceRoot, sinkRoot);
}

bool compatibleShape(const AffineAccess &source, const AffineAccess &sink,
                     const AliasInfo &alias) {
  if (!source.shape || !sink.shape ||
      source.shape->elementType != sink.shape->elementType ||
      source.shape->dims != sink.shape->dims ||
      source.shape->strides != sink.shape->strides ||
      source.shape->indices.size() != sink.shape->indices.size() ||
      !sameShapeOrigin(source, sink, alias))
    return false;
  const i32 elementSize = typeSizeBytes(source.shape->elementType);
  return elementSize > 0 &&
         source.widthBytes == static_cast<u32>(elementSize) &&
         sink.widthBytes == static_cast<u32>(elementSize);
}

DependenceSolution
intersectSolutions(const std::vector<DependenceSolution> &all, u32 depth) {
  VERIFY(!all.empty());
  DependenceSolution result = all.front();
  if (result.status != DependenceStatus::MayDependence)
    return result;
  for (usize solutionIndex = 1; solutionIndex < all.size(); ++solutionIndex) {
    const DependenceSolution &next = all[solutionIndex];
    if (next.status == DependenceStatus::Unknown)
      return next;
    if (next.status == DependenceStatus::NoDependence)
      return next;
    result.directions.erase(
        std::remove_if(result.directions.begin(), result.directions.end(),
                       [&](const DirectionVector &direction) {
                         return std::find(next.directions.begin(),
                                          next.directions.end(),
                                          direction) == next.directions.end();
                       }),
        result.directions.end());
    if (result.directions.empty()) {
      result.status = DependenceStatus::NoDependence;
      result.proof = DependenceProof::Banerjee;
      result.distances.assign(depth, std::nullopt);
      return result;
    }
    if (result.distances.size() != depth)
      result.distances.assign(depth, std::nullopt);
    if (result.distanceMultiples.size() != depth)
      result.distanceMultiples.assign(depth, std::nullopt);
    for (u32 index = 0; index < depth; ++index) {
      const std::optional<i64> candidate =
          index < next.distances.size() ? next.distances[index] : std::nullopt;
      if (!result.distances[index])
        result.distances[index] = candidate;
      else if (candidate && result.distances[index] != candidate) {
        result.status = DependenceStatus::NoDependence;
        result.proof = DependenceProof::SIV;
        result.directions.clear();
        result.distances.assign(depth, std::nullopt);
        return result;
      }
      const std::optional<u64> multiple = index < next.distanceMultiples.size()
                                              ? next.distanceMultiples[index]
                                              : std::nullopt;
      if (!result.distanceMultiples[index])
        result.distanceMultiples[index] = multiple;
      else if (multiple) {
        const u64 common =
            std::gcd(*result.distanceMultiples[index], *multiple);
        VERIFY(common != 0);
        u64 combined = 0;
        if (checkedMul(*result.distanceMultiples[index] / common, *multiple,
                       combined))
          result.distanceMultiples[index] = combined;
        else
          // LCM不可表示时保留较大的单维必要约束
          result.distanceMultiples[index] =
              std::max(*result.distanceMultiples[index], *multiple);
      }
      if (result.distances[index] && result.distanceMultiples[index] &&
          normalizedModulo(*result.distances[index],
                           *result.distanceMultiples[index]) != 0) {
        result.status = DependenceStatus::NoDependence;
        result.proof = DependenceProof::GCD;
        result.directions.clear();
        result.distances.assign(depth, std::nullopt);
        result.distanceMultiples.assign(depth, std::nullopt);
        return result;
      }
    }
  }
  result.status = DependenceStatus::MayDependence;
  return result;
}

std::vector<std::optional<i64>>
tripCounts(const std::vector<const Loop *> &nest, const SCEV &scev) {
  std::vector<std::optional<i64>> result;
  result.reserve(nest.size());
  for (const Loop *loop : nest) {
    const i64 count = scev.getConstantTripCount(loop);
    result.push_back(count > 0 ? std::optional<i64>(count) : std::nullopt);
  }
  return result;
}

bool scalarStartsCannotPartiallyOverlap(const AffineEquationSide &source,
                                        const AffineEquationSide &sink,
                                        const std::vector<i64> &locals,
                                        u32 width) noexcept {
  if (width == 0)
    return false;
  i64 constantDelta = 0;
  if (!checkedSub(source.constant, sink.constant, constantDelta) ||
      constantDelta % static_cast<i64>(width) != 0)
    return false;
  for (i64 coefficient : source.coefficients)
    if (coefficient % static_cast<i64>(width) != 0)
      return false;
  for (i64 coefficient : sink.coefficients)
    if (coefficient % static_cast<i64>(width) != 0)
      return false;
  for (i64 coefficient : locals)
    if (coefficient % static_cast<i64>(width) != 0)
      return false;
  return true;
}

DependenceResult rejected(Inst *source, Inst *sink, const Loop *scope,
                          DependenceKind kind, ProgramOrder order,
                          bool selfPair, DependenceRejectReason reason,
                          std::vector<const Loop *> loops = {}) {
  DependenceResult result;
  result.source = source;
  result.sink = sink;
  result.kind = kind;
  result.order = order;
  result.selfPair = selfPair;
  result.reject = reason;
  result.loops = std::move(loops);
  UNUSED(scope);
  return result;
}

} // namespace

bool DependenceInfo::PairKey::operator==(const PairKey &other) const noexcept {
  return source == other.source && sink == other.sink && scope == other.scope &&
         order == other.order && selfPair == other.selfPair;
}

usize DependenceInfo::PairKeyHash::operator()(
    const PairKey &key) const noexcept {
  usize hash = std::hash<Inst *>{}(key.source);
  hash ^=
      std::hash<Inst *>{}(key.sink) + 0x9e3779b9U + (hash << 6U) + (hash >> 2U);
  hash ^= std::hash<const Loop *>{}(key.scope) + 0x9e3779b9U + (hash << 6U) +
          (hash >> 2U);
  hash ^= static_cast<usize>(key.order) << 1U;
  hash ^= static_cast<usize>(key.selfPair);
  return hash;
}

void DependenceInfo::build(Function *function, const SCEV *scev,
                           const LoopInfo *loops, const AliasInfo *alias,
                           const DominatorTree *dominators,
                           DependenceBudget budget) noexcept {
  function_ = function;
  scev_ = scev;
  loops_ = loops;
  alias_ = alias;
  dominators_ = dominators;
  budget_ = budget;
  accessCache_.clear();
  pairCache_.clear();
}

std::vector<const Loop *>
DependenceInfo::loopNestFor(const Inst *instruction) const {
  std::vector<const Loop *> result;
  const Loop *loop = instruction && loops_
                         ? loops_->getLoopFor(instruction->parentBlock())
                         : nullptr;
  for (; loop; loop = loop->parent())
    result.push_back(loop);
  std::reverse(result.begin(), result.end());
  return result;
}

std::vector<const Loop *> DependenceInfo::commonNest(Inst *first, Inst *second,
                                                     const Loop *scope) const {
  const std::vector<const Loop *> left = loopNestFor(first);
  const std::vector<const Loop *> right = loopNestFor(second);
  std::vector<const Loop *> common;
  const usize limit = std::min(left.size(), right.size());
  for (usize index = 0; index < limit && left[index] == right[index]; ++index)
    common.push_back(left[index]);
  if (!scope)
    return common;
  const auto found = std::find(common.begin(), common.end(), scope);
  if (found == common.end())
    return {};
  common.erase(common.begin(), found);
  return common;
}

const AffineAccess &DependenceInfo::getAccess(Inst *memoryInst) const {
  const auto found = accessCache_.find(memoryInst);
  if (found != accessCache_.end())
    return found->second;
  VERIFY(scev_ && alias_);
  auto inserted = accessCache_.emplace(
      memoryInst, buildAffineAccess(*scev_, *alias_, budget_.access, memoryInst,
                                    loopNestFor(memoryInst)));
  return inserted.first->second;
}

ProgramOrder DependenceInfo::programOrder(Inst *first,
                                          Inst *second) const noexcept {
  if (!first || !second)
    return ProgramOrder::Unordered;
  if (first == second)
    return ProgramOrder::Same;
  BasicBlock *firstBlock = first->parentBlock();
  BasicBlock *secondBlock = second->parentBlock();
  if (!firstBlock || !secondBlock)
    return ProgramOrder::Unordered;
  if (firstBlock == secondBlock) {
    for (Inst *current = first; current; current = current->next())
      if (current == second)
        return ProgramOrder::Before;
    return ProgramOrder::After;
  }
  if (dominators_ && dominators_->dominates(firstBlock, secondBlock))
    return ProgramOrder::Before;
  if (dominators_ && dominators_->dominates(secondBlock, firstBlock))
    return ProgramOrder::After;
  return ProgramOrder::Unordered;
}

DependenceResult DependenceInfo::solvePair(Inst *sourceInst, Inst *sinkInst,
                                           const Loop *scope,
                                           ProgramOrder order,
                                           bool selfPair) const {
  const auto isMemory = [](const Inst *instruction) {
    return instruction &&
           (instruction->getOp() == OP_LOAD ||
            instruction->getOp() == OP_STORE) &&
           instruction->getOperandCount() != 0;
  };
  if (!isMemory(sourceInst) || !isMemory(sinkInst))
    return rejected(sourceInst, sinkInst, scope, DependenceKind::Input, order,
                    selfPair, DependenceRejectReason::InvalidAccess);
  const AffineAccess &source = getAccess(sourceInst);
  const AffineAccess &sink = getAccess(sinkInst);
  const DependenceKind kind = dependenceKind(source, sink);
  std::vector<const Loop *> nest = commonNest(sourceInst, sinkInst, scope);
  if (scope && (nest.empty() || nest.front() != scope))
    return rejected(sourceInst, sinkInst, scope, kind, order, selfPair,
                    DependenceRejectReason::ScopeMismatch);
  if (!selfPair && order == ProgramOrder::Unordered)
    return rejected(sourceInst, sinkInst, scope, kind, order, selfPair,
                    DependenceRejectReason::ProgramOrderUnknown, nest);

  const MemoryLocation sourceLocation =
      MemoryLocation::fromMemoryInstruction(sourceInst);
  const MemoryLocation sinkLocation =
      MemoryLocation::fromMemoryInstruction(sinkInst);
  const bool rootsEqual = sameRoot(source.bytes, sink.bytes);
  if ((!rootsEqual || (alias_->info(source.address).constantOffset &&
                       alias_->info(sink.address).constantOffset)) &&
      alias_->alias(sourceLocation, sinkLocation) == AliasResult::NoAlias) {
    DependenceResult result =
        rejected(sourceInst, sinkInst, scope, kind, order, selfPair,
                 DependenceRejectReason::None, nest);
    result.status = DependenceStatus::NoDependence;
    result.proof = DependenceProofKind::ObjectNoAlias;
    return result;
  }
  if (!rootsEqual)
    return rejected(sourceInst, sinkInst, scope, kind, order, selfPair,
                    DependenceRejectReason::MayAlias, nest);
  if (!source.exact() || !sink.exact())
    return rejected(sourceInst, sinkInst, scope, kind, order, selfPair,
                    accessReject(!source.exact() ? source.status : sink.status),
                    nest);
  if (source.widthBytes != sink.widthBytes)
    return rejected(sourceInst, sinkInst, scope, kind, order, selfPair,
                    DependenceRejectReason::UnsupportedWidth, nest);

  DependenceProblem problem;
  problem.tripCounts = tripCounts(nest, *scev_);
  problem.allowEqualIterations = !selfPair && order == ProgramOrder::Before;
  problem.maxDirectionDepth = budget_.maxDirectionDepth;

  DependenceSolution solution;
  bool usedStructured = compatibleShape(source, sink, *alias_);
  if (usedStructured) {
    std::vector<DependenceSolution> dimensions;
    dimensions.reserve(source.shape->indices.size());
    for (usize index = 0; index < source.shape->indices.size(); ++index) {
      DependenceProblem dimension = problem;
      if (!projectExpression(source.shape->indices[index],
                             sink.shape->indices[index], nest, dimension.source,
                             dimension.sink, dimension.localCoefficients)) {
        usedStructured = false;
        break;
      }
      dimensions.push_back(solveDependence(dimension));
      if (dimensions.back().status == DependenceStatus::Unknown) {
        usedStructured = false;
        break;
      }
      if (dimensions.back().status == DependenceStatus::NoDependence)
        break;
    }
    if (usedStructured)
      solution = intersectSolutions(dimensions, static_cast<u32>(nest.size()));
  }
  if (!usedStructured) {
    const AffineExpr sourceBytes = asAffineExpr(source.bytes);
    const AffineExpr sinkBytes = asAffineExpr(sink.bytes);
    if (!projectExpression(sourceBytes, sinkBytes, nest, problem.source,
                           problem.sink, problem.localCoefficients))
      return rejected(sourceInst, sinkInst, scope, kind, order, selfPair,
                      DependenceRejectReason::SymbolicTerm, nest);
    if (!scalarStartsCannotPartiallyOverlap(problem.source, problem.sink,
                                            problem.localCoefficients,
                                            source.widthBytes))
      return rejected(sourceInst, sinkInst, scope, kind, order, selfPair,
                      DependenceRejectReason::UnsupportedWidth, nest);
    solution = solveDependence(problem);
  }

  DependenceResult result =
      rejected(sourceInst, sinkInst, scope, kind, order, selfPair,
               solverReject(solution.failure), std::move(nest));
  result.status = solution.status;
  result.proof = solverProof(solution.proof);
  result.possible = std::move(solution.directions);
  result.distances = std::move(solution.distances);
  result.distanceMultiples = std::move(solution.distanceMultiples);
  return result;
}

DependenceResult DependenceInfo::dependence(Inst *source, Inst *sink,
                                            const Loop *scope,
                                            ProgramOrder order,
                                            bool selfPair) const {
  const PairKey key{source, sink, scope, order, selfPair};
  const auto found = pairCache_.find(key);
  if (found != pairCache_.end())
    return found->second;
  DependenceResult result = solvePair(source, sink, scope, order, selfPair);
  pairCache_.emplace(key, result);
  return result;
}

std::vector<DependenceResult>
DependenceInfo::getDependences(const Loop *scope, bool includeInput) const {
  std::vector<DependenceResult> result;
  if (!scope || !function_ || !function_->region)
    return result;

  std::vector<Inst *> accesses;
  bool opaqueCall = false;
  for (BasicBlock *block = function_->region->first; block;
       block = block->next()) {
    if (!scope->contains(block))
      continue;
    for (Inst *instruction = block->firstInst(); instruction;
         instruction = instruction->next()) {
      opaqueCall |= instruction->isCallInstruction();
      if (instruction->getOp() == OP_LOAD || instruction->getOp() == OP_STORE)
        accesses.push_back(instruction);
    }
  }
  if (opaqueCall) {
    result.push_back(rejected(nullptr, nullptr, scope, DependenceKind::Output,
                              ProgramOrder::Unordered, false,
                              DependenceRejectReason::OpaqueCall, {scope}));
    return result;
  }
  if (accesses.size() > budget_.maxAccessesPerLoop) {
    result.push_back(rejected(nullptr, nullptr, scope, DependenceKind::Output,
                              ProgramOrder::Unordered, false,
                              DependenceRejectReason::AccessBudgetExceeded,
                              {scope}));
    return result;
  }

  const u64 count = accesses.size();
  const u64 pairs = count * (count + 1U) / 2U;
  if (pairs > budget_.maxPairsPerLoop) {
    result.push_back(rejected(nullptr, nullptr, scope, DependenceKind::Output,
                              ProgramOrder::Unordered, false,
                              DependenceRejectReason::PairBudgetExceeded,
                              {scope}));
    return result;
  }

  for (usize first = 0; first < accesses.size(); ++first) {
    Inst *left = accesses[first];
    if (includeInput || left->getOp() == OP_STORE)
      result.push_back(dependence(left, left, scope, ProgramOrder::Same, true));
    for (usize second = first + 1; second < accesses.size(); ++second) {
      Inst *right = accesses[second];
      if (!includeInput && left->getOp() == OP_LOAD &&
          right->getOp() == OP_LOAD)
        continue;
      const ProgramOrder forward = programOrder(left, right);
      const ProgramOrder reverse =
          forward == ProgramOrder::Before  ? ProgramOrder::After
          : forward == ProgramOrder::After ? ProgramOrder::Before
                                           : ProgramOrder::Unordered;
      result.push_back(dependence(left, right, scope, forward, false));
      result.push_back(dependence(right, left, scope, reverse, false));
    }
  }
  return result;
}

} // namespace svm::ir
