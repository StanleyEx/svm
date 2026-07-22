#include "Alias.h"
#include "Analysis.h"
#include "Utils.h"

#include <limits>
#include <numeric>

namespace svm::ir {

namespace {

std::optional<i64> usableAccessSize(const MemoryLocation &location) noexcept {
  if (!location.accessSize || *location.accessSize == 0 ||
      *location.accessSize > static_cast<u64>(std::numeric_limits<i64>::max()))
    return std::nullopt;
  return static_cast<i64>(*location.accessSize);
}

bool isSelfDerivedPhiIncoming(Inst *incoming, Inst *phi) noexcept {
  Inst *current = incoming;
  for (u32 depth = 0; current && depth < 64; ++depth) {
    if (current == phi)
      return true;
    if (!isAddressingOp(current->getOp()) || current->getOperandCount() == 0)
      return false;
    current = current->getArg(0);
  }
  return false;
}

bool congruenceIntersectsClosedRange(i64 representative, u64 modulus, i64 low,
                                     i64 high) noexcept {
  VERIFY(modulus != 0 && low <= high);
  const u64 residue = normalizedModulo(representative, modulus);
  const u64 lowResidue = normalizedModulo(low, modulus);
  const u64 advance = residue >= lowResidue ? residue - lowResidue
                                            : modulus - (lowResidue - residue);
  const u64 span = static_cast<u64>(high) - static_cast<u64>(low);
  return advance <= span;
}

} // namespace

MemoryLocation
MemoryLocation::fromMemoryInstruction(Inst *instruction) noexcept {
  if (!instruction || instruction->getOperandCount() == 0 ||
      (instruction->getOp() != OP_LOAD && instruction->getOp() != OP_STORE))
    return {};

  const MemPayload &memory = instruction->getMem();
  if (memory.totalSizeBytes != 0)
    return {instruction->getArg(0), static_cast<u64>(memory.totalSizeBytes)};
  const i32 fallback = typeSizeBytes(memory.elementType);
  return {instruction->getArg(0),
          fallback > 0 ? std::optional<u64>(fallback) : std::nullopt};
}

void AliasInfo::build(Function *function, const SCEV *scev,
                      ModuleAnalysisManager *moduleAnalyses) {
  VERIFY(function);
  function_ = function;
  scev_ = scev;
  moduleAnalyses_ = moduleAnalyses;
  pointerInfo_.clear();
  conservative_ = false;

  u32 pointerCount = 0;
  for (u32 index = 0; index < function->paramCount; ++index)
    if (function->params[index] && isPtr(function->params[index]->getType()) &&
        pointerCount <= kMaxPointerCount)
      ++pointerCount;
  forEachInstRecursive(function->region, [&](Inst *instruction) {
    if (isPtr(instruction->getType()) && pointerCount <= kMaxPointerCount)
      ++pointerCount;
  });

  if (pointerCount > kMaxPointerCount) {
    conservative_ = true;
    return;
  }

  pointerInfo_.reserve(pointerCount);
  for (u32 index = 0; index < function->paramCount; ++index)
    if (function->params[index] && isPtr(function->params[index]->getType()))
      UNUSED(info(function->params[index]));
  forEachInstRecursive(function->region, [&](Inst *instruction) {
    if (isPtr(instruction->getType()))
      UNUSED(info(instruction));
  });
}

bool AliasInfo::sameRoot(const PointerInfo &left,
                         const PointerInfo &right) const noexcept {
  if (!left.root || !right.root || left.kind != right.kind)
    return false;
  if (left.root == right.root)
    return true;
  return left.kind == PointerKind::Global &&
         left.root->getOp() == OP_GETGLOBAL &&
         right.root->getOp() == OP_GETGLOBAL &&
         left.root->getGlobal() == right.root->getGlobal();
}

PointerInfo AliasInfo::info(Inst *pointer) const {
  if (!pointer)
    return {};
  if (conservative_)
    return {PointerKind::Opaque, pointer, std::nullopt, std::nullopt};
  const auto found = pointerInfo_.find(pointer);
  if (found != pointerInfo_.end())
    return found->second;

  pointerInfo_.emplace(pointer, PointerInfo{PointerKind::Opaque, pointer,
                                            std::nullopt, std::nullopt});
  PointerInfo result = computePointerInfo(pointer);
  pointerInfo_[pointer] = result;
  return result;
}

bool AliasInfo::isDereferenceable(const MemoryLocation &location,
                                  const AliasQuery &query) const {
  const std::optional<i64> accessSize = usableAccessSize(location);
  if (!location.pointer || !accessSize)
    return false;

  const PointerInfo pointer = info(location.pointer);
  if ((pointer.kind != PointerKind::Alloca &&
       pointer.kind != PointerKind::Global) ||
      !pointer.root || !pointer.objectSize ||
      *pointer.objectSize < static_cast<u64>(*accessSize))
    return false;

  i64 minimumOffset = 0;
  i64 maximumOffset = 0;
  if (pointer.constantOffset) {
    minimumOffset = maximumOffset = *pointer.constantOffset;
  } else {
    if (!query.allowSCEV || !scev_)
      return false;
    MathQuery mathQuery;
    mathQuery.contextBlock = query.contextBlock;
    mathQuery.predicateContext = query.predicateContext;
    const MathBounds bounds =
        scev_->getSignedDeltaBounds(scev_->getSCEV(location.pointer),
                                    scev_->getSCEV(pointer.root), mathQuery);
    if (!bounds.valid)
      return false;
    minimumOffset = bounds.min;
    maximumOffset = bounds.max;
  }

  if (minimumOffset < 0 || maximumOffset < minimumOffset)
    return false;
  const u64 lastOffset = *pointer.objectSize - static_cast<u64>(*accessSize);
  return static_cast<u64>(maximumOffset) <= lastOffset;
}

PointerInfo AliasInfo::computePointerInfo(Inst *pointer) const {
  VERIFY(pointer);
  switch (pointer->getOp()) {
  case OP_ALLOCA: {
    const u32 size = pointer->getMem().totalSizeBytes;
    return {PointerKind::Alloca, pointer, 0,
            size == 0 ? std::nullopt
                      : std::optional<u64>(static_cast<u64>(size))};
  }
  case OP_GETGLOBAL: {
    Global *global = pointer->getGlobal();
    if (!global)
      return {PointerKind::Opaque, pointer, std::nullopt, std::nullopt};
    return {PointerKind::Global, pointer, 0,
            global->totalSizeBytes != 0
                ? std::optional<u64>(global->totalSizeBytes)
                : std::nullopt};
  }
  case OP_PARAM:
    if (isPtr(pointer->getType()))
      return {PointerKind::Param, pointer, 0, std::nullopt};
    return {PointerKind::Opaque, pointer, std::nullopt, std::nullopt};
  case OP_GETPTR: {
    if (pointer->getOperandCount() != 2)
      return {PointerKind::Opaque, pointer, std::nullopt, std::nullopt};
    PointerInfo result = info(pointer->getArg(0));
    Inst *index = pointer->getArg(1);
    if (!result.constantOffset || !index || index->getOp() != OP_ICONST) {
      result.constantOffset = std::nullopt;
      return result;
    }
    i64 scaled = 0;
    i64 offset = 0;
    if (!checkedMul(index->getImm(), pointer->getStride(), scaled) ||
        !checkedAdd(*result.constantOffset, scaled, offset)) {
      result.constantOffset = std::nullopt;
      return result;
    }
    result.constantOffset = offset;
    return result;
  }
  case OP_ARRAYIDX: {
    if (pointer->getOperandCount() == 0)
      return {PointerKind::Opaque, pointer, std::nullopt, std::nullopt};
    PointerInfo result = info(pointer->getArg(0));
    const ArrayPayload &array = pointer->getArray();
    if (!result.constantOffset ||
        array.nDims + 1 != pointer->getOperandCount() ||
        (array.nDims != 0 && !array.strides)) {
      result.constantOffset = std::nullopt;
      return result;
    }

    i64 offset = *result.constantOffset;
    for (u32 index = 0; index < array.nDims; ++index) {
      Inst *subscript = pointer->getArg(index + 1);
      i64 scaled = 0;
      if (!subscript || subscript->getOp() != OP_ICONST ||
          !checkedMul(subscript->getImm(), array.strides[index], scaled) ||
          !checkedAdd(offset, scaled, offset)) {
        result.constantOffset = std::nullopt;
        return result;
      }
    }
    result.constantOffset = offset;
    return result;
  }
  case OP_PHI: {
    PointerInfo common;
    bool hasIncoming = false;
    bool constantOffsetAgrees = true;
    bool skippedSelfDerived = false;
    for (u32 index = 0; index < pointer->getOperandCount(); ++index) {
      Inst *incoming = pointer->getArg(index);
      if (!incoming || incoming == pointer ||
          isSelfDerivedPhiIncoming(incoming, pointer)) {
        skippedSelfDerived = skippedSelfDerived || incoming != nullptr;
        continue;
      }
      PointerInfo incomingInfo = info(incoming);
      if (!hasIncoming) {
        common = incomingInfo;
        hasIncoming = true;
        continue;
      }
      if (!sameRoot(common, incomingInfo))
        return {PointerKind::Opaque, pointer, std::nullopt, std::nullopt};
      constantOffsetAgrees =
          constantOffsetAgrees &&
          common.constantOffset == incomingInfo.constantOffset;
    }
    if (!hasIncoming || common.kind == PointerKind::Opaque)
      return {PointerKind::Opaque, pointer, std::nullopt, std::nullopt};
    if (skippedSelfDerived || !constantOffsetAgrees)
      common.constantOffset = std::nullopt;
    return common;
  }
  case OP_SELECT: {
    if (pointer->getOperandCount() != 3)
      return {PointerKind::Opaque, pointer, std::nullopt, std::nullopt};
    PointerInfo trueInfo = info(pointer->getArg(1));
    PointerInfo falseInfo = info(pointer->getArg(2));
    if (trueInfo.kind == PointerKind::Opaque || !sameRoot(trueInfo, falseInfo))
      return {PointerKind::Opaque, pointer, std::nullopt, std::nullopt};
    if (trueInfo.constantOffset != falseInfo.constantOffset)
      trueInfo.constantOffset = std::nullopt;
    return trueInfo;
  }
  default:
    return {PointerKind::Opaque, pointer, std::nullopt, std::nullopt};
  }
}

AliasResult AliasInfo::alias(Inst *left, Inst *right,
                             const AliasQuery &query) const {
  if (!left || !right || conservative_)
    return AliasResult::MayAlias;
  if (left == right)
    return AliasResult::MustAlias;
  return alias({left, std::nullopt}, {right, std::nullopt}, query);
}

AliasResult AliasInfo::alias(const MemoryLocation &left,
                             const MemoryLocation &right,
                             const AliasQuery &query) const {
  if (!left.pointer || !right.pointer)
    return AliasResult::MayAlias;
  if (conservative_)
    return AliasResult::MayAlias;
  if (left.pointer == right.pointer && left.accessSize && right.accessSize &&
      *left.accessSize != 0 && left.accessSize == right.accessSize)
    return AliasResult::MustAlias;

  const PointerInfo leftInfo = info(left.pointer);
  const PointerInfo rightInfo = info(right.pointer);
  const bool rootsEqual = sameRoot(leftInfo, rightInfo);

  if (rootsEqual && leftInfo.kind != PointerKind::Opaque) {
    if (leftInfo.constantOffset && rightInfo.constantOffset) {
      const std::optional<i64> leftSize = usableAccessSize(left);
      const std::optional<i64> rightSize = usableAccessSize(right);
      if (!leftSize || !rightSize)
        return AliasResult::MayAlias;
      if (*leftInfo.constantOffset == *rightInfo.constantOffset)
        return *leftSize == *rightSize ? AliasResult::MustAlias
                                       : AliasResult::PartialAlias;

      i64 leftEnd = 0;
      i64 rightEnd = 0;
      if (!checkedAdd(*leftInfo.constantOffset, *leftSize, leftEnd) ||
          !checkedAdd(*rightInfo.constantOffset, *rightSize, rightEnd))
        return AliasResult::MayAlias;
      if (leftEnd <= *rightInfo.constantOffset ||
          rightEnd <= *leftInfo.constantOffset)
        return AliasResult::NoAlias;
      return AliasResult::PartialAlias;
    }

    if (proveNoAliasWithSCEV(left, right, leftInfo, rightInfo, query))
      return AliasResult::NoAlias;
    return AliasResult::MayAlias;
  }

  if (leftInfo.kind == PointerKind::Opaque ||
      rightInfo.kind == PointerKind::Opaque)
    return AliasResult::MayAlias;
  if (leftInfo.kind == PointerKind::Alloca &&
      rightInfo.kind == PointerKind::Alloca)
    return AliasResult::NoAlias;
  if (leftInfo.kind == PointerKind::Global &&
      rightInfo.kind == PointerKind::Global)
    return AliasResult::NoAlias;
  if ((leftInfo.kind == PointerKind::Alloca &&
       rightInfo.kind == PointerKind::Global) ||
      (leftInfo.kind == PointerKind::Global &&
       rightInfo.kind == PointerKind::Alloca))
    return AliasResult::NoAlias;
  if ((leftInfo.kind == PointerKind::Alloca &&
       rightInfo.kind == PointerKind::Param) ||
      (leftInfo.kind == PointerKind::Param &&
       rightInfo.kind == PointerKind::Alloca))
    return AliasResult::NoAlias;
  return AliasResult::MayAlias;
}

bool AliasInfo::proveNoAliasWithSCEV(const MemoryLocation &left,
                                     const MemoryLocation &right,
                                     const PointerInfo &leftInfo,
                                     const PointerInfo &rightInfo,
                                     const AliasQuery &query) const {
  if (!query.allowSCEV || !scev_ || !sameRoot(leftInfo, rightInfo))
    return false;
  const std::optional<i64> leftSize = usableAccessSize(left);
  const std::optional<i64> rightSize = usableAccessSize(right);
  if (!leftSize || !rightSize)
    return false;

  SCEVExpr *leftExpr = scev_->getSCEV(left.pointer);
  SCEVExpr *rightExpr = scev_->getSCEV(right.pointer);
  MathQuery mathQuery;
  mathQuery.contextBlock = query.contextBlock;
  mathQuery.predicateContext = query.predicateContext;

  struct AddRecView {
    SCEVExpr *recurrence = nullptr; // 提取出的唯一循环递推
    SCEVExpr *base = nullptr;       // 合入顶层不变量后的零迭代基址
  };
  const auto extractAddRec = [&](SCEVExpr *expression) -> AddRecView {
    if (!expression)
      return {};
    if (expression->kind == SCEVExpr::K_ADDREC)
      return {expression, expression->addRec.base};
    if (expression->kind != SCEVExpr::K_ADD)
      return {};

    SCEVExpr *recurrence = nullptr;
    for (SCEVExpr *operand : expression->nary.ops) {
      if (operand->kind != SCEVExpr::K_ADDREC)
        continue;
      if (recurrence)
        return {};
      recurrence = operand;
    }
    if (!recurrence)
      return {};

    SCEVExpr *base = recurrence->addRec.base;
    for (SCEVExpr *operand : expression->nary.ops) {
      if (operand == recurrence)
        continue;
      if (!operand->isLoopInvariant(recurrence->addRec.loop))
        return {};
      base = scev_->getAddExpr(base, operand);
    }
    return {recurrence, base};
  };

  const AddRecView leftRec = extractAddRec(leftExpr);
  const AddRecView rightRec = extractAddRec(rightExpr);
  const auto hasNoWrapProof = [&](const AddRecView &view) {
    if (!view.recurrence)
      return false;
    if (view.recurrence->nsw)
      return true;
    // 指针AddRec的未知绝对基址不具备i32 range
    // 相对初值的数学delta仍可独立证明其字节偏移递推不回绕
    return scev_
        ->getSignedDeltaBounds(view.recurrence, view.recurrence->addRec.base,
                               mathQuery)
        .valid;
  };
  if (leftRec.recurrence && rightRec.recurrence &&
      leftRec.recurrence->addRec.loop == rightRec.recurrence->addRec.loop &&
      hasNoWrapProof(leftRec) && hasNoWrapProof(rightRec) &&
      leftRec.recurrence->addRec.step->isConstant() &&
      rightRec.recurrence->addRec.step->isConstant()) {
    const i64 leftStep = leftRec.recurrence->addRec.step->cst.v;
    const i64 rightStep = rightRec.recurrence->addRec.step->cst.v;
    if (leftStep != 0 && rightStep != 0) {
      const u64 divisor =
          std::gcd(unsignedMagnitude(leftStep), unsignedMagnitude(rightStep));
      VERIFY(divisor != 0);
      const MathBounds baseDelta =
          scev_->getSignedDeltaBounds(rightRec.base, leftRec.base, mathQuery);
      if (baseDelta.valid && baseDelta.min == baseDelta.max) {
        const i64 overlapLow = -(*rightSize - 1);
        const i64 overlapHigh = *leftSize - 1;
        if (!congruenceIntersectsClosedRange(baseDelta.min, divisor, overlapLow,
                                             overlapHigh))
          return true;
      }
    }
  }

  if (leftInfo.root && rightInfo.root) {
    const MathBounds leftOffset = scev_->getSignedDeltaBounds(
        leftExpr, scev_->getSCEV(leftInfo.root), mathQuery);
    const MathBounds rightOffset = scev_->getSignedDeltaBounds(
        rightExpr, scev_->getSCEV(rightInfo.root), mathQuery);
    if (leftOffset.valid && rightOffset.valid) {
      i64 leftEnd = 0;
      if (checkedAdd(leftOffset.max, *leftSize, leftEnd) &&
          leftEnd <= rightOffset.min)
        return true;
      i64 rightEnd = 0;
      if (checkedAdd(rightOffset.max, *rightSize, rightEnd) &&
          rightEnd <= leftOffset.min)
        return true;
    }
  }

  const MathBounds delta =
      scev_->getSignedDeltaBounds(rightExpr, leftExpr, mathQuery);
  if (!delta.valid)
    return false;
  return delta.min >= *leftSize || delta.max <= -*rightSize;
}

bool AliasInfo::mayOverlapForStoreElim(const MemoryLocation &writer,
                                       const MemoryLocation &reader) const {
  AliasQuery query;
  query.allowSCEV = false;
  return alias(writer, reader, query) != AliasResult::NoAlias;
}

bool AliasInfo::mayOverlapForStoreElim(Inst *writer, Inst *reader) const {
  return mayOverlapForStoreElim({writer, std::nullopt}, {reader, std::nullopt});
}

bool AliasInfo::fullyCovers(const MemoryLocation &covering,
                            const MemoryLocation &covered) const {
  if (!covering.pointer || !covered.pointer)
    return false;
  const std::optional<i64> coveringSize = usableAccessSize(covering);
  const std::optional<i64> coveredSize = usableAccessSize(covered);
  if (!coveringSize || !coveredSize)
    return false;
  if (covering.pointer == covered.pointer)
    return *coveringSize >= *coveredSize;
  if (conservative_)
    return false;
  const PointerInfo coveringInfo = info(covering.pointer);
  const PointerInfo coveredInfo = info(covered.pointer);
  if (coveringInfo.kind == PointerKind::Opaque ||
      !sameRoot(coveringInfo, coveredInfo) || !coveringInfo.constantOffset ||
      !coveredInfo.constantOffset ||
      *coveringInfo.constantOffset > *coveredInfo.constantOffset)
    return false;

  i64 coveringEnd = 0;
  i64 coveredEnd = 0;
  return checkedAdd(*coveringInfo.constantOffset, *coveringSize, coveringEnd) &&
         checkedAdd(*coveredInfo.constantOffset, *coveredSize, coveredEnd) &&
         coveringEnd >= coveredEnd;
}

bool AliasInfo::isNoAliasWithLocals(Inst *pointer) const {
  if (!pointer || conservative_)
    return false;
  const PointerInfo pointerInfo = info(pointer);
  return pointerInfo.kind == PointerKind::Param ||
         pointerInfo.kind == PointerKind::Global;
}

bool AliasInfo::mayAccessMemoryWithIPA(Inst *call,
                                       const MemoryLocation &location,
                                       const EffectSummary &effects,
                                       const AliasQuery &query,
                                       bool writes) const {
  if (!call || !call->isCallInstruction())
    return false;
  if (writes ? effects.writesNoMemory() : effects.readsNoMemory())
    return false;
  if (call->getOp() == MOP_CALL)
    return true;
  if (!location.pointer)
    return true;

  const PointerInfo pointerInfo = info(location.pointer);
  if (pointerInfo.kind == PointerKind::Global && pointerInfo.root &&
      pointerInfo.root->getOp() == OP_GETGLOBAL) {
    Global *global = pointerInfo.root->getGlobal();
    const u8 noGlobalFlag = writes ? EffectSummary::F_NO_WRITE_GLOBAL
                                   : EffectSummary::F_NO_READ_GLOBAL;
    if (!(effects.flags & noGlobalFlag) &&
        (writes ? effects.writesGlobal(global) : effects.readsGlobal(global)))
      return true;
  } else if (pointerInfo.kind != PointerKind::Alloca) {
    return true;
  }

  for (u32 index = 0; index < call->getOperandCount(); ++index) {
    Inst *actual = call->getArg(index);
    if (!actual || !isPtr(actual->getType()))
      continue;
    const bool affected = writes ? effects.writesParam(static_cast<i32>(index))
                                 : effects.readsParam(static_cast<i32>(index));
    if (!affected)
      continue;
    if (alias({actual, std::nullopt}, location, query) != AliasResult::NoAlias)
      return true;
  }
  return false;
}

bool AliasInfo::mayReadMemory(Inst *call, const MemoryLocation &location,
                              const AliasQuery &query) const {
  if (!call || !call->isCallInstruction())
    return false;
  if (!moduleAnalyses_ || !function_ || !function_->module)
    return true;
  const auto &summary =
      moduleAnalyses_->getResult<GlobalSummaryAnalysis>(function_->module)
          .result;
  return mayReadMemory(call, location,
                       summary.calleeEffect(call ? call->getCallee() : nullptr),
                       query);
}

bool AliasInfo::mayWriteMemory(Inst *call, const MemoryLocation &location,
                               const AliasQuery &query) const {
  if (!call || !call->isCallInstruction())
    return false;
  if (!moduleAnalyses_ || !function_ || !function_->module)
    return true;
  const auto &summary =
      moduleAnalyses_->getResult<GlobalSummaryAnalysis>(function_->module)
          .result;
  return mayWriteMemory(
      call, location, summary.calleeEffect(call ? call->getCallee() : nullptr),
      query);
}

} // namespace svm::ir
