#include "Analysis.h"
#include "DeepCopy.h"
#include "DependenceAnalysis.h"
#include "IR.h"
#include "LIRPass.h"
#include "LoopShape.h"
#include "PressureOracle.h"
#include "Utils.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <memory>
#include <optional>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

constexpr u32 kMaxSupportedJamDepth = 6;

u32 allowedUnrollAndJamDepth(const DependenceResult &dependence,
                             const Loop *outer, const Loop *inner,
                             i32 factor) noexcept;

struct PrivatePhiGroup {
  Inst *source = nullptr;       // lane 0的原Phi
  std::vector<Inst *> lanePhis; // lane 1..U-1的私有Phi
};

struct ExitRelay {
  Inst *exitPhi = nullptr;     // 原外层exit Phi
  Inst *mainRelay = nullptr;   // 主循环无余数路径的relay Phi
  Inst *sourceValue = nullptr; // 原outer latch incoming
};

struct UAJPlan {
  CountedLoopShape outer;                    // 被展开的外层循环
  CountedLoopShape inner;                    // 被融合的直接子循环
  std::vector<BasicBlock *> outerBlocks;     // 布局顺序的完整外层块集
  std::vector<BasicBlock *> innerBlocks;     // 布局顺序的完整内层块集
  std::vector<Inst *> preInstructions;       // outer header待复制体
  std::vector<Inst *> innerPreInstructions;  // inner preheader待复制体
  std::vector<Inst *> innerPostInstructions; // inner exit待复制体
  std::vector<Inst *> postInstructions;      // outer latch待复制体
  std::vector<Inst *> singleBlockInnerBody;  // 单块inner待复制体
  std::unique_ptr<UAJPlan> nested;           // 下一层single-child融合计划
  SCEVExpr *trip = nullptr;                  // 原外层循环的精确trip
  i32 factor = 0;                            // 展开因子
  i32 estimatedAddedInstructions = 0;        // projected lowering后增长
  i32 estimatedGPR = 0;                      // projected峰值GPR
  i64 reuseScore = 0;                        // outer-invariant load收益
};

bool isPlainJump(BasicBlock *block, BasicBlock *target) noexcept {
  Inst *terminator = block ? block->terminator() : nullptr;
  return terminator && terminator->getOp() == OP_JMP &&
         terminator->getJumpTarget() == target;
}

bool hasStrictFloatWork(const Loop *loop) noexcept {
  for (BasicBlock *block : loop->blocks()) {
    bool found = false;
    forEachOp(block, [&](Inst *instruction) {
      if (found)
        return;
      const OpCode op = instruction->getOp();
      found = instruction->getType() == TY_F32 || isFloatArithmetic(op) ||
              isFloatCompare(op) || op == OP_I2F || op == OP_F2I ||
              ((op == OP_LOAD || op == OP_STORE) &&
               instruction->getMem().elementType == TY_F32);
      for (u32 index = 0; !found && index < instruction->getOperandCount();
           ++index)
        found = instruction->getArg(index) &&
                instruction->getArg(index)->getType() == TY_F32;
    });
    if (found)
      return true;
  }
  return false;
}

bool hasUnsupportedEffect(const Loop *loop) noexcept {
  for (BasicBlock *block : loop->blocks())
    for (Inst *instruction = block->firstInst(); instruction;
         instruction = instruction->next())
      if (instruction->isCallInstruction() || instruction->getOp() == OP_ALLOCA)
        return true;
  return false;
}

bool coefficientFor(const AffineAccess &access, const Loop *loop,
                    i64 &coefficient) noexcept {
  coefficient = 0;
  for (const LoopCoefficient &term : access.bytes.loops)
    if (term.loop == loop &&
        !checkedAdd(coefficient, term.coefficient, coefficient))
      return false;
  return true;
}

bool collectBefore(Inst *end, std::vector<Inst *> &instructions) {
  BasicBlock *block = end ? end->parentBlock() : nullptr;
  if (!block)
    return false;
  instructions.clear();
  for (Inst *instruction = block->firstInst();
       instruction && instruction != end; instruction = instruction->next()) {
    if (isTerminator(instruction->getOp()))
      return false;
    instructions.push_back(instruction);
  }
  return end->parentBlock() == block;
}

bool onlyControlAfterStep(const CountedLoopShape &shape) noexcept {
  if (!shape.iv.stepInst || !shape.latchTest.comparison ||
      shape.iv.stepInst->parentBlock() != shape.latch ||
      shape.latchTest.comparison->parentBlock() != shape.latch)
    return false;
  bool sawStep = false;
  bool sawComparison = false;
  for (Inst *instruction = shape.latch->firstInst(); instruction;
       instruction = instruction->next()) {
    if (instruction == shape.iv.stepInst) {
      sawStep = true;
      continue;
    }
    if (!sawStep)
      continue;
    if (instruction == shape.latchTest.comparison) {
      sawComparison = true;
      continue;
    }
    if (!isTerminator(instruction->getOp()))
      return false;
  }
  return sawStep && sawComparison;
}

bool branchEntersInner(const UAJPlan &plan) noexcept {
  Inst *terminator = plan.outer.header->terminator();
  BasicBlock *entry = plan.inner.preheader == plan.outer.header
                          ? plan.inner.header
                          : plan.inner.preheader;
  return terminator && terminator->getOp() == OP_JMP &&
         terminator->getJumpTarget() == entry;
}

bool hasExpectedBlocks(const UAJPlan &plan) {
  std::unordered_set<BasicBlock *> expected(plan.inner.loop->blocks().begin(),
                                            plan.inner.loop->blocks().end());
  expected.insert(plan.outer.header);
  expected.insert(plan.outer.latch);
  expected.insert(plan.inner.preheader);
  expected.insert(plan.inner.exit);
  if (expected.size() != plan.outer.loop->blocks().size())
    return false;
  for (BasicBlock *block : plan.outer.loop->blocks())
    if (!expected.count(block))
      return false;
  return true;
}

bool isStrictShape(const CountedLoopShape &shape) noexcept {
  const OpCode expected = shape.iv.step > 0 ? OP_LT : OP_GT;
  return shape.iv.step != 0 && shape.latchTest.canonicalPredicate == expected &&
         shape.latchTest.continueOnTrue &&
         shape.loop->exitingBlocks().size() == 1 &&
         shape.loop->exitingBlocks().front() == shape.latch &&
         shape.latchTest.comparison->parentBlock() == shape.latch &&
         shape.iv.stepConstant && !shape.iv.stepConstant->isUndefValue() &&
         onlyControlAfterStep(shape);
}

bool recognizeNest(Function *function, const CountedLoopShape &outer,
                   const CountedLoopShape &inner, const Loop *root,
                   bool requireSingleOuterPhi, UAJPlan &plan) {
  if (!function || !outer.loop || !inner.loop || !root ||
      inner.loop->parent() != outer.loop ||
      outer.loop->children().size() != 1 ||
      outer.loop->children().front() != inner.loop ||
      outer.header == outer.latch ||
      (requireSingleOuterPhi && (outer.headerPhis.size() != 1 ||
                                 !outer.headerPhis.front().isControlIV)) ||
      !isStrictShape(outer) || !isStrictShape(inner) ||
      !isPlainJump(outer.preheader, outer.header) ||
      (inner.preheader != outer.header &&
       !isPlainJump(inner.preheader, inner.header)) ||
      (inner.exit != outer.latch && !isPlainJump(inner.exit, outer.latch)) ||
      hasUnsupportedEffect(outer.loop) || hasStrictFloatWork(outer.loop))
    return false;

  plan.outer = outer;
  plan.inner = inner;
  if (!branchEntersInner(plan) || !hasExpectedBlocks(plan) ||
      !inner.iv.baseSCEV || !inner.latchTest.boundSCEV ||
      !inner.iv.baseSCEV->isLoopInvariant(root) ||
      !inner.latchTest.boundSCEV->isLoopInvariant(root))
    return false;

  for (const HeaderPhiShape &headerPhi : outer.headerPhis)
    if (!headerPhi.isControlIV && headerPhi.phi->getType() != TY_I32)
      return false;

  for (const HeaderPhiShape &headerPhi : inner.headerPhis)
    if (!headerPhi.isControlIV && headerPhi.phi->getType() != TY_I32)
      return false;
  if (!collectBefore(outer.header->terminator(), plan.preInstructions) ||
      !collectBefore(outer.iv.stepInst, plan.postInstructions))
    return false;
  if (inner.preheader != outer.header) {
    for (Inst *phi = inner.preheader->firstPhi(); phi; phi = phi->next())
      if (phi->getOperandCount() != 1 ||
          phi->getIncomingBlock(0) != outer.header)
        return false;
    if (!collectBefore(inner.preheader->terminator(),
                       plan.innerPreInstructions))
      return false;
  }
  if (inner.exit != outer.latch &&
      !collectBefore(inner.exit->terminator(), plan.innerPostInstructions))
    return false;
  if (inner.header == inner.latch &&
      !collectBefore(inner.iv.stepInst, plan.singleBlockInnerBody))
    return false;
  for (Inst *phi = inner.exit->firstPhi(); phi; phi = phi->next())
    if (!CFGEditor::getPhiIncomingValue(phi, inner.latch))
      return false;
  for (Inst *phi = outer.exit->firstPhi(); phi; phi = phi->next())
    if (!CFGEditor::getPhiIncomingValue(phi, outer.latch))
      return false;

  plan.outerBlocks.clear();
  plan.innerBlocks.clear();
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (outer.loop->contains(block))
      plan.outerBlocks.push_back(block);
    if (inner.loop->contains(block))
      plan.innerBlocks.push_back(block);
  }
  return !plan.outerBlocks.empty() &&
         plan.outerBlocks.front() == outer.header &&
         plan.outerBlocks.size() == outer.loop->blocks().size() &&
         plan.innerBlocks.size() == inner.loop->blocks().size() &&
         DeepCopy::canAddTranslatedExitPhiIncomings(function, plan.outerBlocks);
}

bool recognizeChain(Function *function, const LoopShapeInfo &shapes,
                    const LoopShapeQuery &query, const CountedLoopShape &outer,
                    const Loop *root, u32 remainingDepth,
                    bool requireSingleOuterPhi, UAJPlan &plan) {
  if (remainingDepth == 0 || outer.loop->children().size() != 1)
    return false;
  Loop *innerLoop = outer.loop->children().front();
  const std::optional<CountedLoopShape> inner =
      shapes.getCountedLoop(innerLoop, query);
  if (!inner || !recognizeNest(function, outer, *inner, root,
                               requireSingleOuterPhi, plan))
    return false;

  if (remainingDepth > 1 && innerLoop->children().size() == 1) {
    auto nested = std::make_unique<UAJPlan>();
    if (recognizeChain(function, shapes, query, *inner, root,
                       remainingDepth - 1, false, *nested))
      plan.nested = std::move(nested);
  }
  return true;
}

i32 saturatingCost(i64 value) noexcept {
  return static_cast<i32>(std::clamp(
      value, i64{0}, static_cast<i64>(std::numeric_limits<i32>::max())));
}

u32 fusedDepth(const UAJPlan &plan) noexcept {
  u32 depth = 0;
  for (const UAJPlan *level = &plan; level; level = level->nested.get())
    ++depth;
  return depth;
}

i32 projectedNestCost(const UAJPlan &plan) noexcept {
  i64 cost = 0;
  for (BasicBlock *block : plan.outerBlocks) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      ++cost;
    for (Inst *instruction = block->firstInst(); instruction;
         instruction = instruction->next())
      cost += estimateArrayIndexLoweringCost(instruction).instructions;
  }
  return saturatingCost(cost);
}

bool hasDynamicDivMod(const UAJPlan &plan) noexcept {
  for (BasicBlock *block : plan.outerBlocks)
    for (Inst *instruction = block->firstInst(); instruction;
         instruction = instruction->next()) {
      const OpCode op = instruction->getOp();
      if (op != OP_DIV && op != OP_MOD)
        continue;
      Inst *divisor =
          instruction->getOperandCount() > 1 ? instruction->getArg(1) : nullptr;
      if (!divisor || divisor->getOp() != OP_ICONST)
        return true;
    }
  return false;
}

bool sameReuseOrigin(const AffineAccess &left, const AffineAccess &right,
                     const Loop *outer) noexcept {
  if (!outer || left.bytes.root != right.bytes.root ||
      left.widthBytes != right.widthBytes)
    return false;
  for (const LoopCoefficient &term : left.bytes.loops) {
    if (!outer->containsLoop(term.loop))
      continue;
    i64 leftCoefficient = 0;
    i64 rightCoefficient = 0;
    if (!coefficientFor(left, term.loop, leftCoefficient) ||
        !coefficientFor(right, term.loop, rightCoefficient) ||
        leftCoefficient != rightCoefficient)
      return false;
  }
  for (const LoopCoefficient &term : right.bytes.loops) {
    if (!outer->containsLoop(term.loop))
      continue;
    i64 leftCoefficient = 0;
    i64 rightCoefficient = 0;
    if (!coefficientFor(left, term.loop, leftCoefficient) ||
        !coefficientFor(right, term.loop, rightCoefficient) ||
        leftCoefficient != rightCoefficient)
      return false;
  }
  return true;
}

void emitUAJRemark(DiagnosticEngine *diagnostics, bool enabled,
                   const Function *function, const BasicBlock *origin,
                   i32 factor, u32 depth, const char *decision,
                   const char *stage, i64 reuse, i32 pressure) {
  if (!enabled || !diagnostics)
    return;
  SVM_NOTE(*diagnostics, SourceLocation{},
           "[UAJ] function=%s origin=bb%u factor=%d depth=%u decision=%s "
           "stage=%s reuse=%lld projected-gpr=%d",
           function && function->name ? function->name : "<anonymous>",
           origin ? origin->id : 0, factor, depth, decision, stage,
           static_cast<long long>(reuse), pressure);
}

bool proveMainBounds(const SCEV &scev, UAJPlan &plan, i32 factor) {
  if (factor <= 1 || !plan.outer.iv.baseSCEV || !plan.outer.latchTest.boundSCEV)
    return false;

  const i64 step = plan.outer.iv.step;
  const i64 magnitude = step > 0 ? step : -step;
  i64 scaledStep = 0;
  if (magnitude <= 0 ||
      !checkedMul(step, static_cast<i64>(factor), scaledStep) ||
      scaledStep < std::numeric_limits<i32>::min() ||
      scaledStep > std::numeric_limits<i32>::max())
    return false;

  SCEVExpr *zero = scev.getConstant(0, TY_I32);
  MathQuery query;
  query.contextBlock = plan.outer.preheader;
  SCEVExpr *start = plan.outer.iv.baseSCEV;
  SCEVExpr *stop = plan.outer.latchTest.boundSCEV;
  const MathBounds distanceBounds =
      step > 0 ? scev.getSignedDeltaBounds(stop, start, query)
               : scev.getSignedDeltaBounds(start, stop, query);
  const MathBounds stopBounds = scev.getSignedDeltaBounds(stop, zero, query);
  const i64 adjustment = magnitude - 1;
  i64 adjustedMaximum = 0;
  if (!distanceBounds.valid || !distanceBounds.proof.proven() ||
      distanceBounds.min <= 0 || !stopBounds.valid ||
      !stopBounds.proof.proven() ||
      !checkedAdd(distanceBounds.max, adjustment, adjustedMaximum) ||
      adjustedMaximum > std::numeric_limits<i32>::max() ||
      (step > 0 &&
       stopBounds.max > std::numeric_limits<i32>::max() - adjustment) ||
      (step < 0 &&
       stopBounds.min < std::numeric_limits<i32>::min() + adjustment) ||
      adjustedMaximum / magnitude < factor)
    return false;

  SCEVExpr *negative = scev.getConstant(-1, TY_I32);
  SCEVExpr *distance =
      step > 0 ? scev.getAddExpr(stop, scev.getMulExpr(start, negative))
               : scev.getAddExpr(start, scev.getMulExpr(stop, negative));
  SCEVExpr *numerator =
      adjustment == 0
          ? distance
          : scev.getAddExpr(distance, scev.getConstant(adjustment, TY_I32));
  plan.trip =
      magnitude == 1
          ? numerator
          : scev.getSDivExpr(numerator, scev.getConstant(magnitude, TY_I32));
  return scev.isSafeToExpand(plan.trip, plan.outer.preheader);
}

u32 dependenceLegalDepth(const CountedLoopShape &outer,
                         const CountedLoopShape &inner,
                         const std::vector<DependenceResult> &dependences,
                         i32 factor, u32 maximumDepth) {
  u32 depth = std::min(maximumDepth, kMaxSupportedJamDepth);
  for (const DependenceResult &dependence : dependences) {
    if (dependence.kind == DependenceKind::Input ||
        dependence.status == DependenceStatus::NoDependence)
      continue;
    depth = std::min(depth, allowedUnrollAndJamDepth(dependence, outer.loop,
                                                     inner.loop, factor));
    if (depth == 0)
      break;
  }
  return depth;
}

bool isNoClobberLoad(Inst *load,
                     const std::vector<DependenceResult> &dependences) {
  for (const DependenceResult &dependence : dependences) {
    if (dependence.source != load && dependence.sink != load)
      continue;
    Inst *other =
        dependence.source == load ? dependence.sink : dependence.source;
    if (other && other->getOp() == OP_STORE &&
        dependence.status != DependenceStatus::NoDependence)
      return false;
  }
  return true;
}

bool estimateReuse(UAJPlan &plan, const DependenceInfo &dependenceInfo,
                   const std::vector<DependenceResult> &dependences,
                   i32 minimumScore) {
  i64 score = 0;
  bool sawMemory = false;
  std::vector<const AffineAccess *> origins;
  for (BasicBlock *block : plan.outerBlocks) {
    for (Inst *instruction = block->firstInst(); instruction;
         instruction = instruction->next()) {
      if (instruction->getOp() != OP_LOAD && instruction->getOp() != OP_STORE)
        continue;
      sawMemory = true;
      const AffineAccess &access = dependenceInfo.getAccess(instruction);
      if (!access.exact())
        continue;
      if (instruction->getOp() != OP_LOAD || !plan.inner.loop->contains(block))
        continue;
      i64 outerCoefficient = 0;
      if (!coefficientFor(access, plan.outer.loop, outerCoefficient))
        return false;
      if (outerCoefficient != 0 || !isNoClobberLoad(instruction, dependences))
        continue;
      const bool duplicate =
          std::any_of(origins.begin(), origins.end(), [&](const auto *origin) {
            return sameReuseOrigin(access, *origin, plan.outer.loop);
          });
      if (duplicate)
        continue;
      origins.push_back(&access);
      const i64 innerWeight =
          plan.inner.constantTripCount > 0
              ? std::min<i64>(plan.inner.constantTripCount, i64{100000})
              : i64{10};
      i64 benefit = 0;
      if (!checkedMul(static_cast<i64>(plan.factor - 1), innerWeight,
                      benefit) ||
          !checkedAdd(score, benefit, score))
        return false;
    }
  }
  plan.reuseScore = score;
  return sawMemory && score >= minimumScore;
}

bool pressureAllowsFactor(UAJPlan &plan, const DependenceInfo &dependenceInfo,
                          i32 factor) {
  i64 laneValues = 0;
  std::unordered_set<Inst *> replicatedValues;
  for (const UAJPlan *level = &plan; level; level = level->nested.get()) {
    i32 headerPhis = 0;
    for (const HeaderPhiShape &phi : level->inner.headerPhis)
      headerPhis += !phi.isControlIV;
    i32 exitPhis = 0;
    for (Inst *phi = level->inner.exit->firstPhi(); phi; phi = phi->next())
      ++exitPhis;
    if (level->outer.latch != level->inner.exit)
      for (Inst *phi = level->outer.latch->firstPhi(); phi; phi = phi->next())
        ++exitPhis;
    laneValues += std::max(headerPhis, exitPhis);
    for (const std::vector<Inst *> *instructions :
         {&level->preInstructions, &level->innerPreInstructions}) {
      for (Inst *instruction : *instructions) {
        if (isVoid(instruction->getType()))
          continue;
        for (const Use *use = instruction->uses(); use; use = use->next) {
          BasicBlock *userBlock =
              use->user ? use->user->parentBlock() : nullptr;
          if (userBlock && level->inner.loop->contains(userBlock)) {
            if (replicatedValues.insert(instruction).second)
              ++laneValues;
            break;
          }
        }
      }
    }
  }

  std::vector<const AffineAccess *> pointerOrigins;
  i32 addressTemporaries = 0;
  for (BasicBlock *block : plan.outerBlocks)
    for (Inst *instruction = block->firstInst(); instruction;
         instruction = instruction->next()) {
      addressTemporaries =
          std::max(addressTemporaries,
                   estimateArrayIndexLoweringCost(instruction).temporaries);
      if (instruction->getOp() != OP_LOAD || !plan.inner.loop->contains(block))
        continue;
      const AffineAccess &access = dependenceInfo.getAccess(instruction);
      i64 outerCoefficient = 0;
      if (!access.exact() ||
          !coefficientFor(access, plan.outer.loop, outerCoefficient) ||
          outerCoefficient == 0)
        continue;
      const bool duplicate = std::any_of(
          pointerOrigins.begin(), pointerOrigins.end(),
          [&](const auto *origin) {
            return sameReuseOrigin(access, *origin, plan.outer.loop);
          });
      if (!duplicate) {
        pointerOrigins.push_back(&access);
        ++laneValues;
      }
    }

  i64 estimatedGPR = 5;
  i64 replicated = 0;
  if (!checkedMul(laneValues, static_cast<i64>(factor), replicated) ||
      !checkedAdd(estimatedGPR, replicated, estimatedGPR) ||
      !checkedAdd(estimatedGPR, static_cast<i64>(factor - 1), estimatedGPR) ||
      !checkedAdd(estimatedGPR, static_cast<i64>(addressTemporaries),
                  estimatedGPR)) {
    plan.estimatedGPR = std::numeric_limits<i32>::max();
    return false;
  }
  plan.estimatedGPR = saturatingCost(estimatedGPR);
  return estimatedGPR <= 18;
}

std::vector<PrivatePhiGroup>
createPrivatePhis(Function *function, IRBuilder &builder, BasicBlock *block,
                  const std::vector<Inst *> &sources,
                  std::vector<std::unique_ptr<DeepCopy>> &lanes) {
  std::vector<PrivatePhiGroup> result;
  result.reserve(sources.size());
  for (Inst *source : sources) {
    PrivatePhiGroup group;
    group.source = source;
    for (usize lane = 0; lane < lanes.size(); ++lane) {
      Inst *phi = builder.emitPhi(source->getType(), block,
                                  builder.makeUndef(source->getType()));
      group.lanePhis.push_back(phi);
      lanes[lane]->mapInst(source, phi);
    }
    result.push_back(std::move(group));
  }
  for (const PrivatePhiGroup &group : result)
    for (Inst *phi : group.lanePhis)
      for (const std::unique_ptr<DeepCopy> &lane : lanes)
        lane->mapInst(phi, phi);
  UNUSED(function);
  return result;
}

void fillPrivatePhis(Function *function,
                     const std::vector<PrivatePhiGroup> &groups,
                     const std::vector<std::unique_ptr<DeepCopy>> &lanes) {
  for (const PrivatePhiGroup &group : groups)
    for (usize lane = 0; lane < lanes.size(); ++lane)
      for (u32 index = 0; index < group.source->getOperandCount(); ++index) {
        BasicBlock *predecessor = group.source->getIncomingBlock(index);
        Inst *value = lanes[lane]->translate(group.source->getArg(index));
        VERIFY(CFGEditor::setPhiEdgeValues(
            function, group.lanePhis[lane]->parentBlock(), predecessor,
            {{group.lanePhis[lane], value}}));
      }
}

u32 allowedUnrollAndJamDepth(const DependenceResult &dependence,
                             const Loop *outer, const Loop *inner,
                             i32 factor) noexcept {
  if (!outer || !inner || factor < 2 || inner->parent() != outer)
    return 0;

  std::vector<const Loop *> chain = {outer, inner};
  while (chain.size() <= kMaxSupportedJamDepth &&
         chain.back()->children().size() == 1)
    chain.push_back(chain.back()->children().front());
  const u32 maxDepth = static_cast<u32>(chain.size() - 1);
  if (dependence.kind == DependenceKind::Input ||
      dependence.status == DependenceStatus::NoDependence)
    return maxDepth;
  if (dependence.status != DependenceStatus::MayDependence ||
      dependence.possible.empty())
    return 0;

  const auto outerLoop =
      std::find(dependence.loops.begin(), dependence.loops.end(), outer);
  if (outerLoop == dependence.loops.end())
    return 0;
  const usize outerIndex =
      static_cast<usize>(outerLoop - dependence.loops.begin());

  const auto accessDepth = [&](const Inst *access) {
    if (!access || !access->parentBlock())
      return maxDepth;
    u32 depth = 0;
    for (u32 index = 1; index < chain.size(); ++index) {
      if (!chain[index]->contains(access->parentBlock()))
        break;
      depth = index;
    }
    return depth;
  };
  const u32 sourceDepth = accessDepth(dependence.source);
  const u32 sinkDepth = accessDepth(dependence.sink);
  u32 allowed = maxDepth;

  for (const DirectionVector &direction : dependence.possible) {
    if (direction.size() != dependence.loops.size() ||
        outerIndex >= direction.size())
      return 0;
    const DependenceDirection outerDirection = direction[outerIndex];
    if (outerDirection == DependenceDirection::Equal)
      continue;
    if (outerDirection != DependenceDirection::Less)
      return 0;

    const std::optional<i64> distance = outerIndex < dependence.distances.size()
                                            ? dependence.distances[outerIndex]
                                            : std::nullopt;
    if (distance && (*distance >= static_cast<i64>(factor) ||
                     *distance <= -static_cast<i64>(factor)))
      continue;
    const std::optional<u64> distanceMultiple =
        outerIndex < dependence.distanceMultiples.size()
            ? dependence.distanceMultiples[outerIndex]
            : std::nullopt;
    if (!distance && distanceMultiple &&
        *distanceMultiple >= static_cast<u64>(factor))
      continue;
    u32 limit = std::min({sourceDepth, sinkDepth, maxDepth});
    if (limit == 0)
      return 0;

    u32 directionLimit = limit;
    for (u32 depth = 1; depth <= limit; ++depth) {
      const auto loop = std::find(dependence.loops.begin(),
                                  dependence.loops.end(), chain[depth]);
      if (loop == dependence.loops.end()) {
        directionLimit = depth - 1;
        break;
      }
      const usize index = static_cast<usize>(loop - dependence.loops.begin());
      if (index >= direction.size())
        return 0;
      if (direction[index] == DependenceDirection::Equal)
        continue;
      directionLimit =
          direction[index] == DependenceDirection::Less ? limit : depth - 1;
      break;
    }
    allowed = std::min(allowed, directionLimit);
    if (allowed == 0)
      return 0;
  }
  return allowed;
}

} // namespace

namespace {

void mapSharedSkeleton(const UAJPlan &plan,
                       std::vector<std::unique_ptr<DeepCopy>> &lanes,
                       const std::vector<Inst *> &laneIVs) {
  for (usize index = 0; index < lanes.size(); ++index) {
    DeepCopy &lane = *lanes[index];
    lane.mapInst(plan.outer.iv.phi, laneIVs[index]);
    lane.mapInst(plan.outer.iv.stepInst, plan.outer.iv.stepInst);
    lane.mapInst(plan.outer.latchTest.comparison,
                 plan.outer.latchTest.comparison);
  }
  for (Inst *laneIV : laneIVs)
    for (const std::unique_ptr<DeepCopy> &lane : lanes)
      lane->mapInst(laneIV, laneIV);
}

void mapInnerSkeleton(const CountedLoopShape &shape,
                      std::vector<std::unique_ptr<DeepCopy>> &lanes) {
  for (const std::unique_ptr<DeepCopy> &lane : lanes) {
    lane->mapInst(shape.iv.phi, shape.iv.phi);
    lane->mapInst(shape.iv.stepInst, shape.iv.stepInst);
    lane->mapInst(shape.latchTest.comparison, shape.latchTest.comparison);
  }
}

void cloneInstructionList(const std::vector<Inst *> &instructions,
                          Inst *insertBefore,
                          std::vector<std::unique_ptr<DeepCopy>> &lanes) {
  for (const std::unique_ptr<DeepCopy> &lane : lanes)
    for (Inst *instruction : instructions)
      if (!lane->hasInstMapping(instruction))
        lane->copyInstBefore(instruction, insertBefore);
}

void cloneSingleBlockInner(const UAJPlan &plan,
                           std::vector<std::unique_ptr<DeepCopy>> &lanes) {
  for (const std::unique_ptr<DeepCopy> &lane : lanes)
    for (Inst *instruction : plan.singleBlockInnerBody)
      if (!lane->hasInstMapping(instruction))
        lane->copyInstBefore(instruction, plan.inner.iv.stepInst);
}

void coalesceConnectorInstructions(Function *function, UAJPlan &plan) {
  std::vector<Inst *> preheaderPhis;
  if (plan.inner.preheader != plan.outer.header)
    for (Inst *phi = plan.inner.preheader->firstPhi(); phi; phi = phi->next())
      preheaderPhis.push_back(phi);
  for (Inst *phi : preheaderPhis) {
    replaceAllUsesWith(function, phi, phi->getArg(0));
    VERIFY(phi->eraseFromBlock());
  }

  for (Inst *instruction : plan.innerPreInstructions)
    instruction->moveBefore(plan.outer.header->terminator());
  plan.preInstructions.insert(plan.preInstructions.end(),
                              plan.innerPreInstructions.begin(),
                              plan.innerPreInstructions.end());
  plan.innerPreInstructions.clear();

  Inst *postAnchor = plan.postInstructions.empty()
                         ? plan.outer.iv.stepInst
                         : plan.postInstructions.front();
  for (Inst *instruction : plan.innerPostInstructions)
    instruction->moveBefore(postAnchor);
  plan.postInstructions.insert(plan.postInstructions.begin(),
                               plan.innerPostInstructions.begin(),
                               plan.innerPostInstructions.end());
  plan.innerPostInstructions.clear();
}

void isolateInnerControlLatch(Function *function, UAJPlan &plan,
                              IRBuilder &builder) {
  BasicBlock *bodyLatch = plan.inner.latch;
  Inst *step = plan.inner.iv.stepInst;
  if (plan.inner.header == bodyLatch ||
      (!bodyLatch->firstPhi() && bodyLatch->firstInst() == step))
    return;

  std::vector<BasicBlock *> successors;
  forEachSuccessor(bodyLatch, [&](BasicBlock *successor) {
    if (std::find(successors.begin(), successors.end(), successor) ==
        successors.end())
      successors.push_back(successor);
  });
  VERIFY(successors.size() == 2);

  BasicBlock *controlLatch = builder.newBlockAfter(bodyLatch);
  controlLatch->takeInstructionSuffixFrom(step);
  builder.setInsertAtEnd(bodyLatch);
  builder.emitJump(controlLatch);
  for (BasicBlock *successor : successors)
    VERIFY(CFGEditor::moveAndSetPhiEdgeValues(function, successor, bodyLatch,
                                              controlLatch));

  const auto addControlLatch = [&](std::vector<BasicBlock *> &blocks) {
    const auto body = std::find(blocks.begin(), blocks.end(), bodyLatch);
    VERIFY(body != blocks.end());
    blocks.insert(body + 1, controlLatch);
  };
  addControlLatch(plan.innerBlocks);
  addControlLatch(plan.outerBlocks);
  plan.inner.latch = controlLatch;
}

void prepareJamChain(Function *function, UAJPlan &plan, IRBuilder &builder) {
  coalesceConnectorInstructions(function, plan);
  if (plan.nested)
    prepareJamChain(function, *plan.nested, builder);
  else
    isolateInnerControlLatch(function, plan, builder);
}

void cloneMultiBlockInner(Function *function, const UAJPlan &plan,
                          std::vector<std::unique_ptr<DeepCopy>> &lanes) {
  std::vector<BasicBlock *> bodyBlocks;
  bodyBlocks.reserve(plan.innerBlocks.size() - 1);
  for (BasicBlock *block : plan.innerBlocks)
    if (block != plan.inner.latch)
      bodyBlocks.push_back(block);
  VERIFY(!bodyBlocks.empty());

  BasicBlock *next = plan.inner.latch;
  for (usize reverse = lanes.size(); reverse > 0; --reverse) {
    DeepCopy &lane = *lanes[reverse - 1];
    BlockCloneConfig config;
    config.insertAfter = plan.inner.latch;
    config.freshBlockMappings = true;
    config.externalTargetMode = ExternalTargetMode::Redirect;
    config.redirectTarget = next;
    config.decideInst = [&](BasicBlock *, Inst *instruction, bool) {
      return lane.hasInstMapping(instruction) ? CloneInstAction::SkipMapped
                                              : CloneInstAction::Clone;
    };
    const std::vector<ClonedBlockPair> cloned =
        lane.copyBlocks(bodyBlocks, config);
    VERIFY(cloned.size() == bodyBlocks.size());
    next = lane.translateBlock(plan.inner.header);
  }

  VERIFY(computePreds(function));
  for (BasicBlock *block : bodyBlocks) {
    bool reachesLatch = false;
    forEachSuccessor(block, [&](BasicBlock *successor) {
      reachesLatch |= successor == plan.inner.latch;
    });
    if (reachesLatch)
      VERIFY(
          CFGEditor::redirectEdge(function, block, plan.inner.latch, next, {}));
  }
  computeUses(function);
}

std::vector<Inst *> phiList(BasicBlock *block, Inst *excluded = nullptr) {
  std::vector<Inst *> result;
  for (Inst *phi = block ? block->firstPhi() : nullptr; phi; phi = phi->next())
    if (phi != excluded)
      result.push_back(phi);
  return result;
}

bool jamMainBody(Function *function, UAJPlan &plan, IRBuilder &builder,
                 std::vector<ExitRelay> &relays) {
  std::vector<std::unique_ptr<DeepCopy>> lanes;
  lanes.reserve(static_cast<usize>(plan.factor - 1));
  for (i32 lane = 1; lane < plan.factor; ++lane)
    lanes.push_back(std::make_unique<DeepCopy>(function));

  std::vector<Inst *> laneIVs;
  laneIVs.reserve(lanes.size());
  builder.setInsertAtStart(plan.outer.header);
  for (i32 lane = 1; lane < plan.factor; ++lane) {
    i64 offset = 0;
    VERIFY(checkedMul(static_cast<i64>(lane), plan.outer.iv.step, offset));
    laneIVs.push_back(builder.emit(OP_ADD, TY_I32, plan.outer.iv.phi,
                                   builder.iConst(static_cast<i32>(offset))));
  }
  mapSharedSkeleton(plan, lanes, laneIVs);

  const std::function<void(UAJPlan &)> jamLevel = [&](UAJPlan &level) {
    mapInnerSkeleton(level.inner, lanes);
    cloneInstructionList(level.preInstructions,
                         level.outer.header->terminator(), lanes);

    const std::vector<Inst *> innerHeaderPhis =
        phiList(level.inner.header, level.inner.iv.phi);
    const std::vector<Inst *> innerExitPhis = phiList(level.inner.exit);
    const std::vector<Inst *> outerLatchPhis =
        level.outer.latch == level.inner.exit ? std::vector<Inst *>{}
                                              : phiList(level.outer.latch);
    const std::vector<PrivatePhiGroup> innerHeaderPrivate = createPrivatePhis(
        function, builder, level.inner.header, innerHeaderPhis, lanes);
    const std::vector<PrivatePhiGroup> innerExitPrivate = createPrivatePhis(
        function, builder, level.inner.exit, innerExitPhis, lanes);
    const std::vector<PrivatePhiGroup> outerLatchPrivate = createPrivatePhis(
        function, builder, level.outer.latch, outerLatchPhis, lanes);

    if (level.nested)
      jamLevel(*level.nested);
    else if (level.inner.header == level.inner.latch)
      cloneSingleBlockInner(level, lanes);
    else
      cloneMultiBlockInner(function, level, lanes);

    fillPrivatePhis(function, innerHeaderPrivate, lanes);
    fillPrivatePhis(function, innerExitPrivate, lanes);
    fillPrivatePhis(function, outerLatchPrivate, lanes);
    cloneInstructionList(level.postInstructions, level.outer.iv.stepInst,
                         lanes);
  };
  jamLevel(plan);

  DeepCopy &lastLane = *lanes.back();
  for (ExitRelay &relay : relays) {
    Inst *lastValue = lastLane.translate(relay.sourceValue);
    VERIFY(CFGEditor::setPhiEdgeValues(function, relay.mainRelay->parentBlock(),
                                       plan.outer.latch,
                                       {{relay.mainRelay, lastValue}}));
  }
  return true;
}

bool commitUAJ(Function *function, UAJPlan &plan, const SCEV &scev) {
  SCEVExpander expander(function, &scev);
  Inst *insertBefore = plan.outer.preheader->terminator();
  Inst *tripValue = expander.expandCodeFor(plan.trip, insertBefore);
  if (!tripValue)
    return false;

  IRBuilder builder(function->module, function);
  Inst *outerInitial = plan.outer.headerPhis.front().preheaderValue;
  builder.setInsertBefore(insertBefore);
  Inst *remainder =
      builder.emit(OP_MOD, TY_I32, tripValue, builder.iConst(plan.factor));
  Inst *mainTripValue = builder.emit(OP_SUB, TY_I32, tripValue, remainder);
  Inst *mainOffset = builder.emit(OP_MUL, TY_I32, mainTripValue,
                                  builder.iConst(plan.outer.iv.step));
  Inst *mainBoundValue = builder.emit(OP_ADD, TY_I32, outerInitial, mainOffset);

  BasicBlock *epilogueGate = builder.newBlockAfter(plan.outer.latch);
  DeepCopy epilogue(function);
  BasicBlock *epilogueHeader = builder.newBlockAfter(epilogueGate);
  Inst *epilogueIV =
      epilogue.materializeMappedPhi(plan.outer.iv.phi, epilogueHeader);
  BlockCloneConfig cloneConfig;
  cloneConfig.insertAfter = epilogueGate;
  cloneConfig.createBlock = [&](BasicBlock *source, BasicBlock *after) {
    return source == plan.outer.header ? epilogueHeader
                                       : builder.newBlockAfter(after);
  };
  cloneConfig.decideInst = [&](BasicBlock *, Inst *instruction, bool) {
    return epilogue.hasInstMapping(instruction) ? CloneInstAction::SkipMapped
                                                : CloneInstAction::Clone;
  };
  const std::vector<ClonedBlockPair> cloned =
      epilogue.copyBlocks(plan.outerBlocks, cloneConfig);
  VERIFY(cloned.size() == plan.outerBlocks.size());
  const auto isOuterExit = [&](BasicBlock *, BasicBlock *exit) {
    return !plan.outer.loop->contains(exit);
  };
  const bool translatedExits =
      epilogue.addTranslatedExitPhiIncomings(function, cloned, isOuterExit);
  VERIFY(translatedExits);

  VERIFY(epilogue.translateBlock(plan.outer.header) == epilogueHeader);
  BasicBlock *epilogueLatch = epilogue.translateBlock(plan.outer.latch);
  prepareJamChain(function, plan, builder);
  BasicBlock *mainGuard = builder.newBlockAfter(plan.outer.preheader);

  builder.setInsertAtEnd(mainGuard);
  Inst *hasMain = builder.emit(OP_GT, TY_I1, mainTripValue, builder.iConst(0));
  builder.emitBranch(hasMain, plan.outer.header, epilogueGate);

  builder.setInsertAtEnd(epilogueGate);
  Inst *epilogueBranch = builder.emitBranch(builder.makeUndef(TY_I1),
                                            epilogueHeader, plan.outer.exit);

  std::vector<ExitRelay> relays;
  for (Inst *exitPhi = plan.outer.exit->firstPhi(); exitPhi;
       exitPhi = exitPhi->next()) {
    Inst *sourceValue =
        CFGEditor::getPhiIncomingValue(exitPhi, plan.outer.latch);
    VERIFY(sourceValue);
    relays.push_back({exitPhi, nullptr, sourceValue});
  }

  VERIFY(CFGEditor::moveAndSetPhiEdgeValues(function, plan.outer.header,
                                            plan.outer.preheader, mainGuard));
  VERIFY(CFGEditor::moveAndSetPhiEdgeValues(function, plan.outer.exit,
                                            plan.outer.latch, epilogueGate));
  VERIFY(CFGEditor::rewriteJumpTarget(plan.outer.preheader, mainGuard));
  VERIFY(CFGEditor::rewriteBranchSlot(plan.outer.latch, false, epilogueGate));
  VERIFY(CFGEditor::addPhiEdgeValues(function, epilogueHeader, epilogueGate,
                                     {{epilogueIV, outerInitial}}));
  VERIFY(CFGEditor::addPhiEdgeValues(
      function, epilogueHeader, epilogueLatch,
      {{epilogueIV, epilogue.translate(plan.outer.iv.stepInst)}}));
  VERIFY(computePreds(function));
  computeUses(function);

  Inst *rhoIV =
      builder.emitPhi(TY_I32, epilogueGate, builder.makeUndef(TY_I32));
  VERIFY(CFGEditor::setPhiEdgeValues(function, epilogueGate, mainGuard,
                                     {{rhoIV, outerInitial}}));
  VERIFY(CFGEditor::setPhiEdgeValues(function, epilogueGate, plan.outer.latch,
                                     {{rhoIV, plan.outer.iv.stepInst}}));
  builder.setInsertBefore(epilogueBranch);
  Inst *epilogueCondition =
      plan.outer.latchTest.testedIsLHS
          ? builder.emit(plan.outer.latchTest.comparison->getOp(), TY_I1, rhoIV,
                         plan.outer.latchTest.boundValue)
          : builder.emit(plan.outer.latchTest.comparison->getOp(), TY_I1,
                         plan.outer.latchTest.boundValue, rhoIV);
  epilogueBranch->setArg(0, epilogueCondition);
  VERIFY(CFGEditor::setPhiEdgeValues(function, epilogueHeader, epilogueGate,
                                     {{epilogueIV, rhoIV}}));

  for (ExitRelay &relay : relays) {
    relay.mainRelay =
        builder.emitPhi(relay.exitPhi->getType(), epilogueGate,
                        builder.makeUndef(relay.exitPhi->getType()));
    VERIFY(CFGEditor::setPhiEdgeValues(
        function, epilogueGate, mainGuard,
        {{relay.mainRelay, builder.makeUndef(relay.exitPhi->getType())}}));
    VERIFY(CFGEditor::setPhiEdgeValues(function, epilogueGate, plan.outer.latch,
                                       {{relay.mainRelay, relay.sourceValue}}));
    VERIFY(CFGEditor::setPhiEdgeValues(function, plan.outer.exit, epilogueGate,
                                       {{relay.exitPhi, relay.mainRelay}}));
    Inst *epilogueValue = epilogue.translate(relay.sourceValue);
    VERIFY(CFGEditor::setPhiEdgeValues(function, plan.outer.exit, epilogueLatch,
                                       {{relay.exitPhi, epilogueValue}}));
  }

  VERIFY(jamMainBody(function, plan, builder, relays));
  i64 rawStep = 0;
  VERIFY(checkedMul(static_cast<i64>(plan.outer.iv.stepConstant->getImm()),
                    static_cast<i64>(plan.factor), rawStep));
  plan.outer.iv.stepInst->setArg(
      static_cast<u32>(plan.outer.iv.stepConstantArgIndex),
      builder.iConst(static_cast<i32>(rawStep)));
  plan.outer.latchTest.comparison->setArg(
      static_cast<u32>(plan.outer.latchTest.boundArgIndex), mainBoundValue);

  VERIFY(computePreds(function));
  computeUses(function);
  return true;
}

std::optional<UAJPlan>
findCandidate(Function *function, FunctionAnalysisManager &analyses,
              PressureOracle &oracle, const UnrollAndJamConfig &config,
              u32 &candidateCount,
              const std::unordered_set<BasicBlock *> &originalHeaders,
              const std::unordered_set<BasicBlock *> &consumedHeaders,
              DiagnosticEngine *diagnostics) {
  const LoopInfo &loops = analyses.getResult<LoopInfoAnalysis>(function).info;
  const LoopShapeInfo &shapes =
      analyses.getResult<LoopShapeAnalysis>(function).info;
  const SCEV &scev = analyses.getResult<SCEVAnalysis>(function).info;
  const DependenceInfo &dependenceInfo =
      analyses.getResult<DependenceAnalysis>(function).info;

  std::vector<Loop *> worklist;
  const std::function<void(Loop *)> collectPostorder = [&](Loop *loop) {
    for (Loop *child : loop->children())
      collectPostorder(child);
    worklist.push_back(loop);
  };
  for (Loop *loop : loops.topLevelLoops())
    collectPostorder(loop);

  LoopShapeQuery query;
  query.requireLatchContinueOnTrue = true;
  query.requireLatchCompareInLatch = true;
  std::optional<UAJPlan> best;
  for (Loop *outerLoop : worklist) {
    if (candidateCount >= config.maxCandidatesPerFunction)
      break;
    if (outerLoop->children().size() != 1 ||
        !originalHeaders.count(outerLoop->header()) ||
        consumedHeaders.count(outerLoop->header()))
      continue;
    ++candidateCount;
    Loop *innerLoop = outerLoop->children().front();
    const std::optional<CountedLoopShape> outer =
        shapes.getCountedLoop(outerLoop, query);
    const std::optional<CountedLoopShape> inner =
        shapes.getCountedLoop(innerLoop, query);
    if (!outer || !inner) {
      emitUAJRemark(diagnostics, config.emitRemarks, function,
                    outerLoop->header(), 0, 0, "reject", "shape", -1, -1);
      continue;
    }
    const std::vector<DependenceResult> dependences =
        dependenceInfo.getDependences(outerLoop);
    for (i32 factor : {4, 2}) {
      const u32 legalDepth = dependenceLegalDepth(*outer, *inner, dependences,
                                                  factor, config.maxJamDepth);
      if (legalDepth == 0) {
        emitUAJRemark(diagnostics, config.emitRemarks, function,
                      outerLoop->header(), factor, 0, "reject", "legality", -1,
                      -1);
        continue;
      }
      UAJPlan plan;
      if (!recognizeChain(function, shapes, query, *outer, outerLoop,
                          legalDepth, true, plan)) {
        emitUAJRemark(diagnostics, config.emitRemarks, function,
                      outerLoop->header(), factor, legalDepth, "reject",
                      "shape", -1, -1);
        continue;
      }
      plan.factor = factor;
      if (hasDynamicDivMod(plan)) {
        emitUAJRemark(diagnostics, config.emitRemarks, function,
                      outerLoop->header(), factor, fusedDepth(plan), "reject",
                      "dynamic-divmod", -1, -1);
        continue;
      }
      if (!proveMainBounds(scev, plan, factor)) {
        emitUAJRemark(diagnostics, config.emitRemarks, function,
                      outerLoop->header(), factor, fusedDepth(plan), "reject",
                      "bounds", -1, -1);
        continue;
      }
      if (!pressureAllowsFactor(plan, dependenceInfo, factor)) {
        emitUAJRemark(diagnostics, config.emitRemarks, function,
                      outerLoop->header(), factor, fusedDepth(plan), "reject",
                      "pressure", -1, plan.estimatedGPR);
        continue;
      }
      if (!estimateReuse(plan, dependenceInfo, dependences,
                         config.minimumReuseScore)) {
        emitUAJRemark(diagnostics, config.emitRemarks, function,
                      outerLoop->header(), factor, fusedDepth(plan), "reject",
                      "reuse", plan.reuseScore, plan.estimatedGPR);
        continue;
      }
      const i64 estimated =
          static_cast<i64>(projectedNestCost(plan)) * factor + 32;
      plan.estimatedAddedInstructions = saturatingCost(estimated);
      const GrowthHint growth =
          oracle.hint(function, plan.estimatedAddedInstructions);
      if (growth.functionAfter > config.maxFunctionInstructions ||
          growth.overall == PressureLevel::High ||
          growth.overall == PressureLevel::UnknownLarge) {
        emitUAJRemark(diagnostics, config.emitRemarks, function,
                      outerLoop->header(), factor, fusedDepth(plan), "reject",
                      "growth", plan.reuseScore, plan.estimatedGPR);
        continue;
      }
      emitUAJRemark(diagnostics, config.emitRemarks, function,
                    outerLoop->header(), factor, fusedDepth(plan), "candidate",
                    "profitability", plan.reuseScore, plan.estimatedGPR);
      if (!best || plan.reuseScore > best->reuseScore ||
          (plan.reuseScore == best->reuseScore &&
           fusedDepth(plan) > fusedDepth(*best)))
        best = std::move(plan);
      break;
    }
  }
  return best;
}

} // namespace

UnrollAndJamPass::UnrollAndJamPass(UnrollAndJamConfig config) noexcept
    : config_(config) {}

std::string_view UnrollAndJamPass::name() const noexcept {
  return "unroll-and-jam";
}

PassResult UnrollAndJamPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first ||
      config_.maxTransformsPerFunction == 0 || config_.maxJamDepth == 0 ||
      config_.maxFunctionInstructions <= 0 || !computePreds(function))
    return PassResult::noChange();
  computeUses(function);
  FunctionAnalysisManager &analyses = context.functionAnalyses();
#ifndef NDEBUG
  VERIFY(verifyLoopSimplify(function, analyses));
  VERIFY(verifyLCSSA(function, analyses));
#endif

  PressureOracle oracle(function->module);
  std::unordered_set<BasicBlock *> originalHeaders;
  const LoopInfo &entryLoops =
      analyses.getResult<LoopInfoAnalysis>(function).info;
  const std::function<void(Loop *)> snapshot = [&](Loop *loop) {
    originalHeaders.insert(loop->header());
    for (Loop *child : loop->children())
      snapshot(child);
  };
  for (Loop *loop : entryLoops.topLevelLoops())
    snapshot(loop);
  std::unordered_set<BasicBlock *> consumedHeaders;
  u32 transformed = 0;
  u32 candidates = 0;
  while (transformed < config_.maxTransformsPerFunction &&
         candidates < config_.maxCandidatesPerFunction) {
    std::optional<UAJPlan> plan =
        findCandidate(function, analyses, oracle, config_, candidates,
                      originalHeaders, consumedHeaders, context.diagnostics());
    if (!plan)
      break;
    BasicBlock *origin = plan->outer.header;
    if (!commitUAJ(function, *plan,
                   analyses.getResult<SCEVAnalysis>(function).info)) {
      emitUAJRemark(context.diagnostics(), config_.emitRemarks, function,
                    origin, plan->factor, fusedDepth(*plan), "reject", "commit",
                    plan->reuseScore, plan->estimatedGPR);
      break;
    }
    consumedHeaders.insert(origin);
    emitUAJRemark(context.diagnostics(), config_.emitRemarks, function, origin,
                  plan->factor, fusedDepth(*plan), "accept", "commit",
                  plan->reuseScore, plan->estimatedGPR);
    oracle.recordApplied(function, plan->estimatedAddedInstructions);
    ++transformed;
    UNUSED(repairLoopForm(function, context));
  }
  if (transformed == 0)
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
