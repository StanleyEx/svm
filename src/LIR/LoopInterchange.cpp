#include "Analysis.h"
#include "DeepCopy.h"
#include "DependenceAnalysis.h"
#include "LIRPass.h"
#include "LoopShape.h"
#include "Utils.h"

#include <algorithm>
#include <functional>
#include <optional>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

bool isLegalInterchangeDirection(const DirectionVector &direction,
                                 usize outerIndex, usize innerIndex) noexcept;

struct InterchangePlan {
  CountedLoopShape outer;                // 原外层循环形态
  CountedLoopShape inner;                // 原内层循环形态
  Inst *outerInitial = nullptr;          // 原外层IV初值
  Inst *innerInitial = nullptr;          // 原内层IV初值
  Inst *outerBound = nullptr;            // 原外层退出边界
  Inst *innerBound = nullptr;            // 原内层退出边界
  std::vector<BasicBlock *> innerBlocks; // 按布局排列的克隆块
  i64 scoreDelta = 0;                    // 已证明的局部性收益
};

bool isPureRecomputable(Inst *instruction) noexcept {
  if (!instruction || isTerminator(instruction->getOp()))
    return false;
  const OpCode op = instruction->getOp();
  if (op == OP_DIV || op == OP_MOD || op == OP_FDIV)
    return false;
  return isArithmetic(op) || isCompare(op) || isUnaryArithmetic(op) ||
         isConversion(op) || isAddressingOp(op) || op == OP_SELECT;
}

bool isPlainJump(BasicBlock *block, BasicBlock *target) noexcept {
  Inst *terminator = block ? block->terminator() : nullptr;
  return terminator && terminator->getOp() == OP_JMP &&
         terminator->getJumpTarget() == target;
}

Inst *controlInitialValue(const CountedLoopShape &shape) noexcept {
  for (const HeaderPhiShape &headerPhi : shape.headerPhis)
    if (headerPhi.isControlIV)
      return headerPhi.preheaderValue;
  return nullptr;
}

bool usesOnly(Inst *definition,
              std::initializer_list<Inst *> allowed) noexcept {
  if (!definition)
    return false;
  for (const Use *use = definition->uses(); use; use = use->next) {
    bool accepted = false;
    for (Inst *candidate : allowed)
      accepted |= use->user == candidate;
    if (!accepted)
      return false;
  }
  return true;
}

bool hasOnlyPureInstructions(BasicBlock *block, Inst *firstAllowed = nullptr,
                             Inst *secondAllowed = nullptr) noexcept {
  if (!block)
    return false;
  for (Inst *instruction = block->firstInst(); instruction;
       instruction = instruction->next()) {
    if (isTerminator(instruction->getOp()) || instruction == firstAllowed ||
        instruction == secondAllowed)
      continue;
    if (!isPureRecomputable(instruction))
      return false;
  }
  return true;
}

bool containsOpaqueEffect(const Loop *loop) noexcept {
  for (BasicBlock *block : loop->blocks())
    for (Inst *instruction = block->firstInst(); instruction;
         instruction = instruction->next())
      if (instruction->isCallInstruction() || instruction->getOp() == OP_ALLOCA)
        return true;
  return false;
}

bool hasEscapingDefinition(const Loop *outer) noexcept {
  const std::unordered_set<BasicBlock *> blocks(outer->blocks().begin(),
                                                outer->blocks().end());
  for (BasicBlock *block : outer->blocks()) {
    bool escaping = false;
    forEachOp(block, [&](Inst *definition) {
      if (escaping || isVoid(definition->getType()))
        return;
      for (const Use *use = definition->uses(); use; use = use->next) {
        BasicBlock *userBlock = use->user ? use->user->parentBlock() : nullptr;
        if (!userBlock || !blocks.count(userBlock)) {
          escaping = true;
          break;
        }
      }
    });
    if (escaping)
      return true;
  }
  return false;
}

bool canMaterializeAtOuterEntry(Inst *value, const Loop *outer,
                                std::unordered_set<Inst *> &visiting,
                                std::unordered_set<Inst *> &accepted) {
  BasicBlock *block = value ? value->parentBlock() : nullptr;
  if (!block || !outer->contains(block) || accepted.count(value))
    return true;
  if (!visiting.insert(value).second || value->getOp() == OP_PHI ||
      !isPureRecomputable(value))
    return false;
  for (u32 index = 0; index < value->getOperandCount(); ++index)
    if (!canMaterializeAtOuterEntry(value->getArg(index), outer, visiting,
                                    accepted)) {
      visiting.erase(value);
      return false;
    }
  visiting.erase(value);
  accepted.insert(value);
  return true;
}

bool canTranslateInnerOperand(Inst *value, Inst *user,
                              const CountedLoopShape &outer,
                              const CountedLoopShape &inner,
                              std::unordered_set<Inst *> &visiting,
                              std::unordered_set<Inst *> &accepted) {
  BasicBlock *block = value ? value->parentBlock() : nullptr;
  if (!block || inner.loop->contains(block) || !outer.loop->contains(block) ||
      value == outer.iv.phi || value == inner.iv.phi || accepted.count(value))
    return true;
  if ((user && user->getOp() == OP_PHI) || !visiting.insert(value).second ||
      value->getOp() == OP_PHI || !isPureRecomputable(value))
    return false;
  for (u32 index = 0; index < value->getOperandCount(); ++index)
    if (!canTranslateInnerOperand(value->getArg(index), value, outer, inner,
                                  visiting, accepted)) {
      visiting.erase(value);
      return false;
    }
  visiting.erase(value);
  accepted.insert(value);
  return true;
}

bool canTranslateInnerBody(const InterchangePlan &plan) {
  std::unordered_set<Inst *> visiting;
  std::unordered_set<Inst *> accepted;
  for (BasicBlock *block : plan.innerBlocks) {
    bool valid = true;
    forEachOp(block, [&](Inst *instruction) {
      for (u32 index = 0; valid && index < instruction->getOperandCount();
           ++index)
        valid = canTranslateInnerOperand(instruction->getArg(index),
                                         instruction, plan.outer, plan.inner,
                                         visiting, accepted);
    });
    if (!valid)
      return false;
  }
  return true;
}

bool isPerfectTwoLevelNest(Function *function, const CountedLoopShape &outer,
                           const CountedLoopShape &inner,
                           InterchangePlan &plan) {
  if (!function || !outer.loop || !inner.loop ||
      inner.loop->parent() != outer.loop ||
      outer.loop->children().size() != 1 ||
      outer.loop->children().front() != inner.loop ||
      !inner.loop->children().empty() || outer.headerPhis.size() != 1 ||
      inner.headerPhis.size() != 1 || !outer.headerPhis.front().isControlIV ||
      !inner.headerPhis.front().isControlIV || outer.iv.step <= 0 ||
      inner.iv.step <= 0 || outer.loop->exitingBlocks().size() != 1 ||
      inner.loop->exitingBlocks().size() != 1 ||
      outer.loop->exitingBlocks().front() != outer.latch ||
      inner.loop->exitingBlocks().front() != inner.latch ||
      !outer.latchTest.continueOnTrue || !inner.latchTest.continueOnTrue ||
      outer.latchTest.comparison->parentBlock() != outer.latch ||
      inner.latchTest.comparison->parentBlock() != inner.latch ||
      !outer.backedgeTakenCount || !inner.backedgeTakenCount ||
      outer.backedgeTakenCount->kind == SCEVExpr::K_UNKNOWN ||
      inner.backedgeTakenCount->kind == SCEVExpr::K_UNKNOWN ||
      !outer.iv.stepConstant || outer.iv.stepConstant->isUndefValue() ||
      !inner.iv.stepConstant || inner.iv.stepConstant->isUndefValue())
    return false;

  plan.outer = outer;
  plan.inner = inner;
  plan.outerInitial = controlInitialValue(outer);
  plan.innerInitial = controlInitialValue(inner);
  plan.outerBound = outer.latchTest.boundValue;
  plan.innerBound = inner.latchTest.boundValue;
  if (!plan.outerInitial || !plan.innerInitial || !plan.outerBound ||
      !plan.innerBound || !inner.iv.baseSCEV || !inner.latchTest.boundSCEV ||
      !inner.iv.baseSCEV->isLoopInvariant(outer.loop) ||
      !inner.latchTest.boundSCEV->isLoopInvariant(outer.loop))
    return false;

  if (!isPlainJump(outer.preheader, outer.header) ||
      !isPlainJump(inner.preheader, inner.header) ||
      !isPlainJump(outer.header, inner.preheader == outer.header
                                     ? inner.header
                                     : inner.preheader) ||
      (inner.exit != outer.latch && !isPlainJump(inner.exit, outer.latch)))
    return false;

  std::unordered_set<BasicBlock *> expected(inner.loop->blocks().begin(),
                                            inner.loop->blocks().end());
  expected.insert(outer.header);
  expected.insert(outer.latch);
  expected.insert(inner.preheader);
  expected.insert(inner.exit);
  if (expected.size() != outer.loop->blocks().size())
    return false;
  for (BasicBlock *block : outer.loop->blocks())
    if (!expected.count(block))
      return false;

  if (outer.latch->firstPhi() ||
      (inner.preheader != outer.header && inner.preheader->firstPhi()) ||
      (inner.exit != outer.latch && inner.exit->firstPhi()) ||
      !hasOnlyPureInstructions(outer.header) ||
      !hasOnlyPureInstructions(outer.latch, outer.iv.stepInst,
                               outer.latchTest.comparison) ||
      (inner.preheader != outer.header &&
       !hasOnlyPureInstructions(inner.preheader)) ||
      (inner.exit != outer.latch && !hasOnlyPureInstructions(inner.exit)) ||
      containsOpaqueEffect(outer.loop) || hasEscapingDefinition(outer.loop) ||
      !usesOnly(outer.iv.stepInst,
                {outer.latchTest.comparison, outer.iv.phi}) ||
      !usesOnly(outer.latchTest.comparison, {outer.latch->terminator()}) ||
      !usesOnly(inner.iv.stepInst,
                {inner.latchTest.comparison, inner.iv.phi}) ||
      !usesOnly(inner.latchTest.comparison, {inner.latch->terminator()}))
    return false;

  plan.innerBlocks.clear();
  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    if (inner.loop->contains(block))
      plan.innerBlocks.push_back(block);
  if (plan.innerBlocks.size() != inner.loop->blocks().size())
    return false;

  std::unordered_set<Inst *> visiting;
  std::unordered_set<Inst *> accepted;
  for (Inst *value :
       {plan.outerInitial, plan.innerInitial, plan.outerBound, plan.innerBound})
    if (!canMaterializeAtOuterEntry(value, outer.loop, visiting, accepted))
      return false;
  return canTranslateInnerBody(plan);
}

bool proveDependenceLegality(const InterchangePlan &plan,
                             const DependenceInfo &dependences) {
  for (const DependenceResult &result :
       dependences.getDependences(plan.outer.loop)) {
    if (result.kind == DependenceKind::Input ||
        result.status == DependenceStatus::NoDependence)
      continue;
    if (result.status != DependenceStatus::MayDependence ||
        result.possible.empty())
      return false;
    const auto outer =
        std::find(result.loops.begin(), result.loops.end(), plan.outer.loop);
    const auto inner =
        std::find(result.loops.begin(), result.loops.end(), plan.inner.loop);
    if (outer == result.loops.end() || inner == result.loops.end())
      return false;
    const usize outerIndex = static_cast<usize>(outer - result.loops.begin());
    const usize innerIndex = static_cast<usize>(inner - result.loops.begin());
    for (const DirectionVector &direction : result.possible)
      if (!isLegalInterchangeDirection(direction, outerIndex, innerIndex))
        return false;
  }
  return true;
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

i64 transitionWeight(const CountedLoopShape &shape) noexcept {
  if (shape.constantTripCount == 1)
    return 0;
  if (shape.constantTripCount > 1)
    return std::min<i64>(shape.constantTripCount - 1, 64);
  return 1;
}

bool strideScore(i64 stride, u32 width, i64 &score) noexcept {
  const i64 bytes = static_cast<i64>(width);
  if (stride == bytes)
    return checkedMul(bytes, i64{4}, score);
  if (stride == 0 || stride == -bytes) {
    score = bytes;
    return true;
  }
  score = -bytes;
  return true;
}

bool estimateProfitability(const InterchangePlan &plan,
                           const DependenceInfo &dependences, i64 minimumDelta,
                           i64 &delta) {
  i64 before = 0;
  i64 after = 0;
  bool sawAccess = false;
  for (BasicBlock *block : plan.innerBlocks) {
    for (Inst *instruction = block->firstInst(); instruction;
         instruction = instruction->next()) {
      if (instruction->getOp() != OP_LOAD && instruction->getOp() != OP_STORE)
        continue;
      const AffineAccess &access = dependences.getAccess(instruction);
      if (!access.exact() || access.widthBytes == 0)
        return false;
      i64 innerStride = 0;
      i64 outerStride = 0;
      if (!coefficientFor(access, plan.inner.loop, innerStride) ||
          !coefficientFor(access, plan.outer.loop, outerStride))
        return false;
      const i64 width = static_cast<i64>(access.widthBytes);
      if (instruction->getOp() == OP_STORE && innerStride == width &&
          outerStride != width)
        return false;

      i64 beforeScore = 0;
      i64 afterScore = 0;
      i64 weightedBefore = 0;
      i64 weightedAfter = 0;
      const i64 memoryWeight = instruction->getOp() == OP_STORE ? 2 : 1;
      if (!strideScore(innerStride, access.widthBytes, beforeScore) ||
          !strideScore(outerStride, access.widthBytes, afterScore) ||
          !checkedMul(beforeScore, transitionWeight(plan.inner),
                      weightedBefore) ||
          !checkedMul(weightedBefore, memoryWeight, weightedBefore) ||
          !checkedMul(afterScore, transitionWeight(plan.outer),
                      weightedAfter) ||
          !checkedMul(weightedAfter, memoryWeight, weightedAfter) ||
          !checkedAdd(before, weightedBefore, before) ||
          !checkedAdd(after, weightedAfter, after))
        return false;
      sawAccess = true;
    }
  }
  return sawAccess && checkedSub(after, before, delta) && delta >= minimumDelta;
}

Inst *materializeAtOuterEntry(DeepCopy &copier, Inst *value,
                              const InterchangePlan &plan) {
  BasicBlock *block = value ? value->parentBlock() : nullptr;
  if (!block || !plan.outer.loop->contains(block))
    return value;
  return copier.materializeInstructionSlice(
      value, plan.outer.preheader->terminator(),
      [&](Inst *instruction) {
        BasicBlock *parent = instruction ? instruction->parentBlock() : nullptr;
        return parent && plan.outer.loop->contains(parent);
      },
      isPureRecomputable);
}

void commitInterchange(Function *function, const InterchangePlan &plan) {
  IRBuilder builder(function->module, function);
  DeepCopy entryCopier(function);
  Inst *outerInitial =
      materializeAtOuterEntry(entryCopier, plan.outerInitial, plan);
  Inst *innerInitial =
      materializeAtOuterEntry(entryCopier, plan.innerInitial, plan);
  Inst *outerBound =
      materializeAtOuterEntry(entryCopier, plan.outerBound, plan);
  Inst *innerBound =
      materializeAtOuterEntry(entryCopier, plan.innerBound, plan);
  VERIFY(outerInitial && innerInitial && outerBound && innerBound);

  BasicBlock *newOuterHeader = builder.newBlockAfter(plan.outer.latch);
  BasicBlock *newInnerPreheader = builder.newBlockAfter(newOuterHeader);
  BasicBlock *newInnerLatch = builder.newBlockAfter(newInnerPreheader);

  DeepCopy bodyCopier(function);
  Inst *newOuterIV =
      bodyCopier.materializeMappedPhi(plan.inner.iv.phi, newOuterHeader);
  Inst *newInnerIV = nullptr;
  BasicBlock *newInnerHeader = nullptr;
  const Inst *oldInnerTerminator = plan.inner.latch->terminator();

  BlockCloneConfig cloneConfig;
  cloneConfig.insertAfter = newInnerPreheader;
  cloneConfig.createBlock = [&](BasicBlock *source, BasicBlock *after) {
    BasicBlock *clone = builder.newBlockAfter(after);
    if (source == plan.inner.header) {
      newInnerHeader = clone;
      newInnerIV =
          bodyCopier.materializeMappedPhi(plan.outer.iv.phi, newInnerHeader);
    }
    return clone;
  };
  cloneConfig.decideInst = [&](BasicBlock *, Inst *instruction, bool) {
    if (instruction == plan.inner.iv.stepInst ||
        instruction == plan.inner.latchTest.comparison ||
        instruction == oldInnerTerminator)
      return CloneInstAction::SkipUnmapped;
    return bodyCopier.hasInstMapping(instruction) ? CloneInstAction::SkipMapped
                                                  : CloneInstAction::Clone;
  };
  cloneConfig.skippedTerminatorTarget = [&](Inst *terminator) {
    return terminator == oldInnerTerminator ? newInnerLatch : nullptr;
  };
  cloneConfig.translateOperand = [&](Inst *value, Inst *, Inst *cloneUser) {
    if (bodyCopier.hasInstMapping(value))
      return bodyCopier.translate(value);
    BasicBlock *block = value ? value->parentBlock() : nullptr;
    if (!block || plan.inner.loop->contains(block) ||
        !plan.outer.loop->contains(block))
      return static_cast<Inst *>(nullptr);
    VERIFY(cloneUser->getOp() != OP_PHI && newInnerIV && newOuterIV);
    DeepCopy sliceCopier(function);
    sliceCopier.mapInst(plan.outer.iv.phi, newInnerIV);
    sliceCopier.mapInst(plan.inner.iv.phi, newOuterIV);
    Inst *translated = sliceCopier.materializeInstructionSlice(
        value, cloneUser,
        [&](Inst *instruction) {
          BasicBlock *parent =
              instruction ? instruction->parentBlock() : nullptr;
          return parent && plan.outer.loop->contains(parent) &&
                 !plan.inner.loop->contains(parent);
        },
        isPureRecomputable);
    VERIFY(translated != nullptr);
    return translated;
  };
  const std::vector<ClonedBlockPair> cloned =
      bodyCopier.copyBlocks(plan.innerBlocks, cloneConfig);
  VERIFY(cloned.size() == plan.innerBlocks.size() && newInnerHeader &&
         newInnerIV);

  BasicBlock *newInnerExit = builder.newBlockAfter(newInnerLatch);
  BasicBlock *newOuterLatch = builder.newBlockAfter(newInnerExit);
  Inst *outerStep = builder.iConst(plan.outer.iv.stepConstant->getImm());
  Inst *innerStep = builder.iConst(plan.inner.iv.stepConstant->getImm());

  builder.setInsertAtEnd(newInnerLatch);
  Inst *newInnerNext = builder.emit(
      plan.outer.iv.updateOp, newInnerIV->getType(), newInnerIV, outerStep);
  Inst *newInnerCompare = nullptr;
  if (plan.outer.latchTest.testedIsLHS)
    newInnerCompare = builder.emit(plan.outer.latchTest.comparison->getOp(),
                                   TY_I1, newInnerNext, outerBound);
  else
    newInnerCompare = builder.emit(plan.outer.latchTest.comparison->getOp(),
                                   TY_I1, outerBound, newInnerNext);
  builder.emitBranch(newInnerCompare, newInnerHeader, newInnerExit);

  builder.setInsertAtEnd(newOuterLatch);
  Inst *newOuterNext = builder.emit(
      plan.inner.iv.updateOp, newOuterIV->getType(), newOuterIV, innerStep);
  Inst *newOuterCompare = nullptr;
  if (plan.inner.latchTest.testedIsLHS)
    newOuterCompare = builder.emit(plan.inner.latchTest.comparison->getOp(),
                                   TY_I1, newOuterNext, innerBound);
  else
    newOuterCompare = builder.emit(plan.inner.latchTest.comparison->getOp(),
                                   TY_I1, innerBound, newOuterNext);
  builder.emitBranch(newOuterCompare, newOuterHeader, plan.outer.exit);

  builder.setInsertAtEnd(newOuterHeader);
  builder.emitJump(newInnerPreheader);
  builder.setInsertAtEnd(newInnerPreheader);
  builder.emitJump(newInnerHeader);
  builder.setInsertAtEnd(newInnerExit);
  builder.emitJump(newOuterLatch);

  VERIFY(CFGEditor::addPhiEdgeValues(function, newOuterHeader,
                                     plan.outer.preheader,
                                     {{newOuterIV, innerInitial}}));
  VERIFY(CFGEditor::addPhiEdgeValues(function, newOuterHeader, newOuterLatch,
                                     {{newOuterIV, newOuterNext}}));
  VERIFY(CFGEditor::addPhiEdgeValues(function, newInnerHeader,
                                     newInnerPreheader,
                                     {{newInnerIV, outerInitial}}));
  VERIFY(CFGEditor::addPhiEdgeValues(function, newInnerHeader, newInnerLatch,
                                     {{newInnerIV, newInnerNext}}));

  VERIFY(
      CFGEditor::rewriteBranchSlot(plan.outer.latch, false, plan.outer.header));
  VERIFY(CFGEditor::moveAndSetPhiEdgeValues(function, plan.outer.exit,
                                            plan.outer.latch, newOuterLatch));
  VERIFY(CFGEditor::rewriteJumpTarget(plan.outer.preheader, newOuterHeader));
  VERIFY(cleanupDeadBlocks(function));
  VERIFY(computePreds(function));
  computeUses(function);
}

std::optional<InterchangePlan>
findCandidate(Function *function, FunctionAnalysisManager &analyses,
              const LoopInterchangeConfig &config, u32 &candidateCount) {
  const LoopInfo &loops = analyses.getResult<LoopInfoAnalysis>(function).info;
  const LoopShapeInfo &shapes =
      analyses.getResult<LoopShapeAnalysis>(function).info;
  const DependenceInfo &dependences =
      analyses.getResult<DependenceAnalysis>(function).info;

  std::vector<Loop *> worklist;
  const std::function<void(Loop *)> collect = [&](Loop *loop) {
    worklist.push_back(loop);
    for (Loop *child : loop->children())
      collect(child);
  };
  for (Loop *loop : loops.topLevelLoops())
    collect(loop);

  LoopShapeQuery query;
  query.requireLatchContinueOnTrue = true;
  query.requireLatchCompareInLatch = true;
  for (Loop *innerLoop : worklist) {
    Loop *outerLoop = innerLoop->parent();
    if (!outerLoop)
      continue;
    if (candidateCount >= config.maxCandidatesPerFunction)
      break;
    ++candidateCount;
    std::optional<CountedLoopShape> outer =
        shapes.getCountedLoop(outerLoop, query);
    std::optional<CountedLoopShape> inner =
        shapes.getCountedLoop(innerLoop, query);
    if (!outer || !inner)
      continue;
    InterchangePlan plan;
    if (!isPerfectTwoLevelNest(function, *outer, *inner, plan) ||
        !proveDependenceLegality(plan, dependences) ||
        !estimateProfitability(plan, dependences, config.minScoreDelta,
                               plan.scoreDelta))
      continue;
    return plan;
  }
  return std::nullopt;
}

bool isLegalInterchangeDirection(const DirectionVector &direction,
                                 usize outerIndex, usize innerIndex) noexcept {
  if (outerIndex >= direction.size() || innerIndex >= direction.size() ||
      outerIndex == innerIndex)
    return false;
  for (usize index = 0; index < direction.size(); ++index) {
    const DependenceDirection current =
        index == outerIndex   ? direction[innerIndex]
        : index == innerIndex ? direction[outerIndex]
                              : direction[index];
    if (current == DependenceDirection::Equal)
      continue;
    return current == DependenceDirection::Less;
  }
  return true;
}

} // namespace

LoopInterchangePass::LoopInterchangePass(LoopInterchangeConfig config) noexcept
    : config_(config) {}

std::string_view LoopInterchangePass::name() const noexcept {
  return "loop-interchange";
}

PassResult LoopInterchangePass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first ||
      config_.maxTransformsPerFunction == 0 || !computePreds(function))
    return PassResult::noChange();
  computeUses(function);
  FunctionAnalysisManager &analyses = context.functionAnalyses();
#ifndef NDEBUG
  VERIFY(verifyLoopSimplify(function, analyses));
  VERIFY(verifyLCSSA(function, analyses));
#endif

  u32 transformed = 0;
  u32 candidates = 0;
  while (transformed < config_.maxTransformsPerFunction &&
         candidates < config_.maxCandidatesPerFunction) {
    std::optional<InterchangePlan> plan =
        findCandidate(function, analyses, config_, candidates);
    if (!plan)
      break;
    commitInterchange(function, *plan);
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
