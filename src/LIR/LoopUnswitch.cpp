#include "Analysis.h"
#include "LIRPass.h"
#include "LoopVersioning.h"
#include "PressureOracle.h"
#include "Utils.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

constexpr i32 kMaxTransformsPerFunction = 6;
constexpr i32 kMaxTransformsPerLoop = 4;
constexpr i32 kMaxSliceDepth = 4;
constexpr usize kMaxSliceInstructions = 5;
constexpr i32 kMaxAddedInstructions = 4000;
constexpr i32 kMaxFunctionInstructions = 20000;
constexpr f64 kMaxModuleGrowthRatio = 0.35;
constexpr i32 kMaxModuleGrowth = 20000;
constexpr i32 kMinRatioBudgetBaseline = 128;

struct GuardLink {
  BasicBlock *block = nullptr;          // 条件分支所在块
  Inst *condition = nullptr;            // 循环不变i1条件
  bool continuesOnTrue = true;          // true边是否继续guard链
  BasicBlock *continueTarget = nullptr; // 条件满足后的环内目标
};

struct RawGuardChain {
  std::vector<GuardLink> guards;    // 共享失败目标的连续guard
  BasicBlock *commonSkip = nullptr; // 任一guard失败时的公共目标
};

struct PredicatePlan {
  std::vector<Inst *> order;          // 需要在preheader重建的拓扑序
  std::unordered_set<Inst *> planned; // 已规划的DAG节点
};

struct Candidate {
  LoopVersionPlan plan;             // 已完成全部只读预检的版本计划
  std::vector<GuardLink> guards;    // 原版本中折叠为continue的guard
  BasicBlock *commonSkip = nullptr; // 克隆版本直接跳转目标
  BasicBlock *loopHeader = nullptr; // 跨轮稳定的单循环预算键
  i32 score = 0;                    // 收益分数
};

std::vector<Loop *> collectLoopsPostorder(const LoopInfo &loops) {
  std::vector<Loop *> result;
  const std::function<void(Loop *)> collect = [&](Loop *loop) {
    for (Loop *child : loop->children())
      collect(child);
    result.push_back(loop);
  };
  for (Loop *loop : loops.topLevelLoops())
    collect(loop);
  return result;
}

bool isSafePredicateOp(OpCode op) noexcept {
  if (op == OP_DIV || op == OP_MOD)
    return false;
  return isArithmetic(op) || isUnaryArithmetic(op) || isCompare(op) ||
         isConversion(op) || isAddressingOp(op);
}

bool isReusableAtPreheader(Inst *value, const Loop *loop, BasicBlock *preheader,
                           const DominatorTree &dominators) noexcept {
  if (!value || value->isErased())
    return false;
  BasicBlock *definition = value->parentBlock();
  if (!definition)
    return value->isUndefValue() || value->isPrecoloredDef() ||
           isConstant(value->getOp());
  return !loop->contains(definition) &&
         dominators.dominates(definition, preheader);
}

bool planPredicateValue(Inst *value, Loop *loop, BasicBlock *preheader,
                        const DominatorTree &dominators, PredicatePlan &plan,
                        std::unordered_set<Inst *> &visiting, i32 depth) {
  if (isReusableAtPreheader(value, loop, preheader, dominators) ||
      plan.planned.count(value))
    return true;
  if (!value || depth > kMaxSliceDepth || !value->parentBlock() ||
      !isSafePredicateOp(value->getOp()) || !visiting.insert(value).second)
    return false;
  for (u32 index = 0; index < value->getOperandCount(); ++index) {
    if (!planPredicateValue(value->getArg(index), loop, preheader, dominators,
                            plan, visiting, depth + 1)) {
      visiting.erase(value);
      return false;
    }
  }
  visiting.erase(value);
  if (plan.order.size() >= kMaxSliceInstructions)
    return false;
  plan.order.push_back(value);
  plan.planned.insert(value);
  return true;
}

bool canDiscardGuardBlock(BasicBlock *block) noexcept {
  if (!block)
    return false;
  for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
    if (inst == block->terminator())
      continue;
    if (!isConstant(inst->getOp()) && inst->getOp() != OP_SELECT &&
        !isSafePredicateOp(inst->getOp()))
      return false;
  }
  return true;
}

bool hasSameSkipPhiValues(BasicBlock *first, BasicBlock *next,
                          BasicBlock *skip) noexcept {
  if (!first || !next || !skip)
    return false;
  for (Inst *phi = skip->firstPhi(); phi; phi = phi->next())
    if (CFGEditor::getPhiIncomingValue(phi, first) !=
        CFGEditor::getPhiIncomingValue(phi, next))
      return false;
  return true;
}

std::vector<RawGuardChain>
buildRawChains(BasicBlock *head,
               const std::unordered_set<BasicBlock *> &loopBlocks) {
  std::vector<RawGuardChain> result;
  if (!canDiscardGuardBlock(head))
    return result;
  Inst *branch = head ? head->terminator() : nullptr;
  if (!branch || branch->getOp() != OP_BR)
    return result;
  BasicBlock *trueTarget = branch->getBr().trueBB;
  BasicBlock *falseTarget = branch->getBr().falseBB;

  const auto build = [&](BasicBlock *firstContinue, BasicBlock *skip,
                         bool continuesOnTrue) {
    RawGuardChain chain;
    chain.commonSkip = skip;
    chain.guards.push_back(
        {head, branch->getArg(0), continuesOnTrue, firstContinue});
    BasicBlock *current = firstContinue;
    while (loopBlocks.count(current) && current->getPredecessorCount() == 1) {
      Inst *currentBranch = current->terminator();
      if (!currentBranch || currentBranch->getOp() != OP_BR ||
          !canDiscardGuardBlock(current))
        break;
      BasicBlock *currentTrue = currentBranch->getBr().trueBB;
      BasicBlock *currentFalse = currentBranch->getBr().falseBB;
      if (currentTrue == currentFalse)
        break;
      BasicBlock *next = nullptr;
      bool nextOnTrue = true;
      if (currentFalse == skip) {
        next = currentTrue;
      } else if (currentTrue == skip) {
        next = currentFalse;
        nextOnTrue = false;
      } else {
        break;
      }
      if (next == skip || !loopBlocks.count(next) ||
          !hasSameSkipPhiValues(head, current, skip))
        break;
      chain.guards.push_back(
          {current, currentBranch->getArg(0), nextOnTrue, next});
      current = next;
    }
    return chain;
  };

  if (loopBlocks.count(trueTarget) && loopBlocks.count(falseTarget)) {
    result.push_back(build(trueTarget, falseTarget, true));
    result.push_back(build(falseTarget, trueTarget, false));
  }
  return result;
}

bool hasProtectedEntry(const Loop *loop) noexcept {
  BasicBlock *preheader = loop ? loop->getPreheader() : nullptr;
  if (!preheader || preheader->getPredecessorCount() != 1)
    return false;
  BasicBlock *guard = preheader->getPredecessor(0);
  Inst *branch = guard ? guard->terminator() : nullptr;
  if (!branch || branch->getOp() != OP_BR)
    return false;
  BasicBlock *other =
      branch->getBr().trueBB == preheader    ? branch->getBr().falseBB
      : branch->getBr().falseBB == preheader ? branch->getBr().trueBB
                                             : nullptr;
  return other && !loop->contains(other);
}

bool acceptsGrowth(const LoopVersionPlan &plan, PressureOracle &pressure,
                   Function *function) {
  if (plan.estimatedAddedInstructions > kMaxAddedInstructions)
    return false;
  const GrowthHint hint =
      pressure.hint(function, plan.estimatedAddedInstructions);
  if (hint.functionAfter > kMaxFunctionInstructions ||
      hint.moduleAddedObserved + plan.estimatedAddedInstructions >
          kMaxModuleGrowth ||
      hint.overall == PressureLevel::High ||
      hint.overall == PressureLevel::UnknownLarge)
    return false;
  return hint.moduleBaseline < kMinRatioBudgetBaseline ||
         hint.moduleGrowthRatio <= kMaxModuleGrowthRatio;
}

std::optional<Candidate> buildCandidate(Function *function, Loop *loop,
                                        const RawGuardChain &raw,
                                        const DominatorTree &dominators,
                                        const SCEV &scev,
                                        PressureOracle &pressure) {
  PredicatePlan predicatePlan;
  std::vector<GuardLink> guards;
  std::vector<LoopVersionPredicatePlan> predicates;
  for (const GuardLink &guard : raw.guards) {
    if (!guard.condition || guard.condition->getType() != TY_I1 ||
        guard.condition->isUndefValue() ||
        guard.condition->getOp() == OP_ICONST)
      break;
    PredicateQuery query;
    query.contextBlock = guard.block;
    if (scev.evaluatePredicate(guard.condition, query) != KnownBool::Unknown)
      break;
    PredicatePlan extended = predicatePlan;
    std::unordered_set<Inst *> visiting;
    if (!planPredicateValue(guard.condition, loop, loop->getPreheader(),
                            dominators, extended, visiting, 0))
      break;
    predicatePlan = std::move(extended);
    guards.push_back(guard);
    predicates.push_back({guard.condition, guard.continuesOnTrue});
  }
  if (guards.empty())
    return std::nullopt;

  const bool protectedEntry = hasProtectedEntry(loop);
  const i64 tripCount = scev.getConstantTripCount(loop);
  // 未证明一定入环时, 物化切片会改变zero-trip路径的求值时机
  if (!predicatePlan.order.empty() && !protectedEntry && tripCount < 1)
    return std::nullopt;
  auto plan = planLoopVersion(function, loop, predicates, predicatePlan.order,
                              dominators);
  if (!plan || !acceptsGrowth(*plan, pressure, function))
    return std::nullopt;

  const i64 boundedTrip = tripCount > 0 ? std::min<i64>(tripCount, 4096)
                                        : (loop->depth() >= 2 ? 32 : 8);
  const i64 penalty =
      protectedEntry ? 0 : static_cast<i64>(predicatePlan.order.size());
  const i64 rawScore = static_cast<i64>(guards.size()) * boundedTrip - penalty;
  if (rawScore <= 0)
    return std::nullopt;
  Candidate candidate;
  candidate.plan = std::move(*plan);
  candidate.guards = std::move(guards);
  candidate.commonSkip = raw.commonSkip;
  candidate.loopHeader = loop->header();
  candidate.score = rawScore > std::numeric_limits<i32>::max()
                        ? std::numeric_limits<i32>::max()
                        : static_cast<i32>(rawScore);
  return candidate;
}

std::optional<Candidate>
findCandidate(Function *function, FunctionAnalysisManager &analyses,
              PressureOracle &pressure,
              const std::unordered_map<BasicBlock *, i32> &transformsPerLoop) {
  const DominatorTree &dominators =
      analyses.getResult<DomAnalysis>(function).tree;
  const LoopInfo &loops = analyses.getResult<LoopInfoAnalysis>(function).info;
  const SCEV &scev = analyses.getResult<SCEVAnalysis>(function).info;
  std::optional<Candidate> best;
  for (Loop *loop : collectLoopsPostorder(loops)) {
    const auto applied = transformsPerLoop.find(loop->header());
    if (applied != transformsPerLoop.end() &&
        applied->second >= kMaxTransformsPerLoop)
      continue;
    std::unordered_set<BasicBlock *> loopBlocks(loop->blocks().begin(),
                                                loop->blocks().end());
    for (BasicBlock *block = function->region->first; block;
         block = block->next()) {
      if (!loop->contains(block) || loops.getLoopFor(block) != loop ||
          block == loop->header() ||
          (!loop->latches().empty() && block == loop->latches().front()))
        continue;
      Inst *branch = block->terminator();
      if (!branch || branch->getOp() != OP_BR ||
          branch->getBr().trueBB == branch->getBr().falseBB ||
          !loopBlocks.count(branch->getBr().trueBB) ||
          !loopBlocks.count(branch->getBr().falseBB))
        continue;
      for (const RawGuardChain &raw : buildRawChains(block, loopBlocks)) {
        std::optional<Candidate> candidate =
            buildCandidate(function, loop, raw, dominators, scev, pressure);
        if (candidate && (!best || candidate->score > best->score))
          best = std::move(candidate);
      }
    }
  }
  return best;
}

} // namespace

std::string_view SimpleLoopUnswitchPass::name() const noexcept {
  return "loop-unswitch";
}

PassResult SimpleLoopUnswitchPass::run(Function *function,
                                       PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first || !computePreds(function))
    return PassResult::noChange();
  computeUses(function);

  FunctionAnalysisManager &analyses = context.functionAnalyses();
#ifndef NDEBUG
  VERIFY(verifyLoopSimplify(function, analyses));
  VERIFY(verifyLCSSA(function, analyses));
#endif
  PressureOracle pressure(function->module);
  std::unordered_map<BasicBlock *, i32> transformsPerLoop;
  i32 transformed = 0;
  while (transformed < kMaxTransformsPerFunction) {
    std::optional<Candidate> candidate =
        findCandidate(function, analyses, pressure, transformsPerLoop);
    if (!candidate)
      break;

    const i32 added = candidate->plan.estimatedAddedInstructions;
    std::optional<LoopVersionResult> version =
        commitLoopVersion(function, candidate->plan);
    VERIFY(version.has_value());
    for (const GuardLink &guard : candidate->guards)
      VERIFY(CFGEditor::foldTerminatorToJump(function, guard.block,
                                             guard.continueTarget));
    BasicBlock *clonedHead = version->cloneOf(candidate->guards.front().block);
    BasicBlock *clonedSkip = version->cloneOf(candidate->commonSkip);
    VERIFY(clonedHead && clonedSkip);
    VERIFY(CFGEditor::foldTerminatorToJump(function, clonedHead, clonedSkip));
    UNUSED(cleanupDeadBlocks(function));
    pressure.recordApplied(function, added);
    ++transformsPerLoop[candidate->loopHeader];
    ++transformed;
    VERIFY(computePreds(function));
    computeUses(function);
    UNUSED(repairLoopForm(function, context));
  }

  if (transformed == 0)
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
