#include "LoopVersioning.h"
#include "DomAnalysis.h"
#include "Utils.h"

#include <limits>
#include <unordered_set>

namespace svm::ir {
namespace {

bool isReusableAtPreheader(Function *function, Inst *value, const Loop *loop,
                           BasicBlock *preheader,
                           const DominatorTree &dominators) noexcept {
  if (!function || !value || value->isErased() || !function->ownsValue(value))
    return false;
  BasicBlock *definition = value->parentBlock();
  if (!definition)
    return value->getOp() == OP_PARAM || value->isUndefValue() ||
           value->isPrecoloredDef() || isConstant(value->getOp());
  return !loop->contains(definition) &&
         dominators.dominates(definition, preheader);
}

bool isSafePredicateOp(OpCode op) noexcept {
  if (op == OP_DIV || op == OP_MOD)
    return false;
  return isArithmetic(op) || isUnaryArithmetic(op) || isCompare(op) ||
         isConversion(op) || isAddressingOp(op);
}

bool collectRegionLayout(Function *function, std::vector<BasicBlock *> &layout,
                         std::unordered_set<BasicBlock *> &members) {
  layout.clear();
  members.clear();
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || function->region->function != function ||
      !function->region->first || !function->region->last ||
      function->region->first->previous() || function->region->last->next())
    return false;

  BasicBlock *previous = nullptr;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (block->parentRegion != function->region ||
        block->previous() != previous || !members.insert(block).second)
      return false;
    layout.push_back(block);
    previous = block;
  }
  return previous == function->region->last;
}

bool hasLoopClosedUses(Function *function,
                       const std::vector<BasicBlock *> &regionLayout,
                       const std::unordered_set<BasicBlock *> &loopBlocks) {
  bool valid = true;
  for (BasicBlock *userBlock : regionLayout)
    forEachOp(userBlock, [&](Inst *user) {
      for (u32 index = 0; valid && index < user->getOperandCount(); ++index) {
        Inst *definition = user->getArg(index);
        BasicBlock *definitionBlock =
            definition ? definition->parentBlock() : nullptr;
        if (!definition || !function->ownsValue(definition)) {
          valid = false;
          break;
        }
        if (!loopBlocks.count(definitionBlock) || loopBlocks.count(userBlock))
          continue;
        if (user->getOp() != OP_PHI ||
            !loopBlocks.count(user->getIncomingBlock(index)))
          valid = false;
      }
    });
  return valid;
}

bool validatePredicates(Function *function, const Loop *loop,
                        BasicBlock *preheader,
                        const std::vector<LoopVersionPredicatePlan> &predicates,
                        const std::vector<Inst *> &materializationOrder,
                        const DominatorTree &dominators) {
  if (predicates.empty())
    return false;
  std::unordered_set<Inst *> materialized(materializationOrder.begin(),
                                          materializationOrder.end());
  if (materialized.size() != materializationOrder.size())
    return false;

  std::unordered_set<Inst *> available;
  for (Inst *inst : materializationOrder) {
    if (!inst || inst->isErased() || !inst->parentBlock() ||
        inst->parentBlock()->parentRegion != function->region ||
        !loop->contains(inst->parentBlock()) || isVoid(inst->getType()) ||
        !isSafePredicateOp(inst->getOp()))
      return false;
    for (u32 index = 0; index < inst->getOperandCount(); ++index) {
      Inst *operand = inst->getArg(index);
      if (!available.count(operand) &&
          !isReusableAtPreheader(function, operand, loop, preheader,
                                 dominators))
        return false;
    }
    available.insert(inst);
  }

  for (const LoopVersionPredicatePlan &predicate : predicates) {
    Inst *condition = predicate.condition;
    if (!condition || condition->getType() != TY_I1 || condition->isErased() ||
        condition->isUndefValue() || condition->getOp() == OP_ICONST ||
        (!materialized.count(condition) &&
         !isReusableAtPreheader(function, condition, loop, preheader,
                                dominators)))
      return false;
  }
  return true;
}

i32 countInstructions(const std::vector<BasicBlock *> &blocks,
                      const std::vector<LoopVersionExitPlan> &exits,
                      usize predicates, usize materialized) noexcept {
  // dispatch尾部和两个landing
  i64 count = static_cast<i64>(predicates) + 1 + static_cast<i64>(materialized);
  for (BasicBlock *block : blocks) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      ++count;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      ++count;
  }

  std::unordered_set<BasicBlock *> uniqueExits;
  for (const LoopVersionExitPlan &edge : exits)
    uniqueExits.insert(edge.exit);
  for (BasicBlock *exit : uniqueExits) {
    i64 exitingPredecessors = 0;
    for (const LoopVersionExitPlan &edge : exits)
      exitingPredecessors += edge.exit == exit;
    count += 2; // 两个版本各需一个dedicated-exit jump
    i64 phiCount = 0;
    for (Inst *phi = exit->firstPhi(); phi; phi = phi->next())
      ++phiCount;
    count += 2 * phiCount; // split透传值仍需在两个dedicated exit形成LCSSA
    if (exitingPredecessors > 1)
      count += 2 * phiCount; // 多前驱退出每个版本可能合并Phi
  }
  return count > std::numeric_limits<i32>::max()
             ? std::numeric_limits<i32>::max()
             : static_cast<i32>(count);
}

bool sameExitEdges(const Loop &loop,
                   const std::vector<LoopVersionExitPlan> &exits) {
  if (loop.exitingBlocks().size() != exits.size() ||
      loop.exitBlocks().size() != exits.size())
    return false;
  std::vector<u8> matched(exits.size());
  for (usize index = 0; index < loop.exitBlocks().size(); ++index) {
    bool found = false;
    for (usize edge = 0; edge < exits.size(); ++edge) {
      if (matched[edge] || exits[edge].exiting != loop.exitingBlocks()[index] ||
          exits[edge].exit != loop.exitBlocks()[index])
        continue;
      matched[edge] = 1;
      found = true;
      break;
    }
    if (!found)
      return false;
  }
  return true;
}

std::optional<LoopVersionPlan>
buildLoopVersionPlan(Function *function, Loop *loop,
                     const std::vector<LoopVersionPredicatePlan> &predicates,
                     const std::vector<Inst *> &materializationOrder,
                     const DominatorTree &dominators) {
  if (!function || !loop || !loop->header())
    return std::nullopt;

  std::vector<BasicBlock *> regionLayout;
  std::unordered_set<BasicBlock *> regionBlocks;
  if (!collectRegionLayout(function, regionLayout, regionBlocks))
    return std::nullopt;

  BasicBlock *header = loop->header();
  BasicBlock *preheader = loop->getPreheader();
  if (!regionBlocks.count(header) || !regionBlocks.count(preheader) ||
      !preheader->endsWithTerminator() ||
      preheader->terminator()->getOp() != OP_JMP ||
      preheader->terminator()->getJumpTarget() != header ||
      loop->latches().size() != 1 ||
      !validatePredicates(function, loop, preheader, predicates,
                          materializationOrder, dominators))
    return std::nullopt;

  std::unordered_set<BasicBlock *> loopBlocks;
  for (BasicBlock *block : loop->blocks())
    if (!regionBlocks.count(block) || !loopBlocks.insert(block).second ||
        !dominators.dominates(header, block))
      return std::nullopt;
  BasicBlock *latch = loop->latches().front();
  if (!loopBlocks.count(header) || loopBlocks.count(preheader) ||
      !loopBlocks.count(latch) || !CFGEditor::hasSemanticEdge(latch, header) ||
      !CFGEditor::hasConsistentIncomingState(preheader))
    return std::nullopt;
  if (header->getPredecessorCount() != 2)
    return std::nullopt;
  bool hasPreheader = false;
  bool hasLatch = false;
  for (u32 index = 0; index < header->getPredecessorCount(); ++index) {
    hasPreheader |= header->getPredecessor(index) == preheader;
    hasLatch |= header->getPredecessor(index) == latch;
  }
  if (!hasPreheader || !hasLatch)
    return std::nullopt;

  LoopVersionPlan plan;
  plan.loop = loop;
  plan.preheader = preheader;
  plan.header = header;
  plan.predicates = predicates;
  plan.predicateBranches.resize(predicates.size());
  plan.materializationOrder = materializationOrder;
  for (BasicBlock *block : regionLayout) {
    if (!loopBlocks.count(block))
      continue;
    if (!block->endsWithTerminator() ||
        !CFGEditor::hasConsistentIncomingState(block))
      return std::nullopt;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      if (inst->isErased() || inst->parentBlock() != block ||
          inst->getOp() == OP_ALLOCA ||
          (isTerminator(inst->getOp()) && inst != block->terminator()))
        return std::nullopt;
    plan.layoutBlocks.push_back(block);
    std::vector<BasicBlock *> targets;
    Inst *terminator = block->terminator();
    targets.reserve(terminator->getSuccessorSlotCount());
    for (u32 index = 0; index < terminator->getSuccessorSlotCount(); ++index) {
      BasicBlock *target = terminator->getSuccessorSlot(index);
      if (!regionBlocks.count(target))
        return std::nullopt;
      targets.push_back(target);
    }
    plan.successorTargets.push_back(std::move(targets));
    if (terminator->getOp() == OP_BR)
      for (usize index = 0; index < predicates.size(); ++index)
        if (terminator->getArg(0) == predicates[index].condition)
          plan.predicateBranches[index].push_back(terminator);
  }
  if (plan.layoutBlocks.size() != loopBlocks.size())
    return std::nullopt;
  for (const std::vector<Inst *> &branches : plan.predicateBranches)
    if (branches.empty())
      return std::nullopt;

  bool validExits = true;
  for (BasicBlock *exiting : plan.layoutBlocks)
    forEachSuccessor(exiting, [&](BasicBlock *exit) {
      if (!regionBlocks.count(exit)) {
        validExits = false;
        return;
      }
      if (!loopBlocks.count(exit))
        plan.exits.push_back({exiting, exit});
    });
  if (!validExits || !sameExitEdges(*loop, plan.exits))
    return std::nullopt;

  std::unordered_set<BasicBlock *> checkedExits;
  for (const LoopVersionExitPlan &edge : plan.exits) {
    if (!checkedExits.insert(edge.exit).second)
      continue;
    if (!CFGEditor::hasConsistentIncomingState(edge.exit))
      return std::nullopt;
    for (u32 index = 0; index < edge.exit->getPredecessorCount(); ++index)
      if (!loopBlocks.count(edge.exit->getPredecessor(index)))
        return std::nullopt;
  }

  if (!hasLoopClosedUses(function, regionLayout, loopBlocks) ||
      !DeepCopy::canAddTranslatedExitPhiIncomings(function, plan.layoutBlocks))
    return std::nullopt;
  plan.estimatedAddedInstructions =
      countInstructions(plan.layoutBlocks, plan.exits, plan.predicates.size(),
                        plan.materializationOrder.size());
  return plan;
}

bool matchesSnapshot(const LoopVersionPlan &expected,
                     const LoopVersionPlan &current) noexcept {
  if (expected.preheader != current.preheader ||
      expected.header != current.header ||
      expected.predicates.size() != current.predicates.size() ||
      expected.predicateBranches != current.predicateBranches ||
      expected.materializationOrder != current.materializationOrder ||
      expected.layoutBlocks != current.layoutBlocks ||
      expected.successorTargets != current.successorTargets ||
      expected.exits.size() != current.exits.size() ||
      expected.estimatedAddedInstructions != current.estimatedAddedInstructions)
    return false;
  for (usize index = 0; index < expected.predicates.size(); ++index)
    if (expected.predicates[index].condition !=
            current.predicates[index].condition ||
        expected.predicates[index].originalOnTrue !=
            current.predicates[index].originalOnTrue)
      return false;
  for (usize index = 0; index < expected.exits.size(); ++index)
    if (expected.exits[index].exiting != current.exits[index].exiting ||
        expected.exits[index].exit != current.exits[index].exit)
      return false;
  return true;
}

} // namespace

BasicBlock *LoopVersionResult::cloneOf(BasicBlock *source) const noexcept {
  for (const ClonedBlockPair &pair : clonedBlocks)
    if (pair.source == source)
      return pair.clone;
  return nullptr;
}

std::optional<LoopVersionPlan>
planLoopVersion(Function *function, Loop *loop,
                const std::vector<LoopVersionPredicatePlan> &predicates,
                const std::vector<Inst *> &materializationOrder,
                const DominatorTree &dominators) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !loop || !loop->header())
    return std::nullopt;
  return buildLoopVersionPlan(function, loop, predicates, materializationOrder,
                              dominators);
}

std::optional<LoopVersionResult>
commitLoopVersion(Function *function, const LoopVersionPlan &plan) {
  if (!function || !plan.loop || !plan.preheader || !plan.header ||
      plan.predicates.empty() || plan.layoutBlocks.empty())
    return std::nullopt;

  DominatorTree dominators;
  if (!dominators.build(function))
    return std::nullopt;
  LoopInfo loops;
  loops.build(function, dominators);
  Loop *currentLoop = loops.getLoopFor(plan.header);
  if (!currentLoop || currentLoop->header() != plan.header)
    return std::nullopt;
  std::optional<LoopVersionPlan> current =
      buildLoopVersionPlan(function, currentLoop, plan.predicates,
                           plan.materializationOrder, dominators);
  if (!current || !matchesSnapshot(plan, *current))
    return std::nullopt;

  IRBuilder builder(function->module, function);
  Inst *oldTerminator = plan.preheader->terminator();
  DeepCopy materializer(function);
  for (Inst *inst : plan.materializationOrder)
    VERIFY(materializer.copyInstBefore(inst, oldTerminator));
  std::vector<Inst *> conditions;
  conditions.reserve(plan.predicates.size());
  for (const LoopVersionPredicatePlan &predicate : plan.predicates)
    conditions.push_back(materializer.translate(predicate.condition));

  std::vector<BasicBlock *> dispatchBlocks(plan.predicates.size(),
                                           plan.preheader);
  BasicBlock *layout = plan.preheader;
  for (usize index = 1; index < dispatchBlocks.size(); ++index) {
    dispatchBlocks[index] = builder.newBlockAfter(layout);
    layout = dispatchBlocks[index];
  }
  BasicBlock *trueLanding = builder.newBlockAfter(layout);
  BasicBlock *falseLanding = builder.newBlockAfter(trueLanding);

  DeepCopy copier(function);
  copier.mapBlock(plan.preheader, falseLanding);
  BlockCloneConfig config;
  config.insertAfter = plan.layoutBlocks.back();
  std::vector<ClonedBlockPair> cloned =
      copier.copyBlocks(plan.layoutBlocks, config);
  VERIFY(cloned.size() == plan.layoutBlocks.size());
  VERIFY(copier.addTranslatedExitPhiIncomings(function, cloned));

  BasicBlock *clonedHeader = copier.translateBlock(plan.header);
  VERIFY(clonedHeader);

  builder.setInsertAtEnd(trueLanding);
  builder.emitJump(plan.header);
  builder.setInsertAtEnd(falseLanding);
  builder.emitJump(clonedHeader);

  for (usize index = 1; index < dispatchBlocks.size(); ++index) {
    BasicBlock *next = index + 1 < dispatchBlocks.size()
                           ? dispatchBlocks[index + 1]
                           : trueLanding;
    const LoopVersionPredicatePlan &predicate = plan.predicates[index];
    builder.setInsertAtEnd(dispatchBlocks[index]);
    builder.emitBranch(conditions[index],
                       predicate.originalOnTrue ? next : falseLanding,
                       predicate.originalOnTrue ? falseLanding : next);
  }

  VERIFY(CFGEditor::moveAndSetPhiEdgeValues(function, plan.header,
                                            plan.preheader, trueLanding, {}));
  BasicBlock *next =
      dispatchBlocks.size() > 1 ? dispatchBlocks[1] : trueLanding;
  const LoopVersionPredicatePlan &first = plan.predicates.front();
  builder.replaceWithBranch(oldTerminator, conditions.front(),
                            first.originalOnTrue ? next : falseLanding,
                            first.originalOnTrue ? falseLanding : next);
  VERIFY(computePreds(function));
  computeUses(function);

  LoopVersionResult result;
  result.originalLanding = trueLanding;
  result.clonedLanding = falseLanding;
  result.originalHeader = plan.header;
  result.clonedHeader = clonedHeader;
  result.clonedBlocks = std::move(cloned);
  return result;
}

} // namespace svm::ir
