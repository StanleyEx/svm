#include "Analysis.h"
#include "DeepCopy.h"
#include "LIRPass.h"
#include "PredicateContext.h"

#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

constexpr u32 kMaxEdits = 128;
constexpr u32 kMaxHeaderClones = 16;
constexpr u32 kMaxHeaderCloneInsts = 64;

class BlockWorklist {
public:
  void push(BasicBlock *block) {
    if (block && queued_.insert(block).second)
      blocks_.push_back(block);
  }
  bool empty() const noexcept { return blocks_.empty(); }
  BasicBlock *pop() {
    BasicBlock *block = blocks_.back();
    blocks_.pop_back();
    queued_.erase(block);
    return block;
  }
  void pushNeighborhood(BasicBlock *block) {
    if (!block)
      return;
    push(block);
    for (u32 index = 0; index < block->getPredecessorCount(); ++index)
      push(block->getPredecessor(index));
    forEachSuccessor(block, [&](BasicBlock *successor) { push(successor); });
  }

private:
  std::vector<BasicBlock *> blocks_; // LIFO
  std::unordered_set<BasicBlock *> queued_;
};

struct RepairState {
  bool demotedAny = false; // 是否创建过临时栈槽
};

struct EdgeRepairPlan {
  std::vector<CFGEditor::PhiEdgeValue> destinationValues; // 新边Phi列
  std::vector<Inst *> demotedPhis; // 需通过内存重建的中间Phi
};

struct UseSite {
  Inst *user = nullptr; // 原Phi Use
  u16 argument = 0;     // Use 操作数槽
};

bool isThreadableConditionOp(OpCode op) noexcept {
  return op != OP_DIV && op != OP_MOD &&
         (isIntArithmetic(op) || isIntCompare(op) || op == OP_ZEXT);
}

bool isThreadableConditionBlock(BasicBlock *block, Inst *terminator,
                                bool allowConstantDivisor,
                                bool requireLocalPhis = false) noexcept {
  if (requireLocalPhis)
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      for (const Use *use = phi->uses(); use; use = use->next)
        if (!use->user || use->user->parentBlock() != block)
          return false;

  for (Inst *inst = block->firstInst(); inst && inst != terminator;
       inst = inst->next()) {
    bool allowed = isThreadableConditionOp(inst->getOp());
    if (!allowed && allowConstantDivisor &&
        (inst->getOp() == OP_DIV || inst->getOp() == OP_MOD) &&
        inst->getOperandCount() == 2) {
      Inst *divisor = inst->getArg(1);
      allowed = divisor->getOp() == OP_ICONST && divisor->getImm() != 0;
    }
    if (!allowed)
      return false;
    for (const Use *use = inst->uses(); use; use = use->next)
      if (!use->user || use->user->parentBlock() != block)
        return false;
  }
  return true;
}

// Header-incoming克隆会少执行一次循环头 因此只能跳过不可观测且不陷阱的计算
bool isSkippableHeaderBlock(BasicBlock *block, Inst *terminator) noexcept {
  for (Inst *inst = block->firstInst(); inst && inst != terminator;
       inst = inst->next()) {
    const OpCode op = inst->getOp();
    if (op == OP_DIV || op == OP_MOD) {
      if (inst->getOperandCount() != 2 ||
          inst->getArg(1)->getOp() != OP_ICONST ||
          inst->getArg(1)->getImm() == 0)
        return false;
      continue;
    }
    if (!isBinaryArithmetic(op) && !isUnaryArithmetic(op) && !isCompare(op) &&
        !isConversion(op) && !isAddressingOp(op) && op != OP_SELECT)
      return false;
  }
  return true;
}

bool isLoopHeader(BasicBlock *block, const DominatorTree &dominators) noexcept {
  if (!block)
    return false;
  for (u32 index = 0; index < block->getPredecessorCount(); ++index)
    if (dominators.dominates(block, block->getPredecessor(index)))
      return true;
  return false;
}

u32 physicalSlotsToward(BasicBlock *predecessor,
                        BasicBlock *successor) noexcept {
  Inst *terminator = predecessor ? predecessor->terminator() : nullptr;
  if (!terminator)
    return 0;
  u32 count = 0;
  for (u32 index = 0; index < terminator->getSuccessorSlotCount(); ++index)
    if (terminator->getSuccessorSlot(index) == successor)
      ++count;
  return count;
}

Inst *uniqueIncoming(Inst *phi, BasicBlock *predecessor) noexcept {
  if (!phi || phi->getOp() != OP_PHI || !predecessor)
    return nullptr;
  Inst *result = nullptr;
  for (u32 index = 0; index < phi->getOperandCount(); ++index) {
    if (phi->getIncomingBlock(index) != predecessor)
      continue;
    if (result)
      return nullptr;
    result = phi->getArg(index);
  }
  return result;
}

BasicBlock *proveDirection(const SCEV *scev, BasicBlock *predecessor,
                           BasicBlock *block, Inst *branch) {
  const BrPayload &targets = branch->getBr();
  if (targets.trueBB == targets.falseBB)
    return nullptr;
  Inst *condition = branch->getArg(0);
  if (!condition)
    return nullptr;

  if (condition->getOp() == OP_PHI && condition->parentBlock() == block) {
    Inst *incoming = uniqueIncoming(condition, predecessor);
    if (incoming && incoming->getOp() == OP_ICONST)
      return incoming->getImm() ? targets.trueBB : targets.falseBB;
    return nullptr;
  }
  if (!scev || !isIntCompare(condition->getOp()))
    return nullptr;

  PredicateContext edge = buildEdgeContext(scev, predecessor, block);
  PredicateQuery query;
  query.contextBlock = block;
  query.predicateContext = &edge;
  const KnownBool result = scev->evaluatePredicate(condition, query);
  if (result == KnownBool::AlwaysTrue)
    return targets.trueBB;
  if (result == KnownBool::AlwaysFalse)
    return targets.falseBB;
  return nullptr;
}

void demotePhi(Function *function, Inst *phi, RepairState &repair) {
  const IRType type = phi->getType();
  IRBuilder builder(function->module, function);
  builder.setInsertAtStart(function->region->first);
  Inst *slot = builder.emitAlloca(static_cast<u32>(typeSizeBytes(type)), type);

  std::vector<std::pair<BasicBlock *, Inst *>> incoming;
  incoming.reserve(phi->getOperandCount());
  for (u32 index = 0; index < phi->getOperandCount(); ++index)
    incoming.emplace_back(phi->getIncomingBlock(index), phi->getArg(index));
  for (const auto &[predecessor, value] : incoming) {
    builder.setInsertBefore(predecessor->terminator());
    builder.emitStore(slot, value, type);
  }

  std::vector<UseSite> uses;
  for (const Use *use = phi->uses(); use; use = use->next)
    uses.push_back({use->user, use->argNo});
  for (const UseSite &site : uses) {
    BasicBlock *loadBlock = site.user->getOp() == OP_PHI
                                ? site.user->getIncomingBlock(site.argument)
                                : site.user->parentBlock();
    Inst *anchor =
        site.user->getOp() == OP_PHI ? loadBlock->terminator() : site.user;
    builder.setInsertBefore(anchor);
    site.user->setArg(site.argument, builder.emitLoad(slot, type));
  }
  VERIFY(phi->eraseFromBlock());
  repair.demotedAny = true;
}

bool buildRepairPlan(const DominatorTree &dominators, BasicBlock *predecessor,
                     BasicBlock *block, BasicBlock *destination,
                     EdgeRepairPlan &plan) {
  for (Inst *phi = destination->firstPhi(); phi; phi = phi->next()) {
    Inst *oldValue = CFGEditor::getPhiIncomingValue(phi, block);
    if (!oldValue)
      return false;
    Inst *newValue = nullptr;
    BasicBlock *definition = oldValue->parentBlock();
    if (!definition) {
      newValue = oldValue;
    } else if (definition == block) {
      if (oldValue->getOp() != OP_PHI)
        return false;
      newValue = uniqueIncoming(oldValue, predecessor);
    } else if (dominators.dominates(definition, predecessor)) {
      newValue = oldValue;
    }
    if (!newValue)
      return false;
    plan.destinationValues.push_back({phi, newValue});
  }

  if (CFGEditor::hasSemanticEdge(predecessor, destination))
    for (const CFGEditor::PhiEdgeValue &entry : plan.destinationValues)
      if (CFGEditor::getPhiIncomingValue(entry.phi, predecessor) != entry.value)
        return false;

  for (Inst *phi = block->firstPhi(); phi; phi = phi->next()) {
    bool needsDemotion = false;
    for (const Use *use = phi->uses(); use; use = use->next) {
      Inst *user = use->user;
      if (user && user->parentBlock() != block &&
          (user->getOp() != OP_PHI ||
           user->getIncomingBlock(use->argNo) != block)) {
        needsDemotion = true;
        break;
      }
    }
    if (!needsDemotion)
      continue;
    if (phi->getType() != TY_I1 && phi->getType() != TY_I32 &&
        phi->getType() != TY_F32)
      return false;
    plan.demotedPhis.push_back(phi);
  }
  return true;
}

bool threadOrdinaryBlock(Function *function, const DominatorTree &dominators,
                         const SCEV *scev, BasicBlock *block,
                         RepairState &repair, BlockWorklist &worklist) {
  Inst *branch = block ? block->terminator() : nullptr;
  if (!branch || branch->getOp() != OP_BR || isLoopHeader(block, dominators) ||
      !isThreadableConditionBlock(block, branch, false))
    return false;

  std::vector<BasicBlock *> predecessors;
  for (u32 index = 0; index < block->getPredecessorCount(); ++index)
    predecessors.push_back(block->getPredecessor(index));
  for (BasicBlock *predecessor : predecessors) {
    if (!predecessor || !predecessor->endsWithTerminator() ||
        physicalSlotsToward(predecessor, block) != 1)
      continue;
    BasicBlock *destination = proveDirection(scev, predecessor, block, branch);
    if (!destination || destination == block)
      continue;

    EdgeRepairPlan plan;
    if (!buildRepairPlan(dominators, predecessor, block, destination, plan))
      continue;
    for (Inst *phi : plan.demotedPhis)
      demotePhi(function, phi, repair);

    const bool duplicate = CFGEditor::hasSemanticEdge(predecessor, destination);
    const bool redirected =
        duplicate
            ? CFGEditor::redirectEdgeAndMerge(function, predecessor, block,
                                              destination,
                                              plan.destinationValues)
            : CFGEditor::redirectEdge(function, predecessor, block, destination,
                                      plan.destinationValues);
    VERIFY(redirected);
    VERIFY(computePreds(function));
    worklist.pushNeighborhood(predecessor);
    worklist.pushNeighborhood(block);
    worklist.pushNeighborhood(destination);
    return true;
  }
  return false;
}

bool isCloneableTransition(BasicBlock *block, BasicBlock *header) noexcept {
  if (!block || block == header || block->firstPhi())
    return false;
  Inst *terminator = block->terminator();
  if (!terminator || terminator->getOp() != OP_JMP ||
      terminator->getJumpTarget() != header)
    return false;
  for (Inst *inst = block->firstInst(); inst && inst != terminator;
       inst = inst->next()) {
    const OpCode op = inst->getOp();
    if (!isIntArithmetic(op) && !isIntCompare(op) && op != OP_ZEXT &&
        op != OP_GETPTR)
      return false;
  }
  return true;
}

bool headerAlwaysReaches(const SCEV &scev, BasicBlock *header,
                         BasicBlock *conditionBlock,
                         const PredicateContext &facts) {
  Inst *terminator = header ? header->terminator() : nullptr;
  if (!terminator)
    return false;
  if (terminator->getOp() == OP_JMP)
    return terminator->getJumpTarget() == conditionBlock;
  if (terminator->getOp() != OP_BR ||
      terminator->getBr().trueBB == terminator->getBr().falseBB)
    return false;

  PredicateQuery query;
  query.contextBlock = header;
  query.predicateContext = &facts;
  const KnownBool result = scev.evaluatePredicate(terminator->getArg(0), query);
  return (terminator->getBr().trueBB == conditionBlock &&
          result == KnownBool::AlwaysTrue) ||
         (terminator->getBr().falseBB == conditionBlock &&
          result == KnownBool::AlwaysFalse);
}

BasicBlock *evaluateCondition(const SCEV &scev, BasicBlock *block,
                              const PredicateContext &facts) {
  Inst *branch = block ? block->terminator() : nullptr;
  if (!branch || branch->getOp() != OP_BR ||
      branch->getBr().trueBB == branch->getBr().falseBB ||
      !isIntCompare(branch->getArg(0)->getOp()))
    return nullptr;
  PredicateQuery query;
  query.contextBlock = block;
  query.predicateContext = &facts;
  const KnownBool result = scev.evaluatePredicate(branch->getArg(0), query);
  return result == KnownBool::AlwaysTrue    ? branch->getBr().trueBB
         : result == KnownBool::AlwaysFalse ? branch->getBr().falseBB
                                            : nullptr;
}

bool cloneTransition(Function *function, const DominatorTree &dominators,
                     BasicBlock *predecessor, BasicBlock *header,
                     BasicBlock *source) {
  std::unordered_map<Inst *, Inst *> headerValues;
  for (Inst *phi = header->firstPhi(); phi; phi = phi->next()) {
    Inst *incoming = uniqueIncoming(phi, predecessor);
    if (!incoming)
      return false;
    headerValues.emplace(phi, incoming);
  }

  auto visibleAtPredecessor = [&](Inst *value) {
    if (!value || !value->parentBlock() || headerValues.count(value) ||
        value->parentBlock() == source)
      return true;
    if (value->parentBlock() == header)
      return false;
    return dominators.dominates(value->parentBlock(), predecessor);
  };
  for (Inst *inst = source->firstInst(); inst; inst = inst->next())
    for (u32 index = 0; index < inst->getOperandCount(); ++index)
      if (!visibleAtPredecessor(inst->getArg(index)))
        return false;

  std::vector<std::pair<Inst *, Inst *>> phiSources;
  for (Inst *phi = header->firstPhi(); phi; phi = phi->next()) {
    Inst *value = uniqueIncoming(phi, source);
    if (!value ||
        (!visibleAtPredecessor(value) && value->parentBlock() != source))
      return false;
    phiSources.emplace_back(phi, value);
  }
  if (physicalSlotsToward(predecessor, header) != 1)
    return false;

  IRBuilder builder(function->module, function);
  BasicBlock *clone = builder.newBlockAfter(predecessor);
  builder.setInsertAtEnd(clone);
  Inst *temporaryTerminator = builder.emit(OP_UNREACHABLE, TY_VOID);
  DeepCopy copier(function);
  for (Inst *inst = source->firstInst(); inst && inst != source->terminator();
       inst = inst->next()) {
    Inst *copied = copier.copyInstBefore(
        inst, temporaryTerminator, [&](Inst *value) -> Inst * {
          const auto found = headerValues.find(value);
          return found == headerValues.end() ? nullptr : found->second;
        });
    VERIFY(copied);
  }

  std::vector<CFGEditor::PhiEdgeValue> newHeaderValues;
  for (const auto &[phi, sourceValue] : phiSources) {
    Inst *translated = nullptr;
    const auto headerValue = headerValues.find(sourceValue);
    if (headerValue != headerValues.end())
      translated = headerValue->second;
    else
      translated = copier.translate(sourceValue);
    if (!translated)
      translated = sourceValue;
    newHeaderValues.push_back({phi, translated});
  }

  VERIFY(CFGEditor::redirectEdge(function, predecessor, header, clone));
  builder.replaceWithJump(temporaryTerminator, header);
  VERIFY(CFGEditor::addPhiEdgeValues(function, header, clone, newHeaderValues));
  VERIFY(computePreds(function));
  return true;
}

bool threadHeaderIncoming(Function *function, const DominatorTree &dominators,
                          const SCEV &scev, BasicBlock *header, u32 &cloneCount,
                          BlockWorklist &worklist) {
  if (cloneCount >= kMaxHeaderClones || !header || !header->firstPhi() ||
      !isLoopHeader(header, dominators))
    return false;
  Inst *headerTerminator = header->terminator();
  if (!headerTerminator ||
      (headerTerminator->getOp() != OP_BR &&
       headerTerminator->getOp() != OP_JMP) ||
      !isSkippableHeaderBlock(header, headerTerminator))
    return false;

  BasicBlock *selectedPredecessor = nullptr;
  BasicBlock *selectedDestination = nullptr;
  forEachSuccessor(header, [&](BasicBlock *conditionBlock) {
    if (selectedDestination || !conditionBlock || conditionBlock == header ||
        isLoopHeader(conditionBlock, dominators))
      return;
    Inst *conditionTerminator = conditionBlock->terminator();
    if (!conditionTerminator || conditionTerminator->getOp() != OP_BR ||
        !isThreadableConditionBlock(conditionBlock, conditionTerminator, true,
                                    true))
      return;
    if (!isCloneableTransition(conditionTerminator->getBr().trueBB, header) &&
        !isCloneableTransition(conditionTerminator->getBr().falseBB, header))
      return;

    for (u32 index = 0; index < header->getPredecessorCount(); ++index) {
      BasicBlock *predecessor = header->getPredecessor(index);
      if (!predecessor || !dominators.dominates(header, predecessor) ||
          physicalSlotsToward(predecessor, header) != 1)
        continue;
      PredicateContext path =
          buildUniquePredPathContext(&scev, predecessor, header, 16);
      PredicateContext facts = buildLoopHeaderIncomingContext(
          &scev, predecessor, header, path, dominators);
      if (!headerAlwaysReaches(scev, header, conditionBlock, facts))
        continue;
      BasicBlock *destination = evaluateCondition(scev, conditionBlock, facts);
      if (!isCloneableTransition(destination, header))
        continue;
      u32 instructionCount = 0;
      for (Inst *inst = destination->firstInst(); inst; inst = inst->next())
        ++instructionCount;
      if (instructionCount > kMaxHeaderCloneInsts)
        continue;
      selectedPredecessor = predecessor;
      selectedDestination = destination;
      break;
    }
  });
  if (!selectedDestination ||
      !cloneTransition(function, dominators, selectedPredecessor, header,
                       selectedDestination))
    return false;

  ++cloneCount;
  worklist.pushNeighborhood(selectedPredecessor);
  worklist.pushNeighborhood(header);
  return true;
}

bool runJumpThreading(Function *function, PassContext &context) {
  std::vector<BasicBlock *> rpo = computeRPO(function);
  u32 instructionCount = 0;
  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      ++instructionCount;
  const bool lazyLargeFunction = rpo.size() > 512 || instructionCount > 6000;
  const u32 maxVisits = static_cast<u32>(rpo.size()) * 8 + 64;

  BlockWorklist worklist;
  for (BasicBlock *block : rpo)
    worklist.push(block);
  RepairState repair;
  FunctionAnalysisManager &analyses = context.functionAnalyses();
  const DominatorTree *dominators = nullptr;
  const SCEV *scev = nullptr;
  bool dirty = true;
  auto refresh = [&](bool needSCEV) {
    if (!dirty)
      return;
    VERIFY(computePreds(function));
    analyses.clear(function);
    dominators = &context.get<DomAnalysis>(function).tree;
    scev = needSCEV ? &context.get<SCEVAnalysis>(function).info : nullptr;
    dirty = false;
  };

  bool changed = false;
  u32 edits = 0;
  u32 visits = 0;
  u32 headerClones = 0;
  while (!worklist.empty() && edits < kMaxEdits && visits++ < maxVisits) {
    BasicBlock *block = worklist.pop();
    if (!block || !block->parentRegion || !block->endsWithTerminator())
      continue;
    if (dirty) {
      // 大函数改图后只重建支配树 避免复用旧CFG事实且不重复构建SCEV
      const bool needSCEV = !lazyLargeFunction || !dominators;
      refresh(needSCEV);
    }
    const SCEV *proofSCEV = scev;
    if (threadOrdinaryBlock(function, *dominators, proofSCEV, block, repair,
                            worklist)) {
      ++edits;
      changed = dirty = true;
      continue;
    }
    if (!lazyLargeFunction &&
        threadHeaderIncoming(function, *dominators, *scev, block, headerClones,
                             worklist)) {
      ++edits;
      changed = dirty = true;
    }
  }

  if (!changed)
    return false;
  VERIFY(computePreds(function));
  if (cleanupDeadBlocks(function))
    VERIFY(computePreds(function));
  analyses.clear(function);
  if (repair.demotedAny) {
    Mem2RegPass promotion;
    const PassResult promoted = promotion.run(function, context);
    VERIFY(promoted.changed);
    analyses.clear(function);
  }
  return true;
}

} // namespace

std::string_view JumpThreadingPass::name() const noexcept {
  return "jump-threading";
}

PassResult JumpThreadingPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();
  return runJumpThreading(function, context) ? PassResult::changedIR()
                                             : PassResult::noChange();
}

} // namespace svm::ir
