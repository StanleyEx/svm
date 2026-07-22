#include "MemDep.h"
#include "Utils.h"

#include <optional>
#include <unordered_set>

namespace svm::ir {

namespace {

bool isCall(const Inst *inst) noexcept {
  return inst && (inst->getOp() == OP_CALL || inst->getOp() == MOP_CALL);
}

} // namespace

MemDepOracle::MemDepOracle(const AliasInfo *aliasInfo,
                           const GlobalSummaryResult *globalSummary) noexcept
    : aliasInfo_(aliasInfo), globalSummary_(globalSummary) {
  VERIFY(aliasInfo_, "MemDepOracle requires AliasInfo");
}

bool MemDepOracle::mayReadCall(Inst *call,
                               const MemoryLocation &location) const {
  if (!isCall(call))
    return false;
  if (!globalSummary_)
    return aliasInfo_->mayReadMemory(call, location);
  return aliasInfo_->mayReadMemory(
      call, location, globalSummary_->calleeEffect(call->getCallee()));
}

bool MemDepOracle::mayWriteCall(Inst *call,
                                const MemoryLocation &location) const {
  if (!isCall(call))
    return false;
  if (!globalSummary_)
    return aliasInfo_->mayWriteMemory(call, location);
  return aliasInfo_->mayWriteMemory(
      call, location, globalSummary_->calleeEffect(call->getCallee()));
}

bool MemDepOracle::mayClobber(Inst *definition,
                              const MemoryLocation &location) const {
  if (!definition || !location.pointer)
    return false;
  if (definition->getOp() == OP_STORE)
    return aliasInfo_->alias(MemoryLocation::fromMemoryInstruction(definition),
                             location) != AliasResult::NoAlias;
  return isCall(definition) && mayWriteCall(definition, location);
}

Inst *
MemDepOracle::scanBackwardForClobber(BasicBlock *block, Inst *from,
                                     const MemoryLocation &location) const {
  if (!block)
    return nullptr;
  for (Inst *cursor = from ? from->previous() : block->lastInst(); cursor;
       cursor = cursor->previous())
    if (mayClobber(cursor, location))
      return cursor;
  return nullptr;
}

Inst *MemDepOracle::findPrevStore(Inst *load) const {
  VERIFY(load && load->getOp() == OP_LOAD, "findPrevStore requires a load");
  Inst *hit = scanBackwardForClobber(
      load->parentBlock(), load, MemoryLocation::fromMemoryInstruction(load));
  return hit && hit->getOp() == OP_STORE ? hit : nullptr;
}

Inst *MemDepOracle::findNextLoad(Inst *store) const {
  VERIFY(store && store->getOp() == OP_STORE, "findNextLoad requires a store");
  const MemoryLocation stored = MemoryLocation::fromMemoryInstruction(store);

  for (Inst *current = store->next(); current; current = current->next()) {
    if (current->getOp() == OP_LOAD) {
      if (aliasInfo_->alias(stored, MemoryLocation::fromMemoryInstruction(
                                        current)) != AliasResult::NoAlias)
        return current;
    } else if (current->getOp() == OP_STORE) {
      if (aliasInfo_->alias(stored, MemoryLocation::fromMemoryInstruction(
                                        current)) != AliasResult::NoAlias)
        return nullptr;
    } else if (isCall(current) && mayWriteCall(current, stored)) {
      return nullptr;
    }
  }
  return nullptr;
}

Inst *MemDepOracle::findNextStore(Inst *store) const {
  VERIFY(store && store->getOp() == OP_STORE, "findNextStore requires a store");
  const MemoryLocation stored = MemoryLocation::fromMemoryInstruction(store);

  for (Inst *current = store->next(); current; current = current->next()) {
    if (current->getOp() == OP_STORE) {
      if (aliasInfo_->alias(stored, MemoryLocation::fromMemoryInstruction(
                                        current)) != AliasResult::NoAlias)
        return current;
    } else if (current->getOp() == OP_LOAD) {
      if (aliasInfo_->alias(stored, MemoryLocation::fromMemoryInstruction(
                                        current)) != AliasResult::NoAlias)
        return nullptr;
    } else if (isCall(current) && (mayReadCall(current, stored) ||
                                   mayWriteCall(current, stored))) {
      return nullptr;
    }
  }
  return nullptr;
}

bool MemDepOracle::hasClobberBetween(Inst *from, Inst *to,
                                     Inst *pointer) const {
  VERIFY(from && to && pointer, "clobber query requires non-null inputs");
  return hasClobberBetween(from, to, MemoryLocation{pointer, std::nullopt}) !=
         ClobberResult::NoClobber;
}

bool MemDepOracle::hasClobberInLoop(Inst *pointer, const Loop *loop) const {
  VERIFY(pointer, "loop clobber query requires a pointer");
  return hasClobberInLoop(MemoryLocation{pointer, std::nullopt}, loop);
}

bool MemDepOracle::hasClobberInLoop(const MemoryLocation &location,
                                    const Loop *loop) const {
  VERIFY(location.pointer && loop,
         "loop clobber query requires a location and loop");
  for (BasicBlock *block : loop->blocks())
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      if (mayClobber(inst, location))
        return true;
  return false;
}

Inst *MemDepOracle::findClobberOnLinearPath(Inst *pointer,
                                            BasicBlock *startBlock,
                                            BasicBlock *stopBlock,
                                            bool &gaveUp) const {
  VERIFY(pointer, "linear clobber query requires a pointer");
  return findClobberOnLinearPath(MemoryLocation{pointer, std::nullopt},
                                 startBlock, stopBlock, gaveUp);
}

Inst *MemDepOracle::findClobberOnLinearPath(const MemoryLocation &location,
                                            BasicBlock *startBlock,
                                            BasicBlock *stopBlock,
                                            bool &gaveUp) const {
  gaveUp = false;
  VERIFY(location.pointer && startBlock,
         "linear clobber query requires a location and start block");

  std::unordered_set<BasicBlock *> visited;
  for (BasicBlock *block = startBlock; block;) {
    if (!visited.insert(block).second) {
      gaveUp = true;
      return nullptr;
    }
    if (Inst *hit = scanBackwardForClobber(block, nullptr, location))
      return hit;
    if (block == stopBlock || block->getPredecessorCount() == 0)
      return nullptr;
    if (block->getPredecessorCount() != 1) {
      gaveUp = true;
      return nullptr;
    }
    block = block->getPredecessor(0);
  }
  return nullptr;
}

Inst *MemDepOracle::findNextKillerStore(Inst *store,
                                        MemDepQueryBudget budget) const {
  VERIFY(store && store->getOp() == OP_STORE,
         "findNextKillerStore requires a store");
  if (budget.maxBlocks == 0)
    return nullptr;

  const MemoryLocation target = MemoryLocation::fromMemoryInstruction(store);
  BasicBlock *block = store->parentBlock();
  Inst *current = store->next();
  u32 memoryEvents = 0;
  u32 blocks = 1;

  while (block) {
    while (current) {
      if (current == store)
        return nullptr;
      const OpCode op = current->getOp();
      if (op == OP_LOAD || op == OP_STORE || isCall(current)) {
        if (memoryEvents >= budget.maxMemoryEvents)
          return nullptr;
        ++memoryEvents;
      }

      if (op == OP_LOAD) {
        AliasQuery query;
        query.contextBlock = current->parentBlock();
        if (aliasInfo_->alias(target,
                              MemoryLocation::fromMemoryInstruction(current),
                              query) != AliasResult::NoAlias)
          return nullptr;
      } else if (op == OP_STORE) {
        const MemoryLocation written =
            MemoryLocation::fromMemoryInstruction(current);
        if (aliasInfo_->fullyCovers(written, target))
          return current;
        AliasQuery query;
        query.contextBlock = current->parentBlock();
        if (aliasInfo_->alias(target, written, query) != AliasResult::NoAlias)
          return nullptr;
      } else if (isCall(current) && (mayReadCall(current, target) ||
                                     mayWriteCall(current, target))) {
        return nullptr;
      }
      current = current->next();
    }

    BasicBlock *successor = nullptr;
    u32 successorCount = 0;
    forEachSuccessor(block, [&](BasicBlock *candidate) {
      successor = candidate;
      ++successorCount;
    });
    if (successorCount != 1 || successor->getPredecessorCount() != 1)
      return nullptr;
    if (blocks >= budget.maxBlocks)
      return nullptr;
    ++blocks;
    block = successor;
    current = block->firstInst();
  }
  return nullptr;
}

MemDepOracle::ClobberResult
MemDepOracle::hasClobberBefore(Inst *target,
                               const MemoryLocation &location) const {
  if (!target || !target->parentBlock() || !location.pointer)
    return ClobberResult::MayClobber;

  Inst *hit = scanBackwardForClobber(target->parentBlock(), target, location);
  if (!hit) {
    BasicBlock *block = target->parentBlock();
    if (block->parentRegion && block->parentRegion->first == block)
      return block->getPredecessorCount() == 0 ? ClobberResult::NoClobber
                                               : ClobberResult::MayClobber;
    if (block->getPredecessorCount() == 0)
      return ClobberResult::NoClobber;
    if (block->getPredecessorCount() != 1)
      return ClobberResult::MayClobber;
    bool gaveUp = false;
    hit = findClobberOnLinearPath(location, block->getPredecessor(0), nullptr,
                                  gaveUp);
    if (gaveUp)
      return ClobberResult::MayClobber;
    if (!hit)
      return ClobberResult::NoClobber;
  }

  if (hit->getOp() == OP_STORE &&
      aliasInfo_->alias(MemoryLocation::fromMemoryInstruction(hit), location) ==
          AliasResult::MustAlias)
    return ClobberResult::MustClobber;
  return ClobberResult::MayClobber;
}

MemDepOracle::ClobberResult
MemDepOracle::hasClobberBetween(Inst *from, Inst *to,
                                const MemoryLocation &location) const {
  if (!from || !to || !location.pointer || !from->parentBlock() ||
      from->parentBlock() != to->parentBlock())
    return ClobberResult::MayClobber;

  ClobberResult nearest = ClobberResult::NoClobber;
  for (Inst *current = to->previous(); current; current = current->previous()) {
    if (current == from)
      return nearest;
    if (nearest != ClobberResult::NoClobber)
      continue;
    if (current->getOp() == OP_STORE) {
      const AliasResult alias = aliasInfo_->alias(
          MemoryLocation::fromMemoryInstruction(current), location);
      if (alias == AliasResult::MustAlias)
        nearest = ClobberResult::MustClobber;
      else if (alias != AliasResult::NoAlias)
        nearest = ClobberResult::MayClobber;
    } else if (isCall(current) && mayWriteCall(current, location)) {
      nearest = ClobberResult::MayClobber;
    }
  }
  return ClobberResult::MayClobber;
}

} // namespace svm::ir
