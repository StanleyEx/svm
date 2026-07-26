#include "IR.h"

#include <algorithm>
#include <cstring>
#include <functional>
#include <limits>
#include <unordered_map>
#include <unordered_set>
#include <utility>

namespace svm::ir {
namespace {
bool isFlatCFGBlock(const Function *function,
                    const BasicBlock *block) noexcept {
  return function && function->phase != IRPhase::HIR && function->region &&
         function->region->function == function && block &&
         block->parentRegion == function->region;
}

bool collectFlatCFGBlocks(Function *function, std::vector<BasicBlock *> &blocks,
                          std::unordered_set<BasicBlock *> &blockSet) {
  blocks.clear();
  blockSet.clear();
  if (!function || function->phase == IRPhase::HIR || !function->region ||
      function->region->function != function)
    return false;
  // 保留布局顺序和成员集合 前者决定predecessor顺序
  // 后者用于拒绝跨Region的CFG边和损坏的块链表
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (block->parentRegion != function->region ||
        !blockSet.insert(block).second)
      return false;
    blocks.push_back(block);
  }
  return true;
}

bool collectPhiPlan(BasicBlock *succ,
                    const std::vector<CFGEditor::PhiEdgeValue> &values,
                    std::unordered_map<Inst *, Inst *> &plan,
                    bool requireComplete) {
  plan.clear();
  plan.reserve(values.size());
  if (!requireComplete && values.empty())
    return false;
  for (const CFGEditor::PhiEdgeValue &entry : values) {
    if (!entry.phi || entry.phi->getOp() != OP_PHI ||
        entry.phi->parentBlock() != succ || !entry.value ||
        !plan.emplace(entry.phi, entry.value).second)
      return false;
  }
  if (!requireComplete)
    return true;
  // 新增CFG边必须覆盖目标块的全部Phi 局部改值则只校验给定子集
  u32 phiCount = 0;
  for (Inst *phi = succ ? succ->firstPhi() : nullptr; phi; phi = phi->next())
    ++phiCount;
  return plan.size() == phiCount;
}

// CFG批量事务中物理边和predecessor元数据可暂时错位 此检查只验证元数据自身
bool hasAlignedIncomingMetadata(BasicBlock *block) {
  if (!block || !block->parentRegion)
    return false;
  std::unordered_set<BasicBlock *> predecessors;
  for (u32 index = 0; index < block->getPredecessorCount(); ++index) {
    BasicBlock *predecessor = block->getPredecessor(index);
    if (!predecessor || predecessor->parentRegion != block->parentRegion ||
        !predecessors.insert(predecessor).second)
      return false;
  }
  for (Inst *phi = block->firstPhi(); phi; phi = phi->next()) {
    if (phi->getOperandCount() != block->getPredecessorCount())
      return false;
    for (u32 index = 0; index < phi->getOperandCount(); ++index)
      if (phi->getIncomingBlock(index) != block->getPredecessor(index) ||
          !phi->getArg(index))
        return false;
  }
  return true;
}

} // namespace

std::vector<BasicBlock *> computeRPO(Function *function) {
  std::vector<BasicBlock *> postorder;
  std::vector<BasicBlock *> blocks;
  std::unordered_set<BasicBlock *> blockSet;
  if (!collectFlatCFGBlocks(function, blocks, blockSet) || blocks.empty())
    return postorder;

  std::unordered_set<BasicBlock *> visited;
  bool valid = true;
  std::function<void(BasicBlock *)> dfs = [&](BasicBlock *block) {
    if (!valid || !blockSet.count(block)) {
      valid = false;
      return;
    }
    if (!visited.insert(block).second)
      return;
    forEachSuccessor(block, dfs);
    postorder.push_back(block);
  };
  dfs(blocks.front());
  if (!valid) {
    postorder.clear();
    return postorder;
  }
  std::reverse(postorder.begin(), postorder.end());
  return postorder;
}

bool CFGEditor::hasConsistentIncomingState(BasicBlock *block) {
  if (!block || !block->parentRegion)
    return false;

  // 先推导去重后的语义前驱集合
  std::unordered_set<BasicBlock *> expected;
  for (BasicBlock *pred = block->parentRegion->first; pred;
       pred = pred->next()) {
    bool reachesBlock = false;
    forEachSuccessor(pred, [&](BasicBlock *succ) {
      if (succ == block)
        reachesBlock = true;
    });
    if (reachesBlock)
      expected.insert(pred);
  }

  // 检查predecessor唯一性
  std::unordered_set<BasicBlock *> seen;
  if (block->predecessorCount_ != expected.size())
    return false;
  for (u32 i = 0; i < block->predecessorCount_; ++i) {
    BasicBlock *pred = block->predecessors_[i];
    if (!pred || pred->parentRegion != block->parentRegion ||
        !seen.insert(pred).second || !expected.count(pred))
      return false;
  }

  // Phi槽位对齐和argNo的完整性
  for (Inst *phi = block->phiFirst_; phi; phi = phi->next_) {
    if (phi->op_ != OP_PHI || phi->block_ != block ||
        phi->operandCount_ != block->predecessorCount_)
      return false;

    std::unordered_set<Inst *> definitions;
    for (u32 i = 0; i < phi->operandCount_; ++i) {
      Inst *value = phi->args_[i].inst;
      if (phi->incoming_[i] != block->predecessors_[i] || !value)
        return false;
      if (value->tracksUses())
        definitions.insert(value);
    }

    std::vector<u32> useCounts(phi->operandCount_);
    for (Inst *definition : definitions)
      for (const Use *use = definition->uses(); use; use = use->next)
        if (use->user == phi) {
          if (use->argNo >= phi->operandCount_ ||
              phi->args_[use->argNo].inst != definition)
            return false;
          ++useCounts[use->argNo];
        }
    for (u32 i = 0; i < phi->operandCount_; ++i)
      if (phi->args_[i].inst->tracksUses() && useCounts[i] != 1)
        return false;
  }
  return true;
}

void CFGEditor::rebuildPhiIncomingSlots(Function *function, Inst *phi,
                                        const std::vector<BasicBlock *> &preds,
                                        const std::vector<Inst *> &values) {
  assert(function && phi && phi->op_ == OP_PHI &&
         preds.size() == values.size() &&
         preds.size() <= std::numeric_limits<u16>::max());

  // 先解绑全部旧operand Use, 再按新的predecessor顺序重建槽位
  // 最后统一通过setArg挂回Use, 使incoming, operand和argNo对齐
  for (u32 i = 0; i < phi->operandCount_; ++i)
    if (phi->args_[i].inst)
      phi->dropOperand(i);

  const u32 count = static_cast<u32>(preds.size());
  phi->operandCount_ = static_cast<u16>(count);
  phi->args_ = count <= 2 ? phi->inlineArgs_
                          : function->arena->createArray<InstRef>(count);
  phi->inlineArgs_[0].inst = nullptr;
  phi->inlineArgs_[1].inst = nullptr;
  phi->incoming_ =
      count ? function->arena->createArray<BasicBlock *>(count) : nullptr;
  for (u32 i = 0; i < count; ++i) {
    phi->args_[i].inst = nullptr;
    phi->incoming_[i] = preds[i];
  }
  for (u32 i = 0; i < count; ++i)
    phi->setArg(i, values[i]);
}

u32 CFGEditor::findPredecessorIndex(BasicBlock *block, BasicBlock *pred) {
  if (!block || !pred)
    return std::numeric_limits<u32>::max();
  for (u32 i = 0; i < block->predecessorCount_; ++i)
    if (block->predecessors_[i] == pred)
      return i;
  return std::numeric_limits<u32>::max();
}

void CFGEditor::assignPredecessors(Function *function, BasicBlock *block,
                                   const std::vector<BasicBlock *> &preds) {
  assert(function && function->arena && block &&
         preds.size() <= std::numeric_limits<u32>::max());
  block->predecessorCount_ = static_cast<u32>(preds.size());
  block->predecessors_ = preds.empty()
                             ? nullptr
                             : function->arena->createArray<BasicBlock *>(
                                   static_cast<u32>(preds.size()));
  if (!preds.empty())
    std::copy(preds.begin(), preds.end(), block->predecessors_);
}

bool computePreds(Function *function) {
  struct PhiSnapshot {
    Inst *phi = nullptr;
    std::unordered_map<BasicBlock *, Inst *> values;
  };
  if (!function || !function->arena)
    return false;

  std::vector<BasicBlock *> blocks;
  std::unordered_set<BasicBlock *> blockSet;
  if (!collectFlatCFGBlocks(function, blocks, blockSet))
    return false;

  // 按块布局扫描终结符 重建predecessor顺序
  // forEachSuccessor多个物理槽指向同一目标只记录一次
  std::unordered_map<BasicBlock *, std::vector<BasicBlock *>> canonical;
  canonical.reserve(blocks.size());
  for (BasicBlock *block : blocks)
    canonical.emplace(block, std::vector<BasicBlock *>{});

  for (BasicBlock *pred : blocks) {
    bool valid = true;
    forEachSuccessor(pred, [&](BasicBlock *succ) {
      if (!succ || !blockSet.count(succ)) {
        valid = false;
        return;
      }
      canonical[succ].push_back(pred);
    });
    if (!valid)
      return false;
  }

  // 按incoming block身份快照Phi值并完成全部只读预检
  // predecessor顺序可能变化 因此不能沿用旧槽位下标
  // 新增前驱若找不到已有Phi值则直接失败 不动undef
  std::vector<PhiSnapshot> snapshots;
  for (BasicBlock *block : blocks) {
    if (block->firstPhi() &&
        canonical[block].size() > std::numeric_limits<u16>::max())
      return false;
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next()) {
      if (phi->getOp() != OP_PHI || phi->parentBlock() != block)
        return false;
      PhiSnapshot snapshot;
      snapshot.phi = phi;
      snapshot.values.reserve(phi->getOperandCount());
      for (u32 i = 0; i < phi->getOperandCount(); ++i) {
        BasicBlock *incoming = phi->getIncomingBlock(i);
        Inst *value = phi->getArg(i);
        if (!incoming || !value ||
            !snapshot.values.emplace(incoming, value).second)
          return false;
      }
      for (BasicBlock *pred : canonical[block])
        if (!snapshot.values.count(pred))
          return false;
      snapshots.push_back(std::move(snapshot));
    }
  }

  // 预检通过后统一提交predecessor, 再按同一顺序重建Phi
  // 重建过程会同步更新operand Use和Use::argNo
  for (BasicBlock *block : blocks) {
    const std::vector<BasicBlock *> &preds = canonical[block];
    CFGEditor::assignPredecessors(function, block, preds);
  }

  for (PhiSnapshot &snapshot : snapshots) {
    BasicBlock *block = snapshot.phi->parentBlock();
    const std::vector<BasicBlock *> &preds = canonical[block];
    std::vector<Inst *> values;
    values.reserve(preds.size());
    for (BasicBlock *pred : preds)
      values.push_back(snapshot.values.at(pred));
    CFGEditor::rebuildPhiIncomingSlots(function, snapshot.phi, preds, values);
  }

  for (BasicBlock *block : blocks) {
    assert(CFGEditor::hasConsistentIncomingState(block));
    UNUSED(block);
  }
  return true;
}

void CFGEditor::appendPhiIncomingSlot(Function *function, Inst *phi,
                                      BasicBlock *pred, Inst *value) {
  std::vector<BasicBlock *> preds;
  std::vector<Inst *> values;
  preds.reserve(phi->operandCount_ + 1);
  values.reserve(phi->operandCount_ + 1);
  for (u32 i = 0; i < phi->operandCount_; ++i) {
    preds.push_back(phi->incoming_[i]);
    values.push_back(phi->args_[i].inst);
  }
  preds.push_back(pred);
  values.push_back(value);
  rebuildPhiIncomingSlots(function, phi, preds, values);
}

void CFGEditor::erasePhiIncomingSlot(Function *function, Inst *phi, u32 index) {
  assert(index < phi->operandCount_);
  std::vector<BasicBlock *> preds;
  std::vector<Inst *> values;
  preds.reserve(phi->operandCount_ - 1);
  values.reserve(phi->operandCount_ - 1);
  for (u32 i = 0; i < phi->operandCount_; ++i) {
    if (i == index)
      continue;
    preds.push_back(phi->incoming_[i]);
    values.push_back(phi->args_[i].inst);
  }
  rebuildPhiIncomingSlots(function, phi, preds, values);
}

bool CFGEditor::setPhiIncomingValueSlot(Function *, Inst *phi, BasicBlock *pred,
                                        Inst *value) {
  for (u32 i = 0; i < phi->operandCount_; ++i) {
    if (phi->incoming_[i] != pred)
      continue;
    phi->setArg(i, value);
    return true;
  }
  return false;
}

bool CFGEditor::hasPredecessorSlot(BasicBlock *succ, BasicBlock *pred) {
  return findPredecessorIndex(succ, pred) != std::numeric_limits<u32>::max();
}

void CFGEditor::appendPredecessorSlot(Function *function, BasicBlock *succ,
                                      BasicBlock *pred) {
  assert(function && succ && pred && !hasPredecessorSlot(succ, pred));
  std::vector<BasicBlock *> preds;
  preds.reserve(succ->predecessorCount_ + 1);
  for (u32 i = 0; i < succ->predecessorCount_; ++i)
    preds.push_back(succ->predecessors_[i]);
  preds.push_back(pred);
  assignPredecessors(function, succ, preds);
}

bool CFGEditor::erasePredecessorSlot(BasicBlock *succ, BasicBlock *pred) {
  if (!succ || !pred)
    return false;
  for (u32 i = 0; i < succ->predecessorCount_; ++i) {
    if (succ->predecessors_[i] != pred)
      continue;
    std::move(succ->predecessors_ + i + 1,
              succ->predecessors_ + succ->predecessorCount_,
              succ->predecessors_ + i);
    --succ->predecessorCount_;
    if (!succ->predecessorCount_)
      succ->predecessors_ = nullptr;
    return true;
  }
  return false;
}

bool CFGEditor::addPhiEdgeValues(Function *function, BasicBlock *succ,
                                 BasicBlock *pred,
                                 const std::vector<PhiEdgeValue> &values) {
  if (!isFlatCFGBlock(function, succ) || !isFlatCFGBlock(function, pred) ||
      hasPredecessorSlot(succ, pred) ||
      (succ->firstPhi() &&
       succ->predecessorCount_ == std::numeric_limits<u16>::max()))
    return false;

  std::unordered_map<Inst *, Inst *> plan;
  if (!collectPhiPlan(succ, values, plan, true))
    return false;
  for (Inst *phi = succ->phiFirst_; phi; phi = phi->next_)
    if (getPhiIncomingValue(phi, pred))
      return false;

  appendPredecessorSlot(function, succ, pred);
  for (Inst *phi = succ->phiFirst_; phi; phi = phi->next_)
    appendPhiIncomingSlot(function, phi, pred, plan.at(phi));
  return true;
}

bool CFGEditor::removePhiEdgeValues(Function *function, BasicBlock *succ,
                                    BasicBlock *pred) {
  if (!function || !succ || !pred)
    return false;
  const u32 index = findPredecessorIndex(succ, pred);
  if (index == std::numeric_limits<u32>::max())
    return false;
  for (Inst *phi = succ->phiFirst_; phi; phi = phi->next_) {
    assert(index < phi->operandCount_ && phi->incoming_[index] == pred);
    erasePhiIncomingSlot(function, phi, index);
  }
  return true;
}

bool CFGEditor::movePhiEdgeValues(BasicBlock *succ, BasicBlock *oldPred,
                                  BasicBlock *newPred) {
  if (!succ || !oldPred || !newPred || oldPred == newPred)
    return false;
  const u32 oldIndex = findPredecessorIndex(succ, oldPred);
  if (oldIndex == std::numeric_limits<u32>::max() ||
      hasPredecessorSlot(succ, newPred))
    return false;
  for (Inst *phi = succ->phiFirst_; phi; phi = phi->next_) {
    assert(oldIndex < phi->operandCount_ &&
           phi->incoming_[oldIndex] == oldPred);
    phi->incoming_[oldIndex] = newPred;
  }
  succ->predecessors_[oldIndex] = newPred;
  return true;
}

void CFGEditor::dropIncomingForRemovedEdge(Function *function, BasicBlock *pred,
                                           BasicBlock *succ) {
  VERIFY(removePhiEdgeValues(function, succ, pred) || !succ->phiFirst_);
  VERIFY(erasePredecessorSlot(succ, pred));
}

bool CFGEditor::hasSemanticEdge(BasicBlock *pred, BasicBlock *succ) {
  if (!pred || !succ)
    return false;
  bool found = false;
  forEachSuccessor(pred, [&](BasicBlock *candidate) {
    if (candidate == succ)
      found = true;
  });
  return found;
}

Inst *CFGEditor::getPhiIncomingValue(Inst *phi, BasicBlock *pred) {
  if (!phi || phi->getOp() != OP_PHI || !pred)
    return nullptr;
  for (u32 i = 0; i < phi->getOperandCount(); ++i)
    if (phi->getIncomingBlock(i) == pred)
      return phi->getArg(i);
  return nullptr;
}

bool CFGEditor::setPhiEdgeValues(Function *function, BasicBlock *succ,
                                 BasicBlock *pred,
                                 const std::vector<PhiEdgeValue> &values) {
  if (!isFlatCFGBlock(function, succ) || !isFlatCFGBlock(function, pred) ||
      !hasConsistentIncomingState(succ))
    return false;
  const u32 predIndex = findPredecessorIndex(succ, pred);
  if (predIndex == std::numeric_limits<u32>::max())
    return false;

  std::unordered_map<Inst *, Inst *> plan;
  if (!collectPhiPlan(succ, values, plan, false))
    return false;
  for (const auto &[phi, value] : plan)
    if (phi->args_[predIndex].inst != value)
      phi->setArg(predIndex, value);
  assert(hasConsistentIncomingState(succ));
  return true;
}

bool CFGEditor::setPhiEdgeValues(Function *function, BasicBlock *succ,
                                 BasicBlock *pred,
                                 std::initializer_list<PhiEdgeValue> values) {
  return setPhiEdgeValues(function, succ, pred,
                          std::vector<PhiEdgeValue>(values));
}

bool CFGEditor::moveAndSetPhiEdgeValues(
    Function *function, BasicBlock *succ, BasicBlock *oldPred,
    BasicBlock *newPred, const std::vector<PhiEdgeValue> &values) {
  if (!isFlatCFGBlock(function, succ) || !isFlatCFGBlock(function, oldPred) ||
      !isFlatCFGBlock(function, newPred) || oldPred == newPred ||
      !hasAlignedIncomingMetadata(succ))
    return false;
  const u32 oldIndex = findPredecessorIndex(succ, oldPred);
  if (oldIndex == std::numeric_limits<u32>::max() ||
      hasPredecessorSlot(succ, newPred))
    return false;

  std::unordered_map<Inst *, Inst *> plan;
  plan.reserve(values.size());
  for (const PhiEdgeValue &entry : values)
    if (!entry.phi || entry.phi->getOp() != OP_PHI ||
        entry.phi->parentBlock() != succ || !entry.value ||
        !plan.emplace(entry.phi, entry.value).second)
      return false;

  for (Inst *phi = succ->phiFirst_; phi; phi = phi->next_) {
    assert(oldIndex < phi->operandCount_ &&
           phi->incoming_[oldIndex] == oldPred);
    phi->incoming_[oldIndex] = newPred;
    if (const auto found = plan.find(phi); found != plan.end())
      phi->setArg(oldIndex, found->second);
  }
  succ->predecessors_[oldIndex] = newPred;
  assert(hasAlignedIncomingMetadata(succ));
  return true;
}

bool CFGEditor::rewriteSuccessorEdges(BasicBlock *pred, BasicBlock *oldSucc,
                                      BasicBlock *newSucc) {
  // 只改终结符物理槽 不维护predecessor或Phi
  if (!pred || !oldSucc || !newSucc || !pred->endsWithTerminator())
    return false;
  Inst *term = pred->terminator();
  bool changed = false;
  for (u32 index = 0; index < term->getSuccessorSlotCount(); ++index) {
    if (term->getSuccessorSlot(index) != oldSucc)
      continue;
    term->setSuccessorSlot(index, newSucc);
    changed = true;
  }
  return changed;
}

bool CFGEditor::redirectEdge(Function *function, BasicBlock *pred,
                             BasicBlock *oldSucc, BasicBlock *newSucc,
                             const std::vector<PhiEdgeValue> &values) {
  if (!isFlatCFGBlock(function, pred) || !isFlatCFGBlock(function, oldSucc) ||
      !isFlatCFGBlock(function, newSucc) || oldSucc == newSucc ||
      !hasSemanticEdge(pred, oldSucc) || !hasConsistentIncomingState(pred) ||
      !hasConsistentIncomingState(oldSucc) ||
      !hasConsistentIncomingState(newSucc) ||
      !hasPredecessorSlot(oldSucc, pred))
    return false;

  const bool alreadyReachesNew = hasSemanticEdge(pred, newSucc);
  if (alreadyReachesNew)
    return false;
  std::unordered_map<Inst *, Inst *> plan;
  if (!collectPhiPlan(newSucc, values, plan, true))
    return false;

  VERIFY(rewriteSuccessorEdges(pred, oldSucc, newSucc));
  dropIncomingForRemovedEdge(function, pred, oldSucc);
  VERIFY(addPhiEdgeValues(function, newSucc, pred, values));
  assert(hasConsistentIncomingState(oldSucc));
  assert(hasConsistentIncomingState(newSucc));
  return true;
}

bool CFGEditor::redirectEdge(Function *function, BasicBlock *pred,
                             BasicBlock *oldSucc, BasicBlock *newSucc,
                             std::initializer_list<PhiEdgeValue> values) {
  return redirectEdge(function, pred, oldSucc, newSucc,
                      std::vector<PhiEdgeValue>(values));
}

bool CFGEditor::redirectEdgeAndMerge(Function *function, BasicBlock *pred,
                                     BasicBlock *oldSucc, BasicBlock *newSucc,
                                     const std::vector<PhiEdgeValue> &values) {
  if (!isFlatCFGBlock(function, pred) || !isFlatCFGBlock(function, oldSucc) ||
      !isFlatCFGBlock(function, newSucc) || oldSucc == newSucc ||
      !hasSemanticEdge(pred, oldSucc) || !hasSemanticEdge(pred, newSucc) ||
      !hasConsistentIncomingState(pred) ||
      !hasConsistentIncomingState(oldSucc) ||
      !hasConsistentIncomingState(newSucc) ||
      !hasPredecessorSlot(oldSucc, pred) || !hasPredecessorSlot(newSucc, pred))
    return false;

  std::unordered_map<Inst *, Inst *> plan;
  if (!collectPhiPlan(newSucc, values, plan, true))
    return false;
  for (const auto &[phi, value] : plan)
    if (getPhiIncomingValue(phi, pred) != value)
      return false;

  VERIFY(rewriteSuccessorEdges(pred, oldSucc, newSucc));
  dropIncomingForRemovedEdge(function, pred, oldSucc);
  assert(hasConsistentIncomingState(oldSucc));
  assert(hasConsistentIncomingState(newSucc));
  return true;
}

bool CFGEditor::rewriteBranchSlot(BasicBlock *pred, bool trueEdge,
                                  BasicBlock *newTarget) {
  if (!pred || !newTarget || !pred->endsWithTerminator())
    return false;
  Inst *term = pred->terminator();
  if (term->op_ != OP_BR && !isMachineBranch(term->op_))
    return false;
  (trueEdge ? term->branch_->trueBB : term->branch_->falseBB) = newTarget;
  return true;
}

bool CFGEditor::rewriteJumpTarget(BasicBlock *pred, BasicBlock *newTarget) {
  if (!pred || !newTarget || !pred->endsWithTerminator())
    return false;
  Inst *term = pred->terminator();
  if (term->op_ != OP_JMP && term->op_ != MOP_J)
    return false;
  term->jumpTarget_ = newTarget;
  return true;
}

BasicBlock *CFGEditor::splitCriticalEdge(Function *function, BasicBlock *pred,
                                         BasicBlock *succ) {
  if (!isFlatCFGBlock(function, pred) || !isFlatCFGBlock(function, succ) ||
      !hasSemanticEdge(pred, succ) || !hasConsistentIncomingState(pred) ||
      !hasConsistentIncomingState(succ) || successorCount(pred) <= 1 ||
      succ->getPredecessorCount() <= 1 || !hasPredecessorSlot(succ, pred))
    return nullptr;

  IRBuilder builder(function->module, function);
  BasicBlock *middle = builder.newBlockAfter(pred);
  builder.setInsertAtEnd(middle);
  if (function->phase == IRPhase::MIR) {
    Inst *jump = builder.emit(MOP_J, TY_VOID);
    jump->setJumpTarget(succ);
  } else {
    builder.emitJump(succ);
  }

  VERIFY(rewriteSuccessorEdges(pred, succ, middle));
  VERIFY(movePhiEdgeValues(succ, pred, middle));
  appendPredecessorSlot(function, middle, pred);
  assert(hasConsistentIncomingState(middle));
  assert(hasConsistentIncomingState(succ));
  return middle;
}

BasicBlock *CFGEditor::splitBlockAfter(Function *function, Inst *anchor) {
  if (!function || !anchor || anchor->isErased() || !anchor->parentBlock() ||
      anchor->getOp() == OP_PHI || isTerminator(anchor->getOp()))
    return nullptr;
  BasicBlock *block = anchor->parentBlock();
  if (!isFlatCFGBlock(function, block) || !block->endsWithTerminator() ||
      anchor == block->terminator() || !hasConsistentIncomingState(block))
    return nullptr;

  std::vector<BasicBlock *> successors;
  forEachSuccessor(
      block, [&](BasicBlock *successor) { successors.push_back(successor); });
  for (BasicBlock *successor : successors)
    if (!isFlatCFGBlock(function, successor) ||
        !hasConsistentIncomingState(successor) ||
        !hasPredecessorSlot(successor, block))
      return nullptr;

  IRBuilder builder(function->module, function);
  BasicBlock *continuation = builder.newBlockAfter(block);
  continuation->takeInstructionSuffixAfter(anchor);
  for (BasicBlock *successor : successors)
    VERIFY(movePhiEdgeValues(successor, block, continuation));

  builder.setInsertAtEnd(block);
  builder.emitJump(continuation);
  VERIFY(computePreds(function));
  return continuation;
}

CFGEditor::SplitBlockPredsResult
CFGEditor::splitBlockPredecessors(Function *function, BasicBlock *succ,
                                  BasicBlock *const *preds, u32 predCount,
                                  BasicBlock *insertAfter) {
  SplitBlockPredsResult result;
  if (!isFlatCFGBlock(function, succ) || !preds || !predCount ||
      (insertAfter && !isFlatCFGBlock(function, insertAfter)) ||
      !hasConsistentIncomingState(succ))
    return result;

  std::unordered_set<BasicBlock *> selected;
  for (u32 i = 0; i < predCount; ++i) {
    if (!isFlatCFGBlock(function, preds[i]) ||
        !hasConsistentIncomingState(preds[i]) ||
        !selected.insert(preds[i]).second || !hasSemanticEdge(preds[i], succ) ||
        !hasPredecessorSlot(succ, preds[i]))
      return result;
  }

  struct MergePlan {
    Inst *phi = nullptr;
    std::vector<Inst *> values;
    bool allSame = true;
  };
  // 先收集每个succ Phi在被拆前驱上的值 值全相同时可直接透传
  // 否则必须在middle中建立Phi 保留各条路径的值差异
  std::vector<MergePlan> plans;
  for (Inst *phi = succ->phiFirst_; phi; phi = phi->next_) {
    MergePlan plan;
    plan.phi = phi;
    plan.values.reserve(predCount);
    for (u32 i = 0; i < predCount; ++i) {
      Inst *value = getPhiIncomingValue(phi, preds[i]);
      if (!value)
        return result;
      if (!plan.values.empty() && plan.values.front() != value)
        plan.allSame = false;
      plan.values.push_back(value);
    }
    plans.push_back(std::move(plan));
  }
  if (predCount > std::numeric_limits<u16>::max() &&
      std::any_of(plans.begin(), plans.end(),
                  [](const MergePlan &plan) { return !plan.allSame; }))
    return result;

  IRBuilder builder(function->module, function);
  BasicBlock *middle =
      builder.newBlockAfter(insertAfter ? insertAfter : preds[0]);
  builder.setInsertAtEnd(middle);
  if (function->phase == IRPhase::MIR) {
    Inst *jump = builder.emit(MOP_J, TY_VOID);
    jump->setJumpTarget(succ);
  } else {
    builder.emitJump(succ);
  }

  std::vector<BasicBlock *> middlePreds(preds, preds + predCount);
  assignPredecessors(function, middle, middlePreds);

  for (u32 i = 0; i < predCount; ++i)
    VERIFY(rewriteSuccessorEdges(preds[i], succ, middle));

  std::vector<BasicBlock *> succPreds;
  succPreds.reserve(succ->predecessorCount_ - predCount + 1);
  for (u32 i = 0; i < succ->predecessorCount_; ++i)
    if (!selected.count(succ->predecessors_[i]))
      succPreds.push_back(succ->predecessors_[i]);
  succPreds.push_back(middle);
  assignPredecessors(function, succ, succPreds);

  for (MergePlan &plan : plans) {
    Inst *merged = plan.values.front();
    if (!plan.allSame) {
      Inst *splitPhi = builder.emitPhi(plan.phi->getType(), middle,
                                       builder.makeUndef(plan.phi->getType()));
      for (u32 i = 0; i < predCount; ++i)
        VERIFY(setPhiIncomingValueSlot(function, splitPhi, preds[i],
                                       plan.values[i]));

      merged = splitPhi;
      result.createdPhi = true;
    }

    std::vector<BasicBlock *> rebuiltPreds;
    std::vector<Inst *> rebuiltValues;
    rebuiltPreds.reserve(plan.phi->operandCount_ - predCount + 1);
    rebuiltValues.reserve(plan.phi->operandCount_ - predCount + 1);
    for (u32 i = 0; i < plan.phi->operandCount_; ++i) {
      if (selected.count(plan.phi->incoming_[i]))
        continue;
      rebuiltPreds.push_back(plan.phi->incoming_[i]);
      rebuiltValues.push_back(plan.phi->args_[i].inst);
    }
    rebuiltPreds.push_back(middle);
    rebuiltValues.push_back(merged);
    rebuildPhiIncomingSlots(function, plan.phi, rebuiltPreds, rebuiltValues);
  }

  result.block = middle;
  assert(hasConsistentIncomingState(middle));
  assert(hasConsistentIncomingState(succ));
  return result;
}

bool CFGEditor::rewriteTerminatorToJump(Function *function, BasicBlock *pred,
                                        BasicBlock *target) {
  if (!isFlatCFGBlock(function, pred) || !isFlatCFGBlock(function, target) ||
      !pred->endsWithTerminator())
    return false;
  Inst *term = pred->terminator();
  if ((term->op_ == OP_JMP || term->op_ == MOP_J) &&
      term->jumpTarget_ == target)
    return false;
  IRBuilder builder(function->module, function);
  builder.replaceWithJump(term, target);
  return true;
}

bool CFGEditor::foldTerminatorToJump(Function *function, BasicBlock *pred,
                                     BasicBlock *kept) {
  if (!isFlatCFGBlock(function, pred) || !isFlatCFGBlock(function, kept) ||
      !hasSemanticEdge(pred, kept))
    return false;
  if (!hasConsistentIncomingState(pred))
    return false;
  Inst *term = pred->terminator();
  if ((term->op_ == OP_JMP || term->op_ == MOP_J) && term->jumpTarget_ == kept)
    return false;

  // 先快照去重后的旧语义后继 只删除kept之外的边元数据 再改写终结符
  // 多个物理槽同指kept时, 不能误删其唯一Phi incoming
  std::vector<BasicBlock *> oldSuccessors;
  forEachSuccessor(pred,
                   [&](BasicBlock *succ) { oldSuccessors.push_back(succ); });
  for (BasicBlock *succ : oldSuccessors)
    if (!isFlatCFGBlock(function, succ) || !hasConsistentIncomingState(succ) ||
        !hasPredecessorSlot(succ, pred))
      return false;

  for (BasicBlock *succ : oldSuccessors)
    if (succ != kept)
      dropIncomingForRemovedEdge(function, pred, succ);
  VERIFY(rewriteTerminatorToJump(function, pred, kept));
  for (BasicBlock *succ : oldSuccessors) {
    assert(hasConsistentIncomingState(succ));
    UNUSED(succ);
  }
  return true;
}

bool CFGEditor::bypassTrivialBlock(Function *function, BasicBlock *middle) {
  if (!isFlatCFGBlock(function, middle) || middle == function->region->first ||
      middle->phiFirst_ || !hasConsistentIncomingState(middle))
    return false;
  Inst *jump = middle->instFirst_;
  if (!jump || jump != middle->instLast_ ||
      (jump->op_ != OP_JMP && jump->op_ != MOP_J))
    return false;
  BasicBlock *target = jump->jumpTarget_;
  if (!isFlatCFGBlock(function, target) || target == middle ||
      !hasConsistentIncomingState(target) ||
      !hasPredecessorSlot(target, middle))
    return false;

  std::vector<BasicBlock *> preds;
  std::vector<bool> duplicate;
  for (u32 i = 0; i < middle->predecessorCount_; ++i) {
    BasicBlock *pred = middle->predecessors_[i];
    if (!isFlatCFGBlock(function, pred) || !hasConsistentIncomingState(pred) ||
        !hasSemanticEdge(pred, middle))
      return false;
    preds.push_back(pred);
    duplicate.push_back(hasSemanticEdge(pred, target));
  }

  // pred若原本已经直达target 旁路后两条语义边会合并为一条
  // 只有target的每个Phi在两条边上取值相同才能安全折叠.
  for (Inst *phi = target->phiFirst_; phi; phi = phi->next_) {
    Inst *middleValue = getPhiIncomingValue(phi, middle);
    if (!middleValue)
      return false;
    for (u32 i = 0; i < preds.size(); ++i)
      if (duplicate[i] && getPhiIncomingValue(phi, preds[i]) != middleValue)
        return false;
  }

  std::vector<BasicBlock *> newTargetPreds;
  for (u32 i = 0; i < target->predecessorCount_; ++i)
    if (target->predecessors_[i] != middle)
      newTargetPreds.push_back(target->predecessors_[i]);
  for (u32 i = 0; i < preds.size(); ++i)
    if (!duplicate[i])
      newTargetPreds.push_back(preds[i]);
  if (target->phiFirst_ &&
      newTargetPreds.size() > std::numeric_limits<u16>::max())
    return false;

  for (BasicBlock *pred : preds)
    VERIFY(rewriteSuccessorEdges(pred, middle, target));

  assignPredecessors(function, target, newTargetPreds);

  for (Inst *phi = target->phiFirst_; phi; phi = phi->next_) {
    Inst *middleValue = getPhiIncomingValue(phi, middle);
    std::vector<BasicBlock *> rebuiltPreds;
    std::vector<Inst *> rebuiltValues;
    for (u32 i = 0; i < phi->operandCount_; ++i) {
      if (phi->incoming_[i] == middle)
        continue;
      rebuiltPreds.push_back(phi->incoming_[i]);
      rebuiltValues.push_back(phi->args_[i].inst);
    }
    for (u32 i = 0; i < preds.size(); ++i)
      if (!duplicate[i]) {
        rebuiltPreds.push_back(preds[i]);
        rebuiltValues.push_back(middleValue);
      }
    rebuildPhiIncomingSlots(function, phi, rebuiltPreds, rebuiltValues);
  }

  eraseBlock(function, middle);
  assert(hasConsistentIncomingState(target));
  return true;
}

bool CFGEditor::mergeBlockIntoPredecessor(Function *function, BasicBlock *pred,
                                          BasicBlock *succ) {
  if (!isFlatCFGBlock(function, pred) || !isFlatCFGBlock(function, succ) ||
      pred == succ || succ == function->region->first || succ->phiFirst_ ||
      !hasConsistentIncomingState(pred) || !hasConsistentIncomingState(succ) ||
      succ->predecessorCount_ != 1 || succ->predecessors_[0] != pred ||
      !pred->endsWithTerminator())
    return false;
  Inst *jump = pred->terminator();
  if ((jump->op_ != OP_JMP && jump->op_ != MOP_J) || jump->jumpTarget_ != succ)
    return false;

  // 必须在搬迁前快照succ的后继 splice后pred会接管succ的旧终结符
  // 此时再从succ枚举会混淆变换前后的CFG
  std::vector<BasicBlock *> oldSuccessors;
  forEachSuccessor(
      succ, [&](BasicBlock *target) { oldSuccessors.push_back(target); });
  for (BasicBlock *target : oldSuccessors)
    if (target == succ || !isFlatCFGBlock(function, target) ||
        !hasConsistentIncomingState(target) ||
        !hasPredecessorSlot(target, succ) || hasPredecessorSlot(target, pred))
      return false;

  succ->spliceIntoBefore(jump);
  jump->dropAllOperands();
  jump->unlinkFromBlock();
  jump->erased_ = true;
  jump->undefValue_ = false;
  std::memset(jump->payload_, 0, sizeof(jump->payload_));
  // 指令搬迁不改变边上的值 只需把后继中的incoming身份由succ改名为pred
  // 对应operand Use保持不变
  for (BasicBlock *target : oldSuccessors) {
    VERIFY(movePhiEdgeValues(target, succ, pred));
    assert(hasConsistentIncomingState(target));
  }
  return true;
}

void CFGEditor::eraseBlock(Function *function, BasicBlock *block) {
  if (!block)
    return;
  assert(!function || !block->parentRegion ||
         block->parentRegion->function == function);
  UNUSED(function);
  // 这里只物理删除已脱离活CFG的块 调用时必须先维护活后继的predecessor/Phi
  // 并瓦解块内operand和use-def环
  block->unlinkFromRegion();

  auto eraseInst = [](Inst *inst) {
    assert(inst && inst->operandCount_ == 0 && !inst->hasUses());
    inst->unlinkFromBlock();
    inst->erased_ = true;
    inst->undefValue_ = false;
    std::memset(inst->payload_, 0, sizeof(inst->payload_));
  };
  while (block->phiFirst_)
    eraseInst(block->phiFirst_);
  while (block->instFirst_)
    eraseInst(block->instFirst_);
  block->predecessorCount_ = 0;
  block->predecessors_ = nullptr;
}

bool cleanupDeadBlocks(Function *function) {
  std::vector<BasicBlock *> blocks;
  std::unordered_set<BasicBlock *> blockSet;
  if (!collectFlatCFGBlocks(function, blocks, blockSet) || blocks.empty())
    return false;

  std::unordered_set<BasicBlock *> reachable;
  std::vector<BasicBlock *> worklist{blocks.front()};
  reachable.insert(blocks.front());
  bool valid = true;
  while (!worklist.empty()) {
    BasicBlock *block = worklist.back();
    worklist.pop_back();
    forEachSuccessor(block, [&](BasicBlock *succ) {
      if (!blockSet.count(succ)) {
        valid = false;
        return;
      }
      if (reachable.insert(succ).second)
        worklist.push_back(succ);
    });
  }
  if (!valid)
    return false;

  std::vector<BasicBlock *> dead;
  for (BasicBlock *block : blocks)
    if (!reachable.count(block))
      dead.push_back(block);
  if (dead.empty())
    return false;

  // 修改前先规范化
  if (!computePreds(function))
    return false;

  for (BasicBlock *block : dead)
    forEachSuccessor(block, [&](BasicBlock *succ) {
      if (reachable.count(succ))
        CFGEditor::dropIncomingForRemovedEdge(function, block, succ);
    });
  for (BasicBlock *block : dead)
    forEachOp(block, [](Inst *inst) { inst->dropAllOperands(); });
  for (BasicBlock *block : dead)
    CFGEditor::eraseBlock(function, block);
  for (BasicBlock *block : blocks) {
    assert(!reachable.count(block) ||
           CFGEditor::hasConsistentIncomingState(block));
    UNUSED(block);
  }
  return true;
}

} // namespace svm::ir
