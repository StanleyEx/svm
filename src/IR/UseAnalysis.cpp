#include "IR.h"

#include <cstring>
#include <functional>
#include <unordered_set>

namespace svm::ir {

bool Inst::tracksUses() const noexcept {
  return !isUndefValue() && !isPrecoloredDef();
}

void Inst::dropOperand(u32 index) noexcept {
  assert(!erased_ && index < operandCount_);
  Inst *value = args_[index].inst;
  if (value && value->tracksUses()) {
    // (user, argNo) 标识一条操作数边 二级指针统一处理链头和中间节点
    Use **link = &value->uses_;
    while (*link && !((*link)->user == this && (*link)->argNo == index))
      link = &(*link)->next;
    assert(*link && "缺少Use链表节点");
    *link = (*link)->next;
  }
  args_[index].inst = nullptr;
}

void Inst::setArg(u32 index, Inst *value) noexcept {
  assert(!erased_ && index < operandCount_ && value);
  if (args_[index].inst == value)
    return;

  // 操作数更新同步维护Use-Def 先摘除旧边, 再写入并登记新边
  if (args_[index].inst)
    dropOperand(index);
  args_[index].inst = value;
  if (value->tracksUses()) {
    assert(arena);
    Use *use = arena->create<Use>();
    use->next = value->uses_;
    use->user = this;
    use->argNo = static_cast<u16>(index);
    value->uses_ = use;
  }
}

void Inst::dropAllOperands() noexcept {
  for (u32 index = 0; index < operandCount_; ++index)
    if (args_[index].inst)
      dropOperand(index);
  operandCount_ = 0;
  args_ = inlineArgs_;
  inlineArgs_[0].inst = inlineArgs_[1].inst = nullptr;
}

bool Inst::eraseFromBlock() noexcept {
  if (!block_)
    return false;

  const Function *function =
      block_->parentRegion ? block_->parentRegion->function : nullptr;
  const bool flatCFG = function && function->phase != IRPhase::HIR;
  if (flatCFG && (isLIRTerminator(op_) || isMachineTerminator(op_)))
    return false;
  if (hasUses())
    return false;

  dropAllOperands();
  unlinkFromBlock();
  erased_ = true;
  undefValue_ = false;
  std::memset(payload_, 0, sizeof(payload_));
  return true;
}

void computeUses(Function *function) {
  if (!function || !function->region)
    return;

  // 批量构造或克隆IR后在此修复 以当前操作数为来源
  // 先枚举并清空所有可达定义的旧Use链 再按操作数重建全部边
  std::unordered_set<Inst *> definitions;
  for (u32 index = 0; index < function->paramCount; ++index)
    definitions.insert(function->params[index]);
  for (const auto &entry : function->constPools.iConstPool)
    definitions.insert(entry.second);
  for (const auto &entry : function->constPools.fConstPool)
    definitions.insert(entry.second);
  for (const auto &entry : function->constPools.globalPtrPool)
    definitions.insert(entry.second);

  // 结构化控制流拥有嵌套Region 仅遍历函数顶层会遗漏其中的定义和用户
  std::function<void(Region *, const std::function<void(Inst *)> &)> walkRegion;
  walkRegion = [&](Region *region, const std::function<void(Inst *)> &visit) {
    if (!region)
      return;
    for (BasicBlock *block = region->first; block; block = block->next()) {
      forEachOp(block, [&](Inst *inst) {
        visit(inst);
        if ((inst->op_ == OP_IF || inst->op_ == OP_WHILE) && inst->scf_) {
          walkRegion(inst->scf_->r[0], visit);
          walkRegion(inst->scf_->r[1], visit);
        } else if (inst->op_ == OP_FOR) {
          walkRegion(inst->body_, visit);
        }
      });
    }
  };
  walkRegion(function->region, [&](Inst *inst) {
    definitions.insert(inst);
    // 同时纳入仅通过操作数可达的浮空身份值 例如后续降级保留的Phi结果
    for (u32 index = 0; index < inst->operandCount_; ++index)
      if (inst->args_[index].inst)
        definitions.insert(inst->args_[index].inst);
  });
  for (Inst *definition : definitions)
    definition->uses_ = nullptr;
  walkRegion(function->region, [&](Inst *inst) {
    for (u32 index = 0; index < inst->operandCount_; ++index) {
      Inst *value = inst->args_[index].inst;
      if (!value || !value->tracksUses())
        continue;
      Use *use = function->arena->create<Use>();
      use->user = inst;
      use->argNo = static_cast<u16>(index);
      use->next = value->uses_;
      value->uses_ = use;
    }
  });
}

void replaceAllUsesWith(Function *, Inst *from, Inst *to) {
  assert(from && to && from != to);

  while (from->uses_) {
    Use *use = from->uses_;
    use->user->setArg(use->argNo, to);
  }
}

} // namespace svm::ir
