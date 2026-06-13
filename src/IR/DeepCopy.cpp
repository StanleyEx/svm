#include "DeepCopy.h"

#include <cassert>
#include <unordered_set>
#include <utility>

// 深拷贝统一先建立块和指令映射 再通过setArg连接Use-Def
// 最后翻译Phi, 终结符和JumpTable中的CFG引用
// 该顺序保证前向引用和环边在连线时已经具有稳定映射
namespace svm {
namespace ir {
namespace {

Module *checkedModule(Function *function) noexcept {
  assert(function && function->module && function->arena);
  return function->module;
}

bool carriesJumpTable(const Inst *inst) noexcept {
  return inst->getOp() == MOP_JT_DISPATCH ||
         (inst->getOp() == MOP_LA &&
          inst->getSymbolRef().kind == SymbolRef::SymbolRefKind::JumpTable);
}

void reparentSubregions(Inst *inst, Region *parent) noexcept {
  if (inst->getOp() == OP_FOR) {
    if (Region *body = inst->getBody())
      body->parent = parent;
    return;
  }
  if (inst->getOp() != OP_IF && inst->getOp() != OP_WHILE)
    return;
  for (Region *child : inst->getScf().r)
    if (child)
      child->parent = parent;
}

} // namespace

DeepCopy::DeepCopy(Function *function) noexcept
    : function_(function), diagnostics_(checkedModule(function)->diagnostics),
      builder_(checkedModule(function), function) {}

void DeepCopy::mapInst(Inst *source, Inst *replacement) {
  assert(source && replacement);
  instMap_[source] = replacement;
}

void DeepCopy::mapBlock(BasicBlock *source, BasicBlock *replacement) {
  assert(source && replacement);
  blockMap_[source] = replacement;
}

bool DeepCopy::hasInstMapping(const Inst *source) const noexcept {
  return source && instMap_.count(source) != 0;
}

bool DeepCopy::hasBlockMapping(const BasicBlock *source) const noexcept {
  return source && blockMap_.count(source) != 0;
}

void DeepCopy::note(const Inst *inst, const char *message) const {
  if (!diagnostics_)
    return;
  const SourceLocation location =
      inst && inst->sourceLocation ? *inst->sourceLocation : SourceLocation{};
  SVM_NOTE(*diagnostics_, location, "%s", message);
}

Inst *DeepCopy::lookupInstMapping(const Inst *source) const noexcept {
  const auto found = instMap_.find(source);
  return found == instMap_.end() ? nullptr : found->second;
}

Inst *DeepCopy::translate(Inst *source) const noexcept {
  if (!source || source->isPrecoloredDef())
    return source;
  Inst *mapped = lookupInstMapping(source);
  return mapped ? mapped : source;
}

BasicBlock *DeepCopy::translateBlock(BasicBlock *source) const noexcept {
  const auto found = blockMap_.find(source);
  return found == blockMap_.end() ? source : found->second;
}

Inst *DeepCopy::cloneShell(Inst *source) {
  assert(source && !source->isErased());
  assert(!hasInstMapping(source));
  Inst *clone = builder_.cloneInst(source);
  instMap_.emplace(source, clone);
  return clone;
}

void DeepCopy::appendShell(BasicBlock *destination, Inst *clone, bool phi) {
  // cloneInst只创建未挂接的指令外壳
  // 此处仅维护目标块的Phi或普通指令链 操作数必须留到映射完整后再绑定
  assert(destination && clone && !clone->block_);
  clone->block_ = destination;
  clone->prev_ = phi ? destination->phiLast_ : destination->instLast_;
  clone->next_ = nullptr;
  Inst *&first = phi ? destination->phiFirst_ : destination->instFirst_;
  Inst *&last = phi ? destination->phiLast_ : destination->instLast_;
  if (last)
    last->next_ = clone;
  else
    first = clone;
  last = clone;
}

void DeepCopy::remapPhiIncoming(Inst *clone,
                                const BlockTranslator &translateBlockFn) {
  // cloneInst已经深拷incoming数组 这里只翻译其中的块身份
  // Use-Def只能由setArg建立 不能通过直接改写操作数存储绕过Use链维护
  for (u32 index = 0; index < clone->getOperandCount(); ++index)
    clone->setIncomingBlock(index,
                            translateBlockFn(clone->getIncomingBlock(index)));
}

void DeepCopy::remapTerminatorTargets(Inst *clone,
                                      const BlockTranslator &translateBlockFn) {
  // 这些终结符仍是尚未纳入完整CFG的克隆外壳
  // 因此DeepCopy可以直接翻译payload 已存在CFG上的改边仍必须使用CFGEditor
  const OpCode op = clone->getOp();
  if (op == OP_JMP || op == MOP_J) {
    clone->setJumpTarget(translateBlockFn(clone->getJumpTarget()));
  } else if (op == OP_BR || isMachineBranch(op)) {
    BrPayload &branch = clone->mutableBranch();
    branch.trueBB = translateBlockFn(branch.trueBB);
    branch.falseBB = translateBlockFn(branch.falseBB);
  } else if (op == OP_SWITCH) {
    SwitchPayload &payload = clone->mutableSwitch();
    payload.defaultTarget_ = translateBlockFn(payload.defaultTarget_);
    for (u32 index = 0; index < payload.caseCount_; ++index)
      payload.cases_[index].target_ =
          translateBlockFn(payload.cases_[index].target_);
  }
}

JumpTable *DeepCopy::cloneJumpTable(JumpTable *source,
                                    const BlockTranslator &translateBlockFn) {
  if (!source)
    return nullptr;
  const auto found = jumpTableMap_.find(source);
  if (found != jumpTableMap_.end())
    return found->second;

  // MOP_LA和MOP_JT_DISPATCH可能共享同一张函数级JumpTable
  // 必须按源表去重克隆 否则两条指令会引用不同的侧表
  JumpTable *clone = function_->newJumpTable();
  clone->label = nullptr; // 后端重新分配唯一标签 避免复制函数后的符号冲突
  clone->minValue = source->minValue;
  clone->boundsCheckBlock = translateBlockFn(source->boundsCheckBlock);
  clone->tableLookupBlock = translateBlockFn(source->tableLookupBlock);
  clone->defaultTarget_ = translateBlockFn(source->defaultTarget_);
  // 目标数组必须独立分配并逐项翻译 浅拷会保留源函数块引用
  // 后续改表也会污染源函数中的JumpTable
  clone->resetTargets(function_->arena, source->entryCount_, nullptr);
  for (u32 index = 0; index < source->entryCount_; ++index)
    clone->setTarget(index, translateBlockFn(source->target_[index]));
  jumpTableMap_.emplace(source, clone);
  return clone;
}

void DeepCopy::remapJumpTable(Inst *clone,
                              const BlockTranslator &translateBlockFn) {
  clone->setJumpTable(cloneJumpTable(clone->getJumpTable(), translateBlockFn));
}

Inst *DeepCopy::materializeMappedPhi(Inst *sourcePhi, BasicBlock *destination) {
  assert(sourcePhi && sourcePhi->getOp() == OP_PHI && destination);
  assert(!hasInstMapping(sourcePhi));
  Inst *clone = cloneShell(sourcePhi);
  // 这里物化的是新CFG的Phi外壳 不是旧incoming边的副本
  // 清空cloneInst带来的incoming后 调用方再通过CFGEditor安装新边和值
  clone->operandCount_ = 0;
  clone->inlineArgs_[0] = {};
  clone->inlineArgs_[1] = {};
  clone->args_ = clone->inlineArgs_;
  clone->incoming_ = nullptr;
  appendShell(destination, clone, true);
  return clone;
}

bool DeepCopy::isTargetLocal(const Inst *value) const noexcept {
  if (!value)
    return false;
  if (value->parentBlock())
    return value->parentBlock()->parentRegion &&
           value->parentBlock()->parentRegion->function == function_;
  for (u32 index = 0; index < function_->paramCount; ++index)
    if (function_->params[index] == value)
      return true;
  return false;
}

Inst *DeepCopy::rematerializeConstant(Inst *source) {
  // 跨函数克隆不能复用源函数常量节点
  // 在目标函数重新物化常量, 全局地址和undef 并由目标函数自己的常量池负责去重
  if (source->isUndefValue())
    return builder_.makeUndef(source->getType());
  switch (source->getOp()) {
  case OP_ICONST:
    return source->getType() == TY_I1 ? builder_.i1Const(source->getImm() != 0)
                                      : builder_.iConst(source->getImm());
  case OP_FCONST:
    return builder_.fConst(source->getFimm());
  case OP_GETGLOBAL:
    return builder_.getGlobalPtr(source->getGlobal());
  default:
    return nullptr;
  }
}

Inst *DeepCopy::resolveOperand(Inst *source, const RegionCloneConfig &config) {
  // 解析优先级为:
  // 物理寄存器哨兵, 显式映射, 同函数外部值, 可重物化常量, 已属于目标函数的值
  // RequireMapped下其余值表示非法跨函数引用
  if (!source || source->isPrecoloredDef())
    return source;
  if (Inst *mapped = lookupInstMapping(source))
    return mapped;
  if (config.externalValueMode == ExternalValueMode::Keep)
    return source;
  if (Inst *constant = rematerializeConstant(source)) {
    mapInst(source, constant);
    return constant;
  }
  return isTargetLocal(source) ? source : nullptr;
}

Region *DeepCopy::cloneRegionInto(Region *source,
                                  const RegionCloneConfig &config,
                                  RegionCloneResult &result) {
  assert(source);
  Region *clone = builder_.newRegion(nullptr, nullptr);

  // 先创建全部目标块
  // CFG可能包含后向边和环 块目标必须在任何Phi或终结符翻译前存在
  for (BasicBlock *block = source->first; block; block = block->next())
    mapBlock(block, builder_.newBlockAtEnd(clone));

  // 创建指令外壳并登记Inst映射 remapValueBeforeClone可以把源值直接映射到替身
  // 不生成多余clone
  BasicBlock *destination = clone->first;
  for (BasicBlock *block = source->first; block;
       block = block->next(), destination = destination->next()) {
    auto createShell = [&](Inst *inst, bool phi) {
      if (config.remapValueBeforeClone) {
        if (Inst *replacement = config.remapValueBeforeClone(inst)) {
          assert(replacement->getType() == inst->getType());
          mapInst(inst, replacement);
          return;
        }
      }
      if (hasInstMapping(inst))
        return;
      appendShell(destination, cloneShell(inst), phi);
    };
    forEachPhi(block, [&](Inst *inst) { createShell(inst, true); });
    forEachInst(block, [&](Inst *inst) { createShell(inst, false); });
  }

  const BlockTranslator translateBlockFn = [this](BasicBlock *block) {
    return translateBlock(block);
  };
  // 映射稳定后连线 使用setArg重建Use链 再翻译块引用并递归克隆结构化子Region
  for (BasicBlock *block = source->first; block; block = block->next()) {
    auto link = [&](Inst *inst) {
      Inst *copied = lookupInstMapping(inst);
      // 预映射值可能位于本Region之外, 只连接本轮实际创建并挂入该Region的外壳
      if (!copied || copied->parentBlock() == nullptr ||
          copied->parentBlock()->parentRegion != clone)
        return;
      for (u32 index = 0; index < inst->getOperandCount(); ++index) {
        Inst *operand = resolveOperand(inst->getArg(index), config);
        assert(operand && "DeepCopy: 未映射的跨函数局部值");
        copied->setArg(index, operand);
      }
      if (copied->getOp() == OP_PHI) {
        remapPhiIncoming(copied, translateBlockFn);
      } else if (carriesJumpTable(copied)) {
        remapJumpTable(copied, translateBlockFn);
      } else if (isTerminator(copied->getOp())) {
        const bool isReturn = inst->getOp() == OP_RET;
        // rewriteTerminator可能清空操作数 必须在回调前保存已翻译返回值
        Inst *returnValue =
            isReturn && copied->getOperandCount() ? copied->getArg(0) : nullptr;
        const bool rewritten =
            config.rewriteTerminator && config.rewriteTerminator(inst, copied);
        if (!rewritten)
          remapTerminatorTargets(copied, translateBlockFn);
        if (isReturn)
          result.returns.push_back({copied->parentBlock(), returnValue});
      } else if (isStructuredControl(copied->getOp())) {
        cloneSubregions(inst, copied, config, result);
      }
      if (config.afterCloneInst)
        config.afterCloneInst(inst, copied);
    };
    forEachPhi(block, link);
    forEachInst(block, link);
  }
  return clone;
}

void DeepCopy::cloneSubregions(Inst *source, Inst *clone,
                               const RegionCloneConfig &config,
                               RegionCloneResult &result) {
  auto copyChild = [&](Region *child) {
    if (!child)
      return static_cast<Region *>(nullptr);
    Region *copied = cloneRegionInto(child, config, result);
    // 子Region的owner是克隆后的结构指令 parent则是该结构指令所在的外层Region
    copied->owner = clone;
    copied->parent = clone->parentBlock()->parentRegion;
    return copied;
  };
  if (source->getOp() == OP_FOR) {
    clone->setBody(copyChild(source->getBody()));
    return;
  }
  clone->getScf().r[0] = copyChild(source->getScf().r[0]);
  clone->getScf().r[1] = copyChild(source->getScf().r[1]);
}

RegionCloneResult DeepCopy::copyRegion(Region *source,
                                       const RegionCloneConfig &config) {
  RegionCloneResult result;
  if (!source)
    return result;
  std::function<bool(Region *)> hasMappedBlock = [&](Region *region) {
    if (!region)
      return false;
    for (BasicBlock *block = region->first; block; block = block->next()) {
      if (hasBlockMapping(block))
        return true;
      for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
        if (inst->getOp() == OP_FOR && hasMappedBlock(inst->getBody()))
          return true;
        if ((inst->getOp() == OP_IF || inst->getOp() == OP_WHILE) &&
            (hasMappedBlock(inst->getScf().r[0]) ||
             hasMappedBlock(inst->getScf().r[1])))
          return true;
      }
    }
    return false;
  };
  if (hasMappedBlock(source)) {
    note(source->owner, "DeepCopy拒绝重复克隆同一个Region事务.");
    return result;
  }

  // RequireMapped先验证整个递归Region 再开始分配克隆
  if (config.externalValueMode == ExternalValueMode::RequireMapped) {
    bool valid = true;
    std::unordered_set<Inst *> internal;
    forEachInstRecursive(source, [&](Inst *inst) { internal.insert(inst); });
    forEachInstRecursive(source, [&](Inst *inst) {
      for (u32 index = 0; valid && index < inst->getOperandCount(); ++index) {
        Inst *operand = inst->getArg(index);
        const bool rematerializable =
            operand->isUndefValue() || operand->getOp() == OP_ICONST ||
            operand->getOp() == OP_FCONST || operand->getOp() == OP_GETGLOBAL;
        valid = internal.count(operand) || hasInstMapping(operand) ||
                rematerializable || operand->isPrecoloredDef() ||
                isTargetLocal(operand);
      }
    });
    if (!valid) {
      note(source->owner, "DeepCopy拒绝未映射的跨函数局部值.");
      return result;
    }
  }

  result.region = cloneRegionInto(source, config, result);
  result.entry = result.region->first;
  if (config.insertInto)
    spliceBlocksAfter(result.region, config.insertInto, config.insertAfter);
  return result;
}

Inst *DeepCopy::copyStructuredInstAfter(Inst *source, Inst *insertAfter,
                                        const RegionCloneConfig &config) {
  assert(source && isStructuredControl(source->getOp()));
  assert(insertAfter && insertAfter->parentBlock() && !hasInstMapping(source));
  Inst *clone = cloneShell(source);
  clone->linkAfter(insertAfter);
  for (u32 index = 0; index < source->getOperandCount(); ++index) {
    Inst *operand = resolveOperand(source->getArg(index), config);
    assert(operand);
    clone->setArg(index, operand);
  }
  RegionCloneResult ignored;
  cloneSubregions(source, clone, config, ignored);
  if (config.afterCloneInst)
    config.afterCloneInst(source, clone);
  return clone;
}

Inst *
DeepCopy::copyInstBefore(Inst *source, Inst *insertBefore,
                         const std::function<Inst *(Inst *)> &translateValue) {
  assert(source && insertBefore && insertBefore->parentBlock());
  assert(source->getOp() != OP_PHI && !isTerminator(source->getOp()) &&
         !isStructuredControl(source->getOp()) && !carriesJumpTable(source));
  assert(!hasInstMapping(source));
  Inst *clone = cloneShell(source);
  clone->linkBefore(insertBefore);
  for (u32 index = 0; index < source->getOperandCount(); ++index) {
    Inst *operand = source->getArg(index);
    Inst *mapped = translateValue ? translateValue(operand) : nullptr;
    clone->setArg(index, mapped ? mapped : translate(operand));
  }
  return clone;
}

Inst *DeepCopy::materializeInstructionSlice(
    Inst *root, Inst *insertBefore,
    const std::function<bool(Inst *)> &isSliceLocal,
    const std::function<bool(Inst *)> &canCloneInst) {
  // 只验证依赖闭包 不修改IR
  // Phi, 不可克隆指令或环都会在任何外壳生成前被拒绝
  std::unordered_set<Inst *> validationVisiting;
  std::unordered_set<Inst *> validated;
  std::function<bool(Inst *)> validate = [&](Inst *value) {
    if (!value || lookupInstMapping(value) || !isSliceLocal ||
        !isSliceLocal(value) || validated.count(value))
      return true;
    if (!validationVisiting.insert(value).second) {
      note(value, "DeepCopy拒绝包含环的指令切片.");
      return false;
    }
    if (value->getOp() == OP_PHI) {
      note(value, "DeepCopy拒绝未映射Phi的指令切片.");
      validationVisiting.erase(value);
      return false;
    }
    if (!canCloneInst || !canCloneInst(value)) {
      note(value, "DeepCopy拒绝包含不可克隆指令的切片.");
      validationVisiting.erase(value);
      return false;
    }
    for (u32 index = 0; index < value->getOperandCount(); ++index)
      if (!validate(value->getArg(index))) {
        validationVisiting.erase(value);
        return false;
      }
    validationVisiting.erase(value);
    validated.insert(value);
    return true;
  };
  if (!validate(root))
    return nullptr;

  // 后序物化依赖 显式映射优先 用于复用新IV
  // 累加器和本轮已经物化的公共子表达式 切片外的值由调用方保证支配插入点
  std::function<Inst *(Inst *)> materialize = [&](Inst *value) -> Inst * {
    if (!value)
      return nullptr;
    if (Inst *mapped = lookupInstMapping(value))
      return mapped;
    if (!isSliceLocal || !isSliceLocal(value))
      return value;
    for (u32 index = 0; index < value->getOperandCount(); ++index)
      materialize(value->getArg(index));
    return copyInstBefore(value, insertBefore);
  };
  return materialize(root);
}

void DeepCopy::spliceBlocksAfter(Region *source, Region *destination,
                                 BasicBlock *anchor) {
  // 移动块后还要修正结构化指令子Region的parent
  // 否则嵌套结构仍会指向已经被掏空的临时Region
  assert(source && destination);
  if (!source->first)
    return;
  if (!anchor) {
    while (source->last) {
      BasicBlock *block = source->last;
      block->moveToStart(destination);
      forEachInst(block,
                  [&](Inst *inst) { reparentSubregions(inst, destination); });
    }
    return;
  }
  assert(anchor->parentRegion == destination);
  BasicBlock *position = anchor;
  while (source->first) {
    BasicBlock *block = source->first;
    block->moveAfter(position);
    forEachInst(block,
                [&](Inst *inst) { reparentSubregions(inst, destination); });
    position = block;
  }
}

std::vector<ClonedBlockPair>
DeepCopy::copyBlocks(const std::vector<BasicBlock *> &blocks,
                     const BlockCloneConfig &config) {
  std::vector<ClonedBlockPair> result;
  if (blocks.empty())
    return result;
  // 固化源块集合和逐指令决策
  // 所有可拒绝条件都在修改IR前完成 后续阶段只提交已经验证的克隆计划
  std::unordered_set<BasicBlock *> sourceSet;
  for (BasicBlock *block : blocks) {
    if (!block || !sourceSet.insert(block).second ||
        (!config.freshBlockMappings && hasBlockMapping(block))) {
      note(nullptr, "DeepCopy拒绝无效或重复的基本块集合.");
      return result;
    }
  }
  if (config.externalTargetMode == ExternalTargetMode::Redirect &&
      !config.redirectTarget) {
    note(nullptr, "DeepCopy缺少集合外重定向目标.");
    return result;
  }

  struct PlannedInst {
    BasicBlock *sourceBlock = nullptr;
    Inst *source = nullptr;
    BasicBlock *patchTarget = nullptr;
    CloneInstAction action = CloneInstAction::Clone;
    bool phi = false;
  };
  std::vector<PlannedInst> plan;
  for (BasicBlock *block : blocks) {
    auto planInst = [&](Inst *inst, bool phi) {
      const CloneInstAction action =
          config.decideInst
              ? config.decideInst(block, inst, phi)
              : (hasInstMapping(inst) ? CloneInstAction::SkipMapped
                                      : CloneInstAction::Clone);
      if (action == CloneInstAction::SkipMapped && !hasInstMapping(inst)) {
        note(inst, "DeepCopy的SkipMapped指令缺少显式值映射.");
        return false;
      }
      if (action == CloneInstAction::Clone && hasInstMapping(inst)) {
        note(inst, "DeepCopy不能重复克隆已经映射的指令.");
        return false;
      }
      BasicBlock *patchTarget = nullptr;
      if (action == CloneInstAction::SkipUnmapped &&
          isTerminator(inst->getOp())) {
        patchTarget = config.skippedTerminatorTarget
                          ? config.skippedTerminatorTarget(inst)
                          : nullptr;
        if (!patchTarget) {
          note(inst, "DeepCopy跳过终结符时缺少补尾目标.");
          return false;
        }
      }
      plan.push_back({block, inst, patchTarget, action, phi});
      return true;
    };
    bool valid = true;
    forEachPhi(block, [&](Inst *inst) { valid &= planInst(inst, true); });
    forEachInst(block, [&](Inst *inst) { valid &= planInst(inst, false); });
    if (!valid)
      return {};
  }

  // 按输入顺序创建全部目标块并登记映射
  if (config.freshBlockMappings) {
    blockMap_.clear();
    jumpTableMap_.clear();
  }
  BasicBlock *after = config.insertAfter ? config.insertAfter : blocks.back();
  for (BasicBlock *source : blocks) {
    assert(!hasBlockMapping(source));
    BasicBlock *clone = config.createBlock ? config.createBlock(source, after)
                                           : builder_.newBlockAfter(after);
    mapBlock(source, clone);
    result.push_back({source, clone});
    after = clone;
  }

  // 物化指令外壳 此时只登记值映射 暂不绑定操作数或CFG目标
  struct Pending {
    Inst *source = nullptr;
    Inst *clone = nullptr;
  };
  std::vector<Pending> pending;
  for (const PlannedInst &item : plan) {
    BasicBlock *destination = translateBlock(item.sourceBlock);
    if (item.action == CloneInstAction::SkipMapped)
      continue;
    if (item.action == CloneInstAction::SkipUnmapped) {
      if (item.patchTarget) {
        builder_.setInsertAtEnd(destination);
        builder_.emitJump(translateBlock(item.patchTarget));
      }
      continue;
    }
    Inst *clone = cloneShell(item.source);
    appendShell(destination, clone, item.phi);
    pending.push_back({item.source, clone});
  }

  // 映射完整后连接操作数并翻译CFG引用
  // copyBlocks不递归处理HIR子Region 结构化克隆应使用copyRegion
  const BlockTranslator translateTarget = [&](BasicBlock *target) {
    if (!target)
      return target;
    if (hasBlockMapping(target))
      return translateBlock(target);
    return config.externalTargetMode == ExternalTargetMode::Redirect
               ? config.redirectTarget
               : target;
  };
  for (const Pending &item : pending) {
    for (u32 index = 0; index < item.source->getOperandCount(); ++index) {
      Inst *operand = item.source->getArg(index);
      Inst *mapped =
          config.translateOperand
              ? config.translateOperand(operand, item.source, item.clone)
              : nullptr;
      item.clone->setArg(index, mapped ? mapped : translate(operand));
    }
    if (item.clone->getOp() == OP_PHI)
      remapPhiIncoming(item.clone, translateTarget);
    else if (carriesJumpTable(item.clone))
      remapJumpTable(item.clone, translateTarget);
    else if (isTerminator(item.clone->getOp()))
      remapTerminatorTargets(item.clone, translateTarget);
  }
  // 本入口不重算predecessors或其他派生分析 调用方应在完整变换结束后收尾
  return result;
}

BasicBlock *DeepCopy::copySingleBlockInPath(
    BasicBlock *source, BasicBlock *insertAfter,
    BasicBlock *newTerminatorTarget,
    const std::function<Inst *(Inst *)> &translateValue,
    const std::function<bool(Inst *)> &valueVisible) {
  if (!source)
    return nullptr;
  if (source->firstPhi())
    return nullptr;
  // 路径克隆先验证所有操作数在新路径可见 再复用copyBlocks的分阶段克隆
  for (Inst *inst = source->firstInst(); inst; inst = inst->next())
    for (u32 index = 0; index < inst->getOperandCount(); ++index)
      if (valueVisible && !valueVisible(inst->getArg(index)))
        return nullptr;
  if (newTerminatorTarget &&
      (!source->lastInst() || (source->lastInst()->getOp() != OP_JMP &&
                               source->lastInst()->getOp() != MOP_J))) {
    note(source->lastInst(), "DeepCopy路径重定向只支持无条件跳转块.");
    return nullptr;
  }
  BlockCloneConfig config;
  config.insertAfter = insertAfter;
  config.translateOperand = [&](Inst *value, Inst *, Inst *) {
    return translateValue ? translateValue(value) : nullptr;
  };
  config.externalTargetMode = newTerminatorTarget ? ExternalTargetMode::Redirect
                                                  : ExternalTargetMode::Mirror;
  config.redirectTarget = newTerminatorTarget;
  std::vector<ClonedBlockPair> result = copyBlocks({source}, config);
  return result.empty() ? nullptr : result.front().clone;
}

Function *DeepCopy::copyFunction(Function *source, const char *newName) {
  assert(source && source->module);
  if (source->phase == IRPhase::MIR) {
    if (DiagnosticEngine *diagnostics = source->module->diagnostics)
      SVM_NOTE(*diagnostics, SourceLocation{},
               "DeepCopy不支持携带寄存器分配侧表的MIR函数克隆.");
    return nullptr; // MIR还包含寄存器分配侧表 不能伪装成完整语义克隆
  }
  Module *module = source->module;
  const char *name = newName ? module->arena->duplicateString(newName)
                             : module->arena->duplicateString(source->name);
  Function *clone = module->newFunction(name, source->returnType,
                                        source->paramTypes, source->paramCount,
                                        source->functionType, source->isExtern);
  clone->phase = source->phase;
  clone->mirPhase = source->mirPhase;
  if (source->isExtern)
    return clone;

  // 参数必须在函数体克隆前完成映射
  // 函数体使用RequireMapped 防止目标函数引用源函数局部节点
  // 常量和全局地址由目标函数重新物化
  DeepCopy copier(clone);
  for (u32 index = 0; index < source->paramCount; ++index)
    copier.mapInst(source->params[index], clone->params[index]);
  RegionCloneConfig config;
  config.externalValueMode = ExternalValueMode::RequireMapped;
  config.afterCloneInst = [&](Inst *sourceInst, Inst *cloneInst) {
    if ((sourceInst->getOp() == OP_CALL || sourceInst->getOp() == MOP_CALL) &&
        sourceInst->getCallee() == source)
      cloneInst->setCallee(clone);
  };
  RegionCloneResult body = copier.copyRegion(source->region, config);
  if (!body.region)
    return nullptr;
  clone->region = body.region;
  clone->region->owner = nullptr;
  clone->region->parent = nullptr;
  // 不复制任何分析派生状态
  // 新函数只重建基础CFG predecessor和Use链 其他分析按需重新计算
  computePreds(clone);
  computeUses(clone);
  return clone;
}

void DeepCopy::flattenRegionIntoBlock(Region *source, BasicBlock *destination,
                                      bool keepTrailingTerminator) {
  assert(source && destination && source->first == source->last);
  BasicBlock *block = source->first;
  assert(block && !block->firstPhi());
  assert(!destination->endsWithTerminator());
  if (!keepTrailingTerminator) {
    Inst *terminator = block->lastInst();
    if (!terminator || terminator->getOp() != OP_YIELD ||
        !terminator->eraseFromBlock()) {
      note(terminator, "DeepCopy压平Region时无法删除尾部yield.");
      return;
    }
  }
  if (!block->firstInst())
    return;
  Inst *anchor = destination->lastInst();
  // 每次都从块首摘链 避免unlink改写next导致漏搬
  // 指令payload和Use-Def保持不变 这里只修改物理归属和嵌套Region的parent
  while (Inst *inst = block->firstInst()) {
    inst->unlinkFromBlock();
    if (anchor) {
      inst->linkAfter(anchor);
    } else {
      inst->block_ = destination;
      destination->instFirst_ = destination->instLast_ = inst;
    }
    reparentSubregions(inst, destination->parentRegion);
    anchor = inst;
  }
}

void DeepCopy::addTranslatedExitPhiIncomings(
    Function *function, const std::vector<ClonedBlockPair> &blocks,
    const std::function<bool(BasicBlock *, BasicBlock *)> &filter) {
  assert(function);
  std::unordered_set<BasicBlock *> sourceSet;
  for (const ClonedBlockPair &pair : blocks)
    sourceSet.insert(pair.source);
  // 对每条从克隆集合离开的边
  // 把源predecessor对应的Phi值翻译后安装到克隆predecessor
  // CFGEditor负责保持边和Phi incoming一致
  for (const ClonedBlockPair &pair : blocks) {
    BasicBlock *sourcePred = pair.source;
    forEachSuccessor(sourcePred, [&](BasicBlock *exit) {
      if (sourceSet.count(exit) || (filter && !filter(sourcePred, exit)))
        return;
      std::vector<CFGEditor::PhiEdgeValue> values;
      forEachPhi(exit, [&](Inst *phi) {
        Inst *value = CFGEditor::getPhiIncomingValue(phi, sourcePred);
        if (value)
          values.push_back({phi, translate(value)});
      });
      if (values.empty())
        return;
      const bool added = CFGEditor::addPhiEdgeValues(
          function, exit, translateBlock(sourcePred), values);
      if (!added)
        note(exit->firstPhi(), "DeepCopy无法为克隆退出边补齐Phi incoming.");
    });
  }
}

} // namespace ir
} // namespace svm
