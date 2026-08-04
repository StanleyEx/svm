/// @file SCEVSupport.cpp
/// @brief 实现 SCEV 展开安全检查和 SCEVExpander

#include "SCEV.h"
#include "Utils.h"

namespace svm {
namespace ir {

namespace {

/// @brief 判断 SSA 值能否在目标块或具体插入锚点处可见
bool instructionVisibleAt(Inst *value, const Function *function,
                          BasicBlock *insertBlock, Inst *insertBefore,
                          const DominatorTree *dominatorTree) {
  if (!value || value->isErased())
    return false;
  if (function && !function->ownsValue(value))
    return false;
  if (insertBefore && (!insertBlock || insertBefore->isErased() ||
                       insertBefore->parentBlock() != insertBlock ||
                       (function && !function->ownsValue(insertBefore))))
    return false;

  BasicBlock *valueBlock = value->parentBlock();
  if (!valueBlock)
    return true;
  if (!insertBlock)
    return false;
  if (valueBlock != insertBlock)
    return dominatorTree && dominatorTree->dominates(valueBlock, insertBlock);
  if (!insertBefore || value->getOp() == OP_PHI)
    return true;
  for (Inst *instruction = insertBefore->previous(); instruction;
       instruction = instruction->previous())
    if (instruction == value)
      return true;
  return false;
}

struct ScaledPointerOffset {
  SCEVExpr *index = nullptr; // 需要符号扩展的i32索引
  i32 stride = 0;            // pointer-width字节倍率
};

ScaledPointerOffset matchScaledPointerOffset(SCEVExpr *expr) noexcept {
  if (!expr || expr->ty != TY_I64 || expr->kind != SCEVExpr::K_MUL ||
      expr->nary.ops.size() != 2)
    return {};
  SCEVExpr *constant = nullptr;
  SCEVExpr *index = nullptr;
  for (SCEVExpr *operand : expr->nary.ops) {
    if (!operand)
      return {};
    if (operand->isConstant())
      constant = constant ? nullptr : operand;
    else
      index = index ? nullptr : operand;
  }
  if (!constant || !index || index->ty != TY_I32 || constant->cst.v <= 0 ||
      !fitsI32(constant->cst.v))
    return {};
  return {index, static_cast<i32>(constant->cst.v)};
}

} // namespace

SCEV::ExpansionReuse SCEV::findExpansionReuse(const SCEV *scev,
                                              const Function *function,
                                              SCEVExpr *expr,
                                              BasicBlock *insertBlock,
                                              Inst *insertBefore) {
  if (!scev || !expr)
    return {};
  if (!function)
    function = scev->function_;

  if (expr->kind == SCEVExpr::K_ADDREC &&
      ((expr->ty != TY_I32 && expr->ty != TY_PTR) || !expr->addRec.base ||
       !expr->addRec.step || !expr->addRec.loop))
    return {};

  const auto original = scev->exprToInst_.find(expr);
  if (original != scev->exprToInst_.end() && original->second &&
      original->second->getType() == expr->ty &&
      instructionVisibleAt(original->second, function, insertBlock,
                           insertBefore, scev->dominatorTree_))
    return {original->second, nullptr};

  if (expr->kind != SCEVExpr::K_ADDREC)
    return {};

  for (const auto &[value, known] : scev->cache_)
    if (value && known && value->getType() == expr->ty &&
        known->structurallyEquals(expr) &&
        instructionVisibleAt(value, function, insertBlock, insertBefore,
                             scev->dominatorTree_))
      return {value, nullptr};

  for (const auto &[value, known] : scev->cache_) {
    if (!value || !known || known->kind != SCEVExpr::K_ADDREC ||
        (value->getType() != TY_I32 && value->getType() != TY_PTR) ||
        !known->addRec.base || !known->addRec.step || !known->addRec.loop ||
        known->addRec.loop != expr->addRec.loop ||
        !known->addRec.step->structurallyEquals(expr->addRec.step) ||
        !instructionVisibleAt(value, function, insertBlock, insertBefore,
                              scev->dominatorTree_))
      continue;

    // want = {B + C, +, S}<L>, known = {B, +, S}<L>, 所以 want = known + C
    SCEVExpr *offset = scev->getAddExpr(expr->addRec.base,
                                        scev->getNegExpr(known->addRec.base));
    if (!offset || !offset->isLoopInvariant(expr->addRec.loop))
      continue;
    if (offset->isZero()) {
      if (value->getType() == expr->ty)
        return {value, nullptr};
      continue;
    }

    const bool valueIsPointer = value->getType() == TY_PTR;
    const bool offsetIsPointer =
        offset->kind != SCEVExpr::K_CONSTANT && offset->ty == TY_PTR;
    const u32 pointerOperands =
        static_cast<u32>(valueIsPointer) + static_cast<u32>(offsetIsPointer);
    if (pointerOperands > 1 || (expr->ty == TY_PTR) != (pointerOperands == 1) ||
        !canExpandAt(scev, function, offset, insertBlock, insertBefore))
      continue;
    return {value, offset};
  }
  return {};
}

bool SCEV::canExpandAt(const SCEV *scev, const Function *function,
                       SCEVExpr *expr, BasicBlock *insertBlock,
                       Inst *insertBefore) {
  if (!expr)
    return false;
  if (!function && scev)
    function = scev->function_;
  if (scev && scev->function_ && function && scev->function_ != function)
    return false;
  if (insertBefore && (!insertBlock || insertBefore->isErased() ||
                       insertBefore->parentBlock() != insertBlock ||
                       (function && !function->ownsValue(insertBefore))))
    return false;
  if (function && insertBlock &&
      (!insertBlock->parentRegion ||
       insertBlock->parentRegion->function != function))
    return false;

  if (findExpansionReuse(scev, function, expr, insertBlock, insertBefore).value)
    return true;

  const auto isInteger = [](IRType type) noexcept {
    return type == TY_I32 || type == TY_I64;
  };
  switch (expr->kind) {
  case SCEVExpr::K_CONSTANT:
    return isInteger(expr->ty) && (expr->ty != TY_I64 || fitsI32(expr->cst.v));
  case SCEVExpr::K_UNKNOWN:
    return expr->unk.val && expr->unk.val->getType() == expr->ty &&
           instructionVisibleAt(expr->unk.val, function, insertBlock,
                                insertBefore,
                                scev ? scev->dominatorTree_ : nullptr);
  case SCEVExpr::K_ADD: {
    if (expr->nary.ops.empty())
      return false;
    u32 pointerOperands = 0;
    for (SCEVExpr *operand : expr->nary.ops) {
      if (!operand)
        return false;
      if (operand->kind != SCEVExpr::K_CONSTANT && operand->ty == TY_PTR)
        ++pointerOperands;
      if (expr->ty == TY_PTR && operand->ty == TY_I64) {
        const ScaledPointerOffset scaled = matchScaledPointerOffset(operand);
        if (scaled.index) {
          if (!canExpandAt(scev, function, scaled.index, insertBlock,
                           insertBefore))
            return false;
          continue;
        }
        if (operand->kind != SCEVExpr::K_CONSTANT &&
            operand->kind != SCEVExpr::K_MUL)
          return false;
      }
      if (!canExpandAt(scev, function, operand, insertBlock, insertBefore))
        return false;
    }
    if (expr->ty == TY_I64)
      return false;
    return expr->ty == TY_PTR ? pointerOperands == 1
                              : isInteger(expr->ty) && pointerOperands == 0;
  }
  case SCEVExpr::K_MUL: {
    if (!isInteger(expr->ty) || expr->nary.ops.empty())
      return false;
    if (expr->ty == TY_I64) {
      if (!scev)
        return false;
      MathQuery query;
      query.contextBlock = insertBlock;
      const MathBounds bounds = scev->proveMathBoundsNoWrap(expr, query);
      if (!bounds.valid || !fitsI32(bounds.min, bounds.max))
        return false;
    }
    for (SCEVExpr *operand : expr->nary.ops)
      if (!operand || operand->ty == TY_PTR ||
          !canExpandAt(scev, function, operand, insertBlock, insertBefore))
        return false;
    return true;
  }
  case SCEVExpr::K_SDIV:
  case SCEVExpr::K_SREM:
    return expr->ty == TY_I32 && expr->bin.lhs && expr->bin.rhs &&
           expr->bin.lhs->ty != TY_PTR && expr->bin.rhs->ty != TY_PTR &&
           canExpandAt(scev, function, expr->bin.lhs, insertBlock,
                       insertBefore) &&
           canExpandAt(scev, function, expr->bin.rhs, insertBlock,
                       insertBefore);
  case SCEVExpr::K_ADDREC:
    return false;
  }
  return false;
}

bool SCEV::isSafeToExpand(SCEVExpr *expr, BasicBlock *insertBlock) const {
  return !expr || canExpandAt(this, function_, expr, insertBlock, nullptr);
}

SCEVExpander::SCEVExpander(Function *fn, const SCEV *scev)
    : scev_(scev), builder_(fn->module, fn) {}

Inst *SCEVExpander::expandCodeFor(SCEVExpr *expr, Inst *insertBefore) {
  VERIFY(expr, "expandCodeFor: 表达式不可为空");
  VERIFY(insertBefore, "expandCodeFor: 插入锚点不可为空");
  if (!expr || !insertBefore)
    return nullptr;
  BasicBlock *insertBlock = insertBefore->parentBlock();
  if (!SCEV::canExpandAt(scev_, builder_.function(), expr, insertBlock,
                         insertBefore))
    return nullptr;

  // 缓存只在单次顶层展开内有效, 避免复用位于新锚点之后的旧结果
  expanded_.clear();

  return expand(expr, insertBefore);
}

Inst *SCEVExpander::expand(SCEVExpr *expr, Inst *insertBefore) {
  if (!expr || !insertBefore)
    return nullptr;
  auto it = expanded_.find(expr);
  if (it != expanded_.end())
    return it->second;

  BasicBlock *insertBlock = insertBefore->parentBlock();
  const SCEV::ExpansionReuse reuse = SCEV::findExpansionReuse(
      scev_, builder_.function(), expr, insertBlock, insertBefore);
  if (reuse.value && !reuse.offset) {
    expanded_[expr] = reuse.value;
    return reuse.value;
  }

  Inst *result = nullptr;
  builder_.setInsertBefore(insertBefore);

  // 节点类型由表达式工厂自底向上确定, 不能向子节点强推父节点类型
  IRType emitType = expr->ty;
  if (emitType == TY_I64)
    emitType = TY_I32;

  switch (expr->kind) {
  case SCEVExpr::K_CONSTANT: {
    // OP_ICONST 恒为 TY_I32, 物化边界再次执行确定性的回绕截断
    result = builder_.iConst(i32TruncWrap(expr->cst.v));
    break;
  }

  case SCEVExpr::K_UNKNOWN: {
    // 未知节点只能复用原 SSA 值, 因此需要再次执行锚点级可见性检查
    const DominatorTree *tree = scev_ ? scev_->dominatorTree_ : nullptr;
    if (!expr->unk.val || expr->unk.val->getType() != expr->ty ||
        !instructionVisibleAt(expr->unk.val, builder_.function(), insertBlock,
                              insertBefore, tree))
      return nullptr;
    result = expr->unk.val;
    break;
  }

  case SCEVExpr::K_ADD: {
    if (expr->nary.ops.empty())
      return nullptr;
    u32 pointerOperands = 0;
    for (const SCEVExpr *operand : expr->nary.ops) {
      if (!operand)
        return nullptr;
      pointerOperands +=
          operand->kind != SCEVExpr::K_CONSTANT && operand->ty == TY_PTR ? 1U
                                                                         : 0U;
    }
    if ((expr->ty == TY_PTR && pointerOperands != 1) ||
        (expr->ty != TY_PTR && pointerOperands != 0))
      return nullptr;
    if (expr->ty == TY_PTR) {
      SCEVExpr *pointer = nullptr;
      for (SCEVExpr *operand : expr->nary.ops)
        if (operand && operand->kind != SCEVExpr::K_CONSTANT &&
            operand->ty == TY_PTR)
          pointer = operand;
      result = expand(pointer, insertBefore);
      if (!result || result->getType() != TY_PTR)
        return nullptr;
      for (SCEVExpr *operand : expr->nary.ops) {
        if (operand == pointer)
          continue;
        const ScaledPointerOffset scaled = matchScaledPointerOffset(operand);
        Inst *offset =
            expand(scaled.index ? scaled.index : operand, insertBefore);
        if (!offset || offset->getType() != TY_I32)
          return nullptr;
        builder_.setInsertBefore(insertBefore);
        result = builder_.emitGetPtr(result, offset,
                                     scaled.index ? scaled.stride : 1);
      }
      break;
    }

    // 整数多元加法按操作数顺序左折叠
    result = expand(expr->nary.ops[0], insertBefore);
    if (!result)
      return nullptr;
    for (u32 i = 1; i < expr->nary.ops.size(); ++i) {
      Inst *rhs = expand(expr->nary.ops[i], insertBefore);
      if (!rhs)
        return nullptr;
      builder_.setInsertBefore(insertBefore);
      result = builder_.emit(OP_ADD, TY_I32, result, rhs);
    }
    break;
  }

  case SCEVExpr::K_MUL: {
    if (expr->ty == TY_PTR || expr->nary.ops.empty())
      return nullptr;
    for (const SCEVExpr *operand : expr->nary.ops)
      if (!operand || operand->ty == TY_PTR)
        return nullptr;
    // SysY 不支持指针乘法, K_MUL 恒按整数物化
    result = expand(expr->nary.ops[0], insertBefore);
    if (!result)
      return nullptr;
    for (u32 i = 1; i < expr->nary.ops.size(); ++i) {
      Inst *rhs = expand(expr->nary.ops[i], insertBefore);
      if (!rhs)
        return nullptr;
      builder_.setInsertBefore(insertBefore);
      result = builder_.emit(OP_MUL, emitType, result, rhs);
    }
    break;
  }

  case SCEVExpr::K_SDIV: {
    // OP_DIV 在 LIR 中表示有符号除法
    Inst *lhs = expand(expr->bin.lhs, insertBefore);
    Inst *rhs = expand(expr->bin.rhs, insertBefore);
    if (emitType == TY_PTR || !lhs || !rhs || lhs->getType() == TY_PTR ||
        rhs->getType() == TY_PTR)
      return nullptr;
    builder_.setInsertBefore(insertBefore);
    result = builder_.emit(OP_DIV, emitType, lhs, rhs);
    break;
  }

  case SCEVExpr::K_SREM: {
    // OP_MOD 表示有符号取余, 除零和异常语义由调用方证明
    Inst *lhs = expand(expr->bin.lhs, insertBefore);
    Inst *rhs = expand(expr->bin.rhs, insertBefore);
    if (emitType == TY_PTR || !lhs || !rhs || lhs->getType() == TY_PTR ||
        rhs->getType() == TY_PTR)
      return nullptr;
    builder_.setInsertBefore(insertBefore);
    result = builder_.emit(OP_MOD, emitType, lhs, rhs);
    break;
  }

  case SCEVExpr::K_ADDREC: {
    // 当前循环递推应已被闭式代入, 残留外层递推只能复用已有 SSA 值
    if (!reuse.value || !reuse.offset)
      return nullptr;
    Inst *offset = expand(reuse.offset, insertBefore);
    if (!offset)
      return nullptr;
    builder_.setInsertBefore(insertBefore);
    if (reuse.value->getType() == TY_PTR && offset->getType() != TY_PTR) {
      result = builder_.emitGetPtr(reuse.value, offset);
      result->setStride(1);
    } else if (offset->getType() == TY_PTR &&
               reuse.value->getType() != TY_PTR) {
      result = builder_.emitGetPtr(offset, reuse.value);
      result->setStride(1);
    } else if (reuse.value->getType() == TY_PTR) {
      return nullptr;
    } else {
      result =
          builder_.emit(OP_ADD, reuse.value->getType(), reuse.value, offset);
    }
    if (result->getType() != expr->ty)
      return nullptr;
    break;
  }
  }

  expanded_[expr] = result;
  return result;
}

} // namespace ir
} // namespace svm
