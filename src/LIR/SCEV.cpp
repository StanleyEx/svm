#include "SCEV.h"
#include "Analysis.h"
#include "Utils.h"

#include <algorithm>
#include <cassert>
#include <functional>
#include <limits>
#include <optional>
#include <utility>

namespace svm::ir {
namespace {

constexpr i64 kI32Min = static_cast<i64>(std::numeric_limits<i32>::min());
constexpr i64 kI32Max = static_cast<i64>(std::numeric_limits<i32>::max());

struct LoopPredicate {
  OpCode predicate = OP_ICONST; // 继续循环时成立的规范化比较
  SCEVExpr *tested = nullptr;   // 比较指令的被测表达式 (循环递推项或守卫初值)
  SCEVExpr *bound = nullptr;    // 循环不变边界
  BasicBlock *exit = nullptr;   // 比较失败时到达的退出块
};

// 将回边或守卫分支规范化为被测表达式满足边界谓词时继续循环
std::optional<LoopPredicate>
analyzeLoopPredicate(const SCEV *scev, const Loop *loop, Inst *terminator,
                     SCEVExpr *wanted, BasicBlock *header,
                     BasicBlock *expectedExit) {
  if (!scev || !loop || !terminator || terminator->getOp() != OP_BR ||
      !header || terminator->getOperandCount() == 0)
    return std::nullopt;
  Inst *condition = terminator->getArg(0);
  if (!condition || !isIntCompare(condition->getOp()) ||
      condition->getOperandCount() != 2)
    return std::nullopt;

  BasicBlock *trueBlock = terminator->getBr().trueBB;
  BasicBlock *falseBlock = terminator->getBr().falseBB;
  bool trueContinues = trueBlock == header;
  bool falseContinues = falseBlock == header;
  if (trueContinues == falseContinues)
    return std::nullopt;

  OpCode predicate = condition->getOp();
  if (!trueContinues)
    predicate = invertIntCompare(predicate);
  if (!isIntCompare(predicate))
    return std::nullopt;

  SCEVExpr *left = scev->getSCEV(condition->getArg(0));
  SCEVExpr *right = scev->getSCEV(condition->getArg(1));
  if (!left || !right)
    return std::nullopt;

  const bool leftHasLoopRec = left->containsAddRecOf(loop);
  const bool rightHasLoopRec = right->containsAddRecOf(loop);
  SCEVExpr *tested = nullptr;
  SCEVExpr *bound = nullptr;
  if (leftHasLoopRec != rightHasLoopRec) {
    if (leftHasLoopRec) {
      tested = left;
      bound = right;
    } else {
      tested = right;
      bound = left;
      predicate = swapCompareOperands(predicate);
    }
  } else if (wanted) {
    if (left->structurallyEquals(wanted) || left->containsAddRecOf(loop)) {
      tested = left;
      bound = right;
    } else if (right->structurallyEquals(wanted) ||
               right->containsAddRecOf(loop)) {
      tested = right;
      bound = left;
      predicate = swapCompareOperands(predicate);
    }
  }
  if (!tested || !bound ||
      (wanted ? !tested->structurallyEquals(wanted)
              : !tested->containsAddRecOf(loop)) ||
      !bound->isLoopInvariant(loop))
    return std::nullopt;

  BasicBlock *exit = trueContinues ? falseBlock : trueBlock;
  if (expectedExit && exit != expectedExit)
    return std::nullopt;
  return LoopPredicate{predicate, tested, bound, exit};
}

BasicBlock *uniqueLoopEntryPredecessor(const Loop *loop) noexcept {
  if (!loop || !loop->header())
    return nullptr;
  BasicBlock *entry = nullptr;
  for (u32 index = 0; index < loop->header()->getPredecessorCount(); ++index) {
    BasicBlock *predecessor = loop->header()->getPredecessor(index);
    if (loop->contains(predecessor))
      continue;
    if (entry)
      return nullptr;
    entry = predecessor;
  }
  return entry;
}

BasicBlock *loopGuard(const Loop *loop, BasicBlock *entry,
                      BasicBlock *&continueBlock) noexcept {
  continueBlock = loop ? loop->header() : nullptr;
  if (!entry || !entry->endsWithTerminator())
    return nullptr;
  if (entry->terminator()->getOp() == OP_BR)
    return entry;
  if (entry->terminator()->getOp() != OP_JMP ||
      entry->getPredecessorCount() != 1)
    return nullptr;
  BasicBlock *guard = entry->getPredecessor(0);
  if (!guard || !guard->endsWithTerminator() ||
      guard->terminator()->getOp() != OP_BR)
    return nullptr;
  continueBlock = entry;
  return guard;
}

bool computeConstantBackedges(OpCode predicate, i64 start, i64 step, i64 stop,
                              i64 &backedges) noexcept {
  backedges = 0;
  i64 distance = 0;
  i64 magnitude = step;
  bool roundUp = false;

  switch (predicate) {
  case OP_LT:
    if (step <= 0)
      return false;
    if (start >= stop)
      break;
    if (!checkedSub(stop, start, distance))
      return false;
    roundUp = true;
    break;
  case OP_LE:
    if (step <= 0)
      return false;
    if (start > stop)
      break;
    if (!checkedSub(stop, start, distance))
      return false;
    if (!checkedAdd(distance / step, 1, backedges))
      return false;
    break;
  case OP_GT:
    if (step >= 0 || step == std::numeric_limits<i64>::min())
      return false;
    magnitude = -step;
    if (start <= stop)
      break;
    if (!checkedSub(start, stop, distance))
      return false;
    roundUp = true;
    break;
  case OP_GE:
    if (step >= 0 || step == std::numeric_limits<i64>::min())
      return false;
    magnitude = -step;
    if (start < stop)
      break;
    if (!checkedSub(start, stop, distance))
      return false;
    if (!checkedAdd(distance / magnitude, 1, backedges))
      return false;
    break;
  case OP_NE:
    if (start == stop)
      break;
    if (step == 1 && start < stop) {
      if (!checkedSub(stop, start, backedges))
        return false;
    } else if (step == -1 && start > stop) {
      if (!checkedSub(start, stop, backedges))
        return false;
    } else {
      return false;
    }
    break;
  default:
    return false;
  }

  if (roundUp)
    backedges = distance / magnitude + (distance % magnitude != 0 ? 1 : 0);
  if (backedges < 0 || backedges > std::numeric_limits<i32>::max())
    return false;

  i64 delta = 0;
  i64 finalValue = 0;
  return checkedMul(step, backedges, delta) &&
         checkedAdd(start, delta, finalValue) && finalValue >= kI32Min &&
         finalValue <= kI32Max;
}

} // namespace

bool SCEVExpr::structurallyEquals(const SCEVExpr *other) const noexcept {
  if (this == other)
    return true;
  if (!other || kind != other->kind || ty != other->ty)
    return false;
  const auto sameOperand = [](const SCEVExpr *left,
                              const SCEVExpr *right) noexcept {
    return left == right || (left && left->structurallyEquals(right));
  };
  switch (kind) {
  case K_CONSTANT:
    return cst.v == other->cst.v;
  case K_UNKNOWN:
    return unk.val && other->unk.val && unk.val == other->unk.val;
  case K_ADDREC:
    return addRec.loop == other->addRec.loop &&
           sameOperand(addRec.base, other->addRec.base) &&
           sameOperand(addRec.step, other->addRec.step);
  case K_ADD:
  case K_MUL:
    if (nary.ops.size() != other->nary.ops.size())
      return false;
    for (usize index = 0; index < nary.ops.size(); ++index)
      if (!sameOperand(nary.ops[index], other->nary.ops[index]))
        return false;
    return true;
  case K_SDIV:
  case K_SREM:
    return sameOperand(bin.lhs, other->bin.lhs) &&
           sameOperand(bin.rhs, other->bin.rhs);
  }
  return false;
}

bool SCEVExpr::isLoopInvariant(const Loop *loop) const {
  if (!loop)
    return true;
  switch (kind) {
  case K_CONSTANT:
    return true;
  case K_UNKNOWN: {
    BasicBlock *block = unk.val ? unk.val->parentBlock() : nullptr;
    return !block || !loop->contains(block);
  }
  case K_ADDREC:
    if (addRec.loop == loop || loop->containsLoop(addRec.loop))
      return false;
    return true;
  case K_ADD:
  case K_MUL:
    for (SCEVExpr *operand : nary.ops)
      if (!operand || !operand->isLoopInvariant(loop))
        return false;
    return true;
  case K_SDIV:
  case K_SREM:
    return bin.lhs && bin.rhs && bin.lhs->isLoopInvariant(loop) &&
           bin.rhs->isLoopInvariant(loop);
  }
  return false;
}

bool SCEVExpr::containsAddRecOf(const Loop *loop) const {
  if (!loop)
    return false;
  switch (kind) {
  case K_CONSTANT:
  case K_UNKNOWN:
    return false;
  case K_ADDREC:
    return addRec.loop == loop ||
           (addRec.base && addRec.base->containsAddRecOf(loop)) ||
           (addRec.step && addRec.step->containsAddRecOf(loop));
  case K_ADD:
  case K_MUL:
    for (SCEVExpr *operand : nary.ops)
      if (operand && operand->containsAddRecOf(loop))
        return true;
    return false;
  case K_SDIV:
  case K_SREM:
    return (bin.lhs && bin.lhs->containsAddRecOf(loop)) ||
           (bin.rhs && bin.rhs->containsAddRecOf(loop));
  }
  return false;
}

SCEVExpr *SCEV::allocExpr(SCEVExpr::Kind kind, IRType type) const {
  auto node = std::make_unique<SCEVExpr>();
  node->kind = kind;
  node->ty = type;
  SCEVExpr *result = node.get();
  expressions_.push_back(std::move(node));
  return result;
}

void SCEV::setNoWrap(SCEVExpr *expr) const noexcept {
  if (!expr || expr->nsw)
    return;
  expr->nsw = true;
  if (expr->kind == SCEVExpr::K_ADDREC && expr->addRec.loop)
    btcCache_.erase(expr->addRec.loop);
}

void SCEV::proveAndSetAddRecNoWrap(SCEVExpr *expr) const noexcept {
  if (!expr || expr->kind != SCEVExpr::K_ADDREC || expr->nsw)
    return;
  if (!noWrapProving_.insert(expr).second)
    return;
  if (proveAddRecNoSignedWrap(expr->addRec.base, expr->addRec.step,
                              expr->addRec.loop))
    setNoWrap(expr);
  noWrapProving_.erase(expr);
}

bool SCEV::proveAddRecNoSignedWrap(SCEVExpr *base, SCEVExpr *step,
                                   const Loop *loop) const noexcept {
  if (!base || !step || !loop || !step->isConstant())
    return false;
  const auto bounds = getI32Range(base).signedBounds();
  if (!bounds || getI32Range(base).isFullSet())
    return false;
  const i64 stepValue = step->cst.v;

  // 动态受守卫形式必须先证明无回绕, 否则 BTC 查询会缓存递归产生的未知值
  if (stepValue > 0 && bounds->min >= 0 && loop->latches().size() == 1) {
    BasicBlock *latch = loop->latches().front();
    auto latchPredicate =
        analyzeLoopPredicate(this, loop, latch ? latch->terminator() : nullptr,
                             nullptr, loop->header(), nullptr);
    SCEVExpr *tested = latchPredicate ? latchPredicate->tested : nullptr;
    if (latchPredicate && latchPredicate->predicate == OP_LT && tested &&
        tested->kind == SCEVExpr::K_ADDREC && tested->addRec.loop == loop &&
        tested->addRec.step->structurallyEquals(step) &&
        tested->addRec.base->structurallyEquals(getAddExpr(base, step))) {
      BasicBlock *entry = uniqueLoopEntryPredecessor(loop);
      BasicBlock *continueBlock = nullptr;
      BasicBlock *guard = loopGuard(loop, entry, continueBlock);
      auto guardPredicate = analyzeLoopPredicate(
          this, loop, guard ? guard->terminator() : nullptr, base,
          continueBlock, latchPredicate->exit);
      const auto stopBounds = getI32Range(latchPredicate->bound).signedBounds();
      if (guardPredicate && guardPredicate->predicate == OP_LT &&
          guardPredicate->bound->structurallyEquals(latchPredicate->bound) &&
          stopBounds && stepValue <= kI32Max &&
          stopBounds->max <= kI32Max - (stepValue - 1)) {
        setNoWrap(tested);
        return true;
      }
    }
  }

  const i64 tripCount = getConstantTripCount(loop);
  if (tripCount <= 0)
    return false;
  const i64 count = tripCount - 1;
  i64 delta = 0;
  if (!checkedMul(stepValue, count, delta))
    return false;
  i64 low = 0;
  i64 high = 0;
  if (!checkedAdd(bounds->min, delta, low) ||
      !checkedAdd(bounds->max, delta, high))
    return false;
  return std::min(static_cast<i64>(bounds->min), low) >= kI32Min &&
         std::max(static_cast<i64>(bounds->max), high) <= kI32Max;
}

SCEVExpr *SCEV::getConstant(i64 value, IRType type) const {
  SCEVExpr *expr = allocExpr(SCEVExpr::K_CONSTANT, type);
  expr->cst.v = type == TY_I32 ? i32SignExtendWrap(value) : value;
  return expr;
}

SCEVExpr *SCEV::getUnknown(Inst *value) const {
  SCEVExpr *expr =
      allocExpr(SCEVExpr::K_UNKNOWN, value ? value->getType() : TY_I32);
  expr->unk.val = value;
  return expr;
}

SCEVExpr *SCEV::getAddRecExpr(SCEVExpr *base, SCEVExpr *step,
                              Loop *loop) const {
  VERIFY(base && step && loop);
  if (step->isZero())
    return base;
  SCEVExpr *expr = allocExpr(SCEVExpr::K_ADDREC, base->ty);
  expr->addRec = {base, step, loop};
  return expr;
}

SCEVExpr *SCEV::buildAddCanonical(SCEVExpr *left, SCEVExpr *right) const {
  std::vector<SCEVExpr *> flattened;
  flattened.reserve(8);
  const auto flatten = [&](SCEVExpr *expr, const auto &self) -> void {
    if (expr->kind != SCEVExpr::K_ADD) {
      flattened.push_back(expr);
      return;
    }
    for (SCEVExpr *operand : expr->nary.ops)
      self(operand, self);
  };
  flatten(left, flatten);
  flatten(right, flatten);

  const IRType type = isPtr(left->ty) ? left->ty : right->ty;
  i64 constant = 0;
  std::vector<std::pair<i64, SCEVExpr *>> terms;
  terms.reserve(flattened.size());
  for (SCEVExpr *expr : flattened) {
    if (expr->isConstant()) {
      i64 sum = 0;
      if (checkedAdd(constant, expr->cst.v, sum))
        constant = sum;
      else
        terms.emplace_back(1, expr);
      continue;
    }
    i64 coefficient = 1;
    SCEVExpr *atom = expr;
    if (expr->kind == SCEVExpr::K_MUL && expr->nary.ops.size() == 2) {
      if (expr->nary.ops[0]->isConstant()) {
        coefficient = expr->nary.ops[0]->cst.v;
        atom = expr->nary.ops[1];
      } else if (expr->nary.ops[1]->isConstant()) {
        coefficient = expr->nary.ops[1]->cst.v;
        atom = expr->nary.ops[0];
      }
    }
    terms.emplace_back(coefficient, atom);
  }

  for (usize first = 0; first < terms.size(); ++first) {
    if (!terms[first].second)
      continue;
    for (usize second = first + 1; second < terms.size(); ++second) {
      if (!terms[second].second ||
          !terms[first].second->structurallyEquals(terms[second].second))
        continue;
      i64 sum = 0;
      if (checkedAdd(terms[first].first, terms[second].first, sum)) {
        terms[first].first = sum;
        terms[second].second = nullptr;
      }
    }
  }

  std::vector<SCEVExpr *> operands;
  operands.reserve(terms.size() + 1);
  for (const auto &[coefficient, atom] : terms) {
    if (!atom || coefficient == 0)
      continue;
    if (coefficient == 1)
      operands.push_back(atom);
    else
      operands.push_back(getMulExpr(atom, getConstant(coefficient, atom->ty)));
  }
  if (constant != 0)
    operands.push_back(getConstant(constant, isPtr(type) ? TY_I32 : type));
  if (operands.empty())
    return getConstant(0, type);
  if (operands.size() == 1)
    return operands.front();

  SCEVExpr *result = allocExpr(SCEVExpr::K_ADD, type);
  result->nary.ops = std::move(operands);
  return result;
}

SCEVExpr *SCEV::getAddExpr(SCEVExpr *left, SCEVExpr *right) const {
  VERIFY(left && right);
  if (left->isConstant() && right->isConstant()) {
    i64 value = 0;
    if (checkedAdd(left->cst.v, right->cst.v, value))
      return getConstant(value, isPtr(left->ty) ? left->ty : right->ty);
  }
  if (left->isZero())
    return right;
  if (right->isZero())
    return left;

  if (left->kind == SCEVExpr::K_ADDREC && right->kind == SCEVExpr::K_ADDREC &&
      left->addRec.loop == right->addRec.loop) {
    SCEVExpr *result = getAddRecExpr(
        getAddExpr(left->addRec.base, right->addRec.base),
        getAddExpr(left->addRec.step, right->addRec.step), left->addRec.loop);
    if (result->kind == SCEVExpr::K_ADDREC && left->nsw && right->nsw)
      proveAndSetAddRecNoWrap(result);
    return result;
  }
  if (left->kind == SCEVExpr::K_ADDREC &&
      right->isLoopInvariant(left->addRec.loop)) {
    SCEVExpr *result = getAddRecExpr(getAddExpr(left->addRec.base, right),
                                     left->addRec.step, left->addRec.loop);
    if (result->kind == SCEVExpr::K_ADDREC && left->nsw)
      proveAndSetAddRecNoWrap(result);
    return result;
  }
  if (right->kind == SCEVExpr::K_ADDREC &&
      left->isLoopInvariant(right->addRec.loop)) {
    SCEVExpr *result = getAddRecExpr(getAddExpr(right->addRec.base, left),
                                     right->addRec.step, right->addRec.loop);
    if (result->kind == SCEVExpr::K_ADDREC && right->nsw)
      proveAndSetAddRecNoWrap(result);
    return result;
  }
  return buildAddCanonical(left, right);
}

SCEVExpr *SCEV::getMulExpr(SCEVExpr *left, SCEVExpr *right) const {
  VERIFY(left && right);
  const IRType type = left->ty;
  std::vector<SCEVExpr *> factors;
  factors.reserve(4);
  i64 constant = 1;
  bool overflow = false;
  const auto flatten = [&](SCEVExpr *expr, const auto &self) -> void {
    if (expr->kind == SCEVExpr::K_MUL) {
      for (SCEVExpr *operand : expr->nary.ops)
        self(operand, self);
      return;
    }
    if (expr->isConstant()) {
      i64 product = 0;
      if (!checkedMul(constant, expr->cst.v, product))
        overflow = true;
      else
        constant = product;
      return;
    }
    factors.push_back(expr);
  };
  flatten(left, flatten);
  flatten(right, flatten);

  if (overflow) {
    SCEVExpr *result = allocExpr(SCEVExpr::K_MUL, type);
    result->nary.ops = {left, right};
    return result;
  }
  if (constant == 0)
    return getConstant(0, type);
  if (factors.empty())
    return getConstant(constant, type);

  for (usize recIndex = 0; recIndex < factors.size(); ++recIndex) {
    SCEVExpr *recurrence = factors[recIndex];
    if (recurrence->kind != SCEVExpr::K_ADDREC)
      continue;
    Loop *loop = recurrence->addRec.loop;
    bool invariant = true;
    for (usize index = 0; index < factors.size(); ++index)
      if (index != recIndex && !factors[index]->isLoopInvariant(loop)) {
        invariant = false;
        break;
      }
    if (!invariant)
      continue;

    SCEVExpr *scale = getConstant(constant, type);
    for (usize index = 0; index < factors.size(); ++index)
      if (index != recIndex)
        scale = getMulExpr(scale, factors[index]);
    SCEVExpr *result =
        getAddRecExpr(getMulExpr(recurrence->addRec.base, scale),
                      getMulExpr(recurrence->addRec.step, scale), loop);
    if (result->kind == SCEVExpr::K_ADDREC && recurrence->nsw &&
        scale->isConstant())
      proveAndSetAddRecNoWrap(result);
    return result;
  }

  std::stable_sort(factors.begin(), factors.end(),
                   [](const SCEVExpr *leftExpr, const SCEVExpr *rightExpr) {
                     if (leftExpr->kind != rightExpr->kind)
                       return leftExpr->kind < rightExpr->kind;
                     if (leftExpr->kind == SCEVExpr::K_UNKNOWN) {
                       const u32 leftId =
                           leftExpr->unk.val ? leftExpr->unk.val->id : 0;
                       const u32 rightId =
                           rightExpr->unk.val ? rightExpr->unk.val->id : 0;
                       if (leftId != rightId)
                         return leftId < rightId;
                     }
                     return std::less<const SCEVExpr *>{}(leftExpr, rightExpr);
                   });
  if (constant != 1)
    factors.push_back(getConstant(constant, type));
  if (factors.size() == 1)
    return factors.front();
  SCEVExpr *result = allocExpr(SCEVExpr::K_MUL, type);
  result->nary.ops = std::move(factors);
  return result;
}

SCEVExpr *SCEV::getSDivExpr(SCEVExpr *left, SCEVExpr *right) const {
  VERIFY(left && right);
  if (left->isConstant() && right->isConstant() && right->cst.v != 0) {
    const i64 dividend = left->cst.v;
    const i64 divisor = right->cst.v;
    if (!(dividend == std::numeric_limits<i64>::min() && divisor == -1)) {
      const i64 quotient = dividend / divisor;
      if (left->ty != TY_I32 || (quotient >= kI32Min && quotient <= kI32Max))
        return getConstant(quotient, left->ty);
    }
  }
  if (right->isOne())
    return left;
  SCEVExpr *result = allocExpr(SCEVExpr::K_SDIV, left->ty);
  result->bin = {left, right};
  return result;
}

SCEVExpr *SCEV::getSRemExpr(SCEVExpr *left, SCEVExpr *right) const {
  VERIFY(left && right);
  if (left->isConstant() && right->isConstant() && right->cst.v != 0) {
    const i64 dividend = left->cst.v;
    const i64 divisor = right->cst.v;
    const bool i32Overflow =
        left->ty == TY_I32 && dividend == kI32Min && divisor == -1;
    if (!i32Overflow &&
        !(dividend == std::numeric_limits<i64>::min() && divisor == -1))
      return getConstant(dividend % divisor, left->ty);
  }
  if (right->isConstant() && right->cst.v == 1)
    return getConstant(0, left->ty);
  SCEVExpr *result = allocExpr(SCEVExpr::K_SREM, left->ty);
  result->bin = {left, right};
  return result;
}

SCEVExpr *SCEV::getNegExpr(SCEVExpr *expr) const {
  VERIFY(expr);
  switch (expr->kind) {
  case SCEVExpr::K_CONSTANT:
    if (expr->cst.v != std::numeric_limits<i64>::min() || expr->ty == TY_I32)
      return getConstant(-expr->cst.v, expr->ty);
    break;
  case SCEVExpr::K_ADD: {
    SCEVExpr *result = getNegExpr(expr->nary.ops.front());
    for (usize index = 1; index < expr->nary.ops.size(); ++index)
      result = getAddExpr(result, getNegExpr(expr->nary.ops[index]));
    return result;
  }
  case SCEVExpr::K_ADDREC: {
    SCEVExpr *result =
        getAddRecExpr(getNegExpr(expr->addRec.base),
                      getNegExpr(expr->addRec.step), expr->addRec.loop);
    if (result->kind == SCEVExpr::K_ADDREC && expr->nsw)
      proveAndSetAddRecNoWrap(result);
    return result;
  }
  default:
    break;
  }
  return getMulExpr(expr, getConstant(-1, expr->ty));
}

SCEVExpr *SCEV::getSCEV(Inst *value) const {
  if (!value)
    return getConstant(0, TY_I32);
  if (!function_ || !function_->ownsValue(value)) {
    SCEVExpr *opaque = allocExpr(SCEVExpr::K_UNKNOWN, value->getType());
    opaque->unk.val = nullptr;
    return opaque;
  }
  if (const auto found = cache_.find(value); found != cache_.end())
    return found->second;

  // 占位节点切断 phi -> 回边更新 -> phi 环, 最终表达式生成后再替换缓存
  cache_[value] = getUnknown(value);
  SCEVExpr *result = createSCEV(value);
  cache_[value] = result;
  proveAndSetAddRecNoWrap(result);
  exprToInst_.try_emplace(result, value);
  return result;
}

SCEVExpr *SCEV::createSCEV(Inst *value) const {
  switch (value->getOp()) {
  case OP_ICONST:
    return getConstant(value->getImm(), value->getType());
  case OP_ADD:
    return getAddExpr(getSCEV(value->getArg(0)), getSCEV(value->getArg(1)));
  case OP_SUB:
    return getAddExpr(getSCEV(value->getArg(0)),
                      getNegExpr(getSCEV(value->getArg(1))));
  case OP_MUL:
    return getMulExpr(getSCEV(value->getArg(0)), getSCEV(value->getArg(1)));
  case OP_DIV:
    return getSDivExpr(getSCEV(value->getArg(0)), getSCEV(value->getArg(1)));
  case OP_MOD:
    return getSRemExpr(getSCEV(value->getArg(0)), getSCEV(value->getArg(1)));
  case OP_NEG:
    return getNegExpr(getSCEV(value->getArg(0)));
  case OP_PHI:
    return createNodeForPhi(value);
  case OP_GETPTR: {
    SCEVExpr *base = getSCEV(value->getArg(0));
    SCEVExpr *offset = getSCEV(value->getArg(1));
    const i32 stride = value->getStride();
    if (stride == 1)
      return getAddExpr(base, offset);
    return getAddExpr(
        base,
        getMulExpr(offset, getConstant(static_cast<i64>(stride), TY_I32)));
  }
  default:
    return getUnknown(value);
  }
}

SCEVExpr *SCEV::createNodeForPhi(Inst *phi) const {
  VERIFY(phi && phi->getOp() == OP_PHI);
  BasicBlock *header = phi->parentBlock();
  Loop *loop = header && loopInfo_ ? loopInfo_->getLoopFor(header) : nullptr;
  if (!loop || loop->header() != header || loop->latches().size() != 1)
    return getUnknown(phi);
  BasicBlock *preheader = uniqueLoopEntryPredecessor(loop);
  BasicBlock *latch = loop->latches().front();
  if (!preheader || !latch)
    return getUnknown(phi);

  Inst *baseValue = nullptr;
  Inst *nextValue = nullptr;
  for (u32 index = 0; index < phi->getOperandCount(); ++index) {
    BasicBlock *incoming = phi->getIncomingBlock(index);
    if (incoming == preheader) {
      if (baseValue)
        return getUnknown(phi);
      baseValue = phi->getArg(index);
    } else if (incoming == latch) {
      if (nextValue)
        return getUnknown(phi);
      nextValue = phi->getArg(index);
    } else {
      return getUnknown(phi);
    }
  }
  if (!baseValue || !nextValue)
    return getUnknown(phi);
  SCEVExpr *base = getSCEV(baseValue);

  // 仅当初值是规范余数且未取余的仿射序列无回绕时, 重复有符号取余才有闭式
  if (nextValue->getOp() == OP_MOD && nextValue->getOperandCount() == 2) {
    Inst *sum = nextValue->getArg(0);
    SCEVExpr *modulus = getSCEV(nextValue->getArg(1));
    if (sum && sum->getOp() == OP_ADD && sum->getOperandCount() == 2 &&
        modulus->isConstant() && modulus->cst.v > 0 &&
        modulus->isLoopInvariant(loop)) {
      Inst *first = sum->getArg(0);
      Inst *second = sum->getArg(1);
      SCEVExpr *step = first == phi    ? getSCEV(second)
                       : second == phi ? getSCEV(first)
                                       : nullptr;
      if (step && step->isConstant() && step->isLoopInvariant(loop)) {
        const auto baseBounds = getI32Range(base).signedBounds();
        const i64 modulusValue = modulus->cst.v;
        const bool canonical = baseBounds && baseBounds->min > -modulusValue &&
                               baseBounds->max < modulusValue;
        if (!canonical)
          return getUnknown(phi);
        SCEVExpr *inner = getAddRecExpr(base, step, loop);
        if (inner->kind == SCEVExpr::K_ADDREC)
          proveAndSetAddRecNoWrap(inner);
        if (inner->kind != SCEVExpr::K_ADDREC || inner->nsw)
          return getSRemExpr(inner, modulus);
      }
    }
  }

  SCEVExpr *step = nullptr;
  if (nextValue->getOp() == OP_ADD && nextValue->getOperandCount() == 2) {
    if (nextValue->getArg(0) == phi)
      step = getSCEV(nextValue->getArg(1));
    else if (nextValue->getArg(1) == phi)
      step = getSCEV(nextValue->getArg(0));
  } else if (nextValue->getOp() == OP_SUB &&
             nextValue->getOperandCount() == 2 && nextValue->getArg(0) == phi) {
    step = getNegExpr(getSCEV(nextValue->getArg(1)));
  }

  if (!step) {
    // 匹配仿射更新链, 但不缓存仍引用临时 phi 占位节点的表达式
    std::unordered_set<Inst *> visiting;
    std::unordered_set<Inst *> dependencyStack;
    const auto dependsOnPhi = [&](Inst *value, const auto &self,
                                  u32 depth) -> bool {
      if (!value)
        return false;
      if (value == phi || depth > 64 || !dependencyStack.insert(value).second)
        return true;
      struct DependencyPop {
        std::unordered_set<Inst *> &values; // 当前依赖查询栈
        Inst *value = nullptr;              // 离开时移除的值
        ~DependencyPop() { values.erase(value); }
      } pop{dependencyStack, value};
      for (u32 index = 0; index < value->getOperandCount(); ++index)
        if (self(value->getArg(index), self, depth + 1))
          return true;
      return false;
    };
    const auto matchStep = [&](Inst *value, const auto &self,
                               u32 depth) -> SCEVExpr * {
      if (!value || depth > 64 || !visiting.insert(value).second)
        return nullptr;
      struct VisitPop {
        std::unordered_set<Inst *> &values; // 当前更新链
        Inst *value = nullptr;              // 离开时移除的值
        ~VisitPop() { values.erase(value); }
      } pop{visiting, value};
      if (value == phi)
        return getConstant(0, phi->getType());
      if (value->getOperandCount() != 2)
        return nullptr;

      if (value->getOp() == OP_ADD) {
        for (u32 tracedIndex = 0; tracedIndex < 2; ++tracedIndex) {
          SCEVExpr *prefix = self(value->getArg(tracedIndex), self, depth + 1);
          if (!prefix)
            continue;
          Inst *otherValue = value->getArg(1 - tracedIndex);
          if (dependsOnPhi(otherValue, dependsOnPhi, 0))
            continue;
          SCEVExpr *other = getSCEV(otherValue);
          if (other && other->isLoopInvariant(loop))
            return getAddExpr(prefix, other);
        }
      } else if (value->getOp() == OP_SUB) {
        SCEVExpr *prefix = self(value->getArg(0), self, depth + 1);
        if (!prefix)
          return nullptr;
        Inst *otherValue = value->getArg(1);
        if (dependsOnPhi(otherValue, dependsOnPhi, 0))
          return nullptr;
        SCEVExpr *other = getSCEV(otherValue);
        if (other && other->isLoopInvariant(loop))
          return getAddExpr(prefix, getNegExpr(other));
      }
      return nullptr;
    };
    step = matchStep(nextValue, matchStep, 0);
  }
  if (!step || !step->isLoopInvariant(loop))
    return getUnknown(phi);
  return getAddRecExpr(base, step, loop);
}

SCEVExpr *SCEV::getBackedgeTakenCount(const Loop *loop) const {
  if (!loop)
    return getUnknown(nullptr);
  if (const auto found = btcCache_.find(loop); found != btcCache_.end())
    return found->second;
  SCEVExpr *result = computeBTC(loop);
  // 递归无回绕证明可能遇到临时 phi 占位节点, 此时不能永久缓存未知结果
  if (result->kind != SCEVExpr::K_UNKNOWN || noWrapProving_.empty())
    btcCache_[loop] = result;
  return result;
}

i64 SCEV::getConstantTripCount(const Loop *loop) const {
  SCEVExpr *backedges = getBackedgeTakenCount(loop);
  if (!backedges || !backedges->isConstant() || backedges->cst.v < 0 ||
      backedges->cst.v == std::numeric_limits<i64>::max())
    return -1;
  return backedges->cst.v + 1;
}

SCEVExpr *SCEV::computeBTC(const Loop *loop) const {
  if (!loop || !loop->header() || loop->latches().size() != 1)
    return getUnknown(nullptr);
  BasicBlock *latch = loop->latches().front();
  if (!latch || !latch->endsWithTerminator())
    return getUnknown(nullptr);
  const auto &exitingBlocks = loop->exitingBlocks();
  if (exitingBlocks.empty() ||
      !std::all_of(exitingBlocks.begin(), exitingBlocks.end(),
                   [latch](BasicBlock *block) { return block == latch; }))
    return getUnknown(nullptr);
  const auto normalized = analyzeLoopPredicate(
      this, loop, latch->terminator(), nullptr, loop->header(), nullptr);
  if (!normalized || !normalized->tested || !normalized->bound ||
      normalized->tested->kind != SCEVExpr::K_ADDREC ||
      normalized->tested->addRec.loop != loop)
    return getUnknown(nullptr);

  SCEVExpr *start = normalized->tested->addRec.base;
  SCEVExpr *step = normalized->tested->addRec.step;
  SCEVExpr *stop = normalized->bound;
  if (!start || !step)
    return getUnknown(nullptr);
  const IRType type = start->ty;

  const bool constantStep = step->isConstant();
  const i64 stepValue = constantStep ? step->cst.v : 0;
  bool positiveStep = false;
  bool negativeStep = false;
  if (constantStep) {
    if (stepValue == 0 || stepValue == kI32Min ||
        stepValue == std::numeric_limits<i64>::min())
      return getUnknown(nullptr);
    positiveStep = stepValue > 0;
    negativeStep = stepValue < 0;
  } else {
    RangeQuery query;
    query.contextBlock = loop->header();
    if (const auto bounds = getI32Range(step, query).signedBounds()) {
      positiveStep = bounds->min > 0;
      negativeStep = bounds->max < 0 && bounds->min > kI32Min;
    }
  }

  if (start->isConstant() && step->isConstant() && stop->isConstant()) {
    i64 backedges = 0;
    return computeConstantBackedges(normalized->predicate, start->cst.v,
                                    step->cst.v, stop->cst.v, backedges)
               ? getConstant(backedges, TY_I32)
               : getUnknown(nullptr);
  }

  // 符号闭式使用数学减法和除法, 仅在递推与合成距离均已证明无回绕时有效
  if (!normalized->tested->nsw)
    return getUnknown(nullptr);

  const auto subtract = [&](SCEVExpr *left, SCEVExpr *right) -> SCEVExpr * {
    return getAddExpr(left, getNegExpr(right));
  };
  const auto negateStep = [&]() -> SCEVExpr * {
    return constantStep ? getConstant(-stepValue, type) : getNegExpr(step);
  };
  const auto stepMinusOne = [&]() -> SCEVExpr * {
    return constantStep ? getConstant(stepValue - 1, type)
                        : getAddExpr(step, getConstant(-1, type));
  };

  SCEVExpr *distance = nullptr;
  switch (normalized->predicate) {
  case OP_LT:
    if (!positiveStep)
      return getUnknown(nullptr);
    distance = getAddExpr(subtract(stop, start), stepMinusOne());
    break;
  case OP_LE:
    if (!positiveStep)
      return getUnknown(nullptr);
    distance = getAddExpr(subtract(stop, start), step);
    break;
  case OP_GT:
    if (!negativeStep)
      return getUnknown(nullptr);
    distance = getAddExpr(subtract(start, stop),
                          getAddExpr(negateStep(), getConstant(-1, type)));
    break;
  case OP_GE:
    if (!negativeStep)
      return getUnknown(nullptr);
    distance = getAddExpr(subtract(start, stop), negateStep());
    break;
  case OP_NE:
    if (!constantStep || (stepValue != 1 && stepValue != -1))
      return getUnknown(nullptr);
    distance = stepValue > 0 ? subtract(stop, start) : subtract(start, stop);
    break;
  default:
    return getUnknown(nullptr);
  }
  MathQuery distanceQuery;
  distanceQuery.contextBlock = loop->header();
  const MathBounds distanceBounds =
      proveMathBoundsNoWrap(distance, distanceQuery);
  if (!distanceBounds.valid || distanceBounds.min < 0)
    return getUnknown(nullptr);
  return getSDivExpr(distance, positiveStep ? step : negateStep());
}

SCEVExpr *SCEV::evaluateAtIteration(SCEVExpr *expr, SCEVExpr *iteration,
                                    const Loop *loop) const {
  if (!expr)
    return nullptr;
  switch (expr->kind) {
  case SCEVExpr::K_CONSTANT:
  case SCEVExpr::K_UNKNOWN:
    return expr;
  case SCEVExpr::K_ADDREC:
    if (expr->addRec.loop != loop)
      return expr;
    return getAddExpr(
        evaluateAtIteration(expr->addRec.base, iteration, loop),
        getMulExpr(evaluateAtIteration(expr->addRec.step, iteration, loop),
                   iteration));
  case SCEVExpr::K_ADD: {
    SCEVExpr *result =
        evaluateAtIteration(expr->nary.ops.front(), iteration, loop);
    for (usize index = 1; index < expr->nary.ops.size(); ++index)
      result = getAddExpr(
          result, evaluateAtIteration(expr->nary.ops[index], iteration, loop));
    return result;
  }
  case SCEVExpr::K_MUL: {
    SCEVExpr *result =
        evaluateAtIteration(expr->nary.ops.front(), iteration, loop);
    for (usize index = 1; index < expr->nary.ops.size(); ++index)
      result = getMulExpr(
          result, evaluateAtIteration(expr->nary.ops[index], iteration, loop));
    return result;
  }
  case SCEVExpr::K_SDIV:
    return getSDivExpr(evaluateAtIteration(expr->bin.lhs, iteration, loop),
                       evaluateAtIteration(expr->bin.rhs, iteration, loop));
  case SCEVExpr::K_SREM:
    return getSRemExpr(evaluateAtIteration(expr->bin.lhs, iteration, loop),
                       evaluateAtIteration(expr->bin.rhs, iteration, loop));
  }
  return expr;
}

SCEVExpr *SCEV::getExitValue(Inst *value, const Loop *loop) const {
  if (!value || !loop)
    return nullptr;
  SCEVExpr *expr = getSCEV(value);
  SCEVExpr *result = expr;
  if (expr->containsAddRecOf(loop)) {
    BasicBlock *entry = uniqueLoopEntryPredecessor(loop);
    BasicBlock *continueBlock = nullptr;
    if (loopGuard(loop, entry, continueBlock))
      return nullptr;
    SCEVExpr *backedges = getBackedgeTakenCount(loop);
    if (!backedges || backedges->kind == SCEVExpr::K_UNKNOWN)
      return nullptr;
    result = evaluateAtIteration(expr, backedges, loop);
  }
  return result && result->isLoopInvariant(loop) ? result : nullptr;
}

void SCEV::build(Function *function, FunctionAnalysisManager &manager) {
  VERIFY(function);
  assert(function->phase == IRPhase::LIR && "SCEV requires LIR");

  cache_.clear();
  btcCache_.clear();
  exprToInst_.clear();
  rangeCache_.clear();
  congruenceCache_.clear();
  noWrapProving_.clear();
  expressions_.clear();

  function_ = function;
  dominatorTree_ = &manager.getResult<DomAnalysis>(function).tree;
  loopInfo_ = &manager.getResult<LoopInfoAnalysis>(function).info;

  // 先处理内层循环, 使外层表达式复用已识别递推且不重新形成 phi 环
  for (Loop *top : loopInfo_->topLevelLoops()) {
    std::vector<Loop *> postorder;
    const auto collect = [&](Loop *loop, const auto &self) -> void {
      for (Loop *child : loop->children())
        self(child, self);
      postorder.push_back(loop);
    };
    collect(top, collect);
    for (Loop *loop : postorder)
      forEachPhi(loop->header(), [&](Inst *phi) { UNUSED(getSCEV(phi)); });
  }
}

} // namespace svm::ir
