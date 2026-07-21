#include "Analysis.h"
#include "LIRPass.h"
#include "Matcher.h"
#include "ValueFacts.h"

#include <cassert>
#include <limits>
#include <optional>
#include <unordered_map>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

using namespace PatternMatch;

bool isScalarExpression(OpCode op) noexcept {
  return (op >= OP_ADD && op <= OP_NEG) || (op >= OP_FADD && op <= OP_FNEG) ||
         op == OP_LNOT || isConversion(op) || op == OP_SELECT;
}

void eraseDeadScalarChain(std::vector<Inst *> dead) {
  while (!dead.empty()) {
    Inst *inst = dead.back();
    dead.pop_back();
    if (!inst || inst->isErased() || !inst->parentBlock() || inst->hasUses() ||
        !isScalarExpression(inst->getOp()))
      continue;
    for (u32 index = 0; index < inst->getOperandCount(); ++index)
      dead.push_back(inst->getArg(index));
    VERIFY(inst->eraseFromBlock(), "dead scalar must be erasable");
  }
}

class CombineContext {
public:
  CombineContext(Function *function, PassContext &passContext,
                 bool fastMath) noexcept
      : function_(function), passContext_(passContext),
        builder_(function->module, function), fastMath_(fastMath) {}

  IRBuilder &builder() noexcept { return builder_; }
  bool fastMath() const noexcept { return fastMath_; }

  ValueFactOracle &factOracle() {
    if (factOracle_ && !factsStale_)
      return *factOracle_;
    if (factsStale_) {
      PreservedAnalyses preserved;
      preserved.preserveCFGAnalyses();
      preserved.preserveSSAForm();
      preserved.preserveAllModuleAnalyses();
      passContext_.invalidate(function_, preserved);
      factsStale_ = false;
    }
    const DominatorTree &dominators =
        passContext_.get<DomAnalysis>(function_).tree;
    const SCEV &scev = passContext_.get<SCEVAnalysis>(function_).info;
    factOracle_.emplace(&scev, &dominators);
    return *factOracle_;
  }

  bool replace(Inst *victim, Inst *replacement) {
    std::vector<Inst *> oldOperands = operandsOf(victim);
    const bool replaced = builder_.replace(victim, replacement) ||
                          replaceWithLoopPhi(victim, replacement);
    VERIFY(replaced, "combine replacement failed");
    eraseDeadScalarChain(std::move(oldOperands));
    markFactsStale();
    return true;
  }

  bool replaceWithConst(Inst *victim, i32 value) {
    std::vector<Inst *> oldOperands = operandsOf(victim);
    VERIFY(builder_.replaceWithConst(victim, value),
           "integer combine replacement failed");
    eraseDeadScalarChain(std::move(oldOperands));
    markFactsStale();
    return true;
  }

  bool replaceWithConst(Inst *victim, f32 value) {
    std::vector<Inst *> oldOperands = operandsOf(victim);
    VERIFY(builder_.replaceWithConst(victim, value),
           "floating combine replacement failed");
    eraseDeadScalarChain(std::move(oldOperands));
    markFactsStale();
    return true;
  }

  Inst *rewrite(Inst *victim, OpCode op, IRType type, Inst *arg) {
    std::vector<Inst *> oldOperands = operandsOf(victim);
    Inst *result = builder_.replaceInPlace(victim, op, type, arg);
    eraseDeadScalarChain(std::move(oldOperands));
    markFactsStale();
    return result;
  }

  Inst *rewrite(Inst *victim, OpCode op, IRType type, Inst *left, Inst *right) {
    std::vector<Inst *> oldOperands = operandsOf(victim);
    Inst *result = builder_.replaceInPlace(victim, op, type, left, right);
    eraseDeadScalarChain(std::move(oldOperands));
    markFactsStale();
    return result;
  }

private:
  // 只允许把回边恒等更新折叠成支配该回边的自引用Phi
  bool replaceWithLoopPhi(Inst *victim, Inst *replacement) {
    if (!victim || !replacement || replacement->getOp() != OP_PHI ||
        victim->getType() != replacement->getType() ||
        !function_->ownsValue(victim) || !function_->ownsValue(replacement) ||
        !victim->parentBlock() || !replacement->parentBlock())
      return false;

    const DominatorTree &dominators =
        passContext_.get<DomAnalysis>(function_).tree;
    bool hasSelfIncoming = false;
    for (u32 index = 0; index < replacement->getOperandCount(); ++index) {
      if (replacement->getArg(index) != victim)
        continue;
      BasicBlock *predecessor = replacement->getIncomingBlock(index);
      if (!predecessor ||
          !dominators.dominates(replacement->parentBlock(), predecessor))
        return false;
      hasSelfIncoming = true;
    }
    if (!hasSelfIncoming)
      return false;

    replaceAllUsesWith(function_, victim, replacement);
    return victim->eraseFromBlock();
  }

  static std::vector<Inst *> operandsOf(Inst *inst) {
    std::vector<Inst *> operands;
    operands.reserve(inst->getOperandCount());
    for (u32 index = 0; index < inst->getOperandCount(); ++index)
      operands.push_back(inst->getArg(index));
    return operands;
  }

  // 标记值图相关分析需要延迟重建
  void markFactsStale() noexcept {
    factOracle_.reset();
    factsStale_ = true;
  }

  Function *function_ = nullptr;
  PassContext &passContext_;
  IRBuilder builder_;
  bool fastMath_ = false;
  std::optional<ValueFactOracle> factOracle_;
  bool factsStale_ = false; // 是否发生过尚未同步到分析缓存的改写
};

#define IC_REWRITE(pattern, body)                                              \
  do {                                                                         \
    if (PatternMatch::match(inst, pattern)) {                                  \
      body;                                                                    \
      return true;                                                             \
    }                                                                          \
  } while (false)

void replaceWithFactored(CombineContext &context, Inst *victim, Inst *factor,
                         OpCode innerOp, Inst *left, Inst *right) {
  IRBuilder &builder = context.builder();
  builder.setInsertBefore(victim);
  Inst *inner = builder.emit(innerOp, TY_I32, left, right);
  context.replace(victim, builder.emit(OP_MUL, TY_I32, factor, inner));
}

void replaceWithFactoredImm(CombineContext &context, Inst *victim, Inst *factor,
                            OpCode innerOp, Inst *value, i32 immediate) {
  IRBuilder &builder = context.builder();
  builder.setInsertBefore(victim);
  Inst *inner = builder.emit(innerOp, TY_I32, value, builder.iConst(immediate));
  context.replace(victim, builder.emit(OP_MUL, TY_I32, factor, inner));
}

void rewriteMulNegConst(CombineContext &context, Inst *inst, Inst *value,
                        i32 constant) {
  context.rewrite(inst, OP_MUL, TY_I32, value,
                  context.builder().iConst(i32NegWrap(constant)));
}

bool foldAdd(CombineContext &context, Inst *inst) {
  Capture<Inst> x;
  Capture<Inst> y;
  Capture<Inst> left;
  Capture<Inst> right;

  IC_REWRITE(m_c_Add(m_Value(x), m_Zero()), context.replace(inst, x.get()));
  IC_REWRITE(m_c_Add(m_Value(x), m_NegLike(m_Same(x))),
             context.replaceWithConst(inst, 0));
  IC_REWRITE(m_c_Add(m_Value(x), m_Sub(m_Value(y), m_Same(x))),
             context.replace(inst, y.get()));
  IC_REWRITE(m_c_Add(m_Sub(m_Value(x), m_Value(y)), m_Same(y)),
             context.replace(inst, x.get()));
  IC_REWRITE(
      m_c_Add(m_Sub(m_Value(x), m_Value(y)), m_Sub(m_Same(y), m_Same(x))),
      context.replaceWithConst(inst, 0));
  IC_REWRITE(m_c_Add(m_Value(x), m_NegLike(m_Value(y))),
             context.rewrite(inst, OP_SUB, TY_I32, x.get(), y.get()));
  IC_REWRITE(m_FactorPairMul<OP_ADD>(x, left, right),
             replaceWithFactored(context, inst, x.get(), OP_ADD, left.get(),
                                 right.get()));
  IC_REWRITE(
      m_c_Add(m_Value(x), m_OneUse(m_c_Mul(m_Same(x), m_Value(left)))),
      replaceWithFactoredImm(context, inst, x.get(), OP_ADD, left.get(), 1));
  return false;
}

bool foldRemainderCanonical(CombineContext &context, Inst *inst) {
  Capture<Inst> value;
  i32 divisor = 0;
  i32 multiplier = 0;
  if (!match(inst, m_Sub(m_Value(value),
                         m_c_Mul(m_Div(m_Same(value), m_NonZeroConst(divisor)),
                                 m_NonZeroConst(multiplier)))) ||
      divisor != multiplier)
    return false;
  context.rewrite(inst, OP_MOD, TY_I32, value.get(),
                  context.builder().iConst(divisor));
  return true;
}

bool foldSub(CombineContext &context, Inst *inst) {
  Capture<Inst> x;
  Capture<Inst> y;
  Capture<Inst> left;
  Capture<Inst> right;

  IC_REWRITE(m_Sub(m_Zero(), m_Sub(m_Value(x), m_Value(y))),
             context.rewrite(inst, OP_SUB, TY_I32, y.get(), x.get()));
  IC_REWRITE(m_Sub(m_Value(x), m_Zero()), context.replace(inst, x.get()));
  IC_REWRITE(m_Sub(m_Value(x), m_Same(x)), context.replaceWithConst(inst, 0));
  IC_REWRITE(m_Sub(m_Zero(), m_Value(x)),
             context.rewrite(inst, OP_NEG, TY_I32, x.get()));
  IC_REWRITE(m_Sub(m_Value(x), m_NegLike(m_Value(y))),
             context.rewrite(inst, OP_ADD, TY_I32, x.get(), y.get()));
  IC_REWRITE(m_Sub(m_c_Add(m_Value(x), m_Value(y)), m_Same(x)),
             context.replace(inst, y.get()));
  IC_REWRITE(m_Sub(m_c_Add(m_Value(x), m_Value(y)), m_Same(y)),
             context.replace(inst, x.get()));
  IC_REWRITE(m_Sub(m_Value(x), m_c_Add(m_Same(x), m_Value(y))),
             context.rewrite(inst, OP_NEG, TY_I32, y.get()));
  IC_REWRITE(m_Sub(m_Sub(m_Value(x), m_Value(y)), m_Same(x)),
             context.rewrite(inst, OP_NEG, TY_I32, y.get()));
  IC_REWRITE(m_Sub(m_Value(x), m_Sub(m_Same(x), m_Value(y))),
             context.replace(inst, y.get()));
  IC_REWRITE(m_Sub(m_NegLike(m_Value(x)), m_NegLike(m_Value(y))),
             context.rewrite(inst, OP_SUB, TY_I32, y.get(), x.get()));

  if (foldRemainderCanonical(context, inst))
    return true;

  IC_REWRITE(m_FactorPairMul<OP_SUB>(x, left, right),
             replaceWithFactored(context, inst, x.get(), OP_SUB, left.get(),
                                 right.get()));
  return false;
}

bool foldNeg(CombineContext &context, Inst *inst) {
  Capture<Inst> x;
  Capture<Inst> y;
  i32 constant = 0;

  IC_REWRITE(m_Neg(m_NegLike(m_Value(x))), context.replace(inst, x.get()));
  IC_REWRITE(m_Neg(m_Sub(m_Value(x), m_Value(y))),
             context.rewrite(inst, OP_SUB, TY_I32, y.get(), x.get()));
  IC_REWRITE(m_Neg(m_OneUse(m_c_Mul(m_Value(x), m_Imm(constant)))),
             rewriteMulNegConst(context, inst, x.get(), constant));
  return false;
}

bool foldMul(CombineContext &context, Inst *inst) {
  Capture<Inst> x;
  Capture<Inst> y;
  i32 constant = 0;

  IC_REWRITE(m_c_Mul(m_Value(x), m_Zero()), context.replaceWithConst(inst, 0));
  IC_REWRITE(m_c_Mul(m_Value(x), m_One()), context.replace(inst, x.get()));
  IC_REWRITE(m_c_Mul(m_Value(x), m_MinusOne()),
             context.rewrite(inst, OP_NEG, TY_I32, x.get()));
  IC_REWRITE(m_c_Mul(m_NegLike(m_Value(x)), m_NegLike(m_Value(y))),
             context.rewrite(inst, OP_MUL, TY_I32, x.get(), y.get()));
  IC_REWRITE(m_c_Mul(m_OneUse(m_NegLike(m_Value(x))), m_Imm(constant)),
             rewriteMulNegConst(context, inst, x.get(), constant));
  return false;
}

bool foldDivMod(CombineContext &context, Inst *inst) {
  Capture<Inst> x;

  IC_REWRITE(m_Div(m_Value(x), m_One()), context.replace(inst, x.get()));
  // 零除数的动态执行在LIR中未定义 所有有定义执行均满足除数非零
  IC_REWRITE(m_Div(m_Zero(), m_Any()), context.replaceWithConst(inst, 0));
  IC_REWRITE(m_Mod(m_Value(x), m_One()), context.replaceWithConst(inst, 0));
  IC_REWRITE(m_Mod(m_Zero(), m_Any()), context.replaceWithConst(inst, 0));
  return false;
}

bool foldNot(CombineContext &context, Inst *inst) {
  Capture<Inst> x;
  IC_REWRITE(m_Not(m_Not(m_Type(TY_I1, m_Value(x)))),
             context.replace(inst, x.get()));

  Inst *argument = inst->getArg(0);
  if (!argument->hasOneUse() || !isIntCompare(argument->getOp()))
    return false;
  context.rewrite(inst, invertIntCompare(argument->getOp()), TY_I1,
                  argument->getArg(0), argument->getArg(1));
  return true;
}

bool foldZExtBoolCompare(CombineContext &context, Inst *inst, OpCode op) {
  Inst *left = inst->getArg(0);
  Inst *right = inst->getArg(1);
  Inst *zext = nullptr;
  i32 constant = 0;
  if (left->getOp() == OP_ZEXT && right->getOp() == OP_ICONST) {
    zext = left;
    constant = right->getImm();
  } else if (right->getOp() == OP_ZEXT && left->getOp() == OP_ICONST) {
    zext = right;
    constant = left->getImm();
  }
  if (!zext || (constant != 0 && constant != 1))
    return false;

  Inst *condition = zext->getArg(0);
  if (condition->getType() != TY_I1)
    return false;
  const bool direct = (op == OP_NE) == (constant == 0);
  if (direct)
    return context.replace(inst, condition);

  context.rewrite(inst, OP_LNOT, TY_I1, condition);
  return true;
}

bool matchConstMinusValue(Inst *expression, Inst *value,
                          i32 &constant) noexcept {
  if (!expression || !value || expression->getType() != TY_I32 ||
      value->getType() != TY_I32)
    return false;
  Capture<Inst> same;
  same.value_ = value;
  same.bound_ = true;
  return match(expression, m_Sub(m_Imm(constant), m_Same(same))) ||
         match(expression, m_c_Add(m_NegLike(m_Same(same)), m_Imm(constant)));
}

enum class NonNegativeState : u8 {
  Visiting,  // 当前递归路径正在证明该值
  Disproven, // 语法结构不足以证明非负
  Proven,    // 已证明所有可能结果均非负
};

using NonNegativeMemo = std::unordered_map<Inst *, NonNegativeState>;

bool isSyntacticallyNonNegative(Inst *value, NonNegativeMemo &memo) {
  if (!value || value->getType() != TY_I32)
    return false;
  const auto [position, inserted] =
      memo.emplace(value, NonNegativeState::Visiting);
  if (!inserted)
    return position->second == NonNegativeState::Proven;

  bool result = false;
  switch (value->getOp()) {
  case OP_ICONST:
    result = value->getImm() >= 0;
    break;
  case OP_ZEXT:
    result = true;
    break;
  case OP_SELECT:
    result = isSyntacticallyNonNegative(value->getArg(1), memo) &&
             isSyntacticallyNonNegative(value->getArg(2), memo);
    break;
  case OP_DIV:
  case OP_MOD:
    result = value->getArg(1)->getOp() == OP_ICONST &&
             value->getArg(1)->getImm() > 0 &&
             isSyntacticallyNonNegative(value->getArg(0), memo);
    break;
  default:
    break;
  }
  memo.find(value)->second =
      result ? NonNegativeState::Proven : NonNegativeState::Disproven;
  return result;
}

bool knownNonNegative(CombineContext &context, Inst *value,
                      BasicBlock *contextBlock) {
  NonNegativeMemo memo;
  if (isSyntacticallyNonNegative(value, memo))
    return true;

  if (!value || value->getType() != TY_I32 || !contextBlock)
    return false;
  ValueFactQuery query;
  query.contextBlock = contextBlock;
  const auto lower = context.factOracle().getI32Range(value, query).signedMin();
  return lower && *lower >= 0;
}

bool foldReflectedSubCompare(CombineContext &context, Inst *inst) {
  OpCode predicate = inst->getOp();
  if (predicate != OP_LT && predicate != OP_LE && predicate != OP_GT &&
      predicate != OP_GE)
    return false;

  Inst *left = inst->getArg(0);
  Inst *right = inst->getArg(1);
  Inst *value = nullptr;
  i32 constant = 0;
  if (matchConstMinusValue(right, left, constant)) {
    value = left;
  } else if (matchConstMinusValue(left, right, constant)) {
    value = right;
    predicate = swapCompareOperands(predicate);
  } else {
    return false;
  }
  if (constant < 0)
    return false;

  const bool nonNegative =
      knownNonNegative(context, value, inst->parentBlock());
  if (!nonNegative && constant == std::numeric_limits<i32>::max()) {
    IRBuilder &builder = context.builder();
    builder.setInsertBefore(inst);
    Inst *doubled = builder.emit(OP_ADD, TY_I32, value, value);
    const OpCode exact =
        (predicate == OP_LT || predicate == OP_LE) ? OP_GE : OP_LT;
    context.rewrite(inst, exact, TY_I1, doubled, builder.iConst(0));
    return true;
  }
  if (!nonNegative)
    return false;

  const i32 ceilHalf = static_cast<i32>((static_cast<i64>(constant) + 1) / 2);
  const i32 floorHalf = static_cast<i32>(static_cast<i64>(constant) / 2);
  const i32 threshold =
      (predicate == OP_LT || predicate == OP_GE) ? ceilHalf : floorHalf;
  context.rewrite(inst, predicate, TY_I1, value,
                  context.builder().iConst(threshold));
  return true;
}

struct OffsetExpression {
  Inst *base = nullptr; // 去除单层常量偏移后的基值
  i32 offset = 0;       // 基值上的i32回绕偏移
  bool split = false;   // 是否消费了单Use偏移表达式
};

OffsetExpression splitOffset(Inst *expression) noexcept {
  OffsetExpression result{expression, 0, false};
  if (!expression || !expression->hasOneUse() ||
      expression->getOperandCount() != 2)
    return result;
  if (expression->getOp() == OP_ADD) {
    if (expression->getArg(1)->getOp() == OP_ICONST)
      return {expression->getArg(0), expression->getArg(1)->getImm(), true};
    if (expression->getArg(0)->getOp() == OP_ICONST)
      return {expression->getArg(1), expression->getArg(0)->getImm(), true};
  }
  if (expression->getOp() == OP_SUB &&
      expression->getArg(1)->getOp() == OP_ICONST)
    return {expression->getArg(0), i32NegWrap(expression->getArg(1)->getImm()),
            true};
  return result;
}

bool matchesOffset(Inst *expression, Inst *base, i32 offset) noexcept {
  if (base->getOp() == OP_ICONST)
    return expression->getOp() == OP_ICONST &&
           expression->getImm() == i32AddWrap(base->getImm(), offset);
  if (offset == 0)
    return expression == base;
  return expression->getOp() == OP_ADD && expression->getOperandCount() == 2 &&
         expression->getArg(0) == base &&
         expression->getArg(1)->getOp() == OP_ICONST &&
         expression->getArg(1)->getImm() == offset;
}

bool foldEqNeOffset(CombineContext &context, Inst *inst, OpCode predicate) {
  OffsetExpression left = splitOffset(inst->getArg(0));
  OffsetExpression right = splitOffset(inst->getArg(1));
  if (!left.split && !right.split)
    return false;

  // 赋予常量最高排序权重 迫使其交换到右侧以吸收偏移量
  auto rank = [](Inst *base) -> u32 {
    return base->getOp() == OP_ICONST ? ~0u : base->id;
  };
  if (rank(right.base) < rank(left.base))
    std::swap(left, right);
  const i32 offset = i32SubWrap(right.offset, left.offset);
  if (left.base == right.base)
    return context.replaceWithConst(
        inst, (predicate == OP_EQ) == (offset == 0) ? 1 : 0);
  if (inst->getArg(0) == left.base &&
      matchesOffset(inst->getArg(1), right.base, offset))
    return false;

  IRBuilder &builder = context.builder();
  builder.setInsertBefore(inst);
  Inst *adjusted = right.base;
  if (right.base->getOp() == OP_ICONST)
    adjusted = builder.iConst(i32AddWrap(right.base->getImm(), offset));
  else if (offset != 0)
    adjusted = builder.emit(OP_ADD, TY_I32, right.base, builder.iConst(offset));
  context.rewrite(inst, predicate, TY_I1, left.base, adjusted);
  return true;
}

bool foldCompare(CombineContext &context, Inst *inst) {
  Capture<Inst> x;
  i32 constant = 0;
  const OpCode op = inst->getOp();
  const bool floatCompare = isFloatCompare(op);

  if ((op == OP_EQ || op == OP_NE) && foldZExtBoolCompare(context, inst, op))
    return true;

  if (inst->getArg(0) == inst->getArg(1)) {
    if (floatCompare && !context.fastMath())
      return false;
    const bool result = op == OP_EQ || op == OP_LE || op == OP_GE ||
                        op == OP_FEQ || op == OP_FLE || op == OP_FGE;
    return context.replaceWithConst(inst, result ? 1 : 0);
  }
  if (floatCompare)
    return false;

  if (match(inst, m_c_Eq(m_c_Add(m_Value(x), m_Imm(constant)), m_Same(x))) ||
      match(inst, m_c_NE(m_c_Add(m_Value(x), m_Imm(constant)), m_Same(x)))) {
    const bool result = op == OP_EQ ? constant == 0 : constant != 0;
    return context.replaceWithConst(inst, result ? 1 : 0);
  }

  if (foldReflectedSubCompare(context, inst))
    return true;
  if ((op == OP_EQ || op == OP_NE) && foldEqNeOffset(context, inst, op))
    return true;

  if (inst->getArg(0)->getOp() == OP_ICONST &&
      inst->getArg(1)->getOp() != OP_ICONST) {
    Inst *left = inst->getArg(0);
    Inst *right = inst->getArg(1);
    context.rewrite(inst, swapCompareOperands(op), TY_I1, right, left);
    return true;
  }
  return false;
}

bool foldPhi(CombineContext &context, Inst *phi) {
  const u32 count = phi->getOperandCount();
  if (count <= 1)
    return false;
  Inst *value = phi->getArg(0);
  if (value == phi)
    return false;
  for (u32 index = 1; index < count; ++index)
    if (phi->getArg(index) != value)
      return false;
  return context.replace(phi, value);
}

bool isIntConstant(Inst *value, i32 expected) noexcept {
  return value && value->getOp() == OP_ICONST && value->getImm() == expected;
}

bool foldSelect(CombineContext &context, Inst *inst) {
  Inst *condition = inst->getArg(0);
  Inst *trueValue = inst->getArg(1);
  Inst *falseValue = inst->getArg(2);
  const IRType type = inst->getType();

  if (condition->getOp() == OP_ICONST)
    return context.replace(inst,
                           condition->getImm() != 0 ? trueValue : falseValue);
  if (trueValue == falseValue)
    return context.replace(inst, trueValue);

  IRBuilder &builder = context.builder();
  if (trueValue->getOp() == OP_SELECT && trueValue->getArg(0) == condition) {
    builder.setInsertBefore(inst);
    Inst *args[] = {condition, trueValue->getArg(1), falseValue};
    return context.replace(inst, builder.emitN(OP_SELECT, type, args, 3));
  }
  if (falseValue->getOp() == OP_SELECT && falseValue->getArg(0) == condition) {
    builder.setInsertBefore(inst);
    Inst *args[] = {condition, trueValue, falseValue->getArg(2)};
    return context.replace(inst, builder.emitN(OP_SELECT, type, args, 3));
  }

  if (type == TY_I1) {
    if (isIntConstant(trueValue, 1) && isIntConstant(falseValue, 0))
      return context.replace(inst, condition);
    if (isIntConstant(trueValue, 0) && isIntConstant(falseValue, 1))
      return context.rewrite(inst, OP_LNOT, TY_I1, condition) != nullptr;
  }
  if (type == TY_I32) {
    if (isIntConstant(trueValue, 1) && isIntConstant(falseValue, 0))
      return context.rewrite(inst, OP_ZEXT, TY_I32, condition) != nullptr;
    if (isIntConstant(trueValue, 0) && isIntConstant(falseValue, 1)) {
      builder.setInsertBefore(inst);
      Inst *negated = builder.emit(OP_LNOT, TY_I1, condition);
      return context.rewrite(inst, OP_ZEXT, TY_I32, negated) != nullptr;
    }
  }

  builder.setInsertBefore(inst);
  auto buildAccumulation = [&](OpCode op, Inst *base, Inst *ifTrue,
                               Inst *ifFalse) {
    Inst *args[] = {condition, ifTrue, ifFalse};
    Inst *delta = builder.emitN(OP_SELECT, TY_I32, args, 3);
    context.replace(inst, builder.emit(op, TY_I32, base, delta));
  };
  if (trueValue->getOp() == OP_ADD && trueValue->hasOneUse()) {
    if (trueValue->getArg(0) == falseValue) {
      buildAccumulation(OP_ADD, falseValue, trueValue->getArg(1),
                        builder.iConst(0));
      return true;
    }
    if (trueValue->getArg(1) == falseValue) {
      buildAccumulation(OP_ADD, falseValue, trueValue->getArg(0),
                        builder.iConst(0));
      return true;
    }
  }
  if (falseValue->getOp() == OP_ADD && falseValue->hasOneUse()) {
    if (falseValue->getArg(0) == trueValue) {
      buildAccumulation(OP_ADD, trueValue, builder.iConst(0),
                        falseValue->getArg(1));
      return true;
    }
    if (falseValue->getArg(1) == trueValue) {
      buildAccumulation(OP_ADD, trueValue, builder.iConst(0),
                        falseValue->getArg(0));
      return true;
    }
  }
  if (trueValue->getOp() == OP_SUB && trueValue->hasOneUse() &&
      trueValue->getArg(0) == falseValue) {
    buildAccumulation(OP_SUB, falseValue, trueValue->getArg(1),
                      builder.iConst(0));
    return true;
  }
  return false;
}

bool foldFloat(CombineContext &context, Inst *inst) {
  Capture<Inst> x;
  Capture<Inst> y;

  IC_REWRITE(m_FNeg(m_FNeg(m_Value(x))), context.replace(inst, x.get()));
  IC_REWRITE(m_FDiv(m_Value(x), m_SpecificFloat(2.0F)),
             context.rewrite(inst, OP_FMUL, TY_F32, x.get(),
                             context.builder().fConst(0.5F)));

  if (!context.fastMath())
    return false;

  IC_REWRITE(m_c_FAdd(m_OneUse(m_FSub(m_Value(x), m_Value(y))), m_Same(y)),
             context.replace(inst, x.get()));
  IC_REWRITE(m_FSub(m_OneUse(m_c_FAdd(m_Value(x), m_Value(y))), m_Same(y)),
             context.replace(inst, x.get()));
  IC_REWRITE(m_FSub(m_OneUse(m_c_FAdd(m_Value(x), m_Value(y))), m_Same(x)),
             context.replace(inst, y.get()));
  IC_REWRITE(m_c_FAdd(m_Value(x), m_FZero()), context.replace(inst, x.get()));
  IC_REWRITE(m_FSub(m_Value(x), m_FZero()), context.replace(inst, x.get()));
  IC_REWRITE(m_c_FMul(m_Value(x), m_FOne()), context.replace(inst, x.get()));
  IC_REWRITE(m_c_FMul(m_Value(x), m_FZero()),
             context.replaceWithConst(inst, 0.0F));
  IC_REWRITE(m_c_FMul(m_Value(x), m_SpecificFloat(2.0F)),
             context.rewrite(inst, OP_FADD, TY_F32, x.get(), x.get()));
  IC_REWRITE(m_FDiv(m_Value(x), m_FOne()), context.replace(inst, x.get()));
  IC_REWRITE(m_FDiv(m_Value(x), m_SpecificFloat(-1.0F)),
             context.rewrite(inst, OP_FNEG, TY_F32, x.get()));
  return false;
}

bool tryFold(CombineContext &context, Inst *inst) {
  switch (inst->getOp()) {
  case OP_ADD:
    return foldAdd(context, inst);
  case OP_SUB:
    return foldSub(context, inst);
  case OP_NEG:
    return foldNeg(context, inst);
  case OP_MUL:
    return foldMul(context, inst);
  case OP_DIV:
  case OP_MOD:
    return foldDivMod(context, inst);
  case OP_LNOT:
    return foldNot(context, inst);
  case OP_SELECT:
    return foldSelect(context, inst);
  case OP_EQ:
  case OP_NE:
  case OP_LT:
  case OP_LE:
  case OP_GT:
  case OP_GE:
  case OP_FEQ:
  case OP_FNE:
  case OP_FLT:
  case OP_FLE:
  case OP_FGT:
  case OP_FGE:
    return foldCompare(context, inst);
  case OP_FADD:
  case OP_FSUB:
  case OP_FMUL:
  case OP_FDIV:
  case OP_FNEG:
    return foldFloat(context, inst);
  default:
    return false;
  }
}

bool instCombine(Function *function, PassContext &passContext, bool fastMath) {
  assert(function && function->phase == IRPhase::LIR);
  computeUses(function);
  CombineContext context(function, passContext, fastMath);
  bool changed = false;
  constexpr u32 MaxRounds = 4;

  for (u32 round = 0; round < MaxRounds; ++round) {
    bool roundChanged = false;
    for (BasicBlock *block = function->region->first; block;
         block = block->next()) {
      for (Inst *phi = block->firstPhi(); phi;) {
        Inst *next = phi->next();
        roundChanged |= foldPhi(context, phi);
        phi = next;
      }
      for (Inst *inst = block->firstInst(); inst;) {
        Inst *next = inst->next();
        roundChanged |= tryFold(context, inst);
        inst = next;
      }
    }
    changed |= roundChanged;
    if (!roundChanged)
      break;
  }
  return changed;
}

#undef IC_REWRITE

} // namespace

InstCombinePass::InstCombinePass(bool fastMath) noexcept
    : fastMath_(fastMath) {}

std::string_view InstCombinePass::name() const noexcept {
  return "inst-combine";
}

PassResult InstCombinePass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();
  if (!instCombine(function, context, fastMath_))
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  preserved.preserveAllModuleAnalyses();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
