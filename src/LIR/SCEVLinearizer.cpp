#include "SCEVLinearizer.h"
#include "Utils.h"

namespace svm::ir {
namespace {

struct LinearizeState {
  SCEVLinearForm form; // 当前规范化结果
  u32 maxNodes = 0;    // 节点预算
  u32 maxDepth = 0;    // 深度预算
};

void fail(LinearizeState &state, SCEVLinearizeStatus status) noexcept {
  if (state.form.status == SCEVLinearizeStatus::Exact)
    state.form.status = status;
}

bool addConstant(LinearizeState &state, i64 value, i64 scale) noexcept {
  i64 scaled = 0;
  i64 sum = 0;
  if (!checkedMul(value, scale, scaled) ||
      !checkedAdd(state.form.constant, scaled, sum)) {
    fail(state, SCEVLinearizeStatus::ArithmeticOverflow);
    return false;
  }
  state.form.constant = sum;
  return true;
}

bool addTerm(LinearizeState &state, SCEVExpr *atom, i64 coefficient) noexcept {
  if (!atom) {
    fail(state, SCEVLinearizeStatus::InvalidExpression);
    return false;
  }
  if (coefficient == 0)
    return true;
  for (auto iterator = state.form.terms.begin();
       iterator != state.form.terms.end(); ++iterator) {
    if (iterator->atom != atom)
      continue;
    i64 sum = 0;
    if (!checkedAdd(iterator->coefficient, coefficient, sum)) {
      fail(state, SCEVLinearizeStatus::ArithmeticOverflow);
      return false;
    }
    if (sum == 0)
      state.form.terms.erase(iterator);
    else
      iterator->coefficient = sum;
    return true;
  }
  state.form.terms.push_back({atom, coefficient});
  return true;
}

bool linearizeExpression(SCEVExpr *expression, i64 scale, u32 depth,
                         LinearizeState &state, bool countNode = true) {
  if (!expression) {
    fail(state, SCEVLinearizeStatus::InvalidExpression);
    return false;
  }
  if (depth > state.maxDepth ||
      (countNode && state.form.nodesVisited >= state.maxNodes)) {
    fail(state, SCEVLinearizeStatus::BudgetExceeded);
    return false;
  }
  state.form.nodesVisited += countNode ? 1U : 0U;

  switch (expression->kind) {
  case SCEVExpr::K_CONSTANT:
    return addConstant(state, expression->cst.v, scale);
  case SCEVExpr::K_ADD:
    for (SCEVExpr *operand : expression->nary.ops)
      if (!linearizeExpression(operand, scale, depth + 1, state))
        return false;
    return true;
  case SCEVExpr::K_MUL: {
    if (expression->nary.ops.size() >
        static_cast<usize>(state.maxNodes - state.form.nodesVisited)) {
      fail(state, SCEVLinearizeStatus::BudgetExceeded);
      return false;
    }
    state.form.nodesVisited += static_cast<u32>(expression->nary.ops.size());
    SCEVExpr *variable = nullptr;
    u32 variableCount = 0;
    for (SCEVExpr *operand : expression->nary.ops) {
      if (!operand) {
        fail(state, SCEVLinearizeStatus::InvalidExpression);
        return false;
      }
      if (!operand->isConstant()) {
        variable = operand;
        ++variableCount;
      }
    }
    if (variableCount > 1)
      return addTerm(state, expression, scale);

    i64 combinedScale = scale;
    for (SCEVExpr *operand : expression->nary.ops) {
      if (!operand->isConstant())
        continue;
      if (!checkedMul(combinedScale, operand->cst.v, combinedScale)) {
        fail(state, SCEVLinearizeStatus::ArithmeticOverflow);
        return false;
      }
    }
    if (!variable)
      return addConstant(state, 1, combinedScale);
    return linearizeExpression(variable, combinedScale, depth + 1, state,
                               false);
  }
  case SCEVExpr::K_UNKNOWN:
  case SCEVExpr::K_ADDREC:
  case SCEVExpr::K_SDIV:
  case SCEVExpr::K_SREM:
    return addTerm(state, expression, scale);
  }
  fail(state, SCEVLinearizeStatus::InvalidExpression);
  return false;
}

} // namespace

SCEVLinearizer::SCEVLinearizer(u32 maxNodes, u32 maxDepth) noexcept
    : maxNodes_(maxNodes), maxDepth_(maxDepth) {}

SCEVLinearForm SCEVLinearizer::linearize(SCEVExpr *expression,
                                         i64 scale) const {
  LinearizeState state;
  state.maxNodes = maxNodes_;
  state.maxDepth = maxDepth_;
  state.form.status = SCEVLinearizeStatus::Exact;
  (void)linearizeExpression(expression, scale, 0, state);
  return state.form;
}

} // namespace svm::ir
