/// @file ValueFacts.cpp
/// @brief 实现 ValueFactOracle 的环形值域组合, Phi 合流和局部传递规则

#include "ValueFacts.h"
#include "SCEV.h"

#include <limits>
#include <optional>

namespace svm::ir {
namespace {

/// Phi 展开预算, 超过预算时回退到 SCEV 或完整值域
constexpr u32 kPhiExplorationLimit = 16;

bool isIntValue(const Inst *value) noexcept {
  if (!value || value->isErased() || value->isUndefValue())
    return false;
  const IRType type = value->getType();
  return type == TY_I1 || type == TY_I32;
}

std::optional<i32> constOf(const Inst *value) noexcept {
  if (!value || value->isErased() || value->isUndefValue() ||
      value->getOp() != OP_ICONST)
    return std::nullopt;
  return value->getImm();
}

enum class PropState : u8 {
  Top,
  NonNegative,
  Bottom,
};

PropState meetNonNegative(PropState left, PropState right) noexcept {
  if (left == PropState::Bottom || right == PropState::Bottom)
    return PropState::Bottom;
  if (left == PropState::NonNegative || right == PropState::NonNegative)
    return PropState::NonNegative;
  return PropState::Top;
}

class DemandDrivenPropertySolver {
public:
  DemandDrivenPropertySolver(const SCEV *scev,
                             const ValueFactQuery &query) noexcept
      : scev_(scev), query_(query) {}

  bool isNonNegative(Inst *value) {
    return proveNonNegative(value, 0) == PropState::NonNegative;
  }

private:
  const SCEV *scev_ = nullptr;
  const ValueFactQuery &query_;
  std::unordered_map<Inst *, PropState> state_;
  static constexpr u32 kMaxDepth = 64;

  PropState proveNonNegative(Inst *value, u32 depth) {
    if (!value || value->getType() != TY_I32 || depth > kMaxDepth ||
        value->isErased() || value->isUndefValue())
      return PropState::Bottom;

    const auto known = state_.find(value);
    if (known != state_.end())
      return known->second;

    state_.emplace(value, PropState::Top);
    const PropState result = transfer(value, depth);
    state_[value] = result;
    return result;
  }

  /// 应用常量, SCEV, 谓词上下文和有限 SSA 传递规则
  PropState transfer(Inst *value, u32 depth) {
    const OpCode op = value->getOp();
    if (op == OP_ICONST)
      return value->getImm() >= 0 ? PropState::NonNegative : PropState::Bottom;

    // 只消费非递归事实, 避免把环检测兜底产生的 Top 误作完整值域证明
    if (scev_) {
      RangeQuery rangeQuery;
      rangeQuery.contextBlock = query_.contextBlock;
      rangeQuery.predicateContext = query_.predicateContext;
      const I32Range range = scev_->getI32Range(value, rangeQuery);
      const auto bounds = range.signedBounds();
      if (bounds && bounds->min >= 0)
        return PropState::NonNegative;
    }
    if (query_.predicateContext) {
      const auto bounds =
          query_.predicateContext->getRangeFor(value).signedBounds();
      if (bounds && bounds->min >= 0)
        return PropState::NonNegative;
    }

    // Phi 展开和局部表达式传递必须严格服从调用方精度开关,
    // 否则后置非负证明会绕过 ValueFactOracle 主查询的禁用语义
    if (op == OP_PHI) {
      if (!query_.useNonLoopPhi)
        return PropState::Bottom;
      PropState result = PropState::Top;
      for (u32 index = 0; index < value->getOperandCount(); ++index) {
        result = meetNonNegative(
            result, proveNonNegative(value->getArg(index), depth + 1));
        if (result == PropState::Bottom)
          return PropState::Bottom;
      }
      return result;
    }
    if (!query_.useLocalExpr)
      return PropState::Bottom;

    // 普通 i32 ADD/MUL 允许回绕;
    // 仅双常量且宿主数学结果仍在非负 i32 范围时才提交证明
    if (op == OP_ADD || op == OP_MUL) {
      if (value->getOperandCount() != 2)
        return PropState::Bottom;
      const auto left = constOf(value->getArg(0));
      const auto right = constOf(value->getArg(1));
      if (!left || !right)
        return PropState::Bottom;
      const i64 lhs = *left;
      const i64 rhs = *right;
      const i64 result = op == OP_ADD ? lhs + rhs : lhs * rhs;
      return result >= 0 &&
                     result <= static_cast<i64>(std::numeric_limits<i32>::max())
                 ? PropState::NonNegative
                 : PropState::Bottom;
    }

    // 固定正除数的除法保持被除数的非负性
    if (op == OP_DIV) {
      if (value->getOperandCount() != 2)
        return PropState::Bottom;
      Inst *divisor = value->getArg(1);
      if (!divisor || divisor->getOp() != OP_ICONST || divisor->getImm() <= 0)
        return PropState::Bottom;
      return proveNonNegative(value->getArg(0), depth + 1);
    }

    // 余数的符号随被除数; 非零除数路径上该性质成立
    if (op == OP_MOD) {
      if (value->getOperandCount() != 2)
        return PropState::Bottom;
      return proveNonNegative(value->getArg(0), depth + 1);
    }

    return PropState::Bottom;
  }
};

} // namespace

usize ValueFactOracle::MemoKeyHash::operator()(
    const MemoKey &key) const noexcept {
  usize hash = static_cast<usize>(1469598103934665603ULL);
  const auto mix = [&hash](uintptr value) noexcept {
    hash ^= static_cast<usize>(value);
    hash *= static_cast<usize>(1099511628211ULL);
  };
  mix(reinterpret_cast<uintptr>(key.value));
  mix(reinterpret_cast<uintptr>(key.contextBlock));
  mix(static_cast<uintptr>(key.flags));
  return hash;
}

I32Range ValueFactOracle::getI32Range(Inst *value,
                                      const ValueFactQuery &query) {
  if (!isIntValue(value))
    return I32Range::unknown();

  ValueFactQuery actual = query;
  if (actual.contextBlock && !actual.predicateContext)
    actual.predicateContext = &builder_.buildBlockContext(actual.contextBlock);

  std::unordered_set<Inst *> visited;
  QueryMemo queryMemo;
  return rangeImpl(value, actual, visited, queryMemo).range;
}

ValueFactOracle::RangeResult
ValueFactOracle::rangeImpl(Inst *value, const ValueFactQuery &query,
                           std::unordered_set<Inst *> &visited,
                           QueryMemo &queryMemo) {
  if (!isIntValue(value))
    return {I32Range::unknown(), true};

  if (query.predicateContext && query.predicateContext->isUnreachable())
    return {I32Range::empty(), false};

  if (const auto constant = constOf(value)) {
    I32Range range = I32Range::constant(*constant);
    if (query.predicateContext)
      range = range.intersectWith(query.predicateContext->getRangeFor(value));
    return {range, false};
  }

  if (const auto cached = queryMemo.find(value); cached != queryMemo.end())
    return {cached->second, false};

  // 显式 PredicateContext 的语义可能随调用方状态变化, 禁止缓存查找和写入
  const bool cacheable = query.predicateContext == nullptr;
  const u32 queryFlags = (query.useNonLoopPhi ? u32{1} : u32{0}) |
                         (query.useLocalExpr ? u32{2} : u32{0});
  const MemoKey key{value, query.contextBlock, queryFlags};
  if (cacheable) {
    const auto cached = memo_.find(key);
    if (cached != memo_.end())
      return {cached->second, false};
  }

  // 环边不能被忽略, 否则会把递归 Phi 错误收窄
  // 完整值域仅作递归栈占位, 并通过污染标记阻止它进入缓存
  if (visited.count(value) != 0)
    return {I32Range::full(), true};
  visited.insert(value);

  RangeResult result;
  bool expandPhi = value->getOp() == OP_PHI && query.useNonLoopPhi;
  if (expandPhi && scev_) {
    const SCEVExpr *expression = scev_->getSCEV(value);
    // 循环 AddRec Phi 的回边由 SCEV 处理, 再次枚举输入会丢失精确递推值域
    expandPhi = !expression || expression->kind != SCEVExpr::K_ADDREC;
  }
  result = expandPhi ? rangePhi(value, query, visited)
                     : rangeExpr(value, query, visited, queryMemo);
  visited.erase(value);

  // 对 SCEV 无法表达的非线性值, 按需补充一个有严格基例约束的非负证明
  if (value->getType() == TY_I32 && !result.range.isEmpty()) {
    const auto bounds = result.range.signedBounds();
    const bool alreadyNonNegative = bounds && bounds->min >= 0;
    if (!alreadyNonNegative) {
      DemandDrivenPropertySolver solver(scev_, query);
      if (solver.isNonNegative(value))
        result.range = result.range.intersectWith(
            I32Range::fromSigned(0, std::numeric_limits<i32>::max()));
    }
  }

  if (!result.tainted) {
    queryMemo.emplace(value, result.range);
    if (cacheable)
      memo_.emplace(key, result.range);
  }
  return result;
}

ValueFactOracle::RangeResult
ValueFactOracle::rangeExpr(Inst *value, const ValueFactQuery &query,
                           std::unordered_set<Inst *> &visited,
                           QueryMemo &queryMemo) {
  I32Range range = I32Range::unknown();
  bool tainted = false;

  // i1 在 LIR 中只可能是 0 或 1, 即使 SCEV 没有建立该事实也先播种它
  if (value->getType() == TY_I1)
    range = range.intersectWith(I32Range::fromSigned(0, 1));

  if (scev_) {
    RangeQuery rangeQuery;
    rangeQuery.contextBlock = query.contextBlock;
    rangeQuery.predicateContext = query.predicateContext;
    range = range.intersectWith(scev_->getI32Range(value, rangeQuery));
    if (range.isEmpty())
      return {range, tainted};
  }

  if (query.predicateContext) {
    range = range.intersectWith(query.predicateContext->getRangeFor(value));
    if (range.isEmpty())
      return {range, tainted};
  }

  if (!query.useLocalExpr)
    return {range, tainted};

  auto child = [&](u32 index) noexcept -> I32Range {
    if (index >= value->getOperandCount()) {
      tainted = true;
      return I32Range::unknown();
    }
    const RangeResult childResult =
        rangeImpl(value->getArg(index), query, visited, queryMemo);
    tainted = tainted || childResult.tainted;
    return childResult.range;
  };

  I32Range transfer = I32Range::unknown();
  switch (value->getOp()) {
  case OP_ADD:
    transfer = value->getOperandCount() == 2 ? child(0).add(child(1))
                                             : I32Range::full();
    break;
  case OP_SUB:
    transfer = value->getOperandCount() == 2 ? child(0).sub(child(1))
                                             : I32Range::full();
    break;
  case OP_MUL:
    transfer = value->getOperandCount() == 2 ? child(0).multiply(child(1))
                                             : I32Range::full();
    break;
  case OP_NEG:
    transfer =
        value->getOperandCount() == 1 ? child(0).negate() : I32Range::full();
    break;
  case OP_ZEXT:
    transfer = value->getOperandCount() == 1 ? I32Range::fromSigned(0, 1)
                                             : I32Range::full();
    break;
  case OP_DIV:
    if (value->getOperandCount() == 2) {
      transfer = child(0).sdiv(child(1));
      // 不支持或未知的除法只表示无法收窄, 不能解释为路径矛盾
      if (transfer.isUnknown())
        transfer = I32Range::full();
    } else {
      transfer = I32Range::full();
    }
    break;
  case OP_MOD:
    if (value->getOperandCount() == 2) {
      transfer = child(0).srem(child(1));
      if (transfer.isUnknown())
        transfer = I32Range::full();
    } else {
      transfer = I32Range::full();
    }
    break;
  default:
    // 其余操作码没有 LIR 值域传递规则
    break;
  }

  range = range.intersectWith(transfer);
  if (range.isEmpty())
    return {range, tainted};
  return {range, tainted};
}

ValueFactOracle::RangeResult
ValueFactOracle::rangePhi(Inst *phi, const ValueFactQuery &query,
                          std::unordered_set<Inst *> &visited) {
  const u32 incomingCount = phi->getOperandCount();
  BasicBlock *phiBlock = phi->parentBlock();
  bool tainted = false;

  if (incomingCount == 0)
    return {I32Range::unknown(), tainted};

  // 输入值域的并集只描述 Phi 定义本身,
  // 查询点上的路径事实和 SCEV 事实仍需作为合取约束保留
  I32Range phiRange = I32Range::unknown();
  if (scev_) {
    RangeQuery rangeQuery;
    rangeQuery.contextBlock = query.contextBlock;
    rangeQuery.predicateContext = query.predicateContext;
    phiRange = phiRange.intersectWith(scev_->getI32Range(phi, rangeQuery));
  }
  if (query.predicateContext)
    phiRange = phiRange.intersectWith(query.predicateContext->getRangeFor(phi));
  if (phiRange.isEmpty())
    return {phiRange, tainted};

  I32Range result = I32Range::empty();
  u32 budget = kPhiExplorationLimit;
  bool overBudget = false;

  for (u32 index = 0; index < incomingCount; ++index) {
    if (budget == 0) {
      overBudget = true;
      break;
    }
    --budget;

    BasicBlock *pred = phi->getIncomingBlock(index);
    ValueFactQuery incomingQuery = query;
    incomingQuery.contextBlock = pred;
    PredicateContext incomingContext;
    if (query.predicateContext)
      incomingContext.appendFrom(*query.predicateContext);
    if (pred)
      incomingContext.appendFrom(builder_.buildBlockContext(pred));
    if (pred && phiBlock)
      incomingContext = builder_.withEdgeFact(incomingContext, pred, phiBlock);
    incomingQuery.predicateContext = &incomingContext;

    QueryMemo incomingMemo;
    const RangeResult incoming =
        rangeImpl(phi->getArg(index), incomingQuery, visited, incomingMemo);
    tainted = tainted || incoming.tainted;
    result = result.unionHullWith(incoming.range);
    // 未知输入会污染并集, 后续输入无法恢复有效值域
    if (result.isUnknown())
      break;
  }

  if (!overBudget)
    return {result.intersectWith(phiRange), tainted};

  // 部分输入的并集是欠近似
  // 优先使用 SCEV 结果, 否则返回完整值域并标记污染
  tainted = true;
  if (scev_) {
    RangeQuery rangeQuery;
    rangeQuery.contextBlock = query.contextBlock;
    rangeQuery.predicateContext = query.predicateContext;
    const I32Range scevRange = scev_->getI32Range(phi, rangeQuery);
    const I32Range fallback =
        scevRange.isUnknown() ? I32Range::full() : scevRange;
    return {fallback.intersectWith(phiRange), tainted};
  }
  return {I32Range::full().intersectWith(phiRange), tainted};
}

} // namespace svm::ir
