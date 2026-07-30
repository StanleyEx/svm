/// @file SCEVFacts.cpp
/// @brief 实现 SCEV 的值域, 同余, 无回绕证明和谓词判定
///
/// 普通值域严格按 i32 回绕语义计算, 数学边界仅在整条表达式已证明无回绕时返回
/// 同余先在数学整数域组合, 再由顶层查询按语义域裁剪
/// 未证明无回绕时只保留 2^k 模数事实, 这些事实在模 2^32 回绕下仍然成立
/// PredicateContext 只提供路径事实, 本文件不负责采集控制流条件

#include "SCEV.h"
#include "Utils.h"

#include <algorithm>
#include <limits>
#include <numeric>

namespace svm {
namespace ir {

// i32 值域直接在回绕集合域计算
namespace {

constexpr u64 kI32Modulus = u64{1} << 32;          // i32 回绕模数
constexpr u64 kMaxSupportedModulus = u64{1} << 63; // 与 Congruence 上限一致

MathBounds internalMathBounds(i64 min, i64 max) noexcept {
  return min <= max ? MathBounds{true, min, max, NoWrapInfo{}}
                    : MathBounds::none();
}

/// @brief 按表达式类型给出未收窄的 i32 值域兜底
I32Range widenForTy(IRType ty) {
  if (ty == TY_I32)
    return I32Range::full();
  if (ty == TY_I1)
    return I32Range::fromSigned(0, 1);
  return I32Range::unknown();
}

/// @brief 把 MathQuery 的上下文转换为叶子值域查询, 不改变数学语义策略
RangeQuery toRangeQuery(const MathQuery &q) {
  RangeQuery rq;
  rq.contextBlock = q.contextBlock;
  rq.predicateContext = q.predicateContext;
  rq.maxDepth = q.maxDepth;
  return rq;
}

/// @brief 为 i32 叶子构造数学端点外壳, 跨符号边界时保守扩为完整 i32 域
MathBounds mathHullForLeaf(const I32Range &r, IRType ty) {
  if (r.isEmpty())
    return MathBounds::none();
  if (auto b = r.signedBounds())
    return internalMathBounds(b->min, b->max);
  if (ty == TY_I32)
    return internalMathBounds(INT32_MIN, INT32_MAX);
  if (ty == TY_I1)
    return internalMathBounds(0, 1);
  return MathBounds::none();
}

/// @brief 构造有符号余数的数学端点外壳, 除零或溢出风险会令证明失败
MathBounds remMathBounds(const MathBounds &a, const MathBounds &b) {
  if (!a.valid || !b.valid)
    return MathBounds::none();
  if (!(b.min > 0 || b.max < 0))
    return MathBounds::none();
  if (a.min <= INT32_MIN && a.max >= INT32_MIN && b.min <= -1 && b.max >= -1)
    return MathBounds::none();

  auto iabs = [](i64 x) -> i64 { return x < 0 ? -x : x; };
  i64 B = std::max(iabs(b.min), iabs(b.max));
  if (B <= 0)
    return MathBounds::none();
  i64 bound = B - 1;

  if (a.min >= 0)
    return internalMathBounds(0, bound);
  else if (a.max <= 0)
    return internalMathBounds(-bound, 0);
  else
    return internalMathBounds(-bound, bound);
}

} // namespace

I32Range SCEV::getI32Range(SCEVExpr *expr, const RangeQuery &q) const {
  if (!expr)
    return I32Range::unknown();
  std::unordered_set<SCEVExpr *> onStack;
  RangeMemo memo;
  return computeI32Range(expr, q, q.maxDepth, onStack, memo);
}

I32Range SCEV::getI32Range(Inst *v, const RangeQuery &q) const {
  if (!v)
    return I32Range::unknown();
  return getI32Range(getSCEV(v), q);
}

MathBounds SCEV::getSignedDeltaBounds(SCEVExpr *lhs, SCEVExpr *rhs,
                                      const MathQuery &q) const {
  if (!lhs || !rhs)
    return MathBounds::none();

  struct ComparablePart {
    SCEVExpr *root = nullptr;   // 指针表达式共享的不透明根
    SCEVExpr *offset = nullptr; // 相对根的有符号 i32 偏移
    bool valid = false;         // 分解是否成功
  };

  const auto splitPointer = [&](SCEVExpr *expr,
                                const auto &self) -> ComparablePart {
    if (!expr)
      return {};
    if (!isPtr(expr->ty))
      return {nullptr, expr, true};

    switch (expr->kind) {
    case SCEVExpr::K_CONSTANT:
      return {nullptr, getConstant(expr->cst.v, TY_I32), true};
    case SCEVExpr::K_UNKNOWN:
      return {expr, getConstant(0, TY_I32), true};
    case SCEVExpr::K_ADD: {
      ComparablePart result{nullptr, getConstant(0, TY_I32), true};
      for (SCEVExpr *operand : expr->nary.ops) {
        ComparablePart part = self(operand, self);
        if (!part.valid || (result.root && part.root))
          return {};
        if (part.root)
          result.root = part.root;
        result.offset = getAddExpr(result.offset, part.offset);
      }
      return result.root ? result : ComparablePart{};
    }
    case SCEVExpr::K_ADDREC: {
      ComparablePart base = self(expr->addRec.base, self);
      ComparablePart step = self(expr->addRec.step, self);
      if (!base.valid || !base.root || !step.valid || step.root)
        return {};
      return {base.root,
              getAddRecExpr(base.offset, step.offset, expr->addRec.loop), true};
    }
    case SCEVExpr::K_MUL:
    case SCEVExpr::K_SDIV:
    case SCEVExpr::K_SREM:
      return {};
    }
    return {};
  };

  ComparablePart left = splitPointer(lhs, splitPointer);
  ComparablePart right = splitPointer(rhs, splitPointer);
  if (!left.valid || !right.valid)
    return MathBounds::none();

  const bool hasPointerRoot = left.root || right.root;
  if (hasPointerRoot) {
    const bool sameRoot =
        left.root && right.root && left.root->structurallyEquals(right.root);
    if (!left.root || !right.root || !sameRoot)
      return MathBounds::none();
  }

  const auto hasMathematicalSemantics = [&](SCEVExpr *expr) {
    if (proveMathBoundsNoWrap(expr, q).valid)
      return true;
    return expr && expr->kind == SCEVExpr::K_ADDREC && expr->nsw;
  };
  if (!hasMathematicalSemantics(left.offset) ||
      !hasMathematicalSemantics(right.offset))
    return MathBounds::none();

  // 仅当两侧原值或同根偏移均具备有符号数学语义时才能相消
  SCEVExpr *delta = getAddExpr(left.offset, getNegExpr(right.offset));
  return proveMathBoundsNoWrap(delta, q);
}

// 无回绕证明递归计算数学整数端点, 任一步越出 i32 都会保守失败
// 带 contextBlock 的块敏感证明结果不进入全局缓存
bool SCEV::computeNoWrap(SCEVExpr *expr, const MathQuery &q,
                         MathBounds &mathRange, NoWrapSource &src,
                         u32 depth) const {
  mathRange = MathBounds::none();
  src = NoWrapSource::None;
  if (!expr || depth > q.maxDepth)
    return false;

  switch (expr->kind) {
  // 常量: 值本身即数学区间;落在 i32 即无回绕
  case SCEVExpr::K_CONSTANT:
    mathRange = internalMathBounds(expr->cst.v, expr->cst.v);
    if (fitsI32(expr->cst.v)) {
      src = NoWrapSource::RangeProof;
      return true;
    }
    return false; // i32 SCEV 不应出现 i32 域外常量, 保守失败

  // 叶子未知值: i32 寄存器值天然落在 i32 域, 无"运算回绕"
  case SCEVExpr::K_UNKNOWN: {
    I32Range r = getI32Range(expr, toRangeQuery(q));
    MathBounds hull = mathHullForLeaf(r, expr->ty);
    if (expr->ty == TY_I32 || expr->ty == TY_I1) {
      mathRange =
          hull.valid ? hull : mathHullForLeaf(widenForTy(expr->ty), expr->ty);
      src = NoWrapSource::RangeProof;
      return mathRange.valid;
    }
    // 非 i32 叶子仅在值域证明其落入 i32 域时视为无回绕
    if (hull.valid && fitsI32(hull.min, hull.max)) {
      mathRange = hull;
      src = NoWrapSource::RangeProof;
      return true;
    }
    return false;
  }

  // 加法:数学区间 = 各项数学区间端点之和;须全部子项已证且和落 i32
  case SCEVExpr::K_ADD: {
    i64 lo = 0, hi = 0;
    for (u32 i = 0; i < expr->nary.ops.size(); ++i) {
      MathBounds r;
      NoWrapSource s;
      if (!computeNoWrap(expr->nary.ops[i], q, r, s, depth + 1) || !r.valid)
        return false; // 任一子项未证 -> 整体失败 (已证子项端点必在 i32)
      if (!checkedAdd(lo, r.min, lo) || !checkedAdd(hi, r.max, hi))
        return false;
    }
    if (!fitsI32(lo, hi))
      return false;
    mathRange = internalMathBounds(lo, hi);
    src = NoWrapSource::RangeProof;
    return true;
  }

  // 乘法:数学区间 = 四端点积包络 越出 i32 立即失败
  case SCEVExpr::K_MUL: {
    i64 lo = 0, hi = 0;
    bool started = false;
    for (u32 i = 0; i < expr->nary.ops.size(); ++i) {
      MathBounds r;
      NoWrapSource s;
      if (!computeNoWrap(expr->nary.ops[i], q, r, s, depth + 1) || !r.valid)
        return false;
      if (!started) {
        lo = r.min;
        hi = r.max;
        started = true;
        continue;
      }
      i64 products[4];
      if (!checkedMul(lo, r.min, products[0]) ||
          !checkedMul(lo, r.max, products[1]) ||
          !checkedMul(hi, r.min, products[2]) ||
          !checkedMul(hi, r.max, products[3]))
        return false;
      i64 nlo = *std::min_element(std::begin(products), std::end(products));
      i64 nhi = *std::max_element(std::begin(products), std::end(products));
      // 越出 i32 时机器求值必然回绕
      if (!fitsI32(nlo, nhi))
        return false;
      lo = nlo;
      hi = nhi;
    }
    if (!started || !fitsI32(lo, hi))
      return false;
    mathRange = internalMathBounds(lo, hi);
    src = NoWrapSource::RangeProof;
    return true;
  }

  // 有符号除法:被除数已证且落 i32,除数不含 0,商四端点落 i32
  //   INT32_MIN/-1 = 2^31 这种唯一的 i32 除法溢出会令商端点越界
  //   -> fitsI32 自动失败
  case SCEVExpr::K_SDIV: {
    MathBounds a, b;
    NoWrapSource sa, sb;
    if (!computeNoWrap(expr->bin.lhs, q, a, sa, depth + 1) || !a.valid)
      return false;
    if (!computeNoWrap(expr->bin.rhs, q, b, sb, depth + 1) || !b.valid)
      return false;
    if (!(b.min > 0 || b.max < 0))
      return false; // 除数区间可能含 0
    i64 c0 = a.min / b.min, c1 = a.min / b.max;
    i64 c2 = a.max / b.min, c3 = a.max / b.max;
    i64 lo = std::min(std::min(c0, c1), std::min(c2, c3));
    i64 hi = std::max(std::max(c0, c1), std::max(c2, c3));
    if (!fitsI32(lo, hi))
      return false;
    mathRange = internalMathBounds(lo, hi);
    src = NoWrapSource::RangeProof;
    return true;
  }

  // 有符号取余:|a%b| < |b|; INT_MIN%-1 可能发生时保守放弃
  case SCEVExpr::K_SREM: {
    MathBounds a, b;
    NoWrapSource sa, sb;
    if (!computeNoWrap(expr->bin.lhs, q, a, sa, depth + 1) || !a.valid)
      return false;
    if (!computeNoWrap(expr->bin.rhs, q, b, sb, depth + 1) || !b.valid)
      return false;
    MathBounds r = remMathBounds(a, b);
    if (!r.valid || !fitsI32(r.min, r.max))
      return false;
    mathRange = r;
    src = NoWrapSource::RangeProof;
    return true;
  }

  // 归纳递推:base + step*t, 使用迭代次数上界构造仿射包络
  case SCEVExpr::K_ADDREC: {
    const Loop *L = expr->addRec.loop;
    MathBounds br, sr;
    NoWrapSource sbr, ssr;
    if (!computeNoWrap(expr->addRec.base, q, br, sbr, depth + 1) || !br.valid)
      return false;
    if (!computeNoWrap(expr->addRec.step, q, sr, ssr, depth + 1) || !sr.valid)
      return false;

    // 优先使用精确迭代次数 否则使用 BTC 值域的上界
    i64 T = -1;
    i64 tc = getConstantTripCount(L);
    if (tc > 0) {
      T = tc - 1;
    } else if (SCEVExpr *btc = getBackedgeTakenCount(L)) {
      I32Range tr = getI32Range(btc, toRangeQuery(q));
      if (auto tb = tr.signedBounds(); tb && tb->min >= 0 && fitsI32(tb->max))
        T = tb->max;
    }
    if (T < 0)
      return false; // 无法界定迭代次数 -> 保守失败

    // f(t)=base+step*t 是关于 t 的线性函数, 极值在 t in {0,T} 取得
    // step 端点可正可负,
    // 故 step*t 的贡献取 {0, sr.min*T, sr.max*T} 三者的 min/max (含 t=0)
    // sr/br 端点均已被证落在 i32, T 落在 i32,乘积 <= 2^62 不会溢出
    // 因此 checked i64 足以承载, 同时保留溢出防御
    i64 s1, s2;
    if (!checkedMul(sr.min, T, s1) || !checkedMul(sr.max, T, s2))
      return false;
    i64 smin = std::min(i64{0}, std::min(s1, s2));
    i64 smax = std::max(i64{0}, std::max(s1, s2));
    i64 lo, hi;
    if (!checkedAdd(br.min, smin, lo) || !checkedAdd(br.max, smax, hi) ||
        !fitsI32(lo, hi))
      return false;
    mathRange = internalMathBounds(lo, hi);
    src = NoWrapSource::LoopBoundProof;
    return true;
  }
  }
  return false;
}

MathBounds SCEV::proveMathBoundsNoWrap(SCEVExpr *expr,
                                       const MathQuery &q) const {
  MathBounds r;
  NoWrapSource src;
  // 唯一递归证明器同时验证必要子表达式无有符号回绕并计算数学端点
  if (computeNoWrap(expr, q, r, src, 0) && r.valid && r.min <= r.max)
    return MathBounds::of(r.min, r.max, NoWrapInfo{NoWrapKind::I32Signed, src});
  return MathBounds::none();
}

// 仅默认深度的无上下文顶层查询可读写全局缓存
// 每次顶层查询另按(expr,depth)记忆共享子图 避免DAG重复展开
I32Range SCEV::computeI32Range(SCEVExpr *expr, const RangeQuery &q, u32 depth,
                               std::unordered_set<SCEVExpr *> &onStack,
                               RangeMemo &memo) const {
  const bool cacheReadable = q.contextBlock == nullptr &&
                             q.predicateContext == nullptr &&
                             q.maxDepth == 64 && depth == q.maxDepth;
  if (cacheReadable) {
    auto it = rangeCache_.find(expr);
    if (it != rangeCache_.end())
      return it->second;
  }
  if (depth == 0 || onStack.count(expr)) // 深度上限 / 环 -> 兜底, 不缓存
    return widenForTy(expr->ty);

  if (const auto found = memo.find(expr); found != memo.end())
    for (const RangeMemoEntry &entry : found->second)
      if (entry.depth == depth)
        return entry.range;

  onStack.insert(expr);
  I32Range r;

  switch (expr->kind) {
  case SCEVExpr::K_CONSTANT:
    // I32Range 只描述 i1/i32 其它类型不能在这里静默截断
    r = expr->ty == TY_I1 || expr->ty == TY_I32
            ? I32Range::constant(static_cast<i32>(expr->cst.v))
            : I32Range::unknown();
    break;

  case SCEVExpr::K_UNKNOWN: {
    // 默认按类型放宽到最大值域
    r = widenForTy(expr->ty);

    // 未知叶子只消费类型兜底和显式上下文, 局部 SSA 属性交由 ValueFactOracle
    Inst *unknownValue = expr->unk.val;
    if (unknownValue &&
        (unknownValue->isErased() || unknownValue->isUndefValue()))
      unknownValue = nullptr;

    // 显式边事实只对当前查询有效, 事实矛盾产生的空集表示上下文不可达
    if (!r.isUnknown() && expr->ty == TY_I32 && q.predicateContext &&
        unknownValue) {
      r = r.intersectWith(q.predicateContext->getRangeFor(unknownValue));
    }

    // 块级支配事实与显式边事实使用同一采集规则
    if (!r.isUnknown() && expr->ty == TY_I32 && q.contextBlock &&
        unknownValue) {
      PredicateContextBuilder builder(dominatorTree_);
      r = r.intersectWith(
          builder.buildBlockContext(q.contextBlock).getRangeFor(unknownValue));
    }
    break;
  }

  case SCEVExpr::K_ADD: {
    // 左折叠 i32 环形加法 I32Range::add 能精确处理回绕单点和跨界弧
    r = computeI32Range(expr->nary.ops[0], q, depth - 1, onStack, memo);
    for (u32 i = 1; i < expr->nary.ops.size() && !r.isUnknown(); ++i) {
      I32Range t =
          computeI32Range(expr->nary.ops[i], q, depth - 1, onStack, memo);
      r = r.add(t);
    }
    break;
  }

  case SCEVExpr::K_MUL: {
    r = computeI32Range(expr->nary.ops[0], q, depth - 1, onStack, memo);
    for (u32 i = 1; i < expr->nary.ops.size() && !r.isUnknown(); ++i) {
      I32Range t =
          computeI32Range(expr->nary.ops[i], q, depth - 1, onStack, memo);
      r = r.multiply(t);
    }
    break;
  }

  case SCEVExpr::K_SDIV: {
    I32Range a = computeI32Range(expr->bin.lhs, q, depth - 1, onStack, memo);
    I32Range b = computeI32Range(expr->bin.rhs, q, depth - 1, onStack, memo);
    r = a.sdiv(b);
    break;
  }

  case SCEVExpr::K_SREM: {
    // 有符号余数值域不做模数正则化, 负余数必须保留
    I32Range a = computeI32Range(expr->bin.lhs, q, depth - 1, onStack, memo);
    I32Range b = computeI32Range(expr->bin.rhs, q, depth - 1, onStack, memo);
    r = a.srem(b);
    break;
  }

  case SCEVExpr::K_ADDREC:
    r = computeAddRecI32Range(expr, q, depth, onStack, memo);
    break;
  }

  onStack.erase(expr);
  memo[expr].push_back({depth, r});
  if (cacheReadable)
    rangeCache_[expr] = r;
  return r;
}

// AddRec 值域按 base + step * [0, TC-1] 在 i32 环形集合域计算
// 该计算覆盖所有中间迭代, 遇回绕时只会保守扩宽
// 未知迭代次数仅在已证明无回绕且步长方向单调时保留单侧范围
I32Range SCEV::computeAddRecI32Range(SCEVExpr *expr, const RangeQuery &q,
                                     u32 depth,
                                     std::unordered_set<SCEVExpr *> &onStack,
                                     RangeMemo &memo) const {
  I32Range baseRange =
      computeI32Range(expr->addRec.base, q, depth - 1, onStack, memo);
  I32Range stepRange =
      computeI32Range(expr->addRec.step, q, depth - 1, onStack, memo);
  if (baseRange.isUnknown() || stepRange.isUnknown())
    return I32Range::unknown();

  i64 tc = getConstantTripCount(expr->addRec.loop);
  if (tc <= 0) {
    // 未证明无回绕时, 单调步长仍可能越过整数边界
    if (!expr->nsw)
      return I32Range::unknown();
    auto sb = stepRange.signedBounds();
    auto bb = baseRange.signedBounds();
    if (sb && bb && sb->min >= 0)
      return I32Range::fromSigned(bb->min, INT32_MAX);
    if (sb && bb && sb->max <= 0)
      return I32Range::fromSigned(INT32_MIN, bb->max);
    return I32Range::unknown();
  }
  // 精确迭代次数使用环形乘法和加法覆盖全部迭代值, 避免端点凸包漏值
  i64 n = tc - 1; // 最大迭代下标 (0-based)
  I32Range iterationRange =
      (n <= INT32_MAX) ? I32Range::fromSigned(0, n) : I32Range::full();
  return baseRange.add(stepRange.multiply(iterationRange));
}

// 模运算原语

namespace {

/// @brief 计算若干正因子之积 超过上限时返回与上限的 gcd
u64 boundedFactorProduct(const u64 *factors, usize count, u64 maxMod) noexcept {
  u64 exact = 1;
  u64 residue = maxMod == 0 ? 0 : 1 % maxMod;
  bool exceedsLimit = false;
  for (usize i = 0; i < count; ++i) {
    const u64 factor = factors[i];
    VERIFY(factor != 0);
    if (!exceedsLimit) {
      if (exact > maxMod / factor)
        exceedsLimit = true;
      else
        exact *= factor;
    }
    if (maxMod != 0)
      residue = multiplyModulo(residue, factor, maxMod);
  }
  return exceedsLimit ? (maxMod == 0 ? 0 : std::gcd(residue, maxMod)) : exact;
}

/// @brief 在有符号连续值域与同余类的交集中查找唯一整数
/// @details 跨符号边界的环形集合不强制投影, 避免产生欠近似结果
inline std::optional<i64> uniqueValueInRange(const I32Range &r,
                                             const Congruence &c) noexcept {
  auto b = r.signedBounds();
  if (!b)
    return std::nullopt;
  i64 rmin = b->min;
  i64 rmax = b->max;
  if (c.isConstant()) {
    if (rmin <= c.rem && c.rem <= rmax)
      return c.rem;      // 常量恰落在区间内
    return std::nullopt; // 区间外 -> 空集,不下结论
  }
  u64 m = c.isModulo() ? c.mod : 0;
  if (m <= 1) // 无同余约束
    return (rmin == rmax) ? std::optional<i64>(rmin) : std::nullopt;
  const u64 wanted = normalizedModulo(c.rem, m);
  const u64 atMinimum = normalizedModulo(rmin, m);
  const u64 offset =
      wanted >= atMinimum ? wanted - atMinimum : m - (atMinimum - wanted);
  const u64 span = static_cast<u64>(rmax - rmin);
  if (offset > span)
    return std::nullopt; // 空集 -> 不下结论
  const i64 first = rmin + static_cast<i64>(offset);
  const u64 count = (span - offset) / m + 1;
  return (count == 1) ? std::optional<i64>(first) : std::nullopt;
}

} // namespace

namespace {

/// @brief 加法传递函数: x == rx(mod mx),
///   y == ry(mod my) => x+y  ==  rx+ry (mod gcd(mx,my))
/// @details 常量与未知事实自然兼容: gcd(0,m)=m, gcd(0,0)=0, gcd(1,*)=1
Congruence addCong(const Congruence &a, const Congruence &b) {
  if (!a.valid || !b.valid)
    return Congruence::unknown();
  u64 nm = std::gcd(a.mod, b.mod);
  if (nm == 0) {
    i64 sum;
    return checkedAdd(a.rem, b.rem, sum) ? Congruence::constant(sum)
                                         : Congruence::unknown();
  }
  const u64 rem =
      addModulo(normalizedModulo(a.rem, nm), normalizedModulo(b.rem, nm), nm);
  return Congruence::modulo(nm, static_cast<i64>(rem));
}

/// @brief 乘法同余传递:
///   x = mx*a + rx, y = my*b + ry
///   x*y = (mx*my)ab + (mx*ry)a + (my*rx)b + rx*ry
///   newMod = gcd(mx*my, mx*ry, my*rx) (这些系数分别约束 ab,a,b 的任意性)
///   newRem = rx*ry mod newMod
/// @param maxMod 模数上限, 超过时取与上限的最大公因数
Congruence mulCong(const Congruence &a, const Congruence &b, u64 maxMod) {
  if (!a.valid || !b.valid)
    return Congruence::unknown();
  // 任一因子为精确 0 => 乘积恒为常量 0 (避免随后对 mod=0 做 % 0)
  if (a.isConstant() && a.rem == 0)
    return Congruence::constant(0);
  if (b.isConstant() && b.rem == 0)
    return Congruence::constant(0);

  if (a.isConstant() && b.isConstant()) {
    i64 product;
    return checkedMul(a.rem, b.rem, product) ? Congruence::constant(product)
                                             : Congruence::unknown();
  }

  // 系数 gcd 用因子分解计算, 避免显式构造 ma*mb 这类宽乘积
  u64 factors[4];
  usize factorCount = 0;
  if (a.isConstant()) {
    factors[factorCount++] = b.mod;
    factors[factorCount++] = unsignedMagnitude(a.rem);
  } else if (b.isConstant()) {
    factors[factorCount++] = a.mod;
    factors[factorCount++] = unsignedMagnitude(b.rem);
  } else {
    // gcd(ma*mb, ma*rb) = ma*gcd(mb, rb), 再与 mb*ra 取 gcd
    u64 leftA = a.mod;
    u64 leftB = std::gcd(b.mod, unsignedMagnitude(b.rem));
    u64 rightA = b.mod;
    u64 rightB = unsignedMagnitude(a.rem);
    if (rightB == 0) {
      factors[factorCount++] = leftA;
      factors[factorCount++] = leftB;
    } else {
      factors[factorCount++] = std::gcd(leftA, rightA);
      leftA /= factors[factorCount - 1];
      rightA /= factors[factorCount - 1];
      factors[factorCount++] = std::gcd(leftA, rightB);
      leftA /= factors[factorCount - 1];
      rightB /= factors[factorCount - 1];
      factors[factorCount++] = std::gcd(leftB, rightA);
      leftB /= factors[factorCount - 1];
      rightA /= factors[factorCount - 1];
      factors[factorCount++] = std::gcd(leftB, rightB);
    }
  }

  const u64 g = boundedFactorProduct(factors, factorCount, maxMod);
  if (g <= 1)
    return Congruence::unknown();
  if (g > kMaxSupportedModulus)
    return Congruence::unknown();
  const u64 rem =
      multiplyModulo(normalizedModulo(a.rem, g), normalizedModulo(b.rem, g), g);
  return Congruence::modulo(g, static_cast<i64>(rem));
}

/// @brief 常量除法同余传递
/// @details 若 x == r (mod m), 且 |D| 同时整除 m 与 r,
///          则 x/D == r/D (mod m/|D|)
Congruence divCongByConst(const Congruence &c, i64 D) {
  if (!c.valid || D == 0)
    return Congruence::unknown();
  u64 ad = unsignedMagnitude(D);
  if (c.isConstant()) {
    // 精确常量:C++ 整型除法与 SysY 向零截断一致, 直接折叠
    if (c.rem == std::numeric_limits<i64>::min() && D == -1)
      return Congruence::unknown();
    return Congruence::constant(c.rem / D);
  }
  if (c.isModulo()) {
    // 要求 |D| | mod 且 |D| | rem: 此时每个 x == rem(mod mod) 都是 |D|
    // 的整数倍, 向零截断除法 == 精确除法
    // x = |D|*(mod'*k + rem'), x/D = sign(D)*(mod'*k+rem').
    if (c.mod % ad == 0 && floorMod(c.rem, ad) == 0) {
      u64 nmod = c.mod / ad;
      i64 nrem = c.rem / D; // 已整除, 符号由 D 决定
      return Congruence::modulo(nmod, nrem);
    }
  }
  return Congruence::unknown();
}

bool mayOverflowI32Division(const SCEV *scev, SCEVExpr *expr,
                            const CongruenceQuery &query) {
  if (!scev || !expr || expr->kind != SCEVExpr::K_SDIV || expr->ty != TY_I32 ||
      !expr->bin.rhs || !expr->bin.rhs->isConstant() ||
      expr->bin.rhs->cst.v != -1)
    return false;
  RangeQuery rangeQuery{query.contextBlock, query.predicateContext,
                        query.maxDepth};
  const I32Range numerator = scev->getI32Range(expr->bin.lhs, rangeQuery);
  return numerator.isUnknown() || numerator.containsSigned(INT32_MIN);
}

} // namespace

Congruence SCEV::restrictToDomain(Congruence c, ArithmeticDomain domain,
                                  bool expressionIsNSW) const {
  // 常量, 未知事实和无效事实不受回绕裁剪影响
  if (!c.valid || c.isUnknown() || c.isConstant())
    return c;
  // 数学域或已证明无回绕的表达式保留完整模数
  if (domain == ArithmeticDomain::MathematicalNSW || expressionIsNSW)
    return c;
  // i32 回绕域仅保留模数中的最大 2 的幂因子
  u64 pow2 =
      c.mod & (~c.mod + 1u); // = c.mod & (-c.mod), 能整除 c.mod 的最大 2 的幂
  pow2 = std::min(pow2, kI32Modulus);
  if (pow2 <= 1)
    return Congruence::unknown();
  // rem 重新规范化到 [0, pow2)
  return Congruence::modulo(pow2, floorMod(c.rem, pow2));
}

Congruence
SCEV::computeCongruence(SCEVExpr *expr, const CongruenceQuery &q, u32 depth,
                        std::unordered_set<SCEVExpr *> &onStack) const {
  if (!expr)
    return Congruence::unknown();
  if (depth > q.maxDepth)
    return Congruence::unknown();
  if (!onStack.insert(expr).second)
    return Congruence::unknown(); // 环检测
  struct StackPop {
    std::unordered_set<SCEVExpr *> &stack; // 当前递归栈
    SCEVExpr *expr = nullptr;              // 离开作用域时移除的节点
    ~StackPop() { stack.erase(expr); }     // 恢复递归栈
  } pop{onStack, expr};

  switch (expr->kind) {
  case SCEVExpr::K_CONSTANT:
    // 同余只适用于整数值
    if (!isInt(expr->ty))
      return Congruence::invalid();
    return Congruence::constant(expr->cst.v);

  case SCEVExpr::K_UNKNOWN: {
    Inst *v = expr->unk.val;
    if (!v || !isInt(v->getType()))
      return Congruence::invalid();

    // (1) 显式边事实优先 (JumpThreading 的 P->B)
    if (q.predicateContext) {
      Congruence c = q.predicateContext->getCongruenceFor(v);
      if (!c.isUnknown())
        return c;
    }
    // (2) 非循环头 Phi 对各输入事实取交汇, 未识别的循环头 Phi 不猜测不动点
    if (v->getOp() == OP_PHI && loopInfo_ &&
        !loopInfo_->isLoopHeader(v->parentBlock())) {
      Congruence acc = Congruence::unknown();
      bool first = true;
      for (int k = 0; k < v->getOperandCount(); ++k) {
        Inst *in = v->getArg(k);
        if (!in)
          return Congruence::unknown();
        Congruence c = computeCongruence(getSCEV(in), q, depth + 1, onStack);
        acc = first ? c : meetCongruence(acc, c);
        first = false;
        if (acc.isUnknown())
          break;
      }
      if (!acc.isUnknown())
        return acc;
    }
    // (3) 支配条件收窄 (块内 if(x%C==0){...})
    if (q.contextBlock) {
      PredicateContextBuilder builder(dominatorTree_);
      Congruence c =
          builder.buildBlockContext(q.contextBlock).getCongruenceFor(v);
      if (!c.isUnknown())
        return c;
    }
    return Congruence::unknown();
  }

  case SCEVExpr::K_ADD: {
    Congruence acc = Congruence::constant(0);
    for (u32 i = 0; i < expr->nary.ops.size(); ++i)
      acc = addCong(
          acc, computeCongruence(expr->nary.ops[i], q, depth + 1, onStack));
    return acc;
  }

  case SCEVExpr::K_MUL: {
    Congruence acc = Congruence::constant(1);
    for (u32 i = 0; i < expr->nary.ops.size(); ++i)
      acc = mulCong(acc,
                    computeCongruence(expr->nary.ops[i], q, depth + 1, onStack),
                    q.maxMod);
    return acc;
  }

  case SCEVExpr::K_SDIV: {
    // 除法不是模 2^32 的环同态, 被除数同余必须先裁剪到当前算术域
    Congruence nc = computeCongruence(expr->bin.lhs, q, depth + 1, onStack);
    bool numeratorNSW =
        (expr->bin.lhs->kind == SCEVExpr::K_ADDREC) && expr->bin.lhs->nsw;
    nc = restrictToDomain(nc, q.domain, numeratorNSW);
    SCEVExpr *den = expr->bin.rhs;
    if (mayOverflowI32Division(this, expr, q))
      return Congruence::unknown();
    if (den->kind == SCEVExpr::K_CONSTANT && den->cst.v != 0)
      return divCongByConst(nc, den->cst.v);
    return Congruence::unknown();
  }

  case SCEVExpr::K_SREM: {
    // 有符号取余满足 x = (x/M)*M + (x%M), 因此
    //   (x % M)  ==  x (mod |M|) -- i32 级恒等式
    // 设 lhs 的同余为 {cm, cr},则 (x%M) - cr 同时是 |M| 与 cm 的倍数之和,
    // 故 (x%M)  ==  cr (mod gcd(|M|, cm))
    // 仅当除数为非零常量时成立 (否则 |M| 未知) 该关系是 i32 级恒等式,
    // 顶层 restrictToDomain 仍会按当前算术域做最终裁剪, 故安全
    //
    // 该事实不表示取余是仿射运算, 负数路径禁止合并嵌套取余
    SCEVExpr *den = expr->bin.rhs;
    if (den->kind != SCEVExpr::K_CONSTANT || den->cst.v == 0)
      return Congruence::unknown();
    u64 M = unsignedMagnitude(den->cst.v);
    Congruence cL = computeCongruence(expr->bin.lhs, q, depth + 1, onStack);
    if (!cL.valid)
      return Congruence::unknown();
    if (cL.isConstant()) {
      // lhs 是常量值时余数也是常量; 但常量折叠已在 getSRemExpr 处理,
      // 这里仍给出 modulo(|M|, cr) 作为安全且足够强的事实
      return Congruence::modulo(M, floorMod(cL.rem, M));
    }
    u64 g = std::gcd(M, cL.mod);
    return Congruence::modulo(g, floorMod(cL.rem, g));
  }

  case SCEVExpr::K_ADDREC: {
    // X(t) = base + step*t.若能证明 M | step,则 step*t  ==  0 (mod M),
    // 于是 X(t) == base (mod M).stepDiv 是可证明整除 step 的模数
    SCEVExpr *step = expr->addRec.step;
    Congruence baseC =
        computeCongruence(expr->addRec.base, q, depth + 1, onStack);
    u64 stepDiv = 0;
    bool ok = false;
    if (step->kind == SCEVExpr::K_CONSTANT) {
      stepDiv = unsignedMagnitude(step->cst.v);
      ok = (stepDiv != 0);
    } else {
      Congruence stepC = computeCongruence(step, q, depth + 1, onStack);
      if (stepC.isConstant()) {
        stepDiv = unsignedMagnitude(stepC.rem);
        ok = (stepDiv != 0);
      } else if (stepC.isModulo() && stepC.rem == 0) {
        stepDiv = stepC.mod;
        ok = true;
      }
      // 否则无法证明 step 是某个 >1 模数的整数倍 -> 放弃
    }
    if (!ok || !baseC.valid)
      return Congruence::unknown();
    u64 M = std::gcd(baseC.mod, stepDiv); // base 常量时 gcd(0,stepDiv)=stepDiv
    return Congruence::modulo(M, floorMod(baseC.rem, M));
  }
  }
  return Congruence::unknown();
}

// 同余入口 (getCongruence / satisfiesCongruence)

Congruence SCEV::getCongruence(SCEVExpr *expr, const CongruenceQuery &q) const {
  if (!expr)
    return Congruence::unknown();

  // 显式路径事实描述 SSA 运行值, 不能把任意模数豁免扩展到 Phi 输入交汇
  if (expr->kind == SCEVExpr::K_UNKNOWN && expr->unk.val) {
    if (q.predicateContext) {
      Congruence direct = q.predicateContext->getCongruenceFor(expr->unk.val);
      if (!direct.isUnknown())
        return direct;
    }
    if (q.contextBlock) {
      PredicateContextBuilder builder(dominatorTree_);
      Congruence direct = builder.buildBlockContext(q.contextBlock)
                              .getCongruenceFor(expr->unk.val);
      if (!direct.isUnknown())
        return direct;
    }
  }

  // 仅无上下文的默认查询可缓存, 路径相关事实不能进入全局缓存
  bool cacheable = !q.contextBlock && !q.predicateContext &&
                   q.domain == ArithmeticDomain::I32Wrapping &&
                   q.maxDepth == 64 && q.maxMod == (1ull << 32);
  if (cacheable) {
    auto it = congruenceCache_.find(expr);
    if (it != congruenceCache_.end())
      return it->second;
  }

  std::unordered_set<SCEVExpr *> onStack;
  Congruence math = computeCongruence(expr, q, 0, onStack);
  // 内部先按数学整数域组合, 顶层再按机器语义统一裁剪
  bool nsw = (expr->kind == SCEVExpr::K_ADDREC) && expr->nsw;
  Congruence res = restrictToDomain(math, q.domain, nsw);

  if (cacheable)
    congruenceCache_[expr] = res;
  return res;
}

Congruence SCEV::getCongruence(Inst *v, const CongruenceQuery &q) const {
  if (!v)
    return Congruence::unknown();
  // 先看边事实
  // (K_UNKNOWN 路径也会看,但 Inst 入口直接命中更快且覆盖 AddRec/常量值).
  if (q.predicateContext) {
    Congruence c = q.predicateContext->getCongruenceFor(v);
    if (!c.isUnknown())
      return c;
  }
  return getCongruence(getSCEV(v), q);
}

namespace {

// 非 2^k 目标反推只能穿过已证明不回绕的顶层加法或乘法
bool canBackpropagateTargetCongruence(const SCEV *scev, SCEVExpr *expr, u64 mod,
                                      const CongruenceQuery &query, u32 depth) {
  if (query.domain == ArithmeticDomain::MathematicalNSW ||
      isI32WrappingInvariantModulus(mod))
    return true;
  if (!scev || !expr || expr->ty != TY_I32 || depth > query.maxDepth)
    return false;

  MathQuery mathQuery;
  mathQuery.contextBlock = query.contextBlock;
  mathQuery.predicateContext = query.predicateContext;
  mathQuery.maxDepth = query.maxDepth - depth;
  return scev
      ->getSignedDeltaBounds(expr, scev->getConstant(0, TY_I32), mathQuery)
      .valid;
}

/// @brief satisfiesCongruence 的深度受限递归核心
/// @details 除最强单一同余外, 还按目标模数反推表达式并消费路径排除事实
///          每个分支都规约到更小的 SCEV 子表达式, 深度预算保证终止
bool satisfiesImpl(const SCEV *se, SCEVExpr *expr, u64 mod, i64 rem,
                   const CongruenceQuery &q, u32 depth) {
  if (!expr)
    return false;
  if (mod == 1)
    return true; // 任意值  ==  任意 (mod 1)
  if (depth > q.maxDepth)
    return false;
  if (mod == 0) { // 询问"是否恒等于常量 rem"
    Congruence c = se->getCongruence(expr, q);
    return c.isConstant() && c.rem == rem;
  }
  if (mod > kMaxSupportedModulus)
    return false;
  i64 want = floorMod(rem, mod);

  // (1) 最强单一同余直接判定
  Congruence c = se->getCongruence(expr, q);
  if (c.isConstant())
    return floorMod(c.rem, mod) == want;
  if (c.isModulo() && c.mod % mod == 0)
    return floorMod(c.rem, mod) == want;

  // (2) 同模不等事实排除其它全部余数时, 可证明未知节点取目标余数
  if (expr->kind == SCEVExpr::K_UNKNOWN && q.predicateContext &&
      expr->unk.val) {
    ModExclusionSummary ex =
        q.predicateContext->getModExclusionsFor(expr->unk.val, mod);
    if (auto sole = ex.soleAllowedResidue(); sole && *sole == want)
      return true;
  }

  // (3) AddRec 按目标模数:
  // X(t)=base+step*t  ==  want <=> base == want  &&  step == 0.
  //
  //     域门控分两类:
  //       * MathematicalNSW / expr->nsw:可按数学整数域证明任意模数;
  //       * I32Wrapping + mod=2^k:即使 AddRec 可能有符号回绕, 低 k 位仍与
  //         数学递推一致,因为每次回绕只增减 2^32 的倍数,而 2^k | 2^32.
  //
  //     不能把这个放宽用于 mod 3/5/10 等非 2^k 模数;
  //     例如 i32 回绕会改变 mod 3 余数, 必须继续要求无回绕.
  if (expr->kind == SCEVExpr::K_ADDREC &&
      (q.domain == ArithmeticDomain::MathematicalNSW || expr->nsw ||
       isI32WrappingInvariantModulus(mod))) {
    return satisfiesImpl(se, expr->addRec.base, mod, want, q, depth + 1) &&
           satisfiesImpl(se, expr->addRec.step, mod, 0, q, depth + 1);
  }

  // (4) K_SDIV 整除反推:
  //       目标是证明 q = num / D 满足 q == want (mod M).
  //       SysY 的有符号除法是向零截断, 不能一般地把 `/D` 当作整数环上的可逆运算
  //       只有当能证明 num 恰好落在 D*(M*k + want) 这一类值里时,
  //       num 必定被 D 整除, 截断除法才退化为数学整数除法. 等价条件是:
  //         num  ==  D*want (mod |D|*M)
  //
  //       这个单一条件同时包含"num 可被 |D| 整除"和"商在 mod M 下余数为 want"
  //       例如 x  ==  2 (mod 4) 时, 询问 `(x/2)  ==  1 (mod 2)` 会转成
  //       `x == 2 (mod 4)`, 正好命中奇数分支事实. 模数过大时保守失败
  if (expr->kind == SCEVExpr::K_SDIV) {
    SCEVExpr *den = expr->bin.rhs;
    if (den->kind != SCEVExpr::K_CONSTANT || den->cst.v == 0)
      return false;
    if (mayOverflowI32Division(se, expr, q))
      return false;
    u64 ad = unsignedMagnitude(den->cst.v);
    if (ad == 0)
      return false; // 防御性兜底; den!=0 时 unsignedMagnitude 不会返回 0
    u64 combined;
    if (!checkedMul(ad, mod, combined) || combined == 0 ||
        combined > q.maxMod || combined > static_cast<u64>(INT64_MAX))
      return false;
    const u64 target =
        multiplyModulo(normalizedModulo(den->cst.v, combined),
                       normalizedModulo(want, combined), combined);
    i64 need = static_cast<i64>(target);
    return satisfiesImpl(se, expr->bin.lhs, combined, need, q, depth + 1);
  }

  // (5) K_MUL 按目标模数反推:常量因子并成 C,其余非常量因子并成乘积 P
  //       C*P  ==  want (mod M):
  //         * C  ==  0 (mod M) => 乘积  ==  0,仅 want==0 成立;
  //         * gcd(|C|,M)==1    => C 可逆,P == C^{-1}*want (mod M), 递归验证 P;
  //         * 其余 (1<gcd<M)    => 单点反推会丢解, 保守失败 (交给 (1) 已尽力).
  if (expr->kind == SCEVExpr::K_MUL) {
    if (!canBackpropagateTargetCongruence(se, expr, mod, q, depth))
      return false;
    u64 constantModulo = 1 % mod;
    std::vector<SCEVExpr *> rest;
    for (u32 i = 0; i < expr->nary.ops.size(); ++i) {
      SCEVExpr *op = expr->nary.ops[i];
      if (op->kind == SCEVExpr::K_CONSTANT)
        constantModulo = multiplyModulo(constantModulo,
                                        normalizedModulo(op->cst.v, mod), mod);
      else
        rest.push_back(op);
    }
    if (rest.size() == expr->nary.ops.size())
      return false; // 没有剥离常量时递归目标不会变小
    i64 Cmod = static_cast<i64>(constantModulo); // 折叠到 [0,M)
    if (rest.empty())
      return Cmod == want; // 纯常量积
    if (Cmod == 0)
      return want == 0;
    i64 inv;
    if (modInverse(Cmod, mod, inv)) {
      i64 need = static_cast<i64>(multiplyModulo(
          normalizedModulo(inv, mod), normalizedModulo(want, mod), mod));
      SCEVExpr *prod = rest[0];
      for (usize i = 1; i < rest.size(); ++i)
        prod = se->getMulExpr(prod, rest[i]);
      return satisfiesImpl(se, prod, mod, need, q, depth + 1);
    }
    return false;
  }

  // (6) K_ADD 单未知反推:其余子项余数已知时, 反推出唯一未知子项
  if (expr->kind == SCEVExpr::K_ADD) {
    if (!canBackpropagateTargetCongruence(se, expr, mod, q, depth))
      return false;
    u64 knownSum = 0;
    SCEVExpr *unknown = nullptr;
    int unknownCount = 0;
    for (u32 i = 0; i < expr->nary.ops.size(); ++i) {
      SCEVExpr *op = expr->nary.ops[i];
      Congruence oc = se->getCongruence(op, q);
      bool pinned = oc.isConstant() || (oc.isModulo() && oc.mod % mod == 0);
      if (pinned) {
        knownSum = addModulo(knownSum, normalizedModulo(oc.rem, mod), mod);
      } else if (++unknownCount == 1) {
        unknown = op;
      } else {
        unknown = nullptr;
        break;
      }
    }
    if (unknownCount == 0)
      return knownSum == static_cast<u64>(want);
    if (unknownCount == 1 && unknown) {
      const u64 wanted = static_cast<u64>(want);
      const u64 neededUnsigned =
          wanted >= knownSum ? wanted - knownSum : mod - (knownSum - wanted);
      i64 need = static_cast<i64>(neededUnsigned);
      return satisfiesImpl(se, unknown, mod, need, q, depth + 1);
    }
    return false;
  }

  return false;
}

} // namespace

bool SCEV::satisfiesCongruence(SCEVExpr *expr, u64 mod, i64 rem,
                               const CongruenceQuery &q) const {
  return expr && satisfiesImpl(this, expr, mod, rem, q, 0);
}

bool SCEV::satisfiesCongruence(Inst *v, u64 mod, i64 rem,
                               const CongruenceQuery &q) const {
  if (!v)
    return false;
  if (mod > kMaxSupportedModulus)
    return false;
  // Inst 入口先看边事实里以该 Inst 为键的同模排除摘要, 再转表达式
  if (mod >= 2 && q.predicateContext) {
    ModExclusionSummary ex = q.predicateContext->getModExclusionsFor(v, mod);
    if (auto sole = ex.soleAllowedResidue();
        sole && *sole == floorMod(rem, mod))
      return true;
  }
  // 再消费 Inst 级别的最强单一同余
  // 这里刻意放在 getSCEV(v) 之前: 像`r = x%C` 这样的余数值即便已有 K_SREM
  // 表达式, Inst 入口也能先从操作码本身提取 `(x%C)  ==  x (mod |C|)`, 并消费
  // PredicateContext 的精确边事实. 若直接进入通用表达式递归, 仍然安全,
  // 但会错过这条更直接的 SSA 值事实路径.
  Congruence c = getCongruence(v, q);
  if (mod == 0)
    return c.isConstant() && c.rem == rem;
  i64 want = floorMod(rem, mod);
  if (c.isConstant())
    return floorMod(c.rem, mod) == want;
  if (c.isModulo() && c.mod % mod == 0)
    return floorMod(c.rem, mod) == want;
  return satisfiesCongruence(getSCEV(v), mod, rem, q);
}

namespace {
/// @brief 把 PredicateQuery 投影成 CongruenceQuery
CongruenceQuery toCongQuery(const PredicateQuery &q) {
  CongruenceQuery cq;
  cq.contextBlock = q.contextBlock;
  cq.predicateContext = q.predicateContext;
  cq.domain = q.congruenceDomain;
  return cq;
}
/// @brief 把 PredicateQuery 投影成 RangeQuery
RangeQuery toRangeQuery(const PredicateQuery &q) {
  RangeQuery rq;
  rq.contextBlock = q.contextBlock;
  rq.predicateContext = q.predicateContext;
  return rq;
}
} // namespace

KnownBool SCEV::evaluatePredicate(Inst *pred, const PredicateQuery &q) const {
  if (!pred || !isIntCompare(pred->getOp()))
    return KnownBool::Unknown;
  OpCode op = pred->getOp();
  Inst *a = pred->getArg(0), *b = pred->getArg(1);
  CongruenceQuery cq = toCongQuery(q);
  RangeQuery rq = toRangeQuery(q);

  // 强模式: (x % C) ==/!= R
  // 返回该[相等关系]的判定 (eq=true 表示判定 "==",false 表示 "!=").
  //
  // 有符号余数的边事实使用正向蕴含 `x%C==R => x == R(mod|C|)`
  // (无条件成立); 但要[证明]`x%C==R` 恒真, 需要反向,
  // 而反向依赖 x 的符号 (C 截断取模的符号同被除数):
  //   R==0:x%C==0 <=> x == 0(mod m), 与符号无关, 最干净.
  //   R>0 :需 x>=0 且 x == R(mod m), 此时 x%C = x mod m = R.
  //   R<0 :需 x<=0 且 x == floorMod(R,m)(mod m), 此时 x%C = -( |x| mod m ) = R.
  auto judgeModEq = [&](Inst *modI, Inst *cstI, bool eq) -> KnownBool {
    if (modI->getOp() != OP_MOD || modI->getOperandCount() != 2)
      return KnownBool::Unknown;
    if (modI->getArg(1)->getOp() != OP_ICONST || cstI->getOp() != OP_ICONST)
      return KnownBool::Unknown;
    i64 C = modI->getArg(1)->getImm();
    i64 R = cstI->getImm();
    u64 m = unsignedMagnitude(C);
    if (m <= 1)
      return KnownBool::Unknown;
    Inst *x = modI->getArg(0);

    // |R| >= m: x%C 落在 (-m, m), 绝不可能等于 R -> 等式恒假
    if (unsignedMagnitude(R) >= m)
      return eq ? KnownBool::AlwaysFalse : KnownBool::AlwaysTrue;

    i64 want = floorMod(R, m);
    I32Range xr = getI32Range(x, rq);
    auto xb = xr.signedBounds();

    // 证明恒真: x%C == R 对所有取值成立
    bool eqTrue = false;
    if (R == 0)
      eqTrue = satisfiesCongruence(x, m, 0, cq); // 符号无关
    else if (R > 0)
      eqTrue = xb && xb->min >= 0 && satisfiesCongruence(x, m, want, cq);
    else /* R < 0 */
      eqTrue = xb && xb->max <= 0 && satisfiesCongruence(x, m, want, cq);
    if (eqTrue)
      return eq ? KnownBool::AlwaysTrue : KnownBool::AlwaysFalse;

    // 证明恒假: x%C 绝不等于 R
    // 这里比恒真容易: `x%C==R` 一定蕴含 `x == floorMod(R,|C|)`,
    // 所以只要已知同余事实与该余数不兼容, 就能直接判恒假;
    // 不需要知道 x 的符号. 符号只在恒真方向上需要,
    // 因为有符号 `%` 的结果符号跟随被除数.
    bool eqFalse = false;
    // (a) 同余不兼容: x%C==R => x == want(mod m), 故余数不同即可判定恒假
    Congruence xc = getCongruence(x, cq);
    if ((xc.isConstant() && floorMod(xc.rem, m) != want) ||
        (xc.isModulo() && xc.mod % m == 0 && floorMod(xc.rem, m) != want))
      eqFalse = true;
    // (b) 符号不兼容: R>0 但 x<=0 (余数<=0) / R<0 但 x>=0 (余数>=0)
    if (!eqFalse && R > 0 && xb && xb->max <= 0) {
      eqFalse = true;
    }
    if (!eqFalse && R < 0 && xb && xb->min >= 0) {
      eqFalse = true;
    }
    // (c) 同模不等事实排除目标余数时, `x%C==R` 恒假
    if (!eqFalse && q.predicateContext) {
      ModExclusionSummary ex = q.predicateContext->getModExclusionsFor(x, m);
      if (ex.forbids(want))
        eqFalse = true;
    }
    if (eqFalse)
      return eq ? KnownBool::AlwaysFalse : KnownBool::AlwaysTrue;
    return KnownBool::Unknown;
  };

  if (op == OP_EQ || op == OP_NE) {
    bool eq = (op == OP_EQ);
    KnownBool k = judgeModEq(a, b, eq);
    if (k != KnownBool::Unknown)
      return k;
    k = judgeModEq(b, a, eq);
    if (k != KnownBool::Unknown)
      return k;

    // 一般 a ==/!= b 使用 d = a-b 的值域与同余判定
    SCEVExpr *d = getAddExpr(getSCEV(a), getNegExpr(getSCEV(b)));
    I32Range dr = getI32Range(d, rq);
    if (!dr.isUnknown() && !dr.isEmpty() && !dr.containsSigned(0))
      return eq ? KnownBool::AlwaysFalse : KnownBool::AlwaysTrue; // a!=b
    if (auto single = dr.getSingleSigned(); single && *single == 0)
      return eq ? KnownBool::AlwaysTrue : KnownBool::AlwaysFalse; // a==b
    Congruence dc = getCongruence(d, cq);
    if (dc.isConstant())
      return (dc.rem == 0)
                 ? (eq ? KnownBool::AlwaysTrue : KnownBool::AlwaysFalse)
                 : (eq ? KnownBool::AlwaysFalse : KnownBool::AlwaysTrue);
    if (dc.isModulo() && dc.rem != 0)
      // d 不与 0 同余时 a!=b
      return eq ? KnownBool::AlwaysFalse : KnownBool::AlwaysTrue;
    // 值域与同余若把 d 收窄到唯一值, 即可判定等式
    if (auto s = uniqueValueInRange(dr, dc)) {
      if (*s == 0)
        return eq ? KnownBool::AlwaysTrue : KnownBool::AlwaysFalse;
      return eq ? KnownBool::AlwaysFalse : KnownBool::AlwaysTrue;
    }
    return KnownBool::Unknown;
  }

  // 回绕后的 (a-b) 符号不等价于 a 与 b 的有符号顺序,
  // 必须直接比较两侧运行时值域
  // 例如 x+1 在 x==INT_MAX 时会回绕, 不能据代数差 1 判恒大
  const I32Range ar = getI32Range(a, rq);
  const I32Range br = getI32Range(b, rq);
  switch (op) {
  case OP_LT:
    return evalIntCompare(IntPred::SLT, ar, br);
  case OP_LE:
    return evalIntCompare(IntPred::SLE, ar, br);
  case OP_GT:
    return evalIntCompare(IntPred::SGT, ar, br);
  case OP_GE:
    return evalIntCompare(IntPred::SGE, ar, br);
  default:
    break;
  }
  return KnownBool::Unknown;
}

} // namespace ir
} // namespace svm
