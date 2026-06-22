/// @file ValueRange.cpp
/// @brief I32Range 的集合运算与 i32 环算术 transfer 实现
///
/// 设计核心是把所有 "多段弧合并成单段" 的逻辑收敛到两个原语:
///   intersectArcs : 两条弧求交 -> 最多 2 段 (旋转坐标系精确计算).
///   coverTwo      : 两条弧求最小覆盖单弧 = 补 "最大空隙".
/// 于是 intersectWith / unionHullWith 都用它们拼出来,
/// 避免到处手写易错的端点比较.
///
/// 除法/取余 transfer 不在环上做 (i32 环除法没有 Minkowski 闭式),
/// 而是先要求操作数 signed 投影连续 + 排除陷阱, 再用四角/符号外壳给出 sound
/// 包络, 是工业 ConstantRange 的常用保守做法.

#include "ValueRange.h"

#include <algorithm>
#include <iterator>
#include <limits>

namespace svm::ir {
namespace {
constexpr u64 I32Cardinality = u64{1} << 32; // 2^32, i32 值域的基数
} // namespace

//  fromSigned: 由有符号闭区间构造环形弧
//
// 先 clamp 再 cast, 避免把越界 int64 直接转成 int32 造成实现定义行为.
// clamp 扩大而非缩小集合, 因此保持 sound.

I32Range I32Range::fromSigned(i64 min, i64 max) noexcept {
  if (min > max)
    return empty();

  constexpr i64 I32Min = static_cast<i64>(std::numeric_limits<i32>::min());
  constexpr i64 I32Max = static_cast<i64>(std::numeric_limits<i32>::max());
  if (min <= I32Min && max >= I32Max)
    return full();

  const auto lower = static_cast<i32>(std::clamp(min, I32Min, I32Max));
  const auto upper = static_cast<i32>(std::clamp(max, I32Min, I32Max));
  I32Range range;
  range.kind_ = Kind::Set;
  range.lower_ = static_cast<u32>(lower);
  range.upper_ = static_cast<u32>(upper) + 1U; // 转半开: [lower, upper+1)
  return range;
}

//  signed 投影: signedMin / signedMax
//
// signed 连续弧的下端即 lower_ 的有符号解释; 末元素 upper_-1 的有符号解释.
// 全集时返回 MIN/MAX; sign-wrapped 时无法安全投影, 返回 nullopt.

std::optional<i32> I32Range::signedMin() const noexcept {
  if (kind_ != Kind::Set)
    return std::nullopt;
  if (lower_ == upper_)
    return std::numeric_limits<i32>::min(); // 全集
  if (signedWrapped())
    return std::nullopt; // 跨符号位, 无安全下界
  return i32FromBits(lower_);
}

std::optional<i32> I32Range::signedMax() const noexcept {
  if (kind_ != Kind::Set)
    return std::nullopt;
  if (lower_ == upper_)
    return std::numeric_limits<i32>::max(); // 全集
  if (signedWrapped())
    return std::nullopt; // 跨符号位, 无安全上界
  return i32FromBits(upper_ - 1U);
}

//  弧级原语: intersectArcs
//
// 输入均为 non-empty non-full 弧 (lower != upper).
// 思路: 旋转坐标系使 left 起点对齐到 0 -- rel(x) = x - leftLower (mod 2^32).
// 旋转后 left = [0, leftSize), 不回绕. right = [rightStart,
// rightStart+rightSize) 在 rel 空间, 可能回绕. 与 [0, leftSize)
// 求交是标准区间问题: right 不回绕时至多 1 段, 回绕时至多 2 段.

i32 I32Range::intersectArcs(u32 leftLower, u32 leftUpper, u32 rightLower,
                            u32 rightUpper, I32Range output[2]) noexcept {
  const u32 leftSize = leftUpper - leftLower; // mod 2^32, 落在 [1, 2^32-1]
  const u32 rightSize = rightUpper - rightLower;
  const u32 rightStart = rightLower - leftLower; // right 起点在 rel 空间的位置
  i32 count = 0;

  // emit: 将 rel 空间的交集段 [lower, upper) 旋回绝对坐标
  const auto emit = [&](u32 lower, u32 upper) {
    if (lower < upper)
      output[count++] = fromHalfOpen(lower + leftLower, upper + leftLower);
  };

  // right 在 rel 空间是否回绕: rightStart + rightSize 溢出 2^32. 用 64 位判定.
  const u64 rightEnd = static_cast<u64>(rightStart) + rightSize;
  if (rightEnd <= I32Cardinality) {
    // right 不回绕: rel 段 [rightStart, rightStart+rightSize).
    // 与 [0, leftSize) 求交 = [max(0,rightStart), min(leftSize, rightEnd)).
    if (rightStart < leftSize) {
      const u32 upper = rightEnd == I32Cardinality
                            ? leftSize
                            : std::min(leftSize, static_cast<u32>(rightEnd));
      emit(rightStart, upper);
    }
  } else {
    // right 回绕: rel 段 [rightStart, 2^32) U [0, rightEnd-2^32).
    // 分别与 [0, leftSize) 求交.
    if (rightStart < leftSize)
      emit(rightStart, leftSize); // 第一段: [rightStart, leftSize)
    const auto wrappedEnd = static_cast<u32>(rightEnd - I32Cardinality);
    emit(0, std::min(leftSize, wrappedEnd)); // 第二段: [0, min(leftSize, wrap))
  }
  return count;
}

//  弧级原语: coverTwo
//
// 覆盖 left U right 的最小单弧 = 补 (left, right 都不覆盖的 "最大空隙").
// 未覆盖区域 = complement(left) ∩ complement(right); 它最多 2 段空隙.
// 取最大空隙做补即得最紧覆盖弧.

I32Range I32Range::coverTwo(const I32Range &left,
                            const I32Range &right) noexcept {
  // 防御性处理 unknown/empty/full (调用方通常已处理)
  if (left.isUnknown() || right.isUnknown())
    return unknown();
  if (left.isEmpty())
    return right;
  if (right.isEmpty())
    return left;
  if (left.isFullSet() || right.isFullSet())
    return full();

  const I32Range leftComplement = left.complement(); // [left.upper, left.lower)
  const I32Range rightComplement =
      right.complement(); // [right.upper, right.lower)
  I32Range gaps[2];
  const i32 gapCount =
      intersectArcs(leftComplement.lower_, leftComplement.upper_,
                    rightComplement.lower_, rightComplement.upper_, gaps);
  if (gapCount == 0)
    return full(); // 无空隙 -> 并集是全集
  if (gapCount == 1)
    return gaps[0].complement(); // 唯一空隙 -> 覆盖弧 = 补它

  // 两段空隙: 覆盖弧 = 补最大空隙 (留下最大的洞, 弧最紧)
  if (gaps[0].size() != gaps[1].size())
    return (gaps[0].size() > gaps[1].size() ? gaps[0] : gaps[1]).complement();

  // 空隙等大: 按确定性规则取 signed 投影更紧的覆盖
  const I32Range first = gaps[0].complement();
  const I32Range second = gaps[1].complement();
  if (first.isSignWrapped() != second.isSignWrapped())
    return first.isSignWrapped() ? second
                                 : first; // signed 连续 (可给端点) 更 "紧"
  // 仍无法唯一: 按 lower 和 upper 做确定性选择
  if (first.lower_ != second.lower_)
    return first.lower_ < second.lower_ ? first : second;
  return first.upper_ <= second.upper_ ? first : second;
}

//  交集 / 并集

I32Range I32Range::intersectWith(const I32Range &other) const noexcept {
  // unknown 在交集中是单位元 (无约束): unknown ∩ X = X.
  // empty 是吸收元 (矛盾): empty ∩ X = empty.
  if (isUnknown())
    return other;
  if (other.isUnknown())
    return *this;
  if (isEmpty() || other.isFullSet())
    return *this;
  if (other.isEmpty() || isFullSet())
    return other;

  // 两条 non-empty non-full 弧求精确交, 结果可能是 0/1/2 段
  I32Range pieces[2];
  const i32 pieceCount =
      intersectArcs(lower_, upper_, other.lower_, other.upper_, pieces);
  if (pieceCount == 0)
    return empty(); // 两弧不相交
  if (pieceCount == 1)
    return pieces[0]; // 精确单弧交
  // 两段: 用 coverTwo 合并为最小单弧外壳 (保守但 sound)
  return coverTwo(pieces[0], pieces[1]);
}

I32Range I32Range::unionHullWith(const I32Range &other) const noexcept {
  // unknown 在并集中传染: unknown U X = unknown.
  if (isUnknown() || other.isUnknown())
    return unknown();
  if (isEmpty())
    return other;
  if (other.isEmpty())
    return *this;
  if (isFullSet() || other.isFullSet())
    return full();
  return coverTwo(*this, other);
}

//  i32 环算术 transfer

// add: 两条弧的 Minkowski 和仍是一条弧, 起点相加, 弧长 = sA + sB - 1.
// 跨越 signed/unsigned 边界也不退化 (例如 [INT_MAX]+[1] = [INT_MIN]).
// 只有结果弧长 >= 2^32 (覆盖全集)、或操作数为空/全集时才退化.
I32Range I32Range::add(const I32Range &other) const noexcept {
  if (isEmpty() || other.isEmpty())
    return empty();
  if (isUnknown() || other.isUnknown())
    return unknown();
  if (isFullSet() || other.isFullSet())
    return full();

  const u64 resultSize = size() + other.size() - 1;
  if (resultSize >= I32Cardinality)
    return full();                               // 弧长覆盖全集
  const u32 resultLower = lower_ + other.lower_; // mod 2^32
  return fromHalfOpen(resultLower, resultLower + static_cast<u32>(resultSize));
}

// negate: {-x : x in [lower, upper)} = [1-upper, 1-lower).
// 推导: 最小元素 lower -> -(lower), 最大元素 upper-1 -> -(upper-1).
// 所以新弧 = [-(upper-1), -(lower)+1) = [1-upper, 1-lower).
I32Range I32Range::negate() const noexcept {
  if (isUnknown())
    return unknown();
  if (isEmpty())
    return empty();
  if (isFullSet())
    return full();
  return fromHalfOpen(1U - upper_, 1U - lower_);
}

// sub: 利用 sub(x) = add(x.negate()) 的代数性质.
I32Range I32Range::sub(const I32Range &other) const noexcept {
  return add(other.negate());
}

// multiply: 乘积集合一般不是单弧. 保守做法: 要求两操作数 signed 连续,
// 用四角乘积的数学 hull 反推 i32 环形覆盖弧. signed 跨界则无法安全建模 -> full.
I32Range I32Range::multiply(const I32Range &other) const noexcept {
  if (isEmpty() || other.isEmpty())
    return empty();
  // 特判: 任一操作数为常量 0 -> 结果精确为 0 (即使另一侧是 unknown)
  const auto leftConstant = getSingleSigned();
  const auto rightConstant = other.getSingleSigned();
  if ((leftConstant && *leftConstant == 0) ||
      (rightConstant && *rightConstant == 0))
    return constant(0);
  if (isUnknown() || other.isUnknown())
    return unknown();
  if (isFullSet() || other.isFullSet())
    return full();

  // 需要 signed 连续弧才能安全取四角
  const auto left = signedBounds();
  const auto right = other.signedBounds();
  if (!left || !right)
    return full(); // signed 跨界, 无法安全建模

  // 四角乘积 (用 i64 避免 i32 溢出)
  const i64 products[] = {
      static_cast<i64>(left->min) * right->min,
      static_cast<i64>(left->min) * right->max,
      static_cast<i64>(left->max) * right->min,
      static_cast<i64>(left->max) * right->max,
  };
  const auto [minIt, maxIt] =
      std::minmax_element(std::begin(products), std::end(products));
  // 数学 hull 跨度 >= 2^32 则 i32 环上结果可能覆盖全集
  const u64 span = static_cast<u64>(*maxIt - *minIt);
  if (span + 1 >= I32Cardinality)
    return full();

  // 每个乘积的 i32 映像落在弧 [pmin mod 2^32, (pmax+1) mod 2^32) 内
  const u32 lower = static_cast<u32>(*minIt);
  return fromHalfOpen(lower, lower + static_cast<u32>(span + 1));
}

// sdiv: 有符号除法 (C 向零截断). 不在环上做 (signed division 不是环同态).
// 先要求操作数 signed 连续, 再排除两个陷阱:
//   1) 除数区间可能含 0 -> 运行时可能除零 (trap). 直接退化 full.
//   2) INT_MIN / -1 是唯一会溢出 i32 的有符号除法. 结果数学值 2^31 越界,
//      保守退化 full, 绝不在宿主侧执行该 UB 除法.
// 排除陷阱后, 除数不跨 0 时 x/y 对每个变量 "角单调", 极值必在四角取得.
// 用 i64 执行四角除法, 得到 signed 数学商的包络, 再交给 fromSigned clamp.
I32Range I32Range::sdiv(const I32Range &other) const noexcept {
  if (isEmpty() || other.isEmpty())
    return empty();
  if (isUnknown() || other.isUnknown())
    return unknown();

  const auto dividend = signedBounds();
  const auto divisor = other.signedBounds();
  if (!dividend || !divisor)
    return full(); // signed 跨界, 无法安全推数学商
  // 陷阱防御 1: 除数不含 0 <=> 恒正(min>=1) 或 恒负(max<=-1)
  if (!(divisor->min >= 1 || divisor->max <= -1))
    return full();
  // 陷阱防御 2: INT_MIN / -1 溢出
  if (dividend->min == std::numeric_limits<i32>::min() && divisor->min <= -1 &&
      divisor->max >= -1)
    return full();

  // 四角除法 (已排除除零和 INT_MIN/-1, 不会触发宿主 C++ UB)
  const i64 quotients[] = {
      static_cast<i64>(dividend->min) / divisor->min,
      static_cast<i64>(dividend->min) / divisor->max,
      static_cast<i64>(dividend->max) / divisor->min,
      static_cast<i64>(dividend->max) / divisor->max,
  };
  const auto [minIt, maxIt] =
      std::minmax_element(std::begin(quotients), std::end(quotients));
  return fromSigned(*minIt, *maxIt);
}

// srem: 有符号取余 (C: 余数符号随被除数, |r| < |divisor|).
// 除数可能含 0 或可能触发 INT_MIN%-1 时退化 full.
// 否则按被除数符号给出安全外壳区间:
//   被除数恒非负 -> r in [0, limit]; 恒非正 -> r in [-limit, 0];
//   未知 -> [-limit, limit].
// 这只是值域外壳, 不尝试表达离散同余/同模排除事实.
I32Range I32Range::srem(const I32Range &other) const noexcept {
  if (isEmpty() || other.isEmpty())
    return empty();
  if (isUnknown() || other.isUnknown())
    return unknown();

  const auto dividend = signedBounds();
  const auto divisor = other.signedBounds();
  if (!dividend || !divisor)
    return full();
  // 同 sdiv: 除数可能含 0 或可能触发 INT_MIN%-1 -> 退化 full
  if (!(divisor->min >= 1 || divisor->max <= -1))
    return full();
  if (dividend->min == std::numeric_limits<i32>::min() && divisor->min <= -1 &&
      divisor->max >= -1)
    return full();

  // |divisor| 的最大值; 用 i64 避免 |INT_MIN| 溢出
  const auto magnitude = [](i32 value) noexcept -> i64 {
    return value < 0 ? -static_cast<i64>(value) : static_cast<i64>(value);
  };
  // 余数绝对值上界 = max(|divisor_min|, |divisor_max|) - 1
  const i64 limit =
      std::max(magnitude(divisor->min), magnitude(divisor->max)) - 1;
  // 按被除数符号确定余数符号
  if (dividend->min >= 0)
    return fromSigned(0, limit); // 被除数恒非负
  if (dividend->max <= 0)
    return fromSigned(-limit, 0);   // 被除数恒非正
  return fromSigned(-limit, limit); // 被除数符号未知
}

} // namespace svm::ir
