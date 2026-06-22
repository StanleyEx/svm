/// @file ScalarFacts.cpp
/// @brief 统一标量事实格的实现: KnownBits 位级传递规则,
/// KnownBits<->I32Range投影, Congruence 模运算,
/// ScalarFactBundle 规范化闭包, 谓词比较原语.
#include "ScalarFacts.h"
#include "Utils.h"

#include <limits>
#include <optional>

namespace svm::ir {
namespace {

/// 同余模数上限 超过此值的模数退化为未知事实以避免溢出
constexpr u64 kMaxSupportedModulus = u64{1} << 63;

/// 构造高 count 位置 1 的掩码, 即 [width-count, width-1] 区间.
u64 highMask(u32 count, u32 width) noexcept {
  if (count == 0 || width == 0)
    return 0;
  if (count >= width)
    return KnownBits::maskOfW(width);
  return (KnownBits::maskOfW(width) << (width - count)) &
         KnownBits::maskOfW(width);
}

/// 欧几里得最大公因数 服务于同余交汇和同余组合
u64 gcd(u64 left, u64 right) noexcept {
  while (right != 0) {
    const u64 remainder = left % right;
    left = right;
    right = remainder;
  }
  return left;
}

/// 检查两个 KnownBits 是否都有效且位宽相同 作为位级二元运算的前置检查
bool compatibleWidths(const KnownBits &left, const KnownBits &right) noexcept {
  return left.valid() && right.valid() && left.width == right.width;
}

/// 同值 KnownBits 交汇: 合并两份关于同一值的位事实, 取并集 (更精确)
/// 两份事实都是对同一值的统一描述, 所以可以简单合并
/// 若合并后冲突 (同一位既已知 0 又已知 1), 说明上游有错误, 返回无效事实
KnownBits mergeKnownBits(const KnownBits &left,
                         const KnownBits &right) noexcept {
  if (!left.valid())
    return right;
  if (!right.valid())
    return left;
  if (left.width != right.width)
    return KnownBits::invalid();
  KnownBits result = KnownBits::unknown(left.width);
  result.knownZero = (left.knownZero | right.knownZero) & result.mask();
  result.knownOne = (left.knownOne | right.knownOne) & result.mask();
  return result.conflict() ? KnownBits::invalid() : result;
}

/// 若 KnownBits 已经覆盖全部有效位, 返回其常量值的有符号解释
/// 该判断只服务 canonicalizeBundle 的闭包补全, 不再作为 KnownBits
/// 的公共接口暴露 公开成 KnownBits::getConstant* 会让其它代码绕过
/// 值域/同余/非零事实的统一规范化流程, 重新形成多套常量事实出口
std::optional<i64> constantFromKnownBits(const KnownBits &bits) noexcept {
  if (!bits.valid() || (bits.knownZero | bits.knownOne) != bits.mask())
    return std::nullopt;
  u64 value = bits.knownOne & bits.mask();
  // 符号扩展: 若符号位为 1 且位宽不足 64 位, 需要将高位填充 1
  const u64 sign = u64{1} << (bits.width - 1);
  if ((value & sign) != 0 && bits.width < 64)
    value |= ~bits.mask();
  if (value <= static_cast<u64>(std::numeric_limits<i64>::max()))
    return static_cast<i64>(value);
  return -static_cast<i64>(~value) - 1;
}

/// 把 KnownBits 反投影为可靠的 i32 值集合超集近似
/// 用未知位全 0 / 全 1 得到无符号包络弧 [umin, umax]
/// 这对最高位已知 0 所导出的非负值域等场景能给出有用收窄
/// 位模式不连续时仍只是安全上界 绝不生成欠近似
/// 只在摘要规范化内使用 避免向外暴露独立事实查询路径
I32Range knownBitsToRange(const KnownBits &bits) noexcept {
  if (!bits.valid() || bits.width < 32)
    return I32Range::unknown();
  constexpr u64 I32Mask = 0xffffffffULL;
  const u64 knownZero = bits.knownZero & I32Mask;
  const u64 knownOne = bits.knownOne & I32Mask;
  const u64 unknown = (~(knownZero | knownOne)) & I32Mask;
  const u32 min = static_cast<u32>(knownOne);
  const u32 max = static_cast<u32>(knownOne | unknown);
  return I32Range::fromUnsigned(min, max);
}

/// 同值同余组合: 尝试将新入的同余事实合并到当前事实中
/// 两者皆为同一值的真事实, 故必相容; 返回 false 表示矛盾 (上游错误)
/// 规则:
///   - 常量 vs 常量: 必须相等.
///   - 常量 vs 模同余: 常量必须满足模同余.
///   - 模同余 vs 模同余: 取 GCD 并验证余数相容性.
bool combineCongruence(Congruence &current,
                       const Congruence &incoming) noexcept {
  const CongruenceConjunction conjunction =
      conjoinCongruence(current, incoming);
  if (conjunction.contradiction)
    return false;
  current = conjunction.value;
  return true;
}

} // namespace

u64 unsignedMagnitude(i64 value) noexcept {
  return value < 0 ? u64{0} - static_cast<u64>(value) : static_cast<u64>(value);
}

bool isI32WrappingInvariantModulus(u64 modulus) noexcept {
  constexpr u64 kI32Modulus = u64{1} << 32;
  return modulus >= 2 && modulus <= kI32Modulus &&
         (modulus & (modulus - 1)) == 0;
}

u64 normalizedModulo(i64 value, u64 modulus) noexcept {
  if (modulus == 0)
    return static_cast<u64>(value);
  const u64 magnitude = unsignedMagnitude(value);
  const u64 residue = magnitude % modulus;
  return value < 0 && residue != 0 ? modulus - residue : residue;
}

i64 floorMod(i64 value, u64 modulus) noexcept {
  if (modulus == 0)
    return value;
  const u64 normalized = normalizedModulo(value, modulus);
  VERIFY(normalized <= static_cast<u64>(INT64_MAX));
  return static_cast<i64>(normalized);
}

u64 addModulo(u64 left, u64 right, u64 modulus) noexcept {
  VERIFY(modulus != 0);
  left %= modulus;
  right %= modulus;
  return left >= modulus - right ? left - (modulus - right) : left + right;
}

u64 multiplyModulo(u64 left, u64 right, u64 modulus) noexcept {
  VERIFY(modulus != 0);
  u64 result = 0;
  left %= modulus;
  right %= modulus;
  while (right != 0) {
    if ((right & 1U) != 0)
      result = addModulo(result, left, modulus);
    right >>= 1U;
    if (right != 0)
      left = addModulo(left, left, modulus);
  }
  return result;
}

bool modInverse(i64 value, u64 modulus, i64 &inverse) noexcept {
  if (modulus <= 1 || modulus > kMaxSupportedModulus)
    return false;
  u64 oldR = modulus;
  u64 currentR = normalizedModulo(value, modulus);
  u64 oldCoefficient = 0;
  u64 currentCoefficient = 1;
  while (currentR != 0) {
    const u64 quotient = oldR / currentR;
    const u64 nextR = oldR % currentR;
    const u64 product = multiplyModulo(quotient, currentCoefficient, modulus);
    const u64 nextCoefficient = oldCoefficient >= product
                                    ? oldCoefficient - product
                                    : modulus - (product - oldCoefficient);
    oldR = currentR;
    currentR = nextR;
    oldCoefficient = currentCoefficient;
    currentCoefficient = nextCoefficient;
  }
  if (oldR != 1)
    return false;
  VERIFY(oldCoefficient <= static_cast<u64>(INT64_MAX));
  inverse = static_cast<i64>(oldCoefficient);
  return true;
}

//  KnownBits 位级传递规则 (精确格运算)
//
//  逐位真值表 (z=已知 0, o=已知 1, ?=未知):
//    AND: 任一已知 0 => 0; 两者已知 1 => 1.
//    OR : 任一已知 1 => 1; 两者已知 0 => 0.
//    XOR: (z,z)|(o,o) => 0; (z,o)|(o,z) => 1; 含 ? => ?.

KnownBits kbAnd(const KnownBits &left, const KnownBits &right) noexcept {
  if (!compatibleWidths(left, right))
    return KnownBits::invalid();
  KnownBits result = KnownBits::unknown(left.width);
  // 任一 0 => 0
  result.knownZero = (left.knownZero | right.knownZero) & result.mask();
  // 都 1 => 1
  result.knownOne = (left.knownOne & right.knownOne) & result.mask();
  return result;
}

KnownBits kbOr(const KnownBits &left, const KnownBits &right) noexcept {
  if (!compatibleWidths(left, right))
    return KnownBits::invalid();
  KnownBits result = KnownBits::unknown(left.width);
  // 任一 1 => 1
  result.knownOne = (left.knownOne | right.knownOne) & result.mask();
  // 都 0 => 0
  result.knownZero = (left.knownZero & right.knownZero) & result.mask();
  return result;
}

KnownBits kbXor(const KnownBits &left, const KnownBits &right) noexcept {
  if (!compatibleWidths(left, right))
    return KnownBits::invalid();
  KnownBits result = KnownBits::unknown(left.width);
  result.knownZero =
      ((left.knownZero & right.knownZero) | (left.knownOne & right.knownOne)) &
      result.mask();
  result.knownOne =
      ((left.knownZero & right.knownOne) | (left.knownOne & right.knownZero)) &
      result.mask();
  return result;
}

// 位移传递规则: 语义按低 W 位结果定义
// 移位量 >= 位宽时, 所有有效位都被移出, 结果低 W 位全为 0
// 这里不能让宿主 C++ 执行 x << 32/64, 否则会触发 UB
// 因此先判 amount >= width, 再做真正的位移

KnownBits kbShl(const KnownBits &value, u32 amount) noexcept {
  if (!value.valid())
    return KnownBits::invalid();
  KnownBits result = KnownBits::unknown(value.width);
  if (amount >= value.width) {
    result.knownZero = result.mask(); // 全移出 => 低 W 位确定 0
    return result;
  }
  result.knownOne = (value.knownOne << amount) & result.mask();
  result.knownZero = ((value.knownZero << amount) |
                      KnownBits::maskOfW(amount)) & // 低 amount 位补 0
                     result.mask();
  return result;
}

KnownBits kbLShr(const KnownBits &value, u32 amount) noexcept {
  if (!value.valid())
    return KnownBits::invalid();
  KnownBits result = KnownBits::unknown(value.width);
  if (amount >= value.width) {
    result.knownZero = result.mask();
    return result;
  }
  result.knownOne = value.knownOne >> amount;
  result.knownZero = (value.knownZero >> amount) |
                     highMask(amount, value.width); // 高 amount 位补 0
  return result;
}

/// 算术右移: 高位按符号位传播
/// 符号位未知时, 新高位保持未知 (不假设符号)
KnownBits kbAShr(const KnownBits &value, u32 amount) noexcept {
  if (!value.valid())
    return KnownBits::invalid();
  if (amount == 0)
    return value;

  KnownBits result = KnownBits::unknown(value.width);
  const bool signZero = value.signBitKnownZero();
  const bool signOne = ((value.knownOne >> (value.width - 1)) & 1U) != 0;
  // amount >= width: 所有位由符号位填充
  if (amount >= value.width) {
    if (signZero)
      result.knownZero = result.mask();
    if (signOne)
      result.knownOne = result.mask();
    return result;
  }
  // 正常移位: 原事实右移 + 符号位往高位传播
  result.knownOne = (value.knownOne >> amount) |
                    (signOne ? highMask(amount, value.width) : 0);
  result.knownZero = (value.knownZero >> amount) |
                     (signZero ? highMask(amount, value.width) : 0);
  return result;
}

//  KnownBits <-> I32Range 投影
/// 从 i32 值集合提取可靠位事实
/// 单点集合 => 全位已知; 无符号连续弧 => 取 min^max 的公共前缀位
/// 注意只从 unsignedBounds 提取; 跨越有符号边界的集合无法安全推出高位模式
KnownBits rangeToKnownBits(const I32Range &range) noexcept {
  if (range.isUnknown() || range.isEmpty())
    return KnownBits::invalid();
  if (const auto value = range.getSingleSigned())
    return KnownBits::constant(static_cast<u32>(*value), 32);

  KnownBits bits = KnownBits::unknown(32);
  if (const auto bounds = range.unsignedBounds()) {
    // min ^ max 的有效位数以上的位, min 和 max 必然相同, 可确定.
    const u32 differing = bounds->min ^ bounds->max;
    const u64 commonMask =
        bits.mask() & ~KnownBits::maskOfW(bitWidth(differing));
    bits.knownOne = static_cast<u64>(bounds->min) & commonMask;
    bits.knownZero = (~static_cast<u64>(bounds->min)) & commonMask;
  }
  return bits;
}

/// 构造规范化同余 x === r (mod m), 将 r 规范化到 [0, m).
/// m == 0 => 常量; m == 1 => 未知; m > kMaxSupportedModulus => 未知
/// (防溢出).
Congruence Congruence::modulo(u64 modulus, i64 remainder) noexcept {
  if (modulus == 0)
    return constant(remainder);
  if (modulus == 1)
    return unknown();
  if (modulus > kMaxSupportedModulus)
    return unknown();
  const u64 normalized = normalizedModulo(remainder, modulus);
  return normalized <= static_cast<u64>(INT64_MAX)
             ? Congruence{modulus, static_cast<i64>(normalized), true}
             : unknown();
}

bool Congruence::impliesResidue(u64 modulus, i64 residue) const noexcept {
  if (!valid || isUnknown() || modulus <= 1 || modulus > kMaxSupportedModulus)
    return false;
  if (isConstant())
    return normalizedModulo(rem, modulus) == normalizedModulo(residue, modulus);
  return mod % modulus == 0 &&
         normalizedModulo(rem, modulus) == normalizedModulo(residue, modulus);
}

CongruenceConjunction conjoinCongruence(const Congruence &left,
                                        const Congruence &right) noexcept {
  if (!left.valid)
    return {right, false};
  if (!right.valid || right.isUnknown())
    return {left, false};
  if (left.isUnknown())
    return {right, false};
  if (left.isConstant() || right.isConstant()) {
    const Congruence &constant = left.isConstant() ? left : right;
    const Congruence &other = left.isConstant() ? right : left;
    const bool matches = other.isConstant()
                             ? constant.rem == other.rem
                             : other.impliesResidue(other.mod, constant.rem);
    return {matches ? constant : Congruence::unknown(), !matches};
  }

  const u64 common = gcd(left.mod, right.mod);
  const u64 difference = left.rem >= right.rem
                             ? static_cast<u64>(left.rem - right.rem)
                             : static_cast<u64>(right.rem - left.rem);
  if (difference % common != 0)
    return {Congruence::unknown(), true};

  const u64 rightReduced = right.mod / common;
  if (left.mod > kMaxSupportedModulus / rightReduced)
    return {left.mod >= right.mod ? left : right, false};
  const u64 combinedModulus = left.mod * rightReduced;
  if (rightReduced == 1)
    return {Congruence::modulo(combinedModulus, left.rem), false};

  i64 inverse = 0;
  if (!modInverse(static_cast<i64>((left.mod / common) % rightReduced),
                  rightReduced, inverse))
    return {Congruence::unknown(), false};
  u64 scaledDifference = (difference / common) % rightReduced;
  if (right.rem < left.rem && scaledDifference != 0)
    scaledDifference = rightReduced - scaledDifference;
  const u64 multiplier =
      multiplyModulo(scaledDifference, static_cast<u64>(inverse), rightReduced);
  const u64 solution =
      (static_cast<u64>(left.rem) + left.mod * multiplier) % combinedModulus;
  return {Congruence::modulo(combinedModulus, static_cast<i64>(solution)),
          false};
}

/// 同余格交汇: x === r1 (mod gcd(m1, m2, |r1-r2|)).
/// 两侧都无效或未知时返回未知事实, 不编码 CRT 多解集合.
Congruence meetCongruence(const Congruence &left,
                          const Congruence &right) noexcept {
  if (!left.valid || !right.valid || left.isUnknown() || right.isUnknown())
    return Congruence::unknown();
  const u64 leftBits = static_cast<u64>(left.rem);
  const u64 rightBits = static_cast<u64>(right.rem);
  const u64 difference =
      left.rem >= right.rem ? leftBits - rightBits : rightBits - leftBits;
  const u64 modulus = gcd(gcd(left.mod, right.mod), difference);
  return Congruence::modulo(modulus, left.rem);
}

MathBounds MathBounds::of(i64 min, i64 max, NoWrapInfo proof) noexcept {
  return min <= max && proof.proven() ? MathBounds{true, min, max, proof}
                                      : none();
}

//  ScalarFactBundle 规范化闭包
//
// 规范化管线按以下顺序执行, 保证摘要内部自洽:
//   1. 位宽和掩码规整
//   2. 已知零值约束合并
//   3. 值域 -> KnownBits 提取
//   4. congruence -> KnownBits 低位提取 (2^k 模数回绕安全)
//   5. KnownBits -> congruence 反向提取
//   6. KnownBits -> 值域回投影 (超集包络与现有值域取交)
//   7. 多源非零事实推导 + 矛盾检测
//   8. 最终掩码清理
void canonicalizeBundle(ScalarFactBundle &bundle) noexcept {
  if (!bundle.valid)
    return;
  // 矛盾时清空整个摘要
  const auto fail = [&bundle]() noexcept { bundle = {}; };
  if (bundle.bitWidth == 0 || bundle.bitWidth > 64) {
    return fail();
  }

  // 第 1 阶段: 位宽和掩码规整
  // width=0 表示没有位事实, 不参与后续交汇;
  // width 非 bitWidth 时只允许在自己的掩码内声明事实;
  // 若同一位同时已知为零和已知为一, 说明多个来源给出矛盾事实
  if (bundle.knownBits.width != 0) {
    if (bundle.knownBits.width != bundle.bitWidth) {
      bundle.knownBits = KnownBits::unknown(bundle.bitWidth);
    } else {
      const u64 mask = bundle.knownBits.mask();
      bundle.knownBits.knownZero &= mask;
      bundle.knownBits.knownOne &= mask;
      if (bundle.knownBits.conflict()) {
        return fail();
      }
    }
  }

  // 第 2 阶段: 已知零值约束合并
  // 若已知值为零, 将零值常量事实合并到所有域
  if (bundle.hasNonZero && !bundle.nonzero) {
    const KnownBits zeroBits = KnownBits::constant(0, bundle.bitWidth);
    const KnownBits merged = mergeKnownBits(bundle.knownBits, zeroBits);
    if (!merged.valid() ||
        !combineCongruence(bundle.congruence, Congruence::constant(0))) {
      return fail();
    }
    bundle.knownBits = merged;
    bundle.range = bundle.range.intersectWith(I32Range::constant(0));
  }

  if (bundle.range.isEmpty()) {
    return fail();
  }

  // 第 3 阶段: 值域 -> KnownBits 提取
  // 对 32 位及以上的值, 从值域提取位事实并合并到现有 KnownBits
  if (bundle.bitWidth >= 32) {
    if (bundle.bitWidth == 32 && bundle.hasNonZero && bundle.nonzero)
      bundle.range = bundle.range.intersectWith(I32Range::notEqual(0));
    if (bundle.range.isEmpty()) {
      return fail();
    }

    const KnownBits lowBits = rangeToKnownBits(bundle.range);
    if (lowBits.valid()) {
      KnownBits rangeBits = KnownBits::unknown(bundle.bitWidth);
      rangeBits.knownZero = lowBits.knownZero;
      rangeBits.knownOne = lowBits.knownOne;
      const KnownBits merged = mergeKnownBits(bundle.knownBits, rangeBits);
      if (!merged.valid()) {
        return fail();
      }
      bundle.knownBits = merged;
    }
  }

  // 第 4 阶段: congruence -> KnownBits
  // 常量同余: 直接写入全部位
  // 2^k 模同余: 低 k 位写入 KnownBits (2^k | 2^32, 回绕安全)
  if (bundle.congruence.isConstant()) {
    const KnownBits constantBits = KnownBits::constant(
        static_cast<u64>(bundle.congruence.rem), bundle.bitWidth);
    const KnownBits merged = mergeKnownBits(bundle.knownBits, constantBits);
    if (!merged.valid()) {
      return fail();
    }
    bundle.knownBits = merged;
    if (bundle.bitWidth >= 32) {
      const auto value = static_cast<u32>(bundle.congruence.rem);
      const i64 signedValue =
          value <= static_cast<u32>(std::numeric_limits<i32>::max())
              ? static_cast<i64>(value)
              : static_cast<i64>(value) - (i64{1} << 32);
      bundle.range = bundle.range.intersectWith(
          I32Range::constant(static_cast<i32>(signedValue)));
    }
  } else if (bundle.congruence.isModulo() &&
             (bundle.congruence.mod & (bundle.congruence.mod - 1)) == 0) {
    // 2^k 模同余: 将低 k 位的余数写入 KnownBits
    u32 knownCount = 0;
    u64 modulus = bundle.congruence.mod;
    while (modulus > 1 && knownCount < bundle.bitWidth) {
      ++knownCount;
      modulus >>= 1;
    }
    KnownBits congruenceBits = KnownBits::unknown(bundle.bitWidth);
    const u64 mask = KnownBits::maskOfW(knownCount);
    congruenceBits.knownOne = static_cast<u64>(bundle.congruence.rem) & mask;
    congruenceBits.knownZero = (~congruenceBits.knownOne) & mask;
    const KnownBits merged = mergeKnownBits(bundle.knownBits, congruenceBits);
    if (!merged.valid()) {
      return fail();
    }
    bundle.knownBits = merged;
  }

  if (bundle.range.isEmpty()) {
    return fail();
  }

  // 第 5 阶段: KnownBits -> congruence 反向提取
  // 全位已知 => 升级为精确常量同余
  // 低 k 位连续全已知 => x === rem (mod 2^k)
  // 同余交汇放在公共规范化过程中, MIR 不再复制这段逻辑
  if (bundle.knownBits.valid()) {
    if (const auto constant = constantFromKnownBits(bundle.knownBits)) {
      if (!combineCongruence(bundle.congruence,
                             Congruence::constant(*constant))) {
        return fail();
      }
    } else {
      u32 knownCount = 0;
      const u64 known = bundle.knownBits.knownZero | bundle.knownBits.knownOne;
      while (knownCount < bundle.bitWidth && ((known >> knownCount) & 1U) != 0)
        ++knownCount;
      if (knownCount != 0 && knownCount < 64) {
        const u64 modulus = u64{1} << knownCount;
        const i64 remainder =
            static_cast<i64>(bundle.knownBits.knownOne & (modulus - 1));
        if (!combineCongruence(bundle.congruence,
                               Congruence::modulo(modulus, remainder))) {
          return fail();
        }
      }
    }
  }

  // 第 6 阶段: KnownBits -> 值域回投影
  // 取超集包络与现有值域的交集, 只收窄不扩大
  // 若 KnownBits 自相矛盾则跳过, 避免把错误扩散
  if (bundle.bitWidth >= 32 && bundle.knownBits.valid()) {
    bundle.range =
        bundle.range.intersectWith(knownBitsToRange(bundle.knownBits));
    if (bundle.range.isEmpty()) {
      return fail();
    }
  }

  // 第 7 阶段: 多源非零事实推导 + 矛盾检测
  // 从 KnownBits (某位已知 1) / 值域 (不含 0) / 同余 (常量非 0) 推导非零
  // 反之推导为零. 若与已有零性结论矛盾则清空摘要
  const bool derivedNonZero =
      bundle.knownBits.knownNonZero() ||
      (bundle.bitWidth >= 32 && !bundle.range.isUnknown() &&
       !bundle.range.containsSigned(0)) ||
      (bundle.congruence.isConstant() && bundle.congruence.rem != 0);
  const auto knownConstant = constantFromKnownBits(bundle.knownBits);
  const bool derivedZero =
      (knownConstant && *knownConstant == 0) ||
      (bundle.congruence.isConstant() && bundle.congruence.rem == 0) ||
      (bundle.bitWidth >= 32 && bundle.range == I32Range::constant(0));
  if (derivedNonZero) {
    if (bundle.hasNonZero && !bundle.nonzero) {
      return fail(); // 矛盾: 推导非零但已知为零
    }
    bundle.hasNonZero = true;
    bundle.nonzero = true;
  } else if (derivedZero) {
    if (bundle.hasNonZero && bundle.nonzero) {
      return fail(); // 矛盾: 推导为零但已知非零
    }
    bundle.range = bundle.range.intersectWith(I32Range::constant(0));
    if (bundle.range.isEmpty()) {
      return fail();
    }
    bundle.hasNonZero = true;
    bundle.nonzero = false;
  }

  // 第 8 阶段: 最终掩码清理
  if (bundle.knownBits.valid()) {
    bundle.knownBits.knownZero &= bundle.knownBits.mask();
    bundle.knownBits.knownOne &= bundle.knownBits.mask();
  }
}

//  谓词比较原语
//
// 有符号/无符号比较只消费对应投影端点. 环形区间跨过符号位或
// 无符号 0 边界时, 端点投影会返回 nullopt; 此时必须返回 Unknown
// 绝不能把集合粗暴展开成 [INT_MIN,INT_MAX] 再参与大小判断
// SGT/SGE/UGT/UGE 通过交换操作数归约到 SLT/SLE/ULT/ULE

KnownBool evalIntCompare(IntPred predicate, const I32Range &left,
                         const I32Range &right) noexcept {
  if (left.isEmpty() || right.isEmpty())
    return KnownBool::Unknown;

  const auto signedLeft = left.signedBounds();
  const auto signedRight = right.signedBounds();
  const auto unsignedLeft = left.unsignedBounds();
  const auto unsignedRight = right.unsignedBounds();
  switch (predicate) {
  // 有符号比较
  case IntPred::SLT:
  case IntPred::SLE:
    if (signedLeft && signedRight) {
      const bool inclusive = predicate == IntPred::SLE;
      if (inclusive ? signedLeft->max <= signedRight->min
                    : signedLeft->max < signedRight->min)
        return KnownBool::AlwaysTrue;
      if (inclusive ? signedLeft->min > signedRight->max
                    : signedLeft->min >= signedRight->max)
        return KnownBool::AlwaysFalse;
    }
    break;
  case IntPred::SGT: // x > y <=> y < x
    return evalIntCompare(IntPred::SLT, right, left);
  case IntPred::SGE:
    return evalIntCompare(IntPred::SLE, right, left);
  // 无符号比较
  case IntPred::ULT:
  case IntPred::ULE:
    if (unsignedLeft && unsignedRight) {
      const bool inclusive = predicate == IntPred::ULE;
      if (inclusive ? unsignedLeft->max <= unsignedRight->min
                    : unsignedLeft->max < unsignedRight->min)
        return KnownBool::AlwaysTrue;
      if (inclusive ? unsignedLeft->min > unsignedRight->max
                    : unsignedLeft->min >= unsignedRight->max)
        return KnownBool::AlwaysFalse;
    }
    break;
  case IntPred::UGT:
    return evalIntCompare(IntPred::ULT, right, left);
  case IntPred::UGE:
    return evalIntCompare(IntPred::ULE, right, left);
  // 相等/不等: 集合不相交 / 同一单点集合
  case IntPred::EQ:
  case IntPred::NE:
    if (left.isSingleElement() && right.isSingleElement()) {
      const bool equal = left == right;
      return equal == (predicate == IntPred::EQ) ? KnownBool::AlwaysTrue
                                                 : KnownBool::AlwaysFalse;
    }
    if (left.intersectWith(right).isEmpty())
      return predicate == IntPred::EQ ? KnownBool::AlwaysFalse
                                      : KnownBool::AlwaysTrue;
    break;
  }
  return KnownBool::Unknown;
}

} // namespace svm::ir
