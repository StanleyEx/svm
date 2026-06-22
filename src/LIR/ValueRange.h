#ifndef LIR_VALUE_RANGE_H
#define LIR_VALUE_RANGE_H

/// @file ValueRange.h
/// @brief I32Range -- i32 值集合上的 ConstantRange 风格环形区间
///
/// i32 运行语义是模 2^32 的补码回绕; 值域事实的底层表示必须能直接描述这个环上的
/// 值集合, 而非先落入普通 signed 闭区间再做出口转换. 普通闭区间只能表达
/// `min <= x <= max` 这类不跨界的连续段, 无法表达:
///
///   * 横跨有符号符号位的集合, 例如 {INT_MAX, INT_MIN} = 无符号 {0x7fffffff,
///     0x80000000}, 普通闭区间只能退化成 full, 丢光精度;
///   * 不等事实 `x != C`, 在 i32 上其精确补集恰好是一条环形弧 [C+1, C);
///   * add/sub 跨过 signed/unsigned 边界后仍然精确的回绕单点.
///
///  表示法 (Representation) -- 与 LLVM ConstantRange 同构
///
/// 把 2^32 个 i32 值看成一个环 (0,1,...,0xffffffff, 回到 0). 可分析到的具体集合
/// 恰好是环上一段连续弧(arc), 用半开区间[lower, upper)表示(按 mod 2^32 行走).
/// 另有两个非集合状态用于区分 "无法分析" 和 "上下文矛盾":
///
///   * Kind::Unknown                             : 分析不可用 / top.
///   * Kind::Empty                               : 空集 / 路径事实矛盾.
///   * Kind::Set && lower == upper                : 全集 (整个 i32 域).
///   * Kind::Set && lower != upper && lower < upper : 不回绕弧.
///   * Kind::Set && lower != upper && lower > upper : 回绕弧.
///
/// Unknown 与 full 严格区分: unknown 代表 "没有事实可用", full 代表 "事实可用但
/// 覆盖全集". 二者在 Phi union 中行为完全不同 -- unknown 传染, full 吸收.
///
///  signed / unsigned 投影
///
/// 整数比较消费 signed 投影; 位运算/逻辑右移/mask 消费 unsigned 投影.
/// 当弧在对应视角跨界时, 投影返回 nullopt, 谓词层据此放弃推断, 而绝不把
/// 环形集合展平成不安全的普通闭区间.
///
/// signed 投影的实现技巧: 把无符号值 u 映射到 ss(u) = u + 0x80000000 (mod
/// 2^32), 则 signed 升序 <=> ss 的 unsigned 升序. "弧是否 signed 连续" 等价于
/// "弧在 ss 空间是否不回绕".

#include "Utils.h"

#include <optional>

namespace svm::ir {

/// @brief signed 投影端点对. 只有 signed 连续弧/全集才能给出;
///        sign-wrapped 集合返回 nullopt, 强制消费者意识到不能安全投影.
struct SignedBounds32 {
  i32 min; // 有符号连续弧的最小值 (signed 视角下界)
  i32 max; // 有符号连续弧的最大值 (signed 视角上界)
};

/// @brief unsigned 投影端点对. 只有不回绕弧/全集才能给出; wrapped 返回 nullopt.
struct UnsignedBounds32 {
  u32 min; // 不回绕弧的无符号最小值
  u32 max; // 不回绕弧的无符号最大值
};

/// @brief i32 模 2^32 环上的单弧值集合.
///
/// 三态: Unknown(分析不可用/top) / Empty(矛盾/不可达) / Set(有效环形集合).
/// 有效集合用半开弧 [lower_, upper_) 表示; lower_ == upper_ 时为全集.
/// 关键不变式: non-empty 且 non-full 时恒有 lower_ != upper_;
/// 单点 [C] 用 [C, C+1) 表示, 即使 C == 0xffffffff 也满足 lower_ != upper_.
class I32Range {
public:
  I32Range() noexcept = default;

  /// @brief 分析不可用 (top). 与全集严格区分: unknown 在 Phi union 中传染,
  ///        全集在 union 中吸收. 消费者不得据 unknown 做任何折叠.
  static I32Range unknown() noexcept { return {}; }
  /// @brief 空集: 当前查询上下文事实自相矛盾 (路径不可达).
  static I32Range empty() noexcept {
    I32Range range;
    range.kind_ = Kind::Empty;
    return range;
  }
  /// @brief 全集: i32 整个域 (已知但未收窄). lower_ == upper_ == 0.
  static I32Range full() noexcept {
    I32Range range;
    range.kind_ = Kind::Set;
    return range;
  }
  /// @brief 单点常量 [v, v]. 内部用 [v, v+1) 表示,
  /// mod 2^32 保证 lower_ != upper_.
  static I32Range constant(i32 value) noexcept {
    I32Range range;
    range.kind_ = Kind::Set;
    range.lower_ = static_cast<u32>(value);
    range.upper_ = range.lower_ + 1U;
    return range;
  }
  /// @brief 由有符号闭区间 [min, max] 构造 signed 连续弧.
  /// @note 端点允许临时越出 i32 (使用 i64), 函数会 clamp 到 i32 域;
  ///       clamp 扩大而非缩小集合, 因此保持 sound.
  static I32Range fromSigned(i64 min, i64 max) noexcept;
  /// @brief 由无符号闭区间 [min, max] 构造不回绕弧.
  static I32Range fromUnsigned(u32 min, u32 max) noexcept {
    if (min > max)
      return empty();
    return min == 0 && max == UINT32_MAX ? full() : fromHalfOpen(min, max + 1U);
  }
  /// @brief 直接由半开弧 [lower, upper) 构造 (供内部 transfer 使用).
  ///        lower == upper 时视为全集, 符合环形表示的不变式.
  static I32Range fromHalfOpen(u32 lower, u32 upper) noexcept {
    if (lower == upper)
      return full();
    I32Range range;
    range.kind_ = Kind::Set;
    range.lower_ = lower;
    range.upper_ = upper;
    return range;
  }
  /// @brief `x != C` 的精确补集: 在 i32 环上恰为单环形弧 [C+1, C).
  ///        覆盖除 C 以外全部 2^32-1 个值. 能穿过 add/sub 等环形 transfer 传播.
  static I32Range notEqual(i32 value) noexcept {
    const u32 bits = static_cast<u32>(value);
    return fromHalfOpen(bits + 1U, bits);
  }

  bool isUnknown() const noexcept { return kind_ == Kind::Unknown; }
  bool isEmpty() const noexcept { return kind_ == Kind::Empty; }
  bool isFullSet() const noexcept {
    return kind_ == Kind::Set && lower_ == upper_;
  }
  /// @brief 无符号视角是否回绕. 弧 [lower, upper) 跨过 0xffffffff->0 才算回绕;
  ///        特例 upper == 0 表示弧恰好停在边界 (clean 顶段), 不算回绕.
  bool isWrapped() const noexcept {
    return kind_ == Kind::Set && lower_ != upper_ && upper_ != 0 &&
           lower_ > upper_;
  }
  /// @brief signed 视角是否回绕 (跨符号位). 供消费者判断 signed 投影是否可用.
  bool isSignWrapped() const noexcept {
    return kind_ == Kind::Set && lower_ != upper_ && signedWrapped();
  }
  bool isSingleElement() const noexcept {
    return kind_ == Kind::Set && lower_ != upper_ && upper_ - lower_ == 1U;
  }
  std::optional<i32> getSingleSigned() const noexcept { // 获取有符号单点
    return isSingleElement() ? std::optional<i32>{i32FromBits(lower_)}
                             : std::nullopt;
  }
  /// @brief 集合基数. unknown/empty 返回 0, 全集返回 2^32. 用 u64 承载.
  u64 size() const noexcept {
    if (kind_ != Kind::Set)
      return 0;
    // mod 2^32 弧长: lower_ == upper_ 是全集, 否则 (upper_ - lower_) 落在 [1,
    // 2^32-1]
    return lower_ == upper_ ? u64{1} << 32 : static_cast<u64>(upper_ - lower_);
  }
  /// @brief 查询无符号位模式 value 是否在弧内.
  ///        不回绕弧: lower <= value < upper;
  ///        回绕弧: value >= lower || value < upper.
  bool contains(u32 value) const noexcept {
    if (kind_ != Kind::Set)
      return false;
    if (lower_ == upper_)
      return true;
    return lower_ < upper_ ? value >= lower_ && value < upper_
                           : value >= lower_ || value < upper_;
  }
  bool containsSigned(i32 value) const noexcept {
    return contains(static_cast<u32>(value));
  }

  // 投影 (谓词层/比较折叠据此判定)
  // 当弧在对应视角跨界时, 投影返回 nullopt, 绝不把环形集合展平成不安全的闭区间.

  /// @brief signed 连续弧的下端即 lower_ 的有符号解释. sign-wrapped 时返回
  /// nullopt.
  std::optional<i32> signedMin() const noexcept;
  /// @brief 末元素 upper_-1 的有符号解释. sign-wrapped 时返回 nullopt.
  std::optional<i32> signedMax() const noexcept;
  /// @brief unsigned 不回绕弧的下界. wrapped 时返回 nullopt.
  std::optional<u32> unsignedMin() const noexcept {
    if (kind_ != Kind::Set || isWrapped())
      return std::nullopt;
    return isFullSet() ? 0U : lower_;
  }
  /// @brief unsigned 不回绕弧的上界. wrapped 时返回 nullopt.
  std::optional<u32> unsignedMax() const noexcept {
    if (kind_ != Kind::Set || isWrapped())
      return std::nullopt;
    return isFullSet() ? UINT32_MAX : upper_ - 1U;
  }
  /// @brief signed 投影端点对. full -> [MIN,MAX]; signed 连续 -> 精确端点;
  ///        sign-wrapped / unknown / empty -> nullopt.
  std::optional<SignedBounds32> signedBounds() const noexcept {
    const auto min = signedMin();
    const auto max = signedMax();
    return min && max ? std::optional<SignedBounds32>{{*min, *max}}
                      : std::nullopt;
  }
  /// @brief unsigned 投影端点对. full -> [0,UINT_MAX]; 不回绕 -> 精确端点;
  ///        wrapped -> nullopt.
  std::optional<UnsignedBounds32> unsignedBounds() const noexcept {
    const auto min = unsignedMin();
    const auto max = unsignedMax();
    return min && max ? std::optional<UnsignedBounds32>{{*min, *max}}
                      : std::nullopt;
  }

  bool operator==(const I32Range &other) const noexcept {
    return kind_ == other.kind_ &&
           (kind_ != Kind::Set ||
            (lower_ == other.lower_ && upper_ == other.upper_));
  }
  bool operator!=(const I32Range &other) const noexcept {
    return !(*this == other);
  }

  // 集合运算

  /// @brief 交集. 精确交可能产生两段不相交弧; 此时返回覆盖两段的最小单弧外壳,
  ///        绝不只保留其中一段 (那会 under-approx 导致错编).
  ///        unknown 在交集中是单位元 (无约束): unknown ∩ X = X.
  I32Range intersectWith(const I32Range &other) const noexcept;
  /// @brief 并集的最小单弧覆盖 (凸包). 两弧不相交时取覆盖两者,
  /// 留下最大空隙的弧.
  ///        unknown 在并集中传染: unknown ∪ X = unknown.
  I32Range unionHullWith(const I32Range &other) const noexcept;

  // i32 环上的算术 transfer (回绕语义)
  //
  // add/sub 对 "连续弧" 是精确的: 两条弧的 Minkowski 和/差仍是一条弧,
  // 弧长为 sA + sB - 1, 跨越 signed/unsigned 边界也不退化.
  // 只有结果弧长 >= 2^32 或操作数为空/全集时才退化.

  I32Range add(const I32Range &other) const noexcept; // 环形 Minkowski 加法
  I32Range
  sub(const I32Range &other) const noexcept; // sub(x) = add(x.negate())
  I32Range negate() const noexcept;          // {-x : x in self}
  /// @brief 乘法: 一般无法用单弧精确表达, 返回覆盖所有结果的环形 hull.
  ///        操作数 signed 跨界 / 结果覆盖全集时退化 full.
  I32Range multiply(const I32Range &other) const noexcept;
  /// @brief 有符号除法 (C 向零截断). 陷阱防御: 除数可能含 0 或 INT_MIN/-1
  ///        溢出路径可能发生时退化 full (绝不在宿主侧执行 UB 除法).
  I32Range sdiv(const I32Range &other) const noexcept;
  /// @brief 有符号取余. 余数符号随被除数, |r| < |divisor|.
  ///        除数可能含 0 或 INT_MIN/-1 时退化 full.
  I32Range srem(const I32Range &other) const noexcept;

private:
  enum class Kind : u8 {
    Unknown, // 分析不可用 / top
    Empty,   // 矛盾空集 / 不可达路径
    Set,     // 有效环形集合 (含全集: lower_ == upper_)
  };

  Kind kind_ = Kind::Unknown; // 三态标志
  u32 lower_ = 0;             // 半开弧起点 (包含在集合中)
  u32 upper_ = 0;             // 半开弧终点 (不包含在集合中)

  /// @brief 判断有符号投影是否跨界.
  ///        技巧: 把 [lower, upper) 旋转到 ss 空间 (加 0x80000000),
  ///        使 signed 升序 <=> ss 的 unsigned 升序. 然后判断 ss 空间是否回绕.
  bool signedWrapped() const noexcept {
    const u32 shiftedLower = lower_ + 0x80000000U;
    const u32 shiftedUpper = upper_ + 0x80000000U;
    return shiftedUpper != 0 && shiftedLower > shiftedUpper;
  }
  /// @brief 弧的补集: complement([lower, upper)) = [upper, lower).
  ///        空集 <-> 全集互补; unknown 补 unknown.
  I32Range complement() const noexcept {
    if (isUnknown())
      return unknown();
    if (isEmpty())
      return full();
    return isFullSet() ? empty() : fromHalfOpen(upper_, lower_);
  }
  /// @brief 精确求两条 non-empty non-full 弧的交集, 结果至多两段.
  ///        算法: 旋转坐标系使 left 起点对齐到 0, 转化为标准区间问题.
  static i32 intersectArcs(u32 leftLower, u32 leftUpper, u32 rightLower,
                           u32 rightUpper, I32Range output[2]) noexcept;
  /// @brief 覆盖两条弧的最小单弧 = 补 "最大空隙".
  ///        未覆盖区域 = complement(left) ∩ complement(right), 至多 2 段空隙.
  ///        取最大空隙做补即得最紧覆盖弧.
  static I32Range coverTwo(const I32Range &left,
                           const I32Range &right) noexcept;
};

} // namespace svm::ir

#endif // LIR_VALUE_RANGE_H
