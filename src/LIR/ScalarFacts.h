#ifndef LIR_SCALAR_FACTS_H
#define LIR_SCALAR_FACTS_H

/// @file ScalarFacts.h
/// @brief 统一标量事实格
///
/// 本文件把与 SCEV 无关, LIR 与 MIR 都需要使用的纯值事实类型统一到一处.
/// 唯一依赖是 ValueRange.h (即 I32Range), 不拉 IR.h / SCEV.h, 保证可独立包含.
///
/// 统一后的域划分:
///   - I32Range:          唯一 i32 值集合域 (环形区间)
///   - KnownBits:         与值域并列的位级事实域
///   - Congruence:        单一同余事实 (对齐 / 模余)
///   - MathBounds:        数学整数域边界 (显式与 i32 值集合分离)
///   - ScalarFactBundle:  跨 IR 层传递的稳定事实摘要
///   - NoWrapInfo:        无回绕证明元数据, 不是值域模式

#include "ValueRange.h"

namespace svm::ir {

//  KnownBool -- 三态布尔 (谓词静态判定结果)
/// LIR/MIR/SCEV 共用的谓词判定原语.
enum class KnownBool : u8 {
  Unknown,     // 无法静态判定
  AlwaysFalse, // 恒假
  AlwaysTrue,  // 恒真
};

//  KnownBits -- 逐位 "已知 0 / 已知 1" 格
/// 不变量:
///   - knownZero & knownOne == 0: 同一位不能既已知 0 又已知 1
///   (冲突即矛盾).
///   - knownZero / knownOne 只在低 width 位内有效, width 以上的位一律视为 0.
///   - 既不在 knownZero 也不在 knownOne 的位表示未知.
///   - width == 0 是无效查询哨兵 (指针/浮点/不适用), 等价旧 LIR 的 valid=false
///
/// 对 i32 (width=32), 最高有效位 bit31 是有符号数的符号位.
struct KnownBits {
  u64 knownZero = 0; // 已知为零的位掩码
  u64 knownOne = 0;  // 已知为一的位掩码
  u32 width = 0;     // 有效位宽, 零表示不适用

  // unknown(w): 该值适用位级推理, 但当前没有任何一位可确定
  // invalid(): 该查询本身不适用, 例如指针, 浮点或空类型值
  // 两者必须分开: unknown 可与值域和同余事实继续组合;
  // invalid 则不应参与位事实交汇, 否则会把不适用误当作适用但未知,
  // 并污染后续推导.

  // 构造有效但全未知位事实
  static KnownBits unknown(u32 width) noexcept {
    return {0, 0, width <= 64 ? width : 0};
  }

  // 构造不适用位事实 (width=0)
  static KnownBits invalid() noexcept { return {}; }

  // 构造完整常量位事实
  static KnownBits constant(u64 value, u32 width) noexcept {
    const u64 mask = maskOfW(width);
    return {(~value) & mask, value & mask, width <= 64 ? width : 0};
  }
  // 构造低位宽掩码
  // w==64 时不能写 (1ull << 64), 那是 C++ 未定义行为;
  // w==0 时也需要特殊处理. 集中在这里处理三种边界
  static u64 maskOfW(u32 width) noexcept {
    return width == 0 || width > 64
               ? 0
               : (width == 64 ? UINT64_MAX : (u64{1} << width) - 1);
  }
  // 获取当前有效位掩码
  u64 mask() const noexcept { return maskOfW(width); }
  bool conflict() const noexcept {
    return (knownZero & knownOne & mask()) != 0;
  } // 查询位冲突
  bool valid() const noexcept {
    return width != 0 && width <= 64 && !conflict();
  } // 查询有效性
  bool isUnknown() const noexcept {
    return valid() && ((knownZero | knownOne) & mask()) == 0;
  } // 查询全未知
  bool signBitKnownZero() const noexcept {
    return valid() && ((knownZero >> (width - 1)) & 1U) != 0;
  } // 查询符号位为零
  bool knownNonZero() const noexcept {
    return valid() && (knownOne & mask()) != 0;
  } // 查询已知非零
  u32 minTrailingZeros() const noexcept { // 获取已知最少尾零数
    if (!valid())
      return 0;
    u32 count = 0;
    while (count < width && ((knownZero >> count) & 1U) != 0)
      ++count;
    return count;
  }
};

// KnownBits 位级传递规则 (精确格运算)
// LIR 与 MIR 共用同一份实现, 不再两边各写一遍
// 结果位宽取 left.width, 并要求 left/right 同宽
// 计算按位与事实
KnownBits kbAnd(const KnownBits &left, const KnownBits &right) noexcept;
// 计算按位或事实
KnownBits kbOr(const KnownBits &left, const KnownBits &right) noexcept;
// 计算按位异或事实
KnownBits kbXor(const KnownBits &left, const KnownBits &right) noexcept;
// 逻辑左移; 移出位补 "已知 0"
KnownBits kbShl(const KnownBits &value, u32 amount) noexcept;
// 逻辑右移; 高位补 "已知 0"
KnownBits kbLShr(const KnownBits &value, u32 amount) noexcept;
// 算术右移; 高位按符号位传播 (未知则高位未知)
KnownBits kbAShr(const KnownBits &value, u32 amount) noexcept;

// KnownBits <-> I32Range 投影
/// 从 i32 值集合提取可靠位事实:
///   单点集合 => 全位; 非负 => 符号位 0 + 高零位;
///   恒负 => 符号位 1. 其余位保持未知. width 固定为 32
KnownBits rangeToKnownBits(const I32Range &range) noexcept;

/// 返回有符号值的无符号绝对值, 包括 INT64_MIN
u64 unsignedMagnitude(i64 value) noexcept;
/// 查询模数是否能安全穿过 i32 模 2^32 回绕运算
bool isI32WrappingInvariantModulus(u64 modulus) noexcept;
/// 将有符号值规范化到 [0, modulus), modulus==0 时保留原位模式
u64 normalizedModulo(i64 value, u64 modulus) noexcept;
/// 将有符号值规范化为可由 i64 承载的非负数学余数
i64 floorMod(i64 value, u64 modulus) noexcept;
/// 在不产生宿主整数溢出的前提下计算模加法
u64 addModulo(u64 left, u64 right, u64 modulus) noexcept;
/// 在不产生宿主整数溢出的前提下计算模乘法
u64 multiplyModulo(u64 left, u64 right, u64 modulus) noexcept;
/// 求 value 在 modulus 下的乘法逆元, 不可逆时返回 false
bool modInverse(i64 value, u64 modulus, i64 &inverse) noexcept;

//  Congruence -- 同余事实域 (奇偶 / 对齐 / 任意模数余数)
/// 语义:
///   mod == 1 : unknown (同余格的顶).
///   mod == 0 : 精确常量 rem.
///   mod > 1  : x === rem (mod mod), 即 x 对 mod 取余恒等于 rem.
///   valid == false : 查询不适用 (指针/浮点), 消费者按未知处理.
///
/// 域感知铁律: i32 回绕域下非 2^k 模数事实只有在表达式有 no-wrap 证明时才安全;
/// 否则只保留模数的 2^k 因子. 该裁剪由 SCEV 顶层完成; 本结构只承载 "单一余数".
struct Congruence {
  u64 mod = 1;       // 模数, 零表示常量, 一表示未知
  i64 rem = 0;       // 常量或规范化余数
  bool valid = true; // 查询是否适用于该值

  static Congruence unknown() noexcept { return {}; }
  static Congruence invalid() noexcept { return {1, 0, false}; }
  // 构造精确常量同余
  static Congruence constant(i64 value) noexcept { return {0, value, true}; }
  // 构造规范化同余
  static Congruence modulo(u64 modulus, i64 remainder) noexcept;
  // 查询是否为同余顶
  bool isUnknown() const noexcept { return valid && mod == 1; }
  // 查询是否为精确常量
  bool isConstant() const noexcept { return valid && mod == 0; }
  // 查询是否为非平凡模同余
  bool isModulo() const noexcept { return valid && mod > 1; }
  // 查询当前事实是否蕴含指定模数和余数
  bool impliesResidue(u64 modulus, i64 residue) const noexcept;
};

/// 同一值上两条同时成立的同余事实合取结果.
struct CongruenceConjunction {
  Congruence value = Congruence::unknown(); // 可表示的合取同余
  bool contradiction = false;               // 两条事实是否没有公共解
};

/// 用广义 CRT 合取同一值上的两条同余, 并显式报告不可达状态.
CongruenceConjunction conjoinCongruence(const Congruence &left,
                                        const Congruence &right) noexcept;

// 合流两条同余的公共事实
/// 同余格交汇: 取两条事实都能共同保证的单一同余.
/// 对 x===r1(mod m1) 与 x===r2(mod m2):
///   x === r1 (mod gcd(m1, m2, |r1-r2|))
/// 不编码 CRT 多解集合, 也不把矛盾上下文表示成 bottom.
Congruence meetCongruence(const Congruence &left,
                          const Congruence &right) noexcept;

//  No-Wrap 证明 (NoWrapKind / NoWrapSource / NoWrapInfo)
/// 无回绕是证明元数据, 不是值域模式. 它回答为何 i32 运行值可等同数学
/// 整数值, 只服务数学域消费者, 例如别名偏移排序和 IndVarSimp 出口物化.
/// SysY i32 默认回绕语义不是有符号溢出未定义行为, 因此绝不凭 LanguageRule
/// 乐观假设.
enum class NoWrapKind : u8 {
  None,        // 无证明
  I32Signed,   // 有符号不回绕
  I32Unsigned, // 无符号不回绕
  Both,        // 两种解释均不回绕
};

enum class NoWrapSource : u8 {
  None,                 // 无来源
  LanguageRule,         // 语言规则保证
  LoopBoundProof,       // 循环边界证明
  RangeProof,           // 值域端点证明
  ArrayObjectSizeProof, // 数组对象大小证明
  UserAssumption,       // 显式用户假设
};

struct NoWrapInfo {
  NoWrapKind kind = NoWrapKind::None;       // 已证明的不回绕种类
  NoWrapSource source = NoWrapSource::None; // 证明来源

  bool proven() const noexcept {
    return kind != NoWrapKind::None && source != NoWrapSource::None;
  } // 查询证明是否完整
};

//  ArithmeticDomain -- 算术语义域
/// 所有同余/谓词/数学边界查询共享的语义开关:
///   - I32Wrapping: 真实运行语义. 任意模数同余在回绕下不一定保持,
///     只有 2^k 模数因为整除 2^32 可以安全穿过普通回绕算术.
///   - MathematicalNSW: 调用方已证明表达式可按数学整数解释,
///     允许保留任意模数同余和数学端点.
enum class ArithmeticDomain : u8 {
  I32Wrapping,     // i32 模 2^32 运行语义
  MathematicalNSW, // 已证明无回绕的数学整数语义
};

//  MathBounds -- 数学整数域边界 (与 i32 值集合显式分离)
/// 数学整数边界必须显式分离, 不可作为一般值域暴露给 SCCP/分支折叠
///   valid == true : 表达式在查询上下文可按数学整数解释, 且 [min,max] 端点
///   可靠. proof.kind != None : 必须解释为何 i32 运行值 == 数学值.
/// 用途: Alias offset ordering / 对象越界证明 / no-wrap 强化变换.
/// 绝不表达 wrapped i32 set.
struct MathBounds {
  bool valid = false; // 数学端点是否可用
  i64 min = 0;        // 数学最小值
  i64 max = 0;        // 数学最大值
  NoWrapInfo proof;   // 运行值等同数学值的证明

  static MathBounds none() noexcept { return {}; } // 构造无数学边界状态
  static MathBounds of(i64 min, i64 max,
                       NoWrapInfo proof) noexcept; // 构造经证明的数学边界
};

//  FactSource -- 事实来源标签 (供验证器和调试使用)
/// 来源不改变语义, 只帮助验证与调试
enum class FactSource : u8 {
  None,             // 无来源
  LIR_SCEV,         // LIR 标量演化事实
  LoweringSemantic, // Lowering 规则事实
  MIR_Local,        // MIR 局部传递事实
  MetadataClone,    // 元数据克隆事实
};

//  ScalarFactBundle -- 跨 IR 层传递的稳定事实摘要
/// 它是事实摘要, 不是分析对象. Lowering 把 LIR 的无上下文事实拍成它,
/// 写入 MIR 定义的元数据, MIR ValueFacts 再将其作为种子事实
///
/// 可保存: 无上下文值事实, 保值拷贝事实, 降低语义事实,
///           以及目标指令语义事实
/// 不可保存: 仅边有效事实, 块局部事实, 使用位置敏感事实,
///             SCEVExpr 指针, DomTree/LoopInfo 指针
struct ScalarFactBundle {
  bool valid = false;                   // 摘要是否携带事实
  u32 bitWidth = 32;                    // 标量有效位宽
  I32Range range = I32Range::unknown(); // 低 32 位 i32 值域
  KnownBits knownBits;                  // 位级事实 (width=0 表示无位事实)
  Congruence congruence = Congruence::unknown(); // 同余事实
  bool hasNonZero = false;                       // 是否携带零性结论
  bool nonzero = false;                          // 有零性结论时是否非零
  FactSource source = FactSource::None;          // 事实来源

  // 构造常量摘要
  static ScalarFactBundle
  fromConstant(i32 value,
               FactSource source = FactSource::LoweringSemantic) noexcept {
    return {true,
            32,
            I32Range::constant(value),
            KnownBits::constant(static_cast<u32>(value), 32),
            Congruence::constant(value),
            true,
            value != 0,
            source};
  }
  // 构造 i32 值域摘要
  static ScalarFactBundle fromRange(const I32Range &range,
                                    FactSource source) noexcept {
    if (range.isUnknown() || range.isEmpty())
      return {};
    const bool nonzero = !range.containsSigned(0);
    return {
        true,    32,      range, rangeToKnownBits(range), Congruence::unknown(),
        nonzero, nonzero, source};
  }
};

// 规范化并闭包标量事实
/// 让摘要内部自洽: 值域 -> 符号位写入 KnownBits; KnownBits ->
/// 非负/非零回写值域; 同余(2^k) -> 低位写入 KnownBits. 多次调用幂等
void canonicalizeBundle(ScalarFactBundle &bundle) noexcept;

//  谓词比较原语 (有符号/无符号投影统一公式)
/// 所有 "两个值集合 cmp" 的三态判定收口到一处, 避免 LIR Oracle 与 MIR
/// ValueFacts 各写一遍有符号/无符号端点公式. 调用方把自己的比较操作码
/// 映射到 IntPred 再调用 evalIntCompare.
enum class IntPred : u8 {
  SLT, // 有符号小于
  SLE, // 有符号小于等于
  SGT, // 有符号大于
  SGE, // 有符号大于等于
  EQ,  // 等于
  NE,  // 不等于
  ULT, // 无符号小于
  ULE, // 无符号小于等于
  UGT, // 无符号大于
  UGE, // 无符号大于等于
};

/// 判定整数比较三态结果
/// 投影不可用 (跨界) => 该侧不定论 => Unknown;
/// 绝不把环形集合展平成不安全闭区间.
/// EQ/NE 用集合不相交 / 同一单点集合判定;
/// SSA 同一性 (x==x) 由调用方在更高层优先短路.
KnownBool evalIntCompare(IntPred predicate, const I32Range &left,
                         const I32Range &right) noexcept;

} // namespace svm::ir

#endif // LIR_SCALAR_FACTS_H
