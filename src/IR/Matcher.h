#ifndef SVM_IR_MATCHER_H
#define SVM_IR_MATCHER_H

#include "IR.h"

#include <cassert>
#include <cstring>
#include <limits>
#include <type_traits>
#include <vector>

namespace svm::ir::PatternMatch {

namespace detail {

struct MatchState {
  std::vector<bool *> undoLog; // 撤销项
  usize activeScopes = 0;      // 嵌套深度
};

inline MatchState &matchState() noexcept {
  static thread_local MatchState state;
  return state;
}

inline u32 floatBits(f32 value) noexcept {
  u32 bits = 0;
  static_assert(sizeof(bits) == sizeof(value));
  std::memcpy(&bits, &value, sizeof(bits));
  return bits;
}

inline void forgetCapture(bool *bound) noexcept {
  for (bool *&entry : matchState().undoLog)
    if (entry == bound)
      entry = nullptr;
}

} // namespace detail

class MatchScope {
public:
  MatchScope() noexcept
      : mark_(detail::matchState().undoLog.size()),
        outermost_(detail::matchState().activeScopes++ == 0) {}
  ~MatchScope() noexcept { // 提交或回滚
    detail::MatchState &state = detail::matchState();
    assert(state.activeScopes != 0);
    --state.activeScopes;
    if (!committed_) {
      rollback();
    } else if (outermost_) {
      state.undoLog.resize(mark_);
    }
  }

  MatchScope(const MatchScope &) = delete;
  MatchScope &operator=(const MatchScope &) = delete;
  MatchScope(MatchScope &&) = delete;
  MatchScope &operator=(MatchScope &&) = delete;

  void commit() noexcept { committed_ = true; }

private:
  void rollback() noexcept { // 撤销本作用域内的首次绑定
    std::vector<bool *> &log = detail::matchState().undoLog;
    while (log.size() > mark_) {
      bool *bound = log.back();
      log.pop_back();
      if (bound)
        *bound = false;
    }
  }

  usize mark_ = 0;         // 进入作用域时的撤销栈长度
  bool outermost_ = false; // 是否为当前线程的根事务
  bool committed_ = false; // 是否选择成功路径
};

template <typename T = Inst> struct Capture {
  static_assert(std::is_same_v<T, Inst>, "IR Capture only supports Inst");

  Capture() noexcept = default; // 创建未绑定事务捕获
  ~Capture() noexcept {         // 从仍活跃的外层事务注销捕获
    detail::forgetCapture(&bound_);
  }

  Capture(const Capture &) = delete;            // 禁止复制事务捕获
  Capture &operator=(const Capture &) = delete; // 禁止复制赋值
  Capture(Capture &&) = delete;                 // 禁止移动事务捕获
  Capture &operator=(Capture &&) = delete;      // 禁止移动赋值

  T *get() const noexcept { // 读取成功捕获值
    assert(bound_ && "reading an unbound Capture");
    return value_;
  }

  T *value_ = nullptr; // 捕获的SSA值
  bool bound_ = false; // 捕获值是否有效
};

namespace detail {

template <typename T>
inline bool bindCapture(Capture<T> &capture, Inst *inst) noexcept {
  if (!inst)
    return false;
  if (capture.bound_)
    return capture.value_ == inst;
  capture.value_ = inst;
  capture.bound_ = true;
  MatchState &state = matchState();
  if (state.activeScopes != 0)
    state.undoLog.push_back(&capture.bound_);
  return true;
}

template <typename T>
inline void overwriteCapture(Capture<T> &capture, Inst *inst) noexcept {
  capture.value_ = inst;
  capture.bound_ = true;
  MatchState &state = matchState();
  if (state.activeScopes != 0)
    state.undoLog.push_back(&capture.bound_);
}

} // namespace detail

template <typename Matcher>
inline bool match(Inst *inst, const Matcher &matcher) noexcept {
  MatchScope scope;
  if (inst && matcher.match(inst)) {
    scope.commit();
    return true;
  }
  return false;
}

template <typename T = Inst> struct ValueMatcher {
  static_assert(std::is_same_v<T, Inst>, "IR matcher only supports Inst");

  bool match(Inst *inst) const noexcept { // 绑定任意非空值
    if (!inst)
      return false;
    result = inst;
    return true;
  }

  T *&result; // 调用方的普通绑定槽
};

template <typename T = Inst>
inline ValueMatcher<T> m_Value(T *&value) noexcept {
  return {value};
}

template <typename T> struct CaptureMatcher {
  bool match(Inst *inst) const noexcept { // 首次绑定或检查同一值
    return detail::bindCapture(capture, inst);
  }

  Capture<T> &capture; // 事务捕获槽
};

template <typename T>
inline CaptureMatcher<T> m_Value(Capture<T> &capture) noexcept {
  return {capture};
}

struct ImmediateMatcher {
  bool match(Inst *inst) const noexcept { // 绑定i32/i1常量值
    if (!inst || inst->isUndefValue() || inst->getOp() != OP_ICONST)
      return false;
    value = inst->getImm();
    return true;
  }

  i32 &value; // 调用方的立即数槽
};

inline ImmediateMatcher m_Imm(i32 &value) noexcept { return {value}; }

struct SpecificIntMatcher {
  bool match(Inst *inst) const noexcept { // 匹配指定位模式整数常量
    return inst && !inst->isUndefValue() && inst->getOp() == OP_ICONST &&
           inst->getImm() == expected;
  }

  i32 expected = 0; // 期望的整数值
};

inline SpecificIntMatcher m_Zero() noexcept { return {0}; }
inline SpecificIntMatcher m_One() noexcept { return {1}; }
inline SpecificIntMatcher m_MinusOne() noexcept { return {-1}; }

struct SpecificFloatMatcher {
  bool match(Inst *inst) const noexcept { // 按位匹配f32常量
    return inst && !inst->isUndefValue() && inst->getOp() == OP_FCONST &&
           detail::floatBits(inst->getFimm()) == expectedBits;
  }

  u32 expectedBits = 0; // 期望的IEEE 754位模式
};

inline SpecificFloatMatcher m_SpecificFloat(f32 value) noexcept {
  return {detail::floatBits(value)};
}
inline SpecificFloatMatcher m_FZero() noexcept { return m_SpecificFloat(0.0F); }
inline SpecificFloatMatcher m_FOne() noexcept { return m_SpecificFloat(1.0F); }

struct LoadImmediateMatcher {
  bool match(Inst *inst) const noexcept { // 绑定可表示为i32的MOP_LI
    if (!inst || inst->getOp() != MOP_LI)
      return false;
    const i64 immediate = inst->getImm64();
    if (immediate < std::numeric_limits<i32>::min() ||
        immediate > std::numeric_limits<i32>::max())
      return false;
    value = static_cast<i32>(immediate);
    return true;
  }

  i32 &value; // 调用方的机器立即数槽
};

inline LoadImmediateMatcher m_Li(i32 &value) noexcept { return {value}; }

struct AnyMatcher {
  bool match(Inst *inst) const noexcept {
    return inst != nullptr;
  } // 匹配任意值
};

inline AnyMatcher m_Any() noexcept { return {}; }

template <OpCode Op, typename Arg> struct UnaryMatcher {
  bool match(Inst *inst) const noexcept { // 匹配严格一元操作
    return inst && inst->getOp() == Op && inst->getOperandCount() == 1 &&
           argument.match(inst->getArg(0));
  }

  Arg argument; // 操作数子模式
};

template <typename Arg>
inline UnaryMatcher<OP_NEG, Arg> m_Neg(const Arg &argument) noexcept {
  return {argument};
}
template <typename Arg>
inline UnaryMatcher<OP_LNOT, Arg> m_Not(const Arg &argument) noexcept {
  return {argument};
}
template <typename Arg>
inline UnaryMatcher<OP_FNEG, Arg> m_FNeg(const Arg &argument) noexcept {
  return {argument};
}

template <OpCode Op, typename Left, typename Right> struct BinaryMatcher {
  bool match(Inst *inst) const noexcept { // 按固定顺序匹配严格二元操作
    return inst && inst->getOp() == Op && inst->getOperandCount() == 2 &&
           left.match(inst->getArg(0)) && right.match(inst->getArg(1));
  }

  Left left;
  Right right;
};

template <typename Left, typename Right>
inline BinaryMatcher<OP_SUB, Left, Right> m_Sub(const Left &left,
                                                const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline BinaryMatcher<OP_DIV, Left, Right> m_Div(const Left &left,
                                                const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline BinaryMatcher<OP_MOD, Left, Right> m_Mod(const Left &left,
                                                const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline BinaryMatcher<OP_FSUB, Left, Right> m_FSub(const Left &left,
                                                  const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline BinaryMatcher<OP_FDIV, Left, Right> m_FDiv(const Left &left,
                                                  const Right &right) noexcept {
  return {left, right};
}
template <OpCode Op, typename Left, typename Right>
inline BinaryMatcher<Op, Left, Right> m_BinOp(const Left &left,
                                              const Right &right) noexcept {
  return {left, right};
}

template <OpCode Op, typename Left, typename Right>
struct CommutativeBinaryMatcher {
  bool match(Inst *inst) const noexcept { // 匹配两种操作数顺序
    if (!inst || inst->getOp() != Op || inst->getOperandCount() != 2)
      return false;
    if (left.match(inst->getArg(0)) && right.match(inst->getArg(1)))
      return true;
    return left.match(inst->getArg(1)) && right.match(inst->getArg(0));
  }

  Left left;
  Right right;
};

template <typename Left, typename Right>
inline CommutativeBinaryMatcher<OP_ADD, Left, Right>
m_Add(const Left &left, const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline CommutativeBinaryMatcher<OP_MUL, Left, Right>
m_Mul(const Left &left, const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline CommutativeBinaryMatcher<OP_EQ, Left, Right>
m_Eq(const Left &left, const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline CommutativeBinaryMatcher<OP_NE, Left, Right>
m_NE(const Left &left, const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline CommutativeBinaryMatcher<OP_FMUL, Left, Right>
m_FMul(const Left &left, const Right &right) noexcept {
  return {left, right};
}

template <typename T> struct DeferredMatcher {
  bool match(Inst *inst) const noexcept {
    return inst == expected;
  } // 检查普通绑定值

  T *&expected; // 已由早先子模式绑定的值
};

template <typename T> inline DeferredMatcher<T> m_Deferred(T *&value) noexcept {
  return {value};
}

template <typename Inner> struct OneUseMatcher {
  bool match(Inst *inst) const noexcept { // 限制根值只有一个Use
    return inst && inst->hasOneUse() && inner.match(inst);
  }

  Inner inner; // 被约束的子模式
};

template <typename Inner>
inline OneUseMatcher<Inner> m_OneUse(const Inner &inner) noexcept {
  return {inner};
}

template <typename T> struct SameMatcher {
  bool match(Inst *inst) const noexcept { // 检查事务捕获的同一值
    return capture.bound_ && capture.value_ == inst;
  }

  Capture<T> &capture; // 已绑定事务捕获
};

template <typename T>
inline SameMatcher<T> m_Same(Capture<T> &capture) noexcept {
  return {capture};
}

template <OpCode Op, typename Left, typename Right>
struct TransactionalCommutativeBinaryMatcher {
  bool match(Inst *inst) const noexcept { // 带回滚地尝试两种操作数顺序
    if (!inst || inst->getOp() != Op || inst->getOperandCount() != 2)
      return false;
    Inst *arg0 = inst->getArg(0);
    Inst *arg1 = inst->getArg(1);
    {
      MatchScope scope;
      if (left.match(arg0) && right.match(arg1)) {
        scope.commit();
        return true;
      }
    }
    {
      MatchScope scope;
      if (left.match(arg1) && right.match(arg0)) {
        scope.commit();
        return true;
      }
    }
    return false;
  }

  Left left;
  Right right;
};

template <typename Left, typename Right>
inline TransactionalCommutativeBinaryMatcher<OP_ADD, Left, Right>
m_c_Add(const Left &left, const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline TransactionalCommutativeBinaryMatcher<OP_MUL, Left, Right>
m_c_Mul(const Left &left, const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline TransactionalCommutativeBinaryMatcher<OP_EQ, Left, Right>
m_c_Eq(const Left &left, const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline TransactionalCommutativeBinaryMatcher<OP_NE, Left, Right>
m_c_NE(const Left &left, const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline TransactionalCommutativeBinaryMatcher<OP_FADD, Left, Right>
m_c_FAdd(const Left &left, const Right &right) noexcept {
  return {left, right};
}
template <typename Left, typename Right>
inline TransactionalCommutativeBinaryMatcher<OP_FMUL, Left, Right>
m_c_FMul(const Left &left, const Right &right) noexcept {
  return {left, right};
}

template <typename Argument> struct NegLikeMatcher {
  bool match(Inst *inst) const noexcept { // 匹配neg(A)或sub(0, A)
    if (!inst)
      return false;
    if (inst->getOp() == OP_NEG && inst->getOperandCount() == 1)
      return argument.match(inst->getArg(0));
    return inst->getOp() == OP_SUB && inst->getOperandCount() == 2 &&
           SpecificIntMatcher{0}.match(inst->getArg(0)) &&
           argument.match(inst->getArg(1));
  }

  Argument argument; // 被取负的值模式
};

template <typename Argument>
inline NegLikeMatcher<Argument> m_NegLike(const Argument &argument) noexcept {
  return {argument};
}

struct NonZeroConstMatcher {
  bool match(Inst *inst) const noexcept { // 绑定非零i32/i1常量
    if (!inst || inst->isUndefValue() || inst->getOp() != OP_ICONST ||
        inst->getImm() == 0)
      return false;
    value = inst->getImm();
    return true;
  }

  i32 &value; // 调用方的非零常量槽
};

inline NonZeroConstMatcher m_NonZeroConst(i32 &value) noexcept {
  return {value};
}

template <typename Inner> struct TypeMatcher {
  bool match(Inst *inst) const noexcept { // 先检查结果类型再匹配内部模式
    return inst && inst->getType() == type && inner.match(inst);
  }

  IRType type = TY_VOID; // 期望的IR类型
  Inner inner;           // 类型守卫内的子模式
};

template <typename Inner>
inline TypeMatcher<Inner> m_Type(IRType type, const Inner &inner) noexcept {
  return {type, inner};
}

template <OpCode OuterOp> struct FactorPairMulMatcher {
  static bool isOneUseMul(Inst *inst) noexcept { // 检查严格二元单Use乘法
    return inst && inst->getOp() == OP_MUL && inst->getOperandCount() == 2 &&
           inst->hasOneUse();
  }

  bool bind(Inst *factorValue, Inst *leftValue,
            Inst *rightValue) const noexcept { // 原子绑定三个结果
    detail::overwriteCapture(factor, factorValue);
    detail::overwriteCapture(left, leftValue);
    detail::overwriteCapture(right, rightValue);
    return true;
  }

  bool match(Inst *inst) const noexcept { // 枚举两个乘法的四种公共因子位置
    if (!inst || inst->getOp() != OuterOp || inst->getOperandCount() != 2)
      return false;
    Inst *leftMul = inst->getArg(0);
    Inst *rightMul = inst->getArg(1);
    if (!isOneUseMul(leftMul) || !isOneUseMul(rightMul))
      return false;
    Inst *x0 = leftMul->getArg(0);
    Inst *y0 = leftMul->getArg(1);
    Inst *x1 = rightMul->getArg(0);
    Inst *y1 = rightMul->getArg(1);
    if (x0 == x1 && bind(x0, y0, y1))
      return true;
    if (x0 == y1 && bind(x0, y0, x1))
      return true;
    if (y0 == x1 && bind(y0, x0, y1))
      return true;
    if (y0 == y1 && bind(y0, x0, x1))
      return true;
    return false;
  }

  Capture<Inst> &factor; // 公共因子捕获
  Capture<Inst> &left;   // 左乘法的另一操作数
  Capture<Inst> &right;  // 右乘法的另一操作数
};

template <OpCode OuterOp>
inline FactorPairMulMatcher<OuterOp>
m_FactorPairMul(Capture<Inst> &factor, Capture<Inst> &left,
                Capture<Inst> &right) noexcept {
  return {factor, left, right};
}

} // namespace svm::ir::PatternMatch

#endif // SVM_IR_MATCHER_H
