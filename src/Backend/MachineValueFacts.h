#ifndef BACKEND_MACHINE_VALUE_FACTS_H
#define BACKEND_MACHINE_VALUE_FACTS_H

#include "IR.h"
#include "ScalarFacts.h"

namespace svm::ir {

enum class FactMeetState : u8 {
  Unknown, // 尚未得到有效收窄
  Known,   // 至少得到一条一致事实
  Bottom,  // 事实互相矛盾
};

struct MachineValueFacts {
  I32Range range = I32Range::unknown(); // 低32位i32值域
  KnownBits bits;                       // 位事实 width为零表示未初始化
  bool nonzero = false;                 // 是否已证明非零
  FactMeetState meetState = FactMeetState::Unknown; // 本次查询的合流状态

  bool knownNonNegativeI32() const noexcept; // i32语义下是否非负
  bool knownNonZero() const noexcept;        // 是否必定非零
  bool knownZeroI32() const noexcept;        // 低32位是否精确为零
  u32 minTrailingZeros() const noexcept;     // 已知最少尾零数
};

struct MachineValueFactQuery {
  const Function *function = nullptr;
  const Inst *context = nullptr; // 当前使用点 无上下文查询时为空
  u32 width = 32;                // 位事实有效宽度
  u32 maxDepth = 6;              // 指令递归深度上限
  bool useContext = true;        // 是否消费支配分支上下文

  // 构造定义级查询
  static MachineValueFactQuery
  forDefRewriteI32(const Function *function) noexcept;
  // 构造使用点查询
  static MachineValueFactQuery forUseSiteI32(const Function *function,
                                             const Inst *context) noexcept;
};
// 按需计算综合机器值事实
MachineValueFacts computeMachineValueFacts(const Inst *value,
                                           const MachineValueFactQuery &query);

} // namespace svm::ir

#endif // BACKEND_MACHINE_VALUE_FACTS_H
