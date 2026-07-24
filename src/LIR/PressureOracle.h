#ifndef LIR_PRESSURE_ORACLE_H
#define LIR_PRESSURE_ORACLE_H

#include "IR.h"

#include <unordered_map>

namespace svm::ir {

enum class PressureLevel : u8 {
  Low,          // 较低压力
  Elevated,     // 接近压力上限
  High,         // 大概率产生溢出
  UnknownLarge, // 函数过大而未扫描
};

struct PressureSnapshot {
  i32 liveInstructions = 0; // 当前函数块内指令总数
  i32 peakGPR = 0;          // 整数和指针SSA近似峰值
  i32 peakFPR = 0;          // 浮点SSA近似峰值
  bool tooLarge = false;    // 超过扫描上限
};

struct GrowthHint {
  i32 moduleBaseline = 0;                     // 构造时模块指令总数
  i32 moduleAddedObserved = 0;                // 已记录的模块新增指令数
  i32 functionLiveInstructions = 0;           // 当前函数指令数
  i32 functionAfter = 0;                      // 应用候选后的函数指令数
  i32 functionAddedObserved = 0;              // 已记录到当前函数的新增指令数
  i32 addedInstructions = 0;                  // 当前候选估计新增指令数
  f64 moduleGrowthRatio = 0.0;                // 应用候选后的模块增长比例
  PressureLevel gpr = PressureLevel::Low;     // GPR压力等级
  PressureLevel fpr = PressureLevel::Low;     // FPR压力等级
  PressureLevel overall = PressureLevel::Low; // 综合压力等级
};

struct PressureOracleConfig {
  i32 gprElevated = 96;        // GPR进入Elevated的阈值
  i32 gprHigh = 128;           // GPR进入High的阈值
  i32 fprElevated = 48;        // FPR进入Elevated的阈值
  i32 fprHigh = 64;            // FPR进入High的阈值
  i32 pressureScanCap = 65536; // 精确压力扫描的函数指令上限
};

class PressureOracle {
public:
  explicit PressureOracle(Module *module, PressureOracleConfig config = {});

  // 获取函数压力快照
  const PressureSnapshot &snapshot(Function *function);
  // 落地后的体积和压力信号
  GrowthHint hint(Function *function, i32 addedInstructions) const;
  // 模块构造期指令基线
  i32 moduleBaselineInstructions() const noexcept { return moduleBaseline_; }
  // 本轮已观测的模块增长
  i32 moduleAddedObserved() const noexcept { return moduleAdded_; }

  // 记录已落地增长并失效对应函数快照
  void recordApplied(Function *function, i32 addedInstructions);
  // 失效单个函数的压力快照
  void invalidateFunction(Function *function);
  // 清空全部函数压力快照
  void invalidateAll() noexcept;

private:
  const PressureSnapshot &getSnapshot(Function *function) const;
  PressureSnapshot buildSnapshot(Function *function) const;
  PressureLevel classify(i32 peak, i32 elevated, i32 high,
                         bool tooLarge) const noexcept;

  PressureOracleConfig config_{};
  i32 moduleBaseline_ = 0; // 模块初始活指令数
  i32 moduleAdded_ = 0;    // 模块累计观测新增
  // 函数压力快照缓存
  mutable std::unordered_map<Function *, PressureSnapshot> snapshots_;
  // 每个函数累计观测新增
  std::unordered_map<Function *, i32> functionAdded_;
};

} // namespace svm::ir

#endif // LIR_PRESSURE_ORACLE_H
