#ifndef LIR_LOOP_MUTATOR_H
#define LIR_LOOP_MUTATOR_H

#include "DeepCopy.h"
#include "LoopShape.h"

#include <memory>
#include <vector>

namespace svm::ir {

struct LoopCloneIterationResult {
  std::unique_ptr<DeepCopy> copier; // 本代值与块映射
  BasicBlock *header = nullptr;     // 克隆循环头
  BasicBlock *latch = nullptr;      // 克隆回边块
  BasicBlock *layoutTail = nullptr; // 克隆布局尾块
};

struct IterationChain {
  std::vector<LoopCloneIterationResult> iterations; // 依次排列的克隆代

  bool empty() const noexcept { return iterations.empty(); }
  usize size() const noexcept { return iterations.size(); } // 克隆代数
  DeepCopy *mapAt(i32 index) const noexcept;                // 第index代映射
  BasicBlock *firstHeader() const noexcept;                 // 首代循环头
  BasicBlock *lastLatch() const noexcept;                   // 末代回边块
  DeepCopy *lastMap() const noexcept;                       // 末代映射
};

// 自引用或undef回边的Header Phi始终保持入口初值
bool headerPhiKeepsInitialValue(const HeaderPhiShape &phi) noexcept;

// 连续克隆count份循环体 仅建立映射和布局 不重接CFG
IterationChain cloneLoopIterations(Function *function,
                                   const CountedLoopShape &shape,
                                   const std::vector<BasicBlock *> &loopBlocks,
                                   i32 count);

} // namespace svm::ir

#endif // LIR_LOOP_MUTATOR_H
