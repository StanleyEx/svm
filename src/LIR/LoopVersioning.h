#ifndef LIR_LOOP_VERSIONING_H
#define LIR_LOOP_VERSIONING_H

#include "DeepCopy.h"
#include "LoopInfo.h"

#include <optional>
#include <vector>

namespace svm::ir {

class DominatorTree;

struct LoopVersionExitPlan {
  BasicBlock *exiting = nullptr; // 循环内退出边起点
  BasicBlock *exit = nullptr;    // 循环外退出目标
};

struct LoopVersionPredicatePlan {
  Inst *condition = nullptr;  // dispatch使用的源i1条件
  bool originalOnTrue = true; // true边是否继续进入原版本
};

struct LoopVersionPlan {
  Loop *loop = nullptr;
  BasicBlock *preheader = nullptr;                    // 唯一Preheader
  BasicBlock *header = nullptr;                       // 原循环Header
  std::vector<LoopVersionPredicatePlan> predicates;   // 合取式dispatch条件
  std::vector<std::vector<Inst *>> predicateBranches; // predicate源分支快照
  std::vector<Inst *> materializationOrder;           // 条件切片拓扑序
  std::vector<BasicBlock *> layoutBlocks;             // 布局序循环块
  std::vector<std::vector<BasicBlock *>> successorTargets; // 有序后继槽快照
  std::vector<LoopVersionExitPlan> exits;                  // 已预检的退出边
  i32 estimatedAddedInstructions = 0;                      // 提交后的预计增长
};

struct LoopVersionResult {
  BasicBlock *originalLanding = nullptr;     // 原循环版本入口块
  BasicBlock *clonedLanding = nullptr;       // 克隆循环版本入口块
  BasicBlock *originalHeader = nullptr;      // 原版本Header
  BasicBlock *clonedHeader = nullptr;        // 克隆版本Header
  std::vector<ClonedBlockPair> clonedBlocks; // 源块到克隆块映射

  BasicBlock *cloneOf(BasicBlock *source) const noexcept; // 查询块克隆
};

// 规划Unswitch需要的LoopVersion事务
std::optional<LoopVersionPlan>
planLoopVersion(Function *function, Loop *loop,
                const std::vector<LoopVersionPredicatePlan> &predicates,
                const std::vector<Inst *> &materializationOrder,
                const DominatorTree &dominators);

// 提交预检后的双版本CFG 全部predicate满足时进入原版本
std::optional<LoopVersionResult> commitLoopVersion(Function *function,
                                                   const LoopVersionPlan &plan);

} // namespace svm::ir

#endif // LIR_LOOP_VERSIONING_H
