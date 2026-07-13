#ifndef LIR_MEM_DEP_H
#define LIR_MEM_DEP_H

#include "Alias.h"
#include "GlobalSummary.h"
#include "LoopInfo.h"

namespace svm::ir {

struct MemDepQueryBudget {
  u32 maxMemoryEvents = 128; // 单次查询最多检查的内存事件数
  u32 maxBlocks = 32;        // 单次查询最多跨越的直线块数
};

class MemDepOracle {
public:
  enum class ClobberResult : u8 {
    NoClobber,   // 已证明查询区间内没有相关写
    MustClobber, // 最近相关写与查询位置完全重合
    MayClobber,  // 存在相关写或控制流不足以证明无写
  };

  explicit MemDepOracle(
      const AliasInfo *aliasInfo,
      const GlobalSummaryResult *globalSummary = nullptr) noexcept;

  // 返回同块内首个可读到该 store 位置的 load
  Inst *findNextLoad(Inst *store) const;
  // 返回同块内最近的相关 store
  Inst *findPrevStore(Inst *load) const;
  // 返回同块内首个相关 store
  Inst *findNextStore(Inst *store) const;
  // 同块开区间内对未知宽度 pointer 的写
  bool hasClobberBetween(Inst *from, Inst *to, Inst *pointer) const;
  // 循环内对未知宽度 pointer 的写
  bool hasClobberInLoop(Inst *pointer, const Loop *loop) const;
  // 循环内对给定访问区间的写
  bool hasClobberInLoop(const MemoryLocation &location, const Loop *loop) const;
  // 沿单前驱链反向查询未知宽度 pointer
  Inst *findClobberOnLinearPath(Inst *pointer, BasicBlock *startBlock,
                                BasicBlock *stopBlock, bool &gaveUp) const;
  // 沿单前驱链反向查询给定访问区间
  Inst *findClobberOnLinearPath(const MemoryLocation &location,
                                BasicBlock *startBlock, BasicBlock *stopBlock,
                                bool &gaveUp) const;
  // 证明 store 被直线路径上的完整覆盖写杀死
  Inst *findNextKillerStore(Inst *store, MemDepQueryBudget budget = {}) const;
  // 查询 target 前缀及单前驱链上的最近相关写
  ClobberResult hasClobberBefore(Inst *target,
                                 const MemoryLocation &location) const;
  // 查询同块开区间内对给定访问区间的写
  ClobberResult hasClobberBetween(Inst *from, Inst *to,
                                  const MemoryLocation &location) const;

private:
  bool mayReadCall(Inst *call, const MemoryLocation &location) const;
  bool mayWriteCall(Inst *call, const MemoryLocation &location) const;
  // 判断单条 store/call 是否可能写入位置
  bool mayClobber(Inst *definition, const MemoryLocation &location) const;
  // 从 from 前一条或块尾开始反向寻找最近相关写
  Inst *scanBackwardForClobber(BasicBlock *block, Inst *from,
                               const MemoryLocation &location) const;

  const AliasInfo *aliasInfo_ = nullptr;
  const GlobalSummaryResult *globalSummary_ = nullptr;
};

} // namespace svm::ir

#endif // LIR_MEM_DEP_H
