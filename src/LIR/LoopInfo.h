#ifndef LIR_LOOP_INFO_H
#define LIR_LOOP_INFO_H

#include "IR.h"

#include <memory>
#include <unordered_map>
#include <vector>

namespace svm::ir {

class DominatorTree;

class Loop {
public:
  // 循环头块
  BasicBlock *header() const noexcept { return header_; }
  // 循环体块
  const std::vector<BasicBlock *> &blocks() const noexcept { return blocks_; }
  // 回边块
  const std::vector<BasicBlock *> &latches() const noexcept { return latches_; }
  // 循环内出口块
  const std::vector<BasicBlock *> &exitingBlocks() const noexcept {
    return exiting_;
  }
  // 循环外目标块
  const std::vector<BasicBlock *> &exitBlocks() const noexcept {
    return exits_;
  }
  Loop *parent() const noexcept { return parent_; }
  const std::vector<Loop *> &children() const noexcept { return children_; }
  i32 depth() const noexcept { return depth_; } // 嵌套深度 顶层为一
  bool contains(const BasicBlock *block) const noexcept;
  bool containsLoop(const Loop *loop) const noexcept;
  // 唯一循环外前驱 如不存在返回nullptr
  BasicBlock *getPreheader() const noexcept;

private:
  BasicBlock *header_ = nullptr;      // 唯一循环头块
  std::vector<BasicBlock *> blocks_;  // 循环体 包含子循环块
  std::vector<BasicBlock *> latches_; // 跳回头块的回边尾块
  std::vector<BasicBlock *> exiting_; // 循环内出口块 和exits_同序
  std::vector<BasicBlock *> exits_;   // 循环外目标块 和exiting_同序
  Loop *parent_ = nullptr;            // 直接父循环
  std::vector<Loop *> children_;      // 直接子循环
  i32 depth_ = 1;                     // 循环嵌套深度

  friend class LoopInfo;
};

class LoopInfo {
public:
  LoopInfo() = default;
  LoopInfo(LoopInfo &&) noexcept = default;
  LoopInfo &operator=(LoopInfo &&) noexcept = default;
  LoopInfo(const LoopInfo &) = delete;
  LoopInfo &operator=(const LoopInfo &) = delete;

  const std::vector<Loop *> &topLevelLoops() const noexcept {
    return topLevel_;
  }
  // 返回包含块的最内层循环
  Loop *getLoopFor(const BasicBlock *block) const noexcept;
  i32 getLoopDepth(const BasicBlock *block) const noexcept; // 块的循环深度
  // 判断块是否为循环头
  bool isLoopHeader(const BasicBlock *block) const noexcept;

  void build(Function *function, const DominatorTree &tree);

private:
  std::vector<std::unique_ptr<Loop>> loops_;
  std::vector<Loop *> topLevel_;                             // 顶层循环列表
  std::unordered_map<const BasicBlock *, Loop *> innermost_; // 块到内层循环映射
};

} // namespace svm::ir

#endif // LIR_LOOP_INFO_H
