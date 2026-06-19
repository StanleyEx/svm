#ifndef DOM_ANALYSIS_H
#define DOM_ANALYSIS_H

#include "IR.h"

#include <unordered_map>
#include <vector>

namespace svm::ir {

using DomChildrenMap =
    std::unordered_map<BasicBlock *, std::vector<BasicBlock *>>;
using DomFrontierMap =
    std::unordered_map<BasicBlock *, std::vector<BasicBlock *>>;

class DominatorTree {
public:
  bool build(Function *function);
  bool dominates(const BasicBlock *dominator,
                 const BasicBlock *block) const noexcept;
  BasicBlock *getIDom(BasicBlock *block) const noexcept;
  i32 getDepth(const BasicBlock *block) const noexcept;
  const DomChildrenMap &children() const noexcept { return children_; }
  const DomFrontierMap &frontier() const noexcept { return frontier_; }

private:
  struct Node {
    BasicBlock *idom = nullptr;
    i32 rpo = -1;   // Cooper迭代使用的RPO编号
    i32 depth = -1; // 支配树深度
    i32 in = -1;    // 支配树DFS进入时间
    i32 out = -1;   // 支配树DFS退出时间
  };

  const Node *findNode(const BasicBlock *block) const noexcept;
  void clear() noexcept;

  std::unordered_map<const BasicBlock *, Node> nodes_; // 可达块节点表
  DomChildrenMap children_;                            // 支配树邻接表
  DomFrontierMap frontier_;                            // 支配边界表
};

class PostDominatorTree {
public:
  bool build(Function *function);
  bool postDominates(const BasicBlock *dominator,
                     const BasicBlock *block) const noexcept;
  BasicBlock *getIPostDom(BasicBlock *block) const noexcept;
  BasicBlock *nearestCommonPostDominator(BasicBlock *first,
                                         BasicBlock *second) const noexcept;

  // 沿直接后支配链查询首个匹配块
  template <typename Predicate>
  BasicBlock *nearestPostDomIf(BasicBlock *block, Predicate predicate) const {
    const i32 index = indexOf(block);
    if (index < 0 || ipdom_[index] < 0)
      return nullptr;
    i32 current = ipdom_[index];
    const i32 omega = static_cast<i32>(blocks_.size());
    while (current >= 0 && current != omega) {
      BasicBlock *candidate = blocks_[current];
      if (predicate(candidate))
        return candidate;
      current = ipdom_[current];
    }
    return nullptr;
  }

private:
  i32 indexOf(const BasicBlock *block) const noexcept; // 内部节点编号
  i32 intersect(i32 first, i32 second) const noexcept; // 求反向CFG公共支配者
  void clear() noexcept;

  std::unordered_map<const BasicBlock *, i32> indices_; // 基本块到内部编号
  std::vector<BasicBlock *> blocks_;                    // entry可达块表
  std::vector<i32> ipdom_;                              // 直接后支配编号
  std::vector<i32> rpoNumbers_;                         // 反向CFG的RPO编号
};

} // namespace svm::ir

#endif // DOM_ANALYSIS_H
