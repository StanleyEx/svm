#ifndef LIR_CALL_GRAPH_H
#define LIR_CALL_GRAPH_H

#include "IR.h"

#include <memory>
#include <unordered_map>
#include <vector>

namespace svm::ir {

class CallGraph;

class CGNode {
public:
  struct Edge {
    CGNode *callee = nullptr;
    Inst *callSite = nullptr;
  };

  i32 id = -1;                  // 图内连续节点编号
  Function *function = nullptr; // 节点对应函数
  std::vector<Edge> callees;    // 保留平行边的出边表
  std::vector<Edge> callers;    // 与出边镜像的入边表
  i32 sccId = -1;               // 所属强连通分量编号
  bool inRecursion = false;     // 是否位于递归强连通分量
};

class CallGraph {
public:
  CallGraph() = default;
  CallGraph(CallGraph &&) noexcept = default;
  CallGraph &operator=(CallGraph &&) noexcept = default;
  CallGraph(const CallGraph &) = delete;
  CallGraph &operator=(const CallGraph &) = delete;

  CGNode *getOrCreate(Function *function);
  CGNode *findNode(const Function *function) const noexcept;
  void addEdge(Function *caller, Function *callee, Inst *callSite);
  void computeSCCs();
  void clear() noexcept;

  const std::vector<CGNode *> &nodes() const noexcept { return nodes_; }
  const std::vector<std::vector<CGNode *>> &sccGroups() const noexcept {
    return sccGroups_; // callee SCC 在前的分组
  }

private:
  std::vector<std::unique_ptr<CGNode>> ownedNodes_;
  std::vector<CGNode *> nodes_; // 按编号排列的节点指针表
  std::unordered_map<const Function *, CGNode *> fnToNode_;
  std::vector<std::vector<CGNode *>> sccGroups_;
};

} // namespace svm::ir

#endif // LIR_CALL_GRAPH_H
