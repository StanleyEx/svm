#include "CallGraph.h"

#include <algorithm>

namespace svm::ir {

CGNode *CallGraph::getOrCreate(Function *function) {
  VERIFY(function != nullptr);
  const auto found = fnToNode_.find(function);
  if (found != fnToNode_.end())
    return found->second;

  auto owned = std::make_unique<CGNode>();
  CGNode *node = owned.get();
  node->id = static_cast<i32>(nodes_.size());
  node->function = function;
  ownedNodes_.push_back(std::move(owned));
  nodes_.push_back(node);
  fnToNode_.emplace(function, node);
  return node;
}

CGNode *CallGraph::findNode(const Function *function) const noexcept {
  const auto found = fnToNode_.find(function);
  return found == fnToNode_.end() ? nullptr : found->second;
}

void CallGraph::addEdge(Function *caller, Function *callee, Inst *callSite) {
  VERIFY(caller != nullptr && callee != nullptr && callSite != nullptr);
  CGNode *callerNode = getOrCreate(caller);
  CGNode *calleeNode = getOrCreate(callee);
  callerNode->callees.push_back({calleeNode, callSite});
  calleeNode->callers.push_back({callerNode, callSite});
}

void CallGraph::clear() noexcept {
  sccGroups_.clear();
  fnToNode_.clear();
  nodes_.clear();
  ownedNodes_.clear();
}

void CallGraph::computeSCCs() {
  sccGroups_.clear();
  for (CGNode *node : nodes_) {
    node->sccId = -1;
    node->inRecursion = false;
  }
  if (nodes_.empty())
    return;

  struct Frame {
    CGNode *node = nullptr; // 当前DFS节点
    usize nextEdge = 0;     // 下一条待访问出边
  };

  const usize nodeCount = nodes_.size();
  std::vector<i32> discovery(nodeCount, -1);
  std::vector<i32> low(nodeCount, -1);
  std::vector<bool> onStack(nodeCount, false);
  std::vector<CGNode *> componentStack;
  std::vector<Frame> dfs;
  i32 nextDiscovery = 0;

  auto enter = [&](CGNode *node) {
    const usize id = static_cast<usize>(node->id);
    discovery[id] = low[id] = nextDiscovery++;
    onStack[id] = true;
    componentStack.push_back(node);
    dfs.push_back({node, 0});
  };

  for (CGNode *root : nodes_) {
    if (discovery[static_cast<usize>(root->id)] != -1)
      continue;
    enter(root);

    while (!dfs.empty()) {
      Frame &frame = dfs.back();
      CGNode *node = frame.node;
      const usize nodeId = static_cast<usize>(node->id);
      if (frame.nextEdge < node->callees.size()) {
        CGNode *callee = node->callees[frame.nextEdge++].callee;
        if (!callee || callee->id < 0 ||
            static_cast<usize>(callee->id) >= nodes_.size() ||
            nodes_[static_cast<usize>(callee->id)] != callee)
          continue;
        const usize calleeId = static_cast<usize>(callee->id);
        if (discovery[calleeId] == -1) {
          enter(callee);
          continue;
        }
        if (onStack[calleeId])
          low[nodeId] = std::min(low[nodeId], discovery[calleeId]);
        continue;
      }

      if (low[nodeId] == discovery[nodeId]) {
        std::vector<CGNode *> component;
        while (true) {
          CGNode *member = componentStack.back();
          componentStack.pop_back();
          onStack[static_cast<usize>(member->id)] = false;
          component.push_back(member);
          if (member == node)
            break;
        }
        sccGroups_.push_back(std::move(component));
      }

      dfs.pop_back();
      if (!dfs.empty()) {
        const usize parentId = static_cast<usize>(dfs.back().node->id);
        low[parentId] = std::min(low[parentId], low[nodeId]);
      }
    }
  }

  for (usize index = 0; index < sccGroups_.size(); ++index) {
    std::vector<CGNode *> &component = sccGroups_[index];
    const bool recursive = component.size() > 1;
    for (CGNode *node : component) {
      node->sccId = static_cast<i32>(index);
      node->inRecursion = recursive;
    }
    if (recursive)
      continue;
    CGNode *node = component.front();
    node->inRecursion = std::any_of(
        node->callees.begin(), node->callees.end(),
        [node](const CGNode::Edge &edge) { return edge.callee == node; });
  }
}

} // namespace svm::ir
