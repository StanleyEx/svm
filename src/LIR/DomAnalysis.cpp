#include "DomAnalysis.h"

#include <algorithm>
#include <cassert>

namespace svm::ir {

const DominatorTree::Node *
DominatorTree::findNode(const BasicBlock *block) const noexcept {
  const auto found = nodes_.find(block);
  return found == nodes_.end() ? nullptr : &found->second;
}

void DominatorTree::clear() noexcept {
  nodes_.clear();
  children_.clear();
  frontier_.clear();
}

bool DominatorTree::build(Function *function) {
  clear();
  if (!function || function->isExtern || function->phase == IRPhase::HIR ||
      !function->region || !function->region->first)
    return false;

  const std::vector<BasicBlock *> rpo = computeRPO(function);
  if (rpo.empty())
    return false;
  nodes_.reserve(rpo.size());
  for (usize index = 0; index < rpo.size(); ++index) {
    Node &node = nodes_[rpo[index]];
    node.rpo = static_cast<i32>(index);
  }

  BasicBlock *entry = rpo.front();
  nodes_.at(entry).idom = entry;
  auto intersect = [&](BasicBlock *first, BasicBlock *second) {
    while (first != second) {
      while (nodes_.at(first).rpo > nodes_.at(second).rpo)
        first = nodes_.at(first).idom;
      while (nodes_.at(second).rpo > nodes_.at(first).rpo)
        second = nodes_.at(second).idom;
    }
    return first;
  };

  bool changed = true;
  while (changed) {
    changed = false;
    for (BasicBlock *block : rpo) {
      if (block == entry)
        continue;
      BasicBlock *newIDom = nullptr;
      for (u32 index = 0; index < block->getPredecessorCount(); ++index) {
        BasicBlock *predecessor = block->getPredecessor(index);
        const Node *predNode = findNode(predecessor);
        if (!predNode || !predNode->idom)
          continue;
        newIDom = newIDom ? intersect(predecessor, newIDom) : predecessor;
      }
      Node &node = nodes_.at(block);
      if (node.idom != newIDom) {
        node.idom = newIDom;
        changed = true;
      }
    }
  }
  for (BasicBlock *block : rpo)
    if (block != entry && !nodes_.at(block).idom) {
      clear();
      return false;
    }
  nodes_.at(entry).idom = nullptr;

  for (BasicBlock *block : rpo) {
    BasicBlock *idom = nodes_.at(block).idom;
    if (idom)
      children_[idom].push_back(block);
  }

  struct DFSFrame {
    BasicBlock *block = nullptr; // 当前支配树节点
    usize nextChild = 0;         // 下一个待访问子节点
  };
  i32 clock = 0;
  nodes_.at(entry).depth = 0;
  nodes_.at(entry).in = ++clock;
  std::vector<DFSFrame> stack{{entry, 0}};
  while (!stack.empty()) {
    DFSFrame &frame = stack.back();
    const auto found = children_.find(frame.block);
    if (found != children_.end() && frame.nextChild < found->second.size()) {
      BasicBlock *child = found->second[frame.nextChild++];
      Node &childNode = nodes_.at(child);
      childNode.depth = nodes_.at(frame.block).depth + 1;
      childNode.in = ++clock;
      stack.push_back({child, 0});
      continue;
    }
    nodes_.at(frame.block).out = ++clock;
    stack.pop_back();
  }

  for (BasicBlock *block : rpo) {
    if (block->getPredecessorCount() < 2)
      continue;
    BasicBlock *blockIDom = nodes_.at(block).idom;
    for (u32 index = 0; index < block->getPredecessorCount(); ++index) {
      BasicBlock *runner = block->getPredecessor(index);
      while (runner && runner != blockIDom) {
        const Node *runnerNode = findNode(runner);
        if (!runnerNode)
          break;
        frontier_[runner].push_back(block);
        runner = runnerNode->idom;
      }
    }
  }
  for (auto &[_, blocks] : frontier_) {
    std::sort(blocks.begin(), blocks.end(),
              [](const BasicBlock *left, const BasicBlock *right) {
                return left->id < right->id;
              });
    blocks.erase(std::unique(blocks.begin(), blocks.end()), blocks.end());
  }
  return true;
}

bool DominatorTree::dominates(const BasicBlock *dominator,
                              const BasicBlock *block) const noexcept {
  if (!dominator || !block)
    return false;
  const Node *dominatorNode = findNode(dominator);
  const Node *blockNode = findNode(block);
  if (!dominatorNode || !blockNode || dominatorNode->depth < 0 ||
      blockNode->depth < 0)
    return false;
  return dominatorNode->in <= blockNode->in &&
         blockNode->out <= dominatorNode->out;
}

BasicBlock *DominatorTree::getIDom(BasicBlock *block) const noexcept {
  const Node *node = findNode(block);
  return node ? node->idom : nullptr;
}

i32 DominatorTree::getDepth(const BasicBlock *block) const noexcept {
  const Node *node = findNode(block);
  return node ? node->depth : -1;
}

i32 PostDominatorTree::indexOf(const BasicBlock *block) const noexcept {
  const auto found = indices_.find(block);
  return found == indices_.end() ? -1 : found->second;
}

i32 PostDominatorTree::intersect(i32 first, i32 second) const noexcept {
  while (first != second) {
    while (rpoNumbers_[first] > rpoNumbers_[second])
      first = ipdom_[first];
    while (rpoNumbers_[second] > rpoNumbers_[first])
      second = ipdom_[second];
  }
  return first;
}

void PostDominatorTree::clear() noexcept {
  indices_.clear();
  blocks_.clear();
  ipdom_.clear();
  rpoNumbers_.clear();
}

bool PostDominatorTree::build(Function *function) {
  clear();
  if (!function || function->isExtern || function->phase == IRPhase::HIR ||
      !function->region || !function->region->first)
    return false;

  blocks_ = computeRPO(function);
  if (blocks_.empty())
    return false;
  indices_.reserve(blocks_.size());
  for (usize index = 0; index < blocks_.size(); ++index)
    indices_.emplace(blocks_[index], static_cast<i32>(index));

  const i32 blockCount = static_cast<i32>(blocks_.size());
  std::vector<std::vector<i32>> successors(blockCount);
  std::vector<i32> exits;
  for (i32 index = 0; index < blockCount; ++index) {
    forEachSuccessor(blocks_[index], [&](BasicBlock *successor) {
      const i32 successorIndex = indexOf(successor);
      assert(successorIndex >= 0);
      successors[index].push_back(successorIndex);
    });
    if (successors[index].empty())
      exits.push_back(index);
  }

  const i32 omega = blockCount;
  ipdom_.assign(static_cast<usize>(blockCount + 1), -1);
  rpoNumbers_.assign(static_cast<usize>(blockCount + 1), -1);
  if (exits.empty())
    return true;

  std::vector<u8> safe(blockCount, 0);
  std::vector<i32> worklist = exits;
  for (i32 exit : exits)
    safe[exit] = 1;
  while (!worklist.empty()) {
    const i32 current = worklist.back();
    worklist.pop_back();
    BasicBlock *block = blocks_[current];
    for (u32 slot = 0; slot < block->getPredecessorCount(); ++slot) {
      const i32 predecessor = indexOf(block->getPredecessor(slot));
      if (predecessor >= 0 && !safe[predecessor]) {
        safe[predecessor] = 1;
        worklist.push_back(predecessor);
      }
    }
  }

  worklist.clear();
  for (i32 index = 0; index < blockCount; ++index)
    if (!safe[index])
      worklist.push_back(index);
  while (!worklist.empty()) {
    const i32 current = worklist.back();
    worklist.pop_back();
    BasicBlock *block = blocks_[current];
    for (u32 slot = 0; slot < block->getPredecessorCount(); ++slot) {
      const i32 predecessor = indexOf(block->getPredecessor(slot));
      if (predecessor >= 0 && safe[predecessor]) {
        safe[predecessor] = false;
        worklist.push_back(predecessor);
      }
    }
  }

  struct DFSFrame {
    i32 node = -1;       // 当前反向CFG节点
    usize nextChild = 0; // 下一个待访问后继
  };
  std::vector<i32> postorder;
  std::vector<DFSFrame> stack{{omega, 0}};
  rpoNumbers_[omega] = 0;
  while (!stack.empty()) {
    DFSFrame &frame = stack.back();
    bool descended = false;
    if (frame.node == omega) {
      while (frame.nextChild < exits.size()) {
        const i32 child = exits[frame.nextChild++];
        if (safe[child] && rpoNumbers_[child] < 0) {
          rpoNumbers_[child] = 0;
          stack.push_back({child, 0});
          descended = true;
          break;
        }
      }
    } else {
      BasicBlock *block = blocks_[frame.node];
      while (frame.nextChild < block->getPredecessorCount()) {
        const i32 child = indexOf(block->getPredecessor(frame.nextChild++));
        if (child >= 0 && safe[child] && rpoNumbers_[child] < 0) {
          rpoNumbers_[child] = 0;
          stack.push_back({child, 0});
          descended = true;
          break;
        }
      }
    }
    if (descended)
      continue;
    postorder.push_back(frame.node);
    stack.pop_back();
  }
  std::reverse(postorder.begin(), postorder.end());
  for (usize index = 0; index < postorder.size(); ++index)
    rpoNumbers_[postorder[index]] = static_cast<i32>(index);

  ipdom_[omega] = omega;
  bool changed = true;
  while (changed) {
    changed = false;
    for (i32 node : postorder) {
      if (node == omega)
        continue;
      i32 newIPDom = -1;
      if (successors[node].empty()) {
        newIPDom = omega;
      } else {
        for (i32 successor : successors[node]) {
          if (ipdom_[successor] < 0)
            continue;
          newIPDom = newIPDom < 0 ? successor : intersect(successor, newIPDom);
        }
      }
      if (newIPDom >= 0 && ipdom_[node] != newIPDom) {
        ipdom_[node] = newIPDom;
        changed = true;
      }
    }
  }

  for (i32 index = 0; index < blockCount; ++index)
    if (safe[index] && ipdom_[index] < 0) {
      clear();
      return false;
    }
  return true;
}

bool PostDominatorTree::postDominates(const BasicBlock *dominator,
                                      const BasicBlock *block) const noexcept {
  const i32 target = indexOf(dominator);
  i32 current = indexOf(block);
  if (target < 0 || current < 0 || ipdom_[target] < 0 || ipdom_[current] < 0)
    return false;
  if (target == current)
    return true;
  current = ipdom_[current];
  const i32 omega = static_cast<i32>(blocks_.size());
  while (current >= 0 && current != omega) {
    if (current == target)
      return true;
    current = ipdom_[current];
  }
  return false;
}

BasicBlock *PostDominatorTree::getIPostDom(BasicBlock *block) const noexcept {
  const i32 index = indexOf(block);
  if (index < 0 || ipdom_[index] < 0 ||
      ipdom_[index] == static_cast<i32>(blocks_.size()))
    return nullptr;
  return blocks_[ipdom_[index]];
}

BasicBlock *PostDominatorTree::nearestCommonPostDominator(
    BasicBlock *first, BasicBlock *second) const noexcept {
  const i32 firstIndex = indexOf(first);
  const i32 secondIndex = indexOf(second);
  if (firstIndex < 0 || secondIndex < 0 || ipdom_[firstIndex] < 0 ||
      ipdom_[secondIndex] < 0 || rpoNumbers_[firstIndex] < 0 ||
      rpoNumbers_[secondIndex] < 0)
    return nullptr;
  const i32 common = intersect(firstIndex, secondIndex);
  return common == static_cast<i32>(blocks_.size()) ? nullptr : blocks_[common];
}

} // namespace svm::ir
