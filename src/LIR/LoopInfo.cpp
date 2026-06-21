#include "LoopInfo.h"
#include "DomAnalysis.h"

#include <algorithm>
#include <cassert>
#include <unordered_map>
#include <unordered_set>

namespace svm::ir {

bool Loop::contains(const BasicBlock *block) const noexcept {
  return block &&
         std::find(blocks_.begin(), blocks_.end(), block) != blocks_.end();
}

bool Loop::containsLoop(const Loop *loop) const noexcept {
  for (const Loop *current = loop; current; current = current->parent_)
    if (current == this)
      return true;
  return false;
}

BasicBlock *Loop::getPreheader() const noexcept {
  if (!header_)
    return nullptr;
  BasicBlock *preheader = nullptr;
  for (u32 index = 0; index < header_->getPredecessorCount(); ++index) {
    BasicBlock *predecessor = header_->getPredecessor(index);
    if (contains(predecessor))
      continue;
    if (preheader)
      return nullptr;
    preheader = predecessor;
  }
  // Preheader必须专门跳向header 否则在其中插入代码会影响循环外路径
  if (preheader && successorCount(preheader) != 1)
    return nullptr;
  return preheader;
}

Loop *LoopInfo::getLoopFor(const BasicBlock *block) const noexcept {
  const auto found = innermost_.find(block);
  return found == innermost_.end() ? nullptr : found->second;
}

i32 LoopInfo::getLoopDepth(const BasicBlock *block) const noexcept {
  const Loop *loop = getLoopFor(block);
  return loop ? loop->depth_ : 0;
}

bool LoopInfo::isLoopHeader(const BasicBlock *block) const noexcept {
  const Loop *loop = getLoopFor(block);
  return loop && loop->header_ == block;
}

void LoopInfo::build(Function *function, const DominatorTree &tree) {
  loops_.clear();
  topLevel_.clear();
  innermost_.clear();
  assert(function && function->phase != IRPhase::HIR);
  if (!function || !function->region)
    return;

  std::unordered_map<BasicBlock *, Loop *> byHeader;
  std::unordered_map<Loop *, std::unordered_set<BasicBlock *>> bodies;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    forEachSuccessor(block, [&](BasicBlock *successor) {
      if (!tree.dominates(successor, block))
        return;
      Loop *loop = nullptr;
      const auto found = byHeader.find(successor);
      if (found == byHeader.end()) {
        auto owned = std::make_unique<Loop>();
        owned->header_ = successor;
        loop = owned.get();
        loops_.push_back(std::move(owned));
        byHeader.emplace(successor, loop);
      } else {
        loop = found->second;
      }
      loop->latches_.push_back(block);
      auto &body = bodies[loop];
      if (body.insert(successor).second)
        loop->blocks_.push_back(successor);
      std::vector<BasicBlock *> worklist;
      if (body.insert(block).second) {
        loop->blocks_.push_back(block);
        worklist.push_back(block);
      }
      while (!worklist.empty()) {
        BasicBlock *current = worklist.back();
        worklist.pop_back();
        for (u32 index = 0; index < current->getPredecessorCount(); ++index) {
          BasicBlock *predecessor = current->getPredecessor(index);
          // 前驱数组也含不可达块 自然循环只吸纳被header支配的块
          if (!tree.dominates(successor, predecessor))
            continue;
          if (body.insert(predecessor).second) {
            loop->blocks_.push_back(predecessor);
            worklist.push_back(predecessor);
          }
        }
      }
    });
  }

  for (const auto &owned : loops_) {
    Loop *loop = owned.get();
    for (BasicBlock *ancestor = tree.getIDom(loop->header_); ancestor;
         ancestor = tree.getIDom(ancestor)) {
      const auto found = byHeader.find(ancestor);
      if (found != byHeader.end() &&
          bodies[found->second].count(loop->header_)) {
        loop->parent_ = found->second;
        loop->parent_->children_.push_back(loop);
        break;
      }
    }
    if (!loop->parent_)
      topLevel_.push_back(loop);
  }

  auto assignDepth = [&](Loop *loop, i32 depth, auto &self) -> void {
    loop->depth_ = depth;
    for (Loop *child : loop->children_)
      self(child, depth + 1, self);
  };
  for (Loop *loop : topLevel_)
    assignDepth(loop, 1, assignDepth);

  std::vector<Loop *> deepestFirst;
  deepestFirst.reserve(loops_.size());
  for (const auto &loop : loops_)
    deepestFirst.push_back(loop.get());
  std::stable_sort(deepestFirst.begin(), deepestFirst.end(),
                   [](const Loop *left, const Loop *right) {
                     return left->depth_ > right->depth_;
                   });
  for (Loop *loop : deepestFirst)
    for (BasicBlock *block : loop->blocks_)
      innermost_.emplace(block, loop);

  for (const auto &owned : loops_) {
    Loop *loop = owned.get();
    const auto &body = bodies[loop];
    for (BasicBlock *block : loop->blocks_) {
      forEachSuccessor(block, [&](BasicBlock *successor) {
        if (!body.count(successor)) {
          loop->exiting_.push_back(block);
          loop->exits_.push_back(successor);
        }
      });
    }
  }
}

} // namespace svm::ir
