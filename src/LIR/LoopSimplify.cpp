#include "Analysis.h"
#include "LIRPass.h"
#include "Utils.h"

#include <functional>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

bool formDedicatedPreheader(Function *function, Loop *loop) {
  if (!loop || !loop->header() || loop->getPreheader())
    return false;
  BasicBlock *header = loop->header();
  std::vector<BasicBlock *> predecessors;
  predecessors.reserve(header->getPredecessorCount());
  for (u32 index = 0; index < header->getPredecessorCount(); ++index) {
    BasicBlock *predecessor = header->getPredecessor(index);
    if (!loop->contains(predecessor))
      predecessors.push_back(predecessor);
  }
  if (predecessors.empty())
    return false;

  // Threading既可能增加入口边 也可能让唯一入口保留循环外旁路
  // 收束全部外部边可同时保留Header Phi语义和安全的代码插入面
  return CFGEditor::splitBlockPredecessors(
             function, header, predecessors.data(),
             static_cast<u32>(predecessors.size()), header->previous())
             .block != nullptr;
}

bool formSingleLatch(Function *function, Loop *loop) {
  if (!loop || !loop->header() || loop->latches().size() <= 1)
    return false;
  const std::vector<BasicBlock *> &latches = loop->latches();
  // 回边值不同时split helper会在新latch中建立Phi再向Header透传
  return CFGEditor::splitBlockPredecessors(
             function, loop->header(), latches.data(),
             static_cast<u32>(latches.size()), latches.back())
             .block != nullptr;
}

bool formDedicatedExit(Function *function, Loop *loop) {
  if (!loop)
    return false;
  for (BasicBlock *exit : loop->exitBlocks()) {
    if (!exit)
      continue;
    std::vector<BasicBlock *> insidePredecessors;
    insidePredecessors.reserve(exit->getPredecessorCount());
    bool hasOutsidePredecessor = false;
    for (u32 index = 0; index < exit->getPredecessorCount(); ++index) {
      BasicBlock *predecessor = exit->getPredecessor(index);
      if (loop->contains(predecessor))
        insidePredecessors.push_back(predecessor);
      else
        hasOutsidePredecessor = true;
    }
    if (!hasOutsidePredecessor || insidePredecessors.empty())
      continue;

    // 只收束当前循环的退出边 原共享块及其循环外入口保持不变
    if (CFGEditor::splitBlockPredecessors(
            function, exit, insidePredecessors.data(),
            static_cast<u32>(insidePredecessors.size()), exit->previous())
            .block)
      return true;
  }
  return false;
}

bool simplifyOneLoop(Function *function, FunctionAnalysisManager &analyses) {
  const LoopInfo &loops = analyses.getResult<LoopInfoAnalysis>(function).info;
  std::vector<Loop *> worklist;
  const std::function<void(Loop *)> collectPostorder = [&](Loop *loop) {
    for (Loop *child : loop->children())
      collectPostorder(child);
    worklist.push_back(loop);
  };
  for (Loop *loop : loops.topLevelLoops())
    collectPostorder(loop);

  for (Loop *loop : worklist) {
    if (formDedicatedPreheader(function, loop) ||
        formSingleLatch(function, loop) || formDedicatedExit(function, loop))
      return true;
  }
  return false;
}

} // namespace

bool verifyLoopSimplify(Function *function, FunctionAnalysisManager &analyses) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region)
    return true;
  const LoopInfo &loops = analyses.getResult<LoopInfoAnalysis>(function).info;
  bool valid = true;
  const std::function<void(Loop *)> verifyLoop = [&](Loop *loop) {
    BasicBlock *preheader = loop->getPreheader();
    valid &= preheader && preheader->endsWithTerminator() &&
             preheader->terminator()->getOp() == OP_JMP &&
             preheader->terminator()->getJumpTarget() == loop->header();
    valid &= loop->latches().size() == 1;
    for (BasicBlock *exit : loop->exitBlocks())
      for (u32 index = 0; exit && index < exit->getPredecessorCount(); ++index)
        valid &= loop->contains(exit->getPredecessor(index));
    for (Loop *child : loop->children())
      verifyLoop(child);
  };
  for (Loop *loop : loops.topLevelLoops())
    verifyLoop(loop);
  return valid;
}

bool repairLoopForm(Function *function, PassContext &context) {
  FunctionAnalysisManager &analyses = context.functionAnalyses();
  // 调用点刚完成CFG事务 候选阶段的Dom/Loop/SCEV均已过期
  analyses.clear(function);
  LoopSimplifyPass simplify;
  const PassResult simplified = simplify.run(function, context);
  if (simplified.changed)
    analyses.clear(function);
  const bool closed = formLCSSA(function, analyses);
  if (closed) {
    computeUses(function);
    analyses.clear(function);
  }
#ifndef NDEBUG
  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    VERIFY(CFGEditor::hasConsistentIncomingState(block));
  VERIFY(verifyDominance(function));
  VERIFY(verifyLoopSimplify(function, analyses));
  VERIFY(verifyLCSSA(function, analyses));
#endif
  return simplified.changed || closed;
}

std::string_view LoopSimplifyPass::name() const noexcept {
  return "loop-simplify";
}

PassResult LoopSimplifyPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first || !computePreds(function))
    return PassResult::noChange();

  computeUses(function);
  FunctionAnalysisManager &analyses = context.functionAnalyses();
  bool changed = false;
  // 每次CFG施工后重建LoopInfo 避免内层新块被外层的旧blocks/exits误分类
  while (simplifyOneLoop(function, analyses)) {
    changed = true;
    VERIFY(computePreds(function));
    computeUses(function);
    analyses.clear(function);
  }

  if (!changed)
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
