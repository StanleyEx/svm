#include "Analysis.h"
#include "IR.h"
#include "LIRPass.h"

#include <algorithm>
#include <cstdlib>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

using BlockSet = std::unordered_set<BasicBlock *>;
using ControlDependencies =
    std::unordered_map<BasicBlock *, std::vector<BasicBlock *>>;

struct ADCEChanges {
  bool changed = false;    // 是否修改了指令或 CFG
  bool cfgChanged = false; // 是否修改了 CFG 结构
};

struct PhiRepair {
  Inst *phi = nullptr;   // 目标块中的活 Phi
  Inst *value = nullptr; // 新边应携带的值
};

BlockSet computeReachable(Function *function) {
  BlockSet reachable;
  if (!function || !function->region || !function->region->first)
    return reachable;

  std::vector<BasicBlock *> worklist{function->region->first};
  reachable.insert(function->region->first);
  while (!worklist.empty()) {
    BasicBlock *block = worklist.back();
    worklist.pop_back();
    forEachSuccessor(block, [&](BasicBlock *successor) {
      if (reachable.insert(successor).second)
        worklist.push_back(successor);
    });
  }
  return reachable;
}

ControlDependencies buildControlDependencies(Function *function,
                                             const BlockSet &reachable,
                                             const PostDominatorTree &postDom) {
  ControlDependencies dependencies;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (!reachable.count(block) || successorCount(block) < 2)
      continue;

    BasicBlock *limit = postDom.getIPostDom(block);
    forEachSuccessor(block, [&](BasicBlock *runner) {
      BlockSet seen;
      while (runner && runner != limit && reachable.count(runner) &&
             seen.insert(runner).second) {
        dependencies[runner].push_back(block);
        runner = postDom.getIPostDom(runner);
      }
    });
  }

  for (auto &[_, blocks] : dependencies) {
    std::sort(blocks.begin(), blocks.end(),
              [](const BasicBlock *left, const BasicBlock *right) {
                return left->id < right->id;
              });
    blocks.erase(std::unique(blocks.begin(), blocks.end()), blocks.end());
  }
  return dependencies;
}

bool collectPhiValuesOnBypassedPaths(BasicBlock *start, BasicBlock *target,
                                     const std::vector<Inst *> &targetPhis,
                                     const BlockSet &liveBlocks,
                                     std::vector<Inst *> &values) {
  if (start == target)
    return true;

  BlockSet nodes;
  std::vector<BasicBlock *> worklist{start};
  bool reachedTarget = false;
  while (!worklist.empty()) {
    BasicBlock *block = worklist.back();
    worklist.pop_back();
    if (!block || !nodes.insert(block).second)
      continue;
    if (liveBlocks.count(block))
      return false;

    u32 successorCount = 0;
    bool valid = true;
    forEachSuccessor(block, [&](BasicBlock *successor) {
      ++successorCount;
      if (!valid)
        return;
      if (successor != target) {
        worklist.push_back(successor);
        return;
      }

      reachedTarget = true;
      for (usize index = 0; index < targetPhis.size(); ++index) {
        Inst *value = CFGEditor::getPhiIncomingValue(targetPhis[index], block);
        if (!value || (values[index] && values[index] != value)) {
          valid = false;
          return;
        }
        values[index] = value;
      }
    });
    if (!valid || successorCount == 0)
      return false;
  }

  // 绕过区域必须无环 否则直达 target 会改变可能不终止的执行
  std::unordered_map<BasicBlock *, u32> indegree;
  for (BasicBlock *block : nodes)
    indegree.emplace(block, 0);
  for (BasicBlock *block : nodes) {
    bool valid = true;
    forEachSuccessor(block, [&](BasicBlock *successor) {
      if (successor == target)
        return;
      auto found = indegree.find(successor);
      if (found == indegree.end()) {
        valid = false;
        return;
      }
      ++found->second;
    });
    if (!valid)
      return false;
  }

  std::vector<BasicBlock *> zeroIndegree;
  for (const auto &[block, degree] : indegree)
    if (degree == 0)
      zeroIndegree.push_back(block);
  usize visited = 0;
  while (!zeroIndegree.empty()) {
    BasicBlock *block = zeroIndegree.back();
    zeroIndegree.pop_back();
    ++visited;
    forEachSuccessor(block, [&](BasicBlock *successor) {
      if (successor == target)
        return;
      auto found = indegree.find(successor);
      if (found != indegree.end() && --found->second == 0)
        zeroIndegree.push_back(successor);
    });
  }
  return reachedTarget && visited == nodes.size();
}

bool planPhiRepair(BasicBlock *source, BasicBlock *target,
                   const std::unordered_set<Inst *> &live,
                   const BlockSet &liveBlocks,
                   std::vector<PhiRepair> &repairs) {
  repairs.clear();
  if (!source || !target || source == target)
    return false;

  std::vector<Inst *> targetPhis;
  for (Inst *phi = target->firstPhi(); phi; phi = phi->next())
    if (live.count(phi))
      targetPhis.push_back(phi);
  if (targetPhis.empty())
    return true;

  std::vector<Inst *> values(targetPhis.size(), nullptr);
  u32 oldSuccessorCount = 0;
  bool valid = true;
  forEachSuccessor(source, [&](BasicBlock *successor) {
    ++oldSuccessorCount;
    if (!valid)
      return;
    if (successor == target) {
      for (usize index = 0; index < targetPhis.size(); ++index) {
        Inst *value = CFGEditor::getPhiIncomingValue(targetPhis[index], source);
        if (!value || (values[index] && values[index] != value)) {
          valid = false;
          return;
        }
        values[index] = value;
      }
    } else if (!collectPhiValuesOnBypassedPaths(successor, target, targetPhis,
                                                liveBlocks, values)) {
      valid = false;
    }
  });
  if (!valid || oldSuccessorCount == 0)
    return false;

  for (usize index = 0; index < targetPhis.size(); ++index) {
    if (!values[index])
      return false;
    if (!CFGEditor::getPhiIncomingValue(targetPhis[index], source))
      repairs.push_back({targetPhis[index], values[index]});
  }
  return true;
}

bool redirectToPostDominator(Function *function, BasicBlock *source,
                             BasicBlock *target,
                             const std::vector<PhiRepair> &repairs) {
  if (CFGEditor::hasSemanticEdge(source, target))
    return CFGEditor::foldTerminatorToJump(function, source, target);

  BasicBlock *oldSuccessor = nullptr;
  forEachSuccessor(source, [&](BasicBlock *successor) {
    if (!oldSuccessor)
      oldSuccessor = successor;
  });
  if (!oldSuccessor)
    return false;

  std::vector<CFGEditor::PhiEdgeValue> values;
  values.reserve(repairs.size());
  for (const PhiRepair &repair : repairs)
    values.push_back({repair.phi, repair.value});
  if (!CFGEditor::redirectEdge(function, source, oldSuccessor, target, values))
    return false;

  Inst *terminator = source->terminator();
  if (!terminator || terminator->getOp() != OP_JMP ||
      terminator->getJumpTarget() != target)
    (void)CFGEditor::foldTerminatorToJump(function, source, target);
  return true;
}

void eraseDeadInstructions(Function *function,
                           const std::vector<Inst *> &dead) {
  IRBuilder builder(function->module, function);
  for (Inst *inst : dead)
    builder.replaceInPlace(inst, inst->getOp(), inst->getType());
  for (Inst *inst : dead)
    if (!inst->eraseFromBlock())
      std::abort();
}

ADCEChanges runADCE(Function *function, const PostDominatorTree &postDom,
                    const GlobalSummaryResult *effects, bool initiallyChanged) {
  ADCEChanges result{initiallyChanged, initiallyChanged};
  const BlockSet reachable = computeReachable(function);
  const ControlDependencies controlDependencies =
      buildControlDependencies(function, reachable, postDom);

  std::unordered_set<Inst *> live;
  BlockSet liveBlocks;
  std::vector<Inst *> worklist;
  auto mark = [&](Inst *inst) {
    if (inst && inst->parentBlock() && live.insert(inst).second)
      worklist.push_back(inst);
  };

  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (!reachable.count(block))
      continue;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      const OpCode op = inst->getOp();
      const bool observableCall =
          op == OP_CALL &&
          (!effects || effects->calleeEffect(inst->getCallee()).maySide());
      if (op == OP_RET || op == OP_STORE || observableCall ||
          isLocalInitAnchor(op) ||
          (isLIRTerminator(op) && op != OP_BR && op != OP_JMP))
        mark(inst);
    }
  }

  while (!worklist.empty()) {
    Inst *inst = worklist.back();
    worklist.pop_back();
    for (u32 index = 0; index < inst->getOperandCount(); ++index)
      mark(inst->getArg(index));

    if (inst->getOp() == OP_PHI)
      for (u32 index = 0; index < inst->getOperandCount(); ++index) {
        BasicBlock *predecessor = inst->getIncomingBlock(index);
        if (predecessor)
          mark(predecessor->terminator());
      }

    BasicBlock *block = inst->parentBlock();
    if (!block || !liveBlocks.insert(block).second)
      continue;
    const auto found = controlDependencies.find(block);
    if (found == controlDependencies.end())
      continue;
    for (BasicBlock *controller : found->second)
      mark(controller->terminator());
  }

  IRBuilder builder(function->module, function);
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    Inst *terminator = block->terminator();
    if (!terminator || terminator->getOp() != OP_BR || live.count(terminator))
      continue;
    Inst *condition = terminator->getArg(0);
    if (condition && !live.count(condition)) {
      terminator->setArg(0, builder.i1Const(false));
      result.changed = true;
    }
  }

  std::vector<Inst *> dead;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      if (!live.count(phi))
        dead.push_back(phi);
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      if (!isLIRTerminator(inst->getOp()) && !live.count(inst))
        dead.push_back(inst);
  }
  if (!dead.empty()) {
    eraseDeadInstructions(function, dead);
    result.changed = true;
  }

  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (!reachable.count(block))
      continue;
    Inst *terminator = block->terminator();
    if (!terminator || live.count(terminator) ||
        (terminator->getOp() != OP_BR && terminator->getOp() != OP_JMP))
      continue;

    BasicBlock *target =
        postDom.nearestPostDomIf(block, [&](BasicBlock *candidate) {
          return liveBlocks.count(candidate);
        });
    std::vector<PhiRepair> repairs;
    if (!target || !planPhiRepair(block, target, live, liveBlocks, repairs) ||
        !redirectToPostDominator(function, block, target, repairs))
      continue;
    result.changed = true;
    result.cfgChanged = true;
  }

  if (cleanupDeadBlocks(function)) {
    result.changed = true;
    result.cfgChanged = true;
  }
  if (result.cfgChanged && !computePreds(function))
    std::abort();
  return result;
}

} // namespace

std::string_view ADCEPass::name() const noexcept { return "adce"; }

PassResult ADCEPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();

  computeUses(function);
  const bool removedUnreachable = cleanupDeadBlocks(function);
  if (removedUnreachable)
    context.invalidate(function, PreservedAnalyses::none());
  if (!computePreds(function))
    return removedUnreachable ? PassResult::changedIR()
                              : PassResult::noChange();
  computeUses(function);

  const PostDominatorTree &postDom =
      context.get<PostDomAnalysis>(function).tree;
  // ADCE 不会新增副作用 因此该摘要对于剩余调用仍是 sound 的
  const GlobalSummaryResult *effects =
      function->module
          ? &context.get<GlobalSummaryAnalysis>(function->module).result
          : nullptr;
  const ADCEChanges changes =
      runADCE(function, postDom, effects, removedUnreachable);
  if (!changes.changed)
    return PassResult::noChange();

  PreservedAnalyses preserved;
  preserved.preserveSSAForm();
  if (!changes.cfgChanged)
    preserved.preserveCFGAnalyses();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
