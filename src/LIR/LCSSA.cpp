#include "Analysis.h"
#include "LIRPass.h"
#include "Utils.h"

#include <functional>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

struct UseSite {
  Inst *user = nullptr; // 待重写用户
  u32 argument = 0;     // 待重写操作数
};

class LoopValueCloser {
public:
  LoopValueCloser(Function *function, Loop *loop,
                  const DominatorTree &dominatorTree)
      : function_(function), loop_(loop), dominatorTree_(dominatorTree),
        builder_(function->module, function),
        loopBlocks_(loop->blocks().begin(), loop->blocks().end()) {}

  bool run() {
    std::unordered_map<Inst *, std::vector<UseSite>> escaping;
    for (BasicBlock *block : loop_->blocks())
      forEachOp(block, [&](Inst *definition) {
        if (isVoid(definition->getType()))
          return;
        for (const Use *use = definition->uses(); use; use = use->next) {
          Inst *user = use->user;
          BasicBlock *userBlock = user ? user->parentBlock() : nullptr;
          if (!userBlock || loopBlocks_.count(userBlock))
            continue;
          if (user->getOp() == OP_PHI &&
              loopBlocks_.count(user->getIncomingBlock(use->argNo)))
            continue;
          escaping[definition].push_back({user, use->argNo});
        }
      });

    for (auto &[definition, uses] : escaping)
      closeValue(definition, uses);
    return !escaping.empty();
  }

private:
  Function *function_ = nullptr;
  Loop *loop_ = nullptr;
  const DominatorTree &dominatorTree_;
  IRBuilder builder_;
  std::unordered_set<BasicBlock *> loopBlocks_; // 循环块集合

  // 解析零次执行路径上的Header Phi值
  Inst *bypassValue(Inst *definition, BasicBlock *predecessor,
                    Inst *undef) const {
    if (definition->getOp() != OP_PHI ||
        definition->parentBlock() != loop_->header())
      return undef;
    // 多入口循环先按真实CFG边精确匹配 不能把另一入口的初值带到当前旁路
    for (u32 index = 0; index < definition->getOperandCount(); ++index) {
      BasicBlock *incoming = definition->getIncomingBlock(index);
      if (incoming == predecessor)
        return definition->getArg(index);
    }

    Inst *candidate = nullptr;
    for (u32 index = 0; index < definition->getOperandCount(); ++index) {
      BasicBlock *incoming = definition->getIncomingBlock(index);
      if (loopBlocks_.count(incoming))
        continue;
      Inst *initial = definition->getArg(index);
      BasicBlock *initialBlock = initial->parentBlock();
      if (initialBlock && !dominatorTree_.dominates(initialBlock, predecessor))
        continue;
      if (candidate && candidate != initial)
        return undef;
      candidate = initial;
    }
    return candidate ? candidate : undef;
  }

  // 重建单值的外部SSA
  void closeValue(Inst *definition, const std::vector<UseSite> &uses) {
    Inst *undef = builder_.makeUndef(definition->getType());
    std::unordered_map<BasicBlock *, Inst *> available;
    std::unordered_set<BasicBlock *> uniqueExits(loop_->exitBlocks().begin(),
                                                 loop_->exitBlocks().end());

    for (BasicBlock *exit : uniqueExits) {
      Inst *phi = builder_.emitPhi(definition->getType(), exit, undef);
      for (u32 index = 0; index < exit->getPredecessorCount(); ++index) {
        BasicBlock *predecessor = exit->getPredecessor(index);
        Inst *value = undef;
        if (loopBlocks_.count(predecessor)) {
          if (dominatorTree_.dominates(definition->parentBlock(), predecessor))
            value = definition;
        } else if (dominatorTree_.dominates(exit, predecessor)) {
          value = phi;
        } else {
          value = bypassValue(definition, predecessor, undef);
        }
        VERIFY(CFGEditor::setPhiEdgeValues(function_, exit, predecessor,
                                           {{phi, value}}));
      }
      available.emplace(exit, phi);
    }

    const std::function<Inst *(BasicBlock *)> valueAtEnd =
        [&](BasicBlock *block) -> Inst * {
      if (!block)
        return undef;
      if (loopBlocks_.count(block))
        return dominatorTree_.dominates(definition->parentBlock(), block)
                   ? definition
                   : undef;
      if (const auto found = available.find(block); found != available.end())
        return found->second;
      if (block->getPredecessorCount() == 0) {
        available.emplace(block, undef);
        return undef;
      }

      Inst *phi = builder_.emitPhi(definition->getType(), block, undef);
      available.emplace(block, phi); // 先登记以切断循环外CFG中的递归环
      Inst *common = nullptr;
      bool allSame = true;
      for (u32 index = 0; index < block->getPredecessorCount(); ++index) {
        BasicBlock *predecessor = block->getPredecessor(index);
        Inst *value = valueAtEnd(predecessor);
        VERIFY(CFGEditor::setPhiEdgeValues(function_, block, predecessor,
                                           {{phi, value}}));
        if (!common)
          common = value;
        else
          allSame &= common == value;
      }
      if (allSame && common != phi) {
        replaceAllUsesWith(function_, phi, common);
        // 递归回边可能让多个Block缓存同一乐观Phi
        // RAUW只维护IR Use链
        // 删除前必须同步全部缓存别名 避免后续查询把已擦除指令接回Use-Def链
        for (auto &pair : available)
          if (pair.second == phi)
            pair.second = common;
        VERIFY(phi->eraseFromBlock());
        available[block] = common;
        return common;
      }
      return phi;
    };

    for (const UseSite &use : uses) {
      BasicBlock *effectiveBlock = use.user->parentBlock();
      if (use.user->getOp() == OP_PHI)
        effectiveBlock = use.user->getIncomingBlock(use.argument);
      use.user->setArg(use.argument, valueAtEnd(effectiveBlock));
    }
  }
};

bool teardownTrivialPhis(Function *function) {
  bool changed = false;
  bool roundChanged = false;
  do {
    roundChanged = false;
    for (BasicBlock *block = function->region->first; block;
         block = block->next()) {
      for (Inst *phi = block->firstPhi(); phi;) {
        Inst *next = phi->next();
        if (phi->getOperandCount() != 0) {
          Inst *value = phi->getArg(0);
          bool allSame = true;
          for (u32 index = 1; index < phi->getOperandCount(); ++index)
            allSame &= phi->getArg(index) == value;
          if (allSame && value != phi) {
            replaceAllUsesWith(function, phi, value);
            VERIFY(phi->eraseFromBlock());
            roundChanged = changed = true;
          }
        }
        phi = next;
      }
    }
  } while (roundChanged);
  return changed;
}

} // namespace

bool formLCSSA(Function *function, FunctionAnalysisManager &analyses) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return false;

  computeUses(function);
  const DominatorTree &dominatorTree =
      analyses.getResult<DomAnalysis>(function).tree;
  const LoopInfo &loopInfo =
      analyses.getResult<LoopInfoAnalysis>(function).info;
  std::vector<Loop *> postorder;
  // 先封闭内层循环 外层随后只需处理已经合法的内层出口值
  const std::function<void(Loop *)> collect = [&](Loop *loop) {
    for (Loop *child : loop->children())
      collect(child);
    postorder.push_back(loop);
  };
  for (Loop *loop : loopInfo.topLevelLoops())
    collect(loop);

  bool changed = false;
  for (Loop *loop : postorder)
    if (!loop->exitBlocks().empty())
      changed |= LoopValueCloser(function, loop, dominatorTree).run();
  return changed;
}

bool teardownLCSSA(Function *function) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region)
    return false;
  computeUses(function);
  return teardownTrivialPhis(function);
}

bool verifyLCSSA(Function *function, FunctionAnalysisManager &analyses) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region)
    return true;
  computeUses(function);
  const LoopInfo &loopInfo =
      analyses.getResult<LoopInfoAnalysis>(function).info;

  bool valid = true;
  const std::function<void(Loop *)> verifyLoop = [&](Loop *loop) {
    const std::unordered_set<BasicBlock *> blocks(loop->blocks().begin(),
                                                  loop->blocks().end());
    for (BasicBlock *block : loop->blocks())
      forEachOp(block, [&](Inst *definition) {
        if (isVoid(definition->getType()))
          return;
        for (const Use *use = definition->uses(); use; use = use->next) {
          Inst *user = use->user;
          BasicBlock *userBlock = user ? user->parentBlock() : nullptr;
          if (!userBlock || blocks.count(userBlock))
            continue;
          if (user->getOp() == OP_PHI &&
              blocks.count(user->getIncomingBlock(use->argNo)))
            continue;
          valid = false;
        }
      });
    for (Loop *child : loop->children())
      verifyLoop(child);
  };
  for (Loop *loop : loopInfo.topLevelLoops())
    verifyLoop(loop);
  return valid;
}

std::string_view LCSSAPass::name() const noexcept { return "lcssa"; }

PassResult LCSSAPass::run(Function *function, PassContext &context) {
  if (!formLCSSA(function, context.functionAnalyses()))
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

std::string_view LCSSATeardownPass::name() const noexcept {
  return "lcssa-teardown";
}

PassResult LCSSATeardownPass::run(Function *function, PassContext &context) {
  UNUSED(context);
  if (!teardownLCSSA(function))
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
