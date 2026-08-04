#include "Analysis.h"
#include "LIRPass.h"
#include "LoopShape.h"

#include <limits>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

void collectLoopsPostorder(Loop *loop, std::vector<Loop *> &result) {
  for (Loop *child : loop->children())
    collectLoopsPostorder(child, result);
  result.push_back(loop);
}

i32 decideComparison(const SCEV &scev, Inst *comparison,
                     BasicBlock *contextBlock) {
  PredicateQuery query;
  query.contextBlock = contextBlock;
  const KnownBool result = scev.evaluatePredicate(comparison, query);
  if (result == KnownBool::AlwaysTrue)
    return 1;
  if (result == KnownBool::AlwaysFalse)
    return 0;
  return -1;
}

bool instDependsOn(Inst *root, Inst *needle) {
  if (!root || !needle)
    return false;
  std::unordered_set<Inst *> visited;
  std::vector<Inst *> worklist{root};
  while (!worklist.empty()) {
    Inst *value = worklist.back();
    worklist.pop_back();
    if (!value || !visited.insert(value).second)
      continue;
    if (value == needle)
      return true;
    for (u32 index = 0; index < value->getOperandCount(); ++index)
      worklist.push_back(value->getArg(index));
  }
  return false;
}

// Expander可复用支配出口的循环内定义 这在普通SSA中合法但是会绕过LCSSA封口
bool breaksLCSSAUse(Inst *definition, Inst *user, u32 argument,
                    const LoopInfo &loopInfo) {
  if (!definition || !definition->parentBlock() || !user ||
      !user->parentBlock())
    return false;
  Loop *loop = loopInfo.getLoopFor(definition->parentBlock());
  if (!loop)
    return false;
  if (user->getOp() == OP_PHI && argument < user->getOperandCount()) {
    BasicBlock *incoming = user->getIncomingBlock(argument);
    if (incoming && loop->contains(incoming))
      return false;
  }
  return !loop->contains(user->parentBlock());
}

bool breaksLCSSAInstruction(Inst *inst, const LoopInfo &loopInfo) {
  if (!inst || !inst->parentBlock())
    return false;
  for (u32 index = 0; index < inst->getOperandCount(); ++index)
    if (breaksLCSSAUse(inst->getArg(index), inst, index, loopInfo))
      return true;
  return false;
}

std::vector<Inst *> insertedBefore(BasicBlock *block, Inst *oldPrevious,
                                   Inst *anchor) {
  std::vector<Inst *> result;
  for (Inst *inst = oldPrevious ? oldPrevious->next()
                                : (block ? block->firstInst() : nullptr);
       inst && inst != anchor; inst = inst->next())
    result.push_back(inst);
  return result;
}

bool breaksLCSSAAny(const std::vector<Inst *> &instructions,
                    const LoopInfo &loopInfo) {
  for (Inst *inst : instructions)
    if (breaksLCSSAInstruction(inst, loopInfo))
      return true;
  return false;
}

void rollback(std::vector<Inst *> &instructions) {
  for (auto it = instructions.rbegin(); it != instructions.rend(); ++it)
    if (*it && (*it)->parentBlock())
      VERIFY((*it)->eraseFromBlock());
}

struct CanonicalIVPlan {
  Loop *loop = nullptr;          // 目标循环
  Inst *canonical = nullptr;     // {0,+,1} header Phi
  Inst *canonicalNext = nullptr; // latch上的下一迭代值
};

struct DerivedIVRewrite {
  struct UseSite {
    Inst *user = nullptr; // 待改写的消费者
    u32 argument = 0;     // IV 所在操作数槽位
  };

  Inst *oldIV = nullptr;         // 原header Phi
  Loop *loop = nullptr;          // 所属循环
  SCEVExpr *base = nullptr;      // 原AddRec 初值
  SCEVExpr *step = nullptr;      // 原AddRec 常量步长
  std::vector<UseSite> useSites; // 精确改写点
};

bool isIVRewriteFriendlyUser(Inst *user) noexcept {
  if (!user)
    return false;
  return isAddressingOp(user->getOp()) || isIntCompare(user->getOp());
}

void collectDerivedIVRewrites(const SCEV &scev, Loop *loop,
                              std::vector<DerivedIVRewrite> &result) {
  if (!loop || !loop->header() || !loop->getPreheader() ||
      loop->latches().size() != 1 || !loop->header()->firstInst())
    return;

  for (Inst *phi = loop->header()->firstPhi(); phi; phi = phi->next()) {
    if (phi->getType() != TY_I32)
      continue;
    std::vector<DerivedIVRewrite::UseSite> uses;
    for (const Use *use = phi->uses(); use; use = use->next) {
      Inst *user = use->user;
      if (user && user->parentBlock() && loop->contains(user->parentBlock()) &&
          isIVRewriteFriendlyUser(user))
        uses.push_back({user, use->argNo});
    }
    if (uses.empty())
      continue;

    SCEVExpr *expression = scev.getSCEV(phi);
    if (!expression || expression->kind != SCEVExpr::K_ADDREC ||
        expression->addRec.loop != loop || !expression->addRec.step ||
        !expression->addRec.step->isConstant())
      continue;
    // 动态步长递推已是每轮一次加法 改成canon*step会反向制造热点乘法
    if (expression->addRec.base->isZero() &&
        expression->addRec.step->cst.v == 1)
      continue;
    if (!expression->addRec.base->isLoopInvariant(loop) ||
        !expression->addRec.step->isLoopInvariant(loop) ||
        !scev.isSafeToExpand(expression->addRec.base, loop->header()) ||
        !scev.isSafeToExpand(expression->addRec.step, loop->header()))
      continue;
    result.push_back({phi, loop, expression->addRec.base,
                      expression->addRec.step, std::move(uses)});
  }
}

Inst *getOrCreateCanonicalIV(Function *function, IRBuilder &builder, Loop *loop,
                             CanonicalIVPlan &plan) {
  if (plan.canonical)
    return plan.canonical;
  if (!function || !loop || !loop->header() || !loop->getPreheader() ||
      loop->latches().size() != 1)
    return nullptr;

  BasicBlock *preheader = loop->getPreheader();
  BasicBlock *latch = loop->latches().front();
  for (u32 index = 0; index < loop->header()->getPredecessorCount(); ++index) {
    BasicBlock *predecessor = loop->header()->getPredecessor(index);
    if (predecessor != preheader && predecessor != latch)
      return nullptr;
  }
  if (!latch->endsWithTerminator())
    return nullptr;

  Inst *phi =
      builder.emitPhi(TY_I32, loop->header(), builder.makeUndef(TY_I32));
  builder.setInsertBefore(latch->terminator());
  Inst *next = builder.emit(OP_ADD, TY_I32, phi, builder.iConst(1));
  VERIFY(CFGEditor::setPhiEdgeValues(function, loop->header(), preheader,
                                     {{phi, builder.iConst(0)}}));
  VERIFY(CFGEditor::setPhiEdgeValues(function, loop->header(), latch,
                                     {{phi, next}}));
  plan = {loop, phi, next};
  return phi;
}

Inst *materializeDerivedFromCanonical(IRBuilder &builder,
                                      SCEVExpander &expander,
                                      const DerivedIVRewrite &rewrite,
                                      Inst *canonical) {
  if (!rewrite.oldIV || !rewrite.loop || !canonical)
    return nullptr;
  Inst *anchor = rewrite.loop->header()->firstInst();
  if (!anchor)
    return nullptr;
  Inst *base = expander.expandCodeFor(rewrite.base, anchor);
  Inst *step = expander.expandCodeFor(rewrite.step, anchor);
  if (!base || !step)
    return nullptr;

  builder.setInsertBefore(anchor);
  Inst *scaled = rewrite.step->isOne()
                     ? canonical
                     : builder.emit(OP_MUL, TY_I32, canonical, step);
  if (rewrite.base->isZero())
    return scaled;
  builder.setInsertBefore(anchor);
  return builder.emit(OP_ADD, TY_I32, base, scaled);
}

struct ExitConditionRewrite {
  Loop *loop = nullptr;          // 目标循环
  SCEVExpr *backedges = nullptr; // 精确回边次数
  Inst *branch = nullptr;        // latch条件分支
  bool continueOnTrue = false;   // true边是否回到header
};

void collectExitConditionRewrites(const SCEV &scev, Loop *loop,
                                  std::vector<ExitConditionRewrite> &result) {
  if (!loop || !loop->header() || !loop->getPreheader() ||
      loop->latches().size() != 1)
    return;
  BasicBlock *latch = loop->latches().front();
  if (!latch->endsWithTerminator() || latch->terminator()->getOp() != OP_BR)
    return;
  Inst *branch = latch->terminator();
  const auto predicate = analyzeLoopPredicate(&scev, loop, branch, nullptr,
                                              loop->header(), nullptr, nullptr);
  if (!predicate || !predicate->comparison ||
      !isIntCompare(predicate->comparison->getOp()))
    return;

  const auto isExistingUnitCounter = [&](Inst *value) {
    SCEVExpr *expression = scev.getSCEV(value);
    return expression && expression->kind == SCEVExpr::K_ADDREC &&
           expression->addRec.loop == loop &&
           expression->addRec.base->isConstant() &&
           expression->addRec.step->isConstant() &&
           expression->addRec.step->cst.v == 1 &&
           (expression->addRec.base->cst.v == 0 ||
            expression->addRec.base->cst.v == 1);
  };
  Inst *comparison = predicate->comparison;
  if (isExistingUnitCounter(comparison->getArg(0)) ||
      isExistingUnitCounter(comparison->getArg(1)))
    return;

  // 只消费SCEV证明的BTC 不在Pass内重推正反向与包含边界距离公式
  SCEVExpr *backedges = scev.getBackedgeTakenCount(loop);
  if (!backedges || backedges->kind == SCEVExpr::K_UNKNOWN)
    return;
  if (backedges->isConstant()) {
    const i64 value = backedges->cst.v;
    if (value < 0 ||
        value > static_cast<i64>(std::numeric_limits<i32>::max()) - 1)
      return;
  } else {
    const auto findAddRec = [&](SCEVExpr *expression,
                                const auto &self) -> SCEVExpr * {
      if (!expression)
        return nullptr;
      if (expression->kind == SCEVExpr::K_ADDREC &&
          expression->addRec.loop == loop)
        return expression;
      if (expression->kind == SCEVExpr::K_ADD ||
          expression->kind == SCEVExpr::K_MUL) {
        for (SCEVExpr *operand : expression->nary.ops)
          if (SCEVExpr *found = self(operand, self))
            return found;
      } else if (expression->kind == SCEVExpr::K_SDIV ||
                 expression->kind == SCEVExpr::K_SREM) {
        if (SCEVExpr *found = self(expression->bin.lhs, self))
          return found;
        return self(expression->bin.rhs, self);
      }
      return nullptr;
    };
    SCEVExpr *left =
        findAddRec(scev.getSCEV(comparison->getArg(0)), findAddRec);
    SCEVExpr *right =
        findAddRec(scev.getSCEV(comparison->getArg(1)), findAddRec);
    const bool hasConstantStep =
        (left && left->addRec.step && left->addRec.step->isConstant()) ||
        (right && right->addRec.step && right->addRec.step->isConstant());
    if (!hasConstantStep)
      return;
  }
  if (!scev.isSafeToExpand(backedges, loop->getPreheader()))
    return;
  result.push_back({loop, backedges, branch, predicate->continueOnTrue});
}

bool applyExitConditionRewrite(Function *function, IRBuilder &builder,
                               SCEVExpander &expander,
                               const ExitConditionRewrite &rewrite,
                               CanonicalIVPlan &plan,
                               const LoopInfo &loopInfo) {
  if (!rewrite.loop || !rewrite.branch)
    return false;
  BasicBlock *preheader = rewrite.loop->getPreheader();
  if (!preheader || !preheader->endsWithTerminator())
    return false;

  Inst *anchor = preheader->terminator();
  Inst *oldPrevious = anchor->previous();
  Inst *backedges = expander.expandCodeFor(rewrite.backedges, anchor);
  std::vector<Inst *> inserted = insertedBefore(preheader, oldPrevious, anchor);
  if (!backedges || breaksLCSSAUse(backedges, rewrite.branch, 0, loopInfo) ||
      breaksLCSSAAny(inserted, loopInfo)) {
    rollback(inserted);
    return false;
  }

  Inst *canonical =
      getOrCreateCanonicalIV(function, builder, rewrite.loop, plan);
  if (!canonical || !plan.canonicalNext) {
    rollback(inserted);
    return false;
  }
  builder.setInsertBefore(rewrite.branch);
  Inst *condition = builder.emit(rewrite.continueOnTrue ? OP_LE : OP_GT, TY_I1,
                                 plan.canonicalNext, backedges);
  rewrite.branch->setArg(0, condition);
  return true;
}

CanonicalIVPlan *findPlan(std::vector<CanonicalIVPlan> &plans, Loop *loop) {
  for (CanonicalIVPlan &plan : plans)
    if (plan.loop == loop)
      return &plan;
  plans.push_back({loop, nullptr, nullptr});
  return &plans.back();
}

bool runIndVarSimp(Function *function, PassContext &context) {
  const LoopInfo &loopInfo = context.get<LoopInfoAnalysis>(function).info;
  const SCEV &scev = context.get<SCEVAnalysis>(function).info;

  std::vector<Loop *> loops;
  for (Loop *top : loopInfo.topLevelLoops())
    collectLoopsPostorder(top, loops);

  struct ExitRewrite {
    Inst *phi = nullptr;        // 待替换的LCSSA Phi
    SCEVExpr *closed = nullptr; // 所有边一致的闭式值
    BasicBlock *exit = nullptr; // 物化块
  };
  std::vector<ExitRewrite> exitRewrites;
  std::unordered_set<Inst *> handledPhis;
  for (Loop *loop : loops) {
    if (loop->exitBlocks().empty() || loop->latches().size() != 1)
      continue;
    BasicBlock *latch = loop->latches().front();
    std::vector<BasicBlock *> exits;
    std::unordered_set<BasicBlock *> seenExits;
    for (BasicBlock *exit : loop->exitBlocks())
      if (exit && seenExits.insert(exit).second)
        exits.push_back(exit);

    for (BasicBlock *exit : exits) {
      for (Inst *phi = exit->firstPhi(); phi; phi = phi->next()) {
        if (handledPhis.count(phi))
          continue;
        SCEVExpr *closed = nullptr;
        bool valid = true;
        for (u32 index = 0; index < phi->getOperandCount(); ++index) {
          BasicBlock *predecessor = phi->getIncomingBlock(index);
          Inst *value = phi->getArg(index);
          SCEVExpr *edge = nullptr;
          if (loop->contains(predecessor)) {
            if (predecessor != latch || !value || !value->parentBlock() ||
                !loop->contains(value->parentBlock())) {
              valid = false;
              break;
            }
            edge = scev.getExitValue(value, loop);
          } else {
            edge = scev.getSCEV(value);
            if (!edge || !edge->isLoopInvariant(loop)) {
              valid = false;
              break;
            }
          }
          if (!edge || (closed && !closed->structurallyEquals(edge))) {
            valid = false;
            break;
          }
          closed = edge;
        }
        if (valid && closed) {
          exitRewrites.push_back({phi, closed, exit});
          handledPhis.insert(phi);
        }
      }
    }
  }

  struct BranchFold {
    Inst *branch = nullptr; // 待折叠内部条件分支
    bool value = false;     // 条件常量
  };
  std::vector<BranchFold> branchFolds;
  for (Loop *loop : loops) {
    for (BasicBlock *block : loop->blocks()) {
      if (loopInfo.getLoopFor(block) != loop || !block->endsWithTerminator())
        continue;
      Inst *branch = block->terminator();
      if (branch->getOp() != OP_BR || !loop->contains(branch->getBr().trueBB) ||
          !loop->contains(branch->getBr().falseBB))
        continue;
      Inst *condition = branch->getArg(0);
      if (!condition || !isIntCompare(condition->getOp()))
        continue;
      const i32 result = decideComparison(scev, condition, block);
      if (result == 0 || result == 1)
        branchFolds.push_back({branch, result == 1});
    }
  }

  std::vector<DerivedIVRewrite> derivedRewrites;
  std::vector<ExitConditionRewrite> exitConditionRewrites;
  for (Loop *loop : loops) {
    collectDerivedIVRewrites(scev, loop, derivedRewrites);
    collectExitConditionRewrites(scev, loop, exitConditionRewrites);
  }
  if (exitRewrites.empty() && branchFolds.empty() && derivedRewrites.empty() &&
      exitConditionRewrites.empty())
    return false;

  // 候选基于同一份干净SCEV快照 从这里开始只改写 不再分析新IR
  IRBuilder builder(function->module, function);
  SCEVExpander expander(function, &scev);
  bool changed = false;

  std::vector<Inst *> phisToErase;
  for (const ExitRewrite &rewrite : exitRewrites) {
    Inst *anchor = rewrite.exit->firstInst();
    Inst *oldPrevious = anchor ? anchor->previous() : nullptr;
    Inst *materialized = expander.expandCodeFor(rewrite.closed, anchor);
    std::vector<Inst *> inserted =
        insertedBefore(rewrite.exit, oldPrevious, anchor);
    bool invalidReplacement = false;
    for (const Use *use = rewrite.phi->uses(); materialized && use;
         use = use->next) {
      if (breaksLCSSAUse(materialized, use->user, use->argNo, loopInfo)) {
        invalidReplacement = true;
        break;
      }
    }
    if (!materialized || instDependsOn(materialized, rewrite.phi) ||
        invalidReplacement || breaksLCSSAAny(inserted, loopInfo)) {
      rollback(inserted);
      continue;
    }
    replaceAllUsesWith(function, rewrite.phi, materialized);
    phisToErase.push_back(rewrite.phi);
    changed = true;
  }
  // 后续候选仍可能基于旧SCEV快照合法复用较早的出口Phi 只删除最终无使用者的候选
  for (Inst *phi : phisToErase)
    if (phi->hasNoUses())
      VERIFY(phi->eraseFromBlock());

  for (const BranchFold &fold : branchFolds) {
    fold.branch->setArg(0, builder.i1Const(fold.value));
    changed = true;
  }

  std::vector<CanonicalIVPlan> plans;
  for (const DerivedIVRewrite &rewrite : derivedRewrites) {
    CanonicalIVPlan *plan = findPlan(plans, rewrite.loop);
    const bool hadCanonical = plan->canonical != nullptr;
    Inst *canonical =
        getOrCreateCanonicalIV(function, builder, rewrite.loop, *plan);
    if (!canonical)
      continue;
    changed |= !hadCanonical;

    Inst *anchor = rewrite.loop->header()->firstInst();
    Inst *oldPrevious = anchor ? anchor->previous() : nullptr;
    Inst *materialized =
        materializeDerivedFromCanonical(builder, expander, rewrite, canonical);
    std::vector<Inst *> inserted =
        insertedBefore(rewrite.loop->header(), oldPrevious, anchor);
    if (!materialized || breaksLCSSAAny(inserted, loopInfo)) {
      rollback(inserted);
      continue;
    }
    bool rewroteUse = false;
    for (const DerivedIVRewrite::UseSite &site : rewrite.useSites) {
      if (!site.user || site.argument >= site.user->getOperandCount() ||
          site.user->getArg(site.argument) != rewrite.oldIV)
        continue;
      site.user->setArg(site.argument, materialized);
      rewroteUse = true;
    }
    changed |= rewroteUse;
  }

  for (const ExitConditionRewrite &rewrite : exitConditionRewrites) {
    CanonicalIVPlan *plan = findPlan(plans, rewrite.loop);
    changed |= applyExitConditionRewrite(function, builder, expander, rewrite,
                                         *plan, loopInfo);
  }
  return changed;
}

} // namespace

std::string_view IndVarSimpPass::name() const noexcept { return "indvars"; }

PassResult IndVarSimpPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();
  if (!runIndVarSimp(function, context))
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
