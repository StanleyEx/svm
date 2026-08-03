#include "Analysis.h"
#include "IR.h"
#include "LIRPass.h"

#include <vector>

namespace svm::ir {
namespace {

constexpr u32 kMaxHoistedInstructions = 2;

bool isHoistableConditionOp(OpCode op) noexcept {
  switch (op) {
  case OP_ICONST:
  case OP_EQ:
  case OP_NE:
  case OP_LT:
  case OP_LE:
  case OP_GT:
  case OP_GE:
  case OP_LNOT:
  case OP_ZEXT:
  case OP_SELECT:
    return true;
  default:
    return false;
  }
}

bool isHoistableRHS(BasicBlock *rhs, BasicBlock *head) noexcept {
  if (!rhs || rhs == head || rhs->getPredecessorCount() != 1 ||
      rhs->getPredecessor(0) != head || rhs->firstPhi())
    return false;
  Inst *terminator = rhs->terminator();
  if (!terminator || terminator->getOp() != OP_BR)
    return false;

  u32 count = 0;
  for (Inst *inst = rhs->firstInst(); inst && inst != terminator;
       inst = inst->next()) {
    if (!isHoistableConditionOp(inst->getOp()) ||
        (inst->getType() != TY_I1 && inst->getType() != TY_I32) ||
        ++count > kMaxHoistedInstructions)
      return false;
  }
  return true;
}

bool phiValuesAgree(BasicBlock *block, BasicBlock *first,
                    BasicBlock *second) noexcept {
  for (Inst *phi = block->firstPhi(); phi; phi = phi->next()) {
    Inst *firstValue = CFGEditor::getPhiIncomingValue(phi, first);
    Inst *secondValue = CFGEditor::getPhiIncomingValue(phi, second);
    if (!firstValue || firstValue != secondValue)
      return false;
  }
  return true;
}

bool collectMovedEdgeValues(BasicBlock *target, BasicBlock *oldPredecessor,
                            BasicBlock *newPredecessor,
                            const DominatorTree &dom, BasicBlock *rhs,
                            std::vector<CFGEditor::PhiEdgeValue> &values) {
  values.clear();
  for (Inst *phi = target->firstPhi(); phi; phi = phi->next()) {
    Inst *value = CFGEditor::getPhiIncomingValue(phi, oldPredecessor);
    if (!value || CFGEditor::getPhiIncomingValue(phi, newPredecessor))
      return false;
    BasicBlock *definition = value->parentBlock();
    if (definition && definition != rhs &&
        !dom.dominates(definition, newPredecessor))
      return false;
    values.push_back({phi, value});
  }
  return true;
}

bool foldOneShortCircuit(Function *function, const DominatorTree &dom) {
  for (BasicBlock *head = function->region->first; head; head = head->next()) {
    Inst *headTerminator = head->terminator();
    if (!headTerminator || headTerminator->getOp() != OP_BR)
      continue;

    Inst *leftCondition = headTerminator->getArg(0);
    BasicBlock *headTrue = headTerminator->getBr().trueBB;
    BasicBlock *headFalse = headTerminator->getBr().falseBB;
    if (!leftCondition || leftCondition->getType() != TY_I1 ||
        headTrue == headFalse)
      continue;

    for (u32 mode = 0; mode < 2; ++mode) {
      const bool isAnd = mode == 0;
      BasicBlock *rhs = isAnd ? headTrue : headFalse;
      if (!isHoistableRHS(rhs, head))
        continue;

      Inst *rhsTerminator = rhs->terminator();
      Inst *rightCondition = rhsTerminator->getArg(0);
      BasicBlock *rhsTrue = rhsTerminator->getBr().trueBB;
      BasicBlock *rhsFalse = rhsTerminator->getBr().falseBB;
      if (!rightCondition || rightCondition->getType() != TY_I1)
        continue;

      BasicBlock *trueTarget = nullptr;
      BasicBlock *falseTarget = nullptr;
      if (isAnd) {
        if (rhsFalse != headFalse)
          continue;
        trueTarget = rhsTrue;
        falseTarget = headFalse;
      } else {
        if (rhsTrue != headTrue)
          continue;
        trueTarget = headTrue;
        falseTarget = rhsFalse;
      }
      if (!trueTarget || !falseTarget || trueTarget == falseTarget ||
          trueTarget == rhs || falseTarget == rhs || trueTarget == head ||
          falseTarget == head || dom.dominates(trueTarget, head) ||
          dom.dominates(falseTarget, head))
        continue;

      BasicBlock *common = isAnd ? falseTarget : trueTarget;
      BasicBlock *nonCommon = isAnd ? trueTarget : falseTarget;
      if (!phiValuesAgree(common, head, rhs))
        continue;

      std::vector<CFGEditor::PhiEdgeValue> movedValues;
      if (!collectMovedEdgeValues(nonCommon, rhs, head, dom, rhs, movedValues))
        continue;

      // 唯一前驱保证RHS纯指令可前移 临时锚点只处理空head的链表约束
      IRBuilder builder(function->module, function);
      Inst *insertionAnchor = headTerminator->previous();
      Inst *temporaryAnchor = nullptr;
      if (!insertionAnchor) {
        builder.setInsertBefore(headTerminator);
        temporaryAnchor = builder.emit(OP_ICONST, TY_I32);
        temporaryAnchor->setImm(0);
        insertionAnchor = temporaryAnchor;
      }
      for (Inst *inst = rhs->firstInst(); inst && inst != rhsTerminator;) {
        Inst *next = inst->next();
        inst->moveAfter(insertionAnchor);
        insertionAnchor = inst;
        inst = next;
      }
      if (temporaryAnchor)
        VERIFY(temporaryAnchor->eraseFromBlock());

      builder.setInsertBefore(headTerminator);
      builder.setCurrentSourceLocation(headTerminator->sourceLocation);
      Inst *selectArgs[3] = {
          leftCondition,
          isAnd ? rightCondition : builder.i1Const(true),
          isAnd ? builder.i1Const(false) : rightCondition,
      };
      Inst *condition = builder.emitN(OP_SELECT, TY_I1, selectArgs, 3);
      builder.replaceWithBranch(headTerminator, condition, trueTarget,
                                falseTarget);

      // 新的head->nonCommon边先补全Phi列 死rhs边由统一清扫删除
      if (nonCommon->firstPhi())
        VERIFY(CFGEditor::addPhiEdgeValues(function, nonCommon, head,
                                           movedValues));
      VERIFY(cleanupDeadBlocks(function));
      return true;
    }
  }
  return false;
}

} // namespace

std::string_view ShortCircuitCanonicalizePass::name() const noexcept {
  return "short-circuit-canonicalize";
}

PassResult ShortCircuitCanonicalizePass::run(Function *function,
                                             PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();
  VERIFY(computePreds(function));

  bool changed = false;
  while (true) {
    const DomAnalysis &dom = context.get<DomAnalysis>(function);
    if (!foldOneShortCircuit(function, dom.tree))
      break;
    changed = true;
    context.invalidate(function, PreservedAnalyses::none());
  }
  if (!changed)
    return PassResult::noChange();
  VERIFY(computePreds(function));

  PreservedAnalyses preserved;
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
