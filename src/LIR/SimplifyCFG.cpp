#include "IR.h"
#include "LIRPass.h"

#include <cstdlib>

namespace svm::ir {
namespace {

BasicBlock *foldableJumpTarget(BasicBlock *block) {
  Inst *terminator = block ? block->terminator() : nullptr;
  if (!terminator)
    return nullptr;

  if (terminator->getOp() == OP_BR) {
    Inst *condition = terminator->getArg(0);
    if (condition && !condition->isUndefValue() &&
        condition->getOp() == OP_ICONST)
      return condition->getImm() ? terminator->getBr().trueBB
                                 : terminator->getBr().falseBB;
    if (terminator->getBr().trueBB == terminator->getBr().falseBB)
      return terminator->getBr().trueBB;
    return nullptr;
  }

  if (terminator->getOp() != OP_SWITCH)
    return nullptr;
  Inst *selector = terminator->getArg(0);
  const SwitchPayload &payload = terminator->getSwitch();
  if (selector && !selector->isUndefValue() && selector->getOp() == OP_ICONST) {
    const i32 value = selector->getImm();
    for (u32 index = 0; index < payload.getCaseCount(); ++index)
      if (payload.getCase(index).getValue() == value)
        return payload.getCase(index).getTarget();
    return payload.getDefaultTarget();
  }

  BasicBlock *only = nullptr;
  bool multiple = false;
  forEachSuccessor(block, [&](BasicBlock *successor) {
    if (!only)
      only = successor;
    else
      multiple = true;
  });
  return multiple ? nullptr : only;
}

bool foldTerminators(Function *function) {
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    if (BasicBlock *target = foldableJumpTarget(block))
      changed |= CFGEditor::foldTerminatorToJump(function, block, target);
  return changed;
}

bool simplifyTrivialPhi(Function *function, Inst *phi, IRBuilder &builder) {
  Inst *same = nullptr;
  for (u32 index = 0; index < phi->getOperandCount(); ++index) {
    Inst *value = phi->getArg(index);
    if (value == phi || value == same)
      continue;
    if (same)
      return false;
    same = value;
  }
  if (!same)
    same = builder.makeUndef(phi->getType());

  replaceAllUsesWith(function, phi, same);
  if (!phi->eraseFromBlock())
    std::abort();
  return true;
}

bool simplifyPhis(Function *function, IRBuilder &builder) {
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    for (Inst *phi = block->firstPhi(); phi;) {
      Inst *next = phi->next();
      changed |= simplifyTrivialPhi(function, phi, builder);
      phi = next;
    }
  return changed;
}

bool bypassTrivialBlocks(Function *function) {
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;) {
    BasicBlock *next = block->next();
    changed |= CFGEditor::bypassTrivialBlock(function, block);
    block = next;
  }
  return changed;
}

bool mergeLinearChains(Function *function) {
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;) {
    Inst *terminator = block->terminator();
    if (terminator && terminator->getOp() == OP_JMP &&
        CFGEditor::mergeBlockIntoPredecessor(function, block,
                                             terminator->getJumpTarget())) {
      changed = true;
      continue;
    }
    block = block->next();
  }
  return changed;
}

} // namespace

std::string_view SimplifyCFGPass::name() const noexcept {
  return "simplify-cfg";
}

PassResult SimplifyCFGPass::run(Function *function, PassContext &) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first || !computePreds(function))
    return PassResult::noChange();

  computeUses(function);
  IRBuilder builder(function->module, function);
  bool changed = false;
  bool roundChanged = false;
  do {
    roundChanged = false;
    roundChanged |= foldTerminators(function);
    roundChanged |= simplifyPhis(function, builder);
    roundChanged |= bypassTrivialBlocks(function);
    roundChanged |= mergeLinearChains(function);
    roundChanged |= cleanupDeadBlocks(function);
    changed |= roundChanged;
  } while (roundChanged);

  if (!changed)
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
