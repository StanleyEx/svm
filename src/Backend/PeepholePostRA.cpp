#include "MIRPass.h"

#include <cassert>

namespace svm::ir {
namespace {

OpCode flippedBranch(OpCode op) noexcept {
  switch (op) {
  case MOP_BEQ:
    return MOP_BNE;
  case MOP_BNE:
    return MOP_BEQ;
  case MOP_BLT:
    return MOP_BGE;
  case MOP_BGE:
    return MOP_BLT;
  default:
    return MOP_NOP;
  }
}

bool isSelfCopy(const Inst *inst) noexcept {
  if (!inst || !isMachineCopy(inst->getOp()) || inst->getOperandCount() != 1)
    return false;
  const Inst *source = inst->getArg(0);
  return source->isPrecoloredDef() && source->id == inst->id;
}

bool cleanupTrivialInstructions(Function *function) {
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    forEachInst(block, [&](Inst *inst) {
      const bool redundant =
          (inst->getOp() == MOP_NOP && inst->hasNoUses()) || isSelfCopy(inst);
      if (!redundant)
        return;
      VERIFY(inst->eraseFromBlock());
      changed = true;
    });
  }
  return changed;
}

bool foldSameTargetBranches(Function *function) {
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (!block->endsWithTerminator())
      continue;
    Inst *terminator = block->terminator();
    if (!isMachineBranch(terminator->getOp()))
      continue;
    const BrPayload &branch = terminator->getBr();
    if (branch.trueBB == branch.falseBB)
      changed |=
          CFGEditor::foldTerminatorToJump(function, block, branch.trueBB);
  }
  return changed;
}

bool bypassJumpBlocks(Function *function) {
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;) {
    BasicBlock *next = block->next();
    changed |= CFGEditor::bypassTrivialBlock(function, block);
    block = next;
  }
  return changed;
}

bool mergeLinearBlocks(Function *function) {
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    bool merged = true;
    while (merged) {
      merged = false;
      if (!block->endsWithTerminator() || block->terminator()->getOp() != MOP_J)
        break;
      BasicBlock *successor = block->terminator()->getJumpTarget();
      if (CFGEditor::mergeBlockIntoPredecessor(function, block, successor)) {
        changed = true;
        merged = true;
      }
    }
  }
  return changed;
}

bool simplifyCFG(Function *function) {
  bool any = false;
  bool changed = true;
  u32 iterations = 0;
  constexpr u32 kMaxIterations = 1U << 16;
  while (changed && iterations++ < kMaxIterations) {
    changed = false;
    if (!computePreds(function))
      break;
    changed |= foldSameTargetBranches(function);
    if (!computePreds(function))
      break;
    changed |= bypassJumpBlocks(function);
    changed |= cleanupDeadBlocks(function);
    if (!computePreds(function))
      break;
    changed |= mergeLinearBlocks(function);
    any |= changed;
  }
  assert(iterations < kMaxIterations && "Post-RA CFG simplification diverged");
  computePreds(function);
  return any;
}

bool forwardStoreToLoad(Function *function, Inst *store) {
  Inst *load = store->next();
  if (!load || !isMachineLoad(load->getOp()) || store->getOperandCount() != 2 ||
      load->getOperandCount() != 1 || load->getArg(0) != store->getArg(0) ||
      load->getImm() != store->getImm())
    return false;

  Inst *value = store->getArg(1);
  if (typeSizeBytes(value->getType()) != typeSizeBytes(load->getType()) ||
      isFloat(value->getType()) != isFloat(load->getType()))
    return false;

  IRBuilder builder(function->module, function);
  builder.replaceInPlace(load, isFloat(load->getType()) ? MOP_FCOPY : MOP_COPY,
                         load->getType(), value);
  return true;
}

bool normalizeFallthrough(Function *function, BasicBlock *block,
                          Inst *terminator) {
  const BrPayload branch = terminator->getBr();
  if (branch.trueBB != block->next())
    return false;
  const OpCode flipped = flippedBranch(terminator->getOp());
  if (flipped == MOP_NOP)
    return false;

  Inst *left = terminator->getArg(0);
  Inst *right = terminator->getArg(1);
  IRBuilder builder(function->module, function);
  builder.replaceInPlace(terminator, flipped, TY_VOID, left, right);
  VERIFY(CFGEditor::rewriteBranchSlot(block, true, branch.falseBB));
  VERIFY(CFGEditor::rewriteBranchSlot(block, false, branch.trueBB));
  return true;
}

bool eliminateInverseMoves(Inst *first) {
  Inst *second = first->next();
  if (!second || second->getOperandCount() != 1)
    return false;
  const OpCode firstOp = first->getOp();
  const OpCode secondOp = second->getOp();
  const bool inverse = (isMachineCopy(firstOp) && secondOp == firstOp) ||
                       (firstOp == MOP_FMV_W_X && secondOp == MOP_FMV_X_W) ||
                       (firstOp == MOP_FMV_X_W && secondOp == MOP_FMV_W_X);
  if (!inverse)
    return false;
  Inst *firstSource = first->getArg(0);
  Inst *secondSource = second->getArg(0);
  if (!firstSource->isPrecoloredDef() || !secondSource->isPrecoloredDef() ||
      first->id != secondSource->id || second->id != firstSource->id)
    return false;
  VERIFY(second->eraseFromBlock());
  return true;
}

bool physicalPeephole(Function *function) {
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *inst = block->firstInst(); inst;) {
      Inst *next = inst->next();
      const OpCode op = inst->getOp();
      if (isMachineStore(op))
        changed |= forwardStoreToLoad(function, inst);
      if (isMachineBranch(op))
        changed |= normalizeFallthrough(function, block, inst);
      if ((isMachineCopy(op) || op == MOP_FMV_W_X || op == MOP_FMV_X_W) &&
          inst->getOperandCount() == 1) {
        if (isSelfCopy(inst)) {
          VERIFY(inst->eraseFromBlock());
          changed = true;
          inst = next;
          continue;
        }
        changed |= eliminateInverseMoves(inst);
        next = inst->next();
      }
      inst = next;
    }
  }
  return changed;
}

} // namespace

std::string_view PeepholePostRAPass::name() const noexcept {
  return "peephole-post-ra";
}

PassResult PeepholePostRAPass::run(Function *function, PassContext &) {
  if (!function || function->phase != IRPhase::MIR ||
      (function->mirPhase != MIRPhase::PostRegAlloc &&
       function->mirPhase != MIRPhase::Emittable) ||
      function->isExtern || !function->region || !function->region->first)
    return PassResult::noChange();

  bool changed = function->mirPhase != MIRPhase::Emittable;
  changed |= cleanupTrivialInstructions(function);
  changed |= simplifyCFG(function);
  changed |= physicalPeephole(function);
  function->mirPhase = MIRPhase::Emittable;
  return changed ? PassResult::changedIR(PreservedAnalyses::none())
                 : PassResult::noChange();
}

} // namespace svm::ir
