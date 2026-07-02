#include "MIRPass.h"
#include "MachineValueFacts.h"
#include "RV64.h"

#include <vector>

namespace svm::ir {
namespace {

bool isWSuffix(OpCode op) noexcept {
  switch (op) {
  case MOP_ADDW:
  case MOP_ADDIW:
  case MOP_SUBW:
  case MOP_MULW:
  case MOP_DIVW:
  case MOP_REMW:
  case MOP_SLLIW:
  case MOP_SRAIW:
  case MOP_SRLIW:
  case MOP_SEXT_W:
    return true;
  default:
    return false;
  }
}

bool isStrictBoolean(Inst *value) noexcept {
  return value && (isMachineBooleanResult(value->getOp()) ||
                   (value->getOp() == MOP_ANDI && value->getImm() == 1));
}

bool simplifyAddImmediate(IRBuilder &builder, Inst *inst) {
  const OpCode op = inst->getOp();
  const i32 immediate = inst->getImm();
  Inst *source = inst->getArg(0);
  if (immediate == 0) {
    if (isWSuffix(op))
      builder.replaceInPlace(inst, MOP_SEXT_W, inst->getType(), source);
    else
      return builder.replace(inst, source);
    return true;
  }

  if (op == MOP_ADDI && inst->uses()) {
    std::vector<Inst *> memoryUsers;
    bool foldable = true;
    for (const Use *use = inst->uses(); use; use = use->next) {
      Inst *memory = use->user;
      if ((!isMachineLoad(memory->getOp()) &&
           !isMachineStore(memory->getOp())) ||
          use->argNo != 0) {
        foldable = false;
        break;
      }
      const i64 merged = static_cast<i64>(memory->getImm()) + immediate;
      if (!rv64::fitsImm12(merged)) {
        foldable = false;
        break;
      }
      memoryUsers.push_back(memory);
    }
    if (foldable) {
      for (Inst *memory : memoryUsers) {
        memory->setImm(
            i32TruncWrap(static_cast<i64>(memory->getImm()) + immediate));
        memory->setArg(0, source);
      }
      return true;
    }
  }

  if (source->getOp() == MOP_LUI && source->hasOneUse()) {
    const i32 value =
        i32TruncWrap((static_cast<i64>(source->getImm()) << 12) + immediate);
    builder.replaceInPlace(inst, MOP_LI, inst->getType());
    inst->setImm(value);
    source->eraseFromBlock();
    return true;
  }
  return false;
}

bool simplifyALU(IRBuilder &builder, Inst *inst, Inst *zero) {
  const OpCode op = inst->getOp();
  Inst *left = inst->getArg(0);
  Inst *right = inst->getArg(1);
  if ((op == MOP_ADD || op == MOP_ADDW || op == MOP_SUB || op == MOP_SUBW ||
       op == MOP_OR || op == MOP_XOR) &&
      right == zero) {
    if (isWSuffix(op))
      builder.replaceInPlace(inst, MOP_SEXT_W, inst->getType(), left);
    else
      return builder.replace(inst, left);
    return true;
  }
  if (op == MOP_AND && (left == zero || right == zero))
    return builder.replace(inst, zero);
  if ((op == MOP_ADD || op == MOP_ADDW || op == MOP_OR || op == MOP_XOR) &&
      left == zero) {
    if (isWSuffix(op))
      builder.replaceInPlace(inst, MOP_SEXT_W, inst->getType(), right);
    else
      return builder.replace(inst, right);
    return true;
  }

  const bool commutative = op == MOP_ADD || op == MOP_ADDW || op == MOP_AND ||
                           op == MOP_OR || op == MOP_XOR;
  if (commutative && left->getOp() == MOP_LI && right->getOp() != MOP_LI) {
    std::swap(left, right);
    inst->setArg(0, left);
    inst->setArg(1, right);
  }
  if ((op == MOP_SUB || op == MOP_SUBW) && right->getOp() == MOP_LI) {
    const u64 negatedBits = u64{0} - static_cast<u64>(right->getImm64());
    const i64 negated = static_cast<i64>(negatedBits);
    if (rv64::fitsImm12(negated)) {
      builder.replaceInPlace(inst, op == MOP_SUB ? MOP_ADDI : MOP_ADDIW,
                             inst->getType(), left);
      inst->setImm(static_cast<i32>(negated));
      return true;
    }
  }
  OpCode immediateOp = MOP_NOP;
  switch (op) {
  case MOP_ADD:
    immediateOp = MOP_ADDI;
    break;
  case MOP_ADDW:
    immediateOp = MOP_ADDIW;
    break;
  case MOP_AND:
    immediateOp = MOP_ANDI;
    break;
  case MOP_OR:
    immediateOp = MOP_ORI;
    break;
  case MOP_XOR:
    immediateOp = MOP_XORI;
    break;
  default:
    break;
  }
  if (immediateOp != MOP_NOP && right->getOp() == MOP_LI &&
      rv64::fitsImm12(right->getImm64())) {
    builder.replaceInPlace(inst, immediateOp, inst->getType(), left);
    inst->setImm(static_cast<i32>(right->getImm64()));
    return true;
  }
  return false;
}

bool simplifyImmediateIdentity(IRBuilder &builder, Inst *inst, Inst *zero) {
  if (inst->getImm() != 0)
    return false;
  switch (inst->getOp()) {
  case MOP_ORI:
  case MOP_XORI:
  case MOP_SLLI:
  case MOP_SRLI:
  case MOP_SRAI:
    return builder.replace(inst, inst->getArg(0));
  case MOP_SLLIW:
  case MOP_SRLIW:
  case MOP_SRAIW:
    builder.replaceInPlace(inst, MOP_SEXT_W, inst->getType(), inst->getArg(0));
    return true;
  case MOP_ANDI:
    return builder.replace(inst, zero);
  default:
    return false;
  }
}

Inst *emitShiftBefore(IRBuilder &builder, Inst *anchor, OpCode op, IRType type,
                      Inst *source, i32 amount) {
  if (amount == 0)
    return source;
  builder.setInsertBefore(anchor);
  builder.setCurrentSourceLocation(anchor->sourceLocation);
  Inst *shift = builder.emit(op, type, source);
  shift->setImm(amount);
  return shift;
}

bool simplifyMultiply(IRBuilder &builder, Inst *inst, Inst *zero) {
  const OpCode op = inst->getOp();
  Inst *left = inst->getArg(0);
  Inst *right = inst->getArg(1);
  if (left->getOp() == MOP_LI && right->getOp() == MOP_LI) {
    builder.replaceInPlace(inst, MOP_LI, inst->getType());
    if (op == MOP_MULW)
      inst->setImm(i32MulWrap(left->getImm(), right->getImm()));
    else
      inst->setImm64(static_cast<i64>(static_cast<u64>(left->getImm64()) *
                                      static_cast<u64>(right->getImm64())));
    return true;
  }
  if (left->getOp() == MOP_LI) {
    std::swap(left, right);
    inst->setArg(0, left);
    inst->setArg(1, right);
  }
  if (right->getOp() != MOP_LI || right->getImm64() < INT32_MIN ||
      right->getImm64() > INT32_MAX)
    return false;

  const i32 constant = static_cast<i32>(right->getImm64());
  if (constant == 0)
    return builder.replace(inst, zero);
  if (constant == 1)
    return builder.replace(inst, left);

  const OpCode shiftOp = op == MOP_MULW ? MOP_SLLIW : MOP_SLLI;
  if (constant > 0 &&
      (static_cast<u32>(constant) & (static_cast<u32>(constant) - 1)) == 0) {
    builder.replaceInPlace(inst, shiftOp, inst->getType(), left);
    inst->setImm(static_cast<i32>(__builtin_ctz(static_cast<u32>(constant))));
    return true;
  }
  if (constant > 0 && __builtin_popcount(static_cast<u32>(constant)) == 2) {
    const i32 first =
        static_cast<i32>(__builtin_ctz(static_cast<u32>(constant)));
    const u32 remaining = static_cast<u32>(constant) - (u32{1} << first);
    const i32 second = static_cast<i32>(__builtin_ctz(remaining));
    Inst *firstValue =
        emitShiftBefore(builder, inst, shiftOp, inst->getType(), left, first);
    Inst *secondValue =
        emitShiftBefore(builder, inst, shiftOp, inst->getType(), left, second);
    builder.replaceInPlace(inst, op == MOP_MULW ? MOP_ADDW : MOP_ADD,
                           inst->getType(), firstValue, secondValue);
    return true;
  }
  if (constant > 0) {
    for (i32 place = 0; place < 31; ++place) {
      const u32 sum = static_cast<u32>(constant) + (u32{1} << place);
      if (__builtin_popcount(sum) != 1)
        continue;
      const i32 high = static_cast<i32>(__builtin_ctz(sum));
      Inst *highValue =
          emitShiftBefore(builder, inst, shiftOp, inst->getType(), left, high);
      Inst *lowValue =
          emitShiftBefore(builder, inst, shiftOp, inst->getType(), left, place);
      builder.replaceInPlace(inst, op == MOP_MULW ? MOP_SUBW : MOP_SUB,
                             inst->getType(), highValue, lowValue);
      return true;
    }
  }
  return false;
}

bool simplifyBranch(IRBuilder &builder, Inst *branch, Inst *zero) {
  if (branch->getArg(1) != zero)
    return false;
  Inst *condition = branch->getArg(0);
  const OpCode op = branch->getOp();
  OpCode replacement = op;
  Inst *source = nullptr;
  if (condition->getOp() == MOP_SEQZ) {
    replacement = op == MOP_BEQ ? MOP_BNE : MOP_BEQ;
    source = condition->getArg(0);
  } else if (condition->getOp() == MOP_SNEZ) {
    source = condition->getArg(0);
  } else if (condition->getOp() == MOP_XORI && condition->getImm() == 1 &&
             isStrictBoolean(condition->getArg(0))) {
    replacement = op == MOP_BEQ ? MOP_BNE : MOP_BEQ;
    source = condition->getArg(0);
  }
  if (!source)
    return false;

  const BrPayload targets = branch->getBr();
  builder.replaceInPlace(branch, replacement, TY_VOID, source, zero);
  const bool trueRewritten =
      CFGEditor::rewriteBranchSlot(branch->parentBlock(), true, targets.trueBB);
  const bool falseRewritten = CFGEditor::rewriteBranchSlot(
      branch->parentBlock(), false, targets.falseBB);
  return trueRewritten && falseRewritten;
}

bool simplifyAndImmediate(Function *function, IRBuilder &builder, Inst *inst) {
  Inst *source = inst->getArg(0);
  const i32 mask = inst->getImm();
  if (source->getOp() == MOP_ANDI) {
    const i32 merged = source->getImm() & mask;
    if (rv64::fitsImm12(merged)) {
      builder.replaceInPlace(inst, MOP_ANDI, inst->getType(),
                             source->getArg(0));
      inst->setImm(merged);
      return true;
    }
  }
  if (mask < 0)
    return false;
  const MachineValueFacts facts = computeMachineValueFacts(
      source, MachineValueFactQuery::forDefRewriteI32(function));
  const u32 cleared = ~static_cast<u32>(mask);
  const bool alreadyZero =
      (cleared & ~static_cast<u32>(facts.bits.knownZero)) == 0;
  return alreadyZero && facts.knownNonNegativeI32() &&
         builder.replace(inst, source);
}

bool simplifyBoolean(Function *function, IRBuilder &builder, Inst *inst) {
  Inst *source = inst->getArg(0);
  const OpCode op = inst->getOp();
  if (op == MOP_SNEZ && isMachineBooleanResult(source->getOp()))
    return builder.replace(inst, source);
  if (op == MOP_SEQZ && source->getOp() == MOP_SEQZ) {
    builder.replaceInPlace(inst, MOP_SNEZ, TY_I32, source->getArg(0));
    return true;
  }
  if (op == MOP_SEQZ && source->getOp() == MOP_SNEZ) {
    builder.replaceInPlace(inst, MOP_SEQZ, TY_I32, source->getArg(0));
    return true;
  }
  if (source->getOp() == MOP_XORI && source->getImm() == 1 &&
      isStrictBoolean(source->getArg(0))) {
    builder.replaceInPlace(inst, op == MOP_SNEZ ? MOP_SEQZ : MOP_SNEZ, TY_I32,
                           source->getArg(0));
    return true;
  }
  const MachineValueFacts facts = computeMachineValueFacts(
      source, MachineValueFactQuery::forDefRewriteI32(function));
  if (!facts.knownNonZero() && !facts.knownZeroI32())
    return false;
  builder.replaceInPlace(inst, MOP_LI, TY_I32);
  const bool result =
      op == MOP_SNEZ ? facts.knownNonZero() : facts.knownZeroI32();
  inst->setImm(result ? 1 : 0);
  return true;
}

bool simplifySignExtend(IRBuilder &builder, Inst *inst) {
  Inst *source = inst->getArg(0);
  if (source->getOp() == MOP_SEXT_W) {
    builder.replaceInPlace(inst, MOP_SEXT_W, inst->getType(),
                           source->getArg(0));
    return true;
  }
  if (source->getOp() == MOP_LI) {
    builder.replaceInPlace(inst, MOP_LI, inst->getType());
    inst->setImm(i32TruncWrap(source->getImm64()));
    return true;
  }
  return false;
}

bool runRound(Function *function) {
  bool changed = false;
  IRBuilder builder(function->module, function);
  Inst *zero = function->module->physicalRegister(rv64::ZERO);
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *inst = block->firstInst(); inst;) {
      Inst *next = inst->next();
      switch (inst->getOp()) {
      case MOP_LI:
        if (inst->getImm64() == 0)
          changed |= builder.replace(inst, zero);
        break;
      case MOP_ADDIW:
      case MOP_ADDI:
        changed |= simplifyAddImmediate(builder, inst);
        break;
      case MOP_ADD:
      case MOP_ADDW:
      case MOP_SUB:
      case MOP_SUBW:
      case MOP_AND:
      case MOP_OR:
      case MOP_XOR:
        changed |= simplifyALU(builder, inst, zero);
        break;
      case MOP_MUL:
      case MOP_MULW:
        changed |= simplifyMultiply(builder, inst, zero);
        break;
      case MOP_BEQ:
      case MOP_BNE:
        changed |= simplifyBranch(builder, inst, zero);
        break;
      case MOP_ANDI:
        if (!simplifyImmediateIdentity(builder, inst, zero))
          changed |= simplifyAndImmediate(function, builder, inst);
        else
          changed = true;
        break;
      case MOP_ORI:
      case MOP_XORI:
      case MOP_SLLI:
      case MOP_SRLI:
      case MOP_SRAI:
      case MOP_SLLIW:
      case MOP_SRLIW:
      case MOP_SRAIW:
        changed |= simplifyImmediateIdentity(builder, inst, zero);
        break;
      case MOP_SNEZ:
      case MOP_SEQZ:
        changed |= simplifyBoolean(function, builder, inst);
        break;
      case MOP_SEXT_W:
        changed |= simplifySignExtend(builder, inst);
        break;
      default:
        break;
      }
      inst = next;
    }
  }
  return changed;
}

} // namespace

std::string_view PeepholePass::name() const noexcept { return "peephole"; }

PassResult PeepholePass::run(Function *function, PassContext &) {
  if (!function || function->phase != IRPhase::MIR ||
      function->mirPhase != MIRPhase::SSA || function->isExtern ||
      !function->region || !function->region->first)
    return PassResult::noChange();

  bool any = false;
  bool changed = true;
  computeUses(function);
  while (changed) {
    changed = runRound(function);
    changed |= MachineDCE(function);
    any |= changed;
  }
  if (!any)
    return PassResult::noChange();

  PreservedAnalyses preserved = PreservedAnalyses::none();
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
