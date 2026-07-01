#include "MIRPass.h"

#include "MachineValueFacts.h"
#include "RV64.h"
#include "VReg.h"

#include <cassert>
#include <limits>

namespace svm::ir {
namespace {

struct MagicS32 {
  i32 multiplier = 0; // 有符号高半乘法使用的魔数
  u32 shift = 0;      // 取高半结果后的算术右移量
};

u32 absBits(i32 value) noexcept {
  return static_cast<u32>(value >= 0 ? static_cast<i64>(value)
                                     : -static_cast<i64>(value));
}

bool isPowerOfTwoAbs(i32 value) noexcept {
  const u32 magnitude = absBits(value);
  return magnitude != 0 && (magnitude & (magnitude - 1)) == 0;
}

u32 log2Abs(i32 value) noexcept {
  const u32 magnitude = absBits(value);
  u32 shift = 0;
  while ((u32{1} << shift) != magnitude)
    ++shift;
  return shift;
}

MagicS32 computeMagic(i32 divisor) noexcept {
  assert(divisor != 0 && divisor != 1 && divisor != -1 &&
         !isPowerOfTwoAbs(divisor));
  constexpr u32 two31 = u32{1} << 31;
  const u32 magnitude = absBits(divisor);
  const u32 sign = divisor < 0 ? 1U : 0U;
  const u32 threshold = two31 + sign;
  const u32 critical = threshold - 1 - threshold % magnitude;

  u32 exponent = 31;
  u32 q1 = two31 / critical;
  u32 r1 = two31 - q1 * critical;
  u32 q2 = two31 / magnitude;
  u32 r2 = two31 - q2 * magnitude;
  u32 delta = 0;
  do {
    ++exponent;
    q1 *= 2;
    r1 *= 2;
    if (r1 >= critical) {
      ++q1;
      r1 -= critical;
    }
    q2 *= 2;
    r2 *= 2;
    if (r2 >= magnitude) {
      ++q2;
      r2 -= magnitude;
    }
    delta = magnitude - r2;
  } while (q1 < delta || (q1 == delta && r1 == 0));

  i32 multiplier = i32FromBits(q2 + 1);
  if (divisor < 0)
    multiplier = i32FromBits(u32{0} - static_cast<u32>(multiplier));
  return {multiplier, exponent - 32};
}

Inst *emitLI(IRBuilder &builder, IRType type, i64 value) {
  Inst *result = builder.emit(MOP_LI, type);
  result->setImm64(value);
  return result;
}

Inst *emitShift(IRBuilder &builder, OpCode op, IRType type, Inst *value,
                u32 amount) {
  Inst *result = builder.emit(op, type, value);
  result->setImm(static_cast<i32>(amount));
  return result;
}

Inst *emitSignedBias(IRBuilder &builder, Inst *dividend, u32 shift) {
  assert(shift >= 1 && shift <= 31);
  if (shift == 1)
    return emitShift(builder, MOP_SRLIW, TY_I32, dividend, 31);
  Inst *sign = emitShift(builder, MOP_SRAIW, TY_I32, dividend, 31);
  return emitShift(builder, MOP_SRLIW, TY_I32, sign, 32 - shift);
}

Inst *emitPowerOfTwoDiv(IRBuilder &builder, Inst *dividend, i32 divisor,
                        bool nonNegative, u32 trailingZeros) {
  const u32 shift = log2Abs(divisor);
  Inst *quotient = nullptr;
  if (nonNegative || trailingZeros >= shift) {
    quotient = emitShift(builder, MOP_SRAIW, TY_I32, dividend, shift);
  } else {
    Inst *bias = emitSignedBias(builder, dividend, shift);
    Inst *adjusted = builder.emit(MOP_ADDW, TY_I32, dividend, bias);
    quotient = emitShift(builder, MOP_SRAIW, TY_I32, adjusted, shift);
  }
  return divisor < 0 ? builder.emit(MOP_NEGW, TY_I32, quotient) : quotient;
}

Inst *emitGeneralDiv(IRBuilder &builder, Inst *dividend, i32 divisor,
                     bool nonNegative) {
  const MagicS32 magic = computeMagic(divisor);
  Inst *wideDividend = builder.emit(MOP_SEXT_W, TY_I64, dividend);
  Inst *multiplier = emitLI(builder, TY_I64, magic.multiplier);
  Inst *product = builder.emit(MOP_MUL, TY_I64, wideDividend, multiplier);
  const bool needsFix = (divisor > 0 && magic.multiplier < 0) ||
                        (divisor < 0 && magic.multiplier > 0);

  Inst *high = emitShift(builder, MOP_SRAI, TY_I64, product,
                         needsFix ? 32 : 32 + magic.shift);
  Inst *quotient = builder.emit(MOP_SEXT_W, TY_I32, high);
  if (needsFix) {
    quotient = divisor > 0 ? builder.emit(MOP_ADDW, TY_I32, quotient, dividend)
                           : builder.emit(MOP_SUBW, TY_I32, quotient, dividend);
    if (magic.shift != 0)
      quotient = emitShift(builder, MOP_SRAIW, TY_I32, quotient, magic.shift);
  }

  if (!nonNegative || divisor < 0) {
    Inst *sign = emitShift(builder, MOP_SRLIW, TY_I32, quotient, 31);
    quotient = builder.emit(MOP_ADDW, TY_I32, quotient, sign);
  }
  return quotient;
}

Inst *emitDiv(IRBuilder &builder, Inst *dividend, i32 divisor, bool nonNegative,
              u32 trailingZeros) {
  if (divisor == 1)
    return builder.emit(MOP_COPY, TY_I32, dividend);
  if (divisor == -1)
    return builder.emit(MOP_NEGW, TY_I32, dividend);
  if (isPowerOfTwoAbs(divisor))
    return emitPowerOfTwoDiv(builder, dividend, divisor, nonNegative,
                             trailingZeros);
  return emitGeneralDiv(builder, dividend, divisor, nonNegative);
}

Inst *emitPowerOfTwoRem(IRBuilder &builder, Inst *dividend, i32 divisor,
                        bool nonNegative) {
  const u32 magnitude = absBits(divisor);
  if (nonNegative) {
    const i32 mask = static_cast<i32>(magnitude - 1);
    if (rv64::fitsImm12(mask)) {
      Inst *result = builder.emit(MOP_ANDI, TY_I32, dividend);
      result->setImm(mask);
      return result;
    }
    return builder.emit(MOP_AND, TY_I32, dividend,
                        emitLI(builder, TY_I32, mask));
  }

  const u32 shift = log2Abs(divisor);
  Inst *bias = emitSignedBias(builder, dividend, shift);
  Inst *adjusted = builder.emit(MOP_ADDW, TY_I32, dividend, bias);
  const i32 mask = i32FromBits(u32{0} - magnitude);
  Inst *truncated = nullptr;
  if (rv64::fitsImm12(mask)) {
    truncated = builder.emit(MOP_ANDI, TY_I32, adjusted);
    truncated->setImm(mask);
  } else {
    truncated =
        builder.emit(MOP_AND, TY_I32, adjusted, emitLI(builder, TY_I32, mask));
  }
  return builder.emit(MOP_SUBW, TY_I32, dividend, truncated);
}

bool rewriteDivRem(Function *function, Inst *inst) {
  const OpCode op = inst->getOp();
  if ((op != MOP_DIVW && op != MOP_REMW) || inst->getOperandCount() != 2)
    return false;
  Inst *dividend = inst->getArg(0);
  Inst *divisorDef = inst->getArg(1);
  if (!divisorDef || divisorDef->getOp() != MOP_LI)
    return false;
  const i64 wideDivisor = divisorDef->getImm64();
  if (wideDivisor < std::numeric_limits<i32>::min() ||
      wideDivisor > std::numeric_limits<i32>::max() || wideDivisor == 0)
    return false;
  const i32 divisor = static_cast<i32>(wideDivisor);

  const MachineValueFactQuery query =
      MachineValueFactQuery::forUseSiteI32(function, inst);
  const MachineValueFacts facts = computeMachineValueFacts(dividend, query);
  IRBuilder builder(function->module, function);
  builder.setInsertBefore(inst);
  builder.setCurrentSourceLocation(inst->sourceLocation);

  Inst *replacement = nullptr;
  if (op == MOP_DIVW) {
    replacement =
        emitDiv(builder, dividend, divisor, facts.knownNonNegativeI32(),
                facts.minTrailingZeros());
  } else if (divisor == 1 || divisor == -1) {
    replacement = emitLI(builder, TY_I32, 0);
  } else if (isPowerOfTwoAbs(divisor)) {
    replacement = emitPowerOfTwoRem(builder, dividend, divisor,
                                    facts.knownNonNegativeI32());
  } else {
    Inst *quotient =
        emitDiv(builder, dividend, divisor, facts.knownNonNegativeI32(),
                facts.minTrailingZeros());
    Inst *product = builder.emit(MOP_MULW, TY_I32, quotient,
                                 emitLI(builder, TY_I32, divisor));
    replacement = builder.emit(MOP_SUBW, TY_I32, dividend, product);
  }

  if (!builder.replace(inst, replacement))
    return false;
  cloneVRegMetadata(function, inst, replacement, 0);
  return true;
}

} // namespace

std::string_view DivByConstPass::name() const noexcept {
  return "div-by-const";
}

PassResult DivByConstPass::run(Function *function, PassContext &) {
  if (!function || function->isExtern || !function->region ||
      function->phase != IRPhase::MIR || function->mirPhase != MIRPhase::SSA)
    return PassResult::noChange();
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *inst = block->firstInst(); inst;) {
      Inst *next = inst->next();
      changed |= rewriteDivRem(function, inst);
      inst = next;
    }
  }
  if (!changed)
    return PassResult::noChange();
  PreservedAnalyses preserved = PreservedAnalyses::none();
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
