#include "MIRPass.h"
#include "MachineValueFacts.h"
#include "RV64.h"

#include <utility>

namespace svm::ir {
namespace {

bool matchLi(const Inst *value, i32 &result) noexcept {
  if (!value)
    return false;
  if (value->getOp() == OP_ICONST) {
    result = value->getImm();
    return true;
  }
  if (value->getOp() != MOP_LI)
    return false;
  const i64 immediate = value->getImm64();
  if (immediate < INT32_MIN || immediate > INT32_MAX)
    return false;
  result = static_cast<i32>(immediate);
  return true;
}

bool isPowerOfTwoAbs(i32 value) noexcept {
  if (value == 0 || value == INT32_MIN)
    return false;
  const u32 magnitude = value < 0 ? static_cast<u32>(-static_cast<i64>(value))
                                  : static_cast<u32>(value);
  return (magnitude & (magnitude - 1)) == 0;
}

u32 unsignedAbs(i32 value) noexcept {
  return value < 0 ? static_cast<u32>(-static_cast<i64>(value))
                   : static_cast<u32>(value);
}

struct ConsumerSite {
  Inst *consumer = nullptr;
  Inst *tested = nullptr;
  bool isSnez = false; // 是否直接生成不等于零布尔值

  explicit operator bool() const noexcept { // 是否匹配成功
    return consumer && tested;
  }
};

ConsumerSite matchConsumerSite(Inst *inst) noexcept {
  if (!inst)
    return {};
  switch (inst->getOp()) {
  case MOP_SEQZ:
    return inst->getOperandCount() >= 1
               ? ConsumerSite{inst, inst->getArg(0), false}
               : ConsumerSite{};
  case MOP_SNEZ:
    return inst->getOperandCount() >= 1
               ? ConsumerSite{inst, inst->getArg(0), true}
               : ConsumerSite{};
  case MOP_BEQ:
  case MOP_BNE: {
    if (inst->getOperandCount() < 2)
      return {};
    Inst *zero = inst->getArg(1);
    if (!zero || !zero->isPrecoloredDef() || zero->id != rv64::ZERO)
      return {};
    return {inst, inst->getArg(0), false};
  }
  default:
    return {};
  }
}

bool tryRemPowerOfTwoZeroCompare(Inst *inst, IRBuilder &builder) {
  const ConsumerSite site = matchConsumerSite(inst);
  if (!site)
    return false;
  Inst *remainder = site.tested;
  if (!remainder || remainder->getOp() != MOP_REMW ||
      remainder->getOperandCount() < 2 || !remainder->hasOneUse())
    return false;
  i32 divisor = 0;
  if (!matchLi(remainder->getArg(1), divisor) || !isPowerOfTwoAbs(divisor))
    return false;
  const u32 mask = unsignedAbs(divisor) - 1;
  if (!rv64::fitsImm12(mask))
    return false;

  builder.setInsertBefore(inst);
  builder.setCurrentSourceLocation(inst->sourceLocation);
  Inst *low = builder.emit(MOP_ANDI, TY_I32, remainder->getArg(0));
  low->setImm(i32FromBits(mask));
  site.consumer->setArg(0, low);
  return true;
}

bool tryRemPowerOfTwoConstantCompare(Function *function, Inst *inst,
                                     IRBuilder &builder) {
  const ConsumerSite site = matchConsumerSite(inst);
  if (!site)
    return false;
  Inst *tested = site.tested;
  if (!tested || tested->getOp() != MOP_XORI || tested->getOperandCount() < 1 ||
      !tested->hasOneUse())
    return false;
  Inst *remainder = tested->getArg(0);
  if (!remainder || remainder->getOp() != MOP_REMW ||
      remainder->getOperandCount() < 2 || !remainder->hasOneUse())
    return false;
  i32 divisor = 0;
  if (!matchLi(remainder->getArg(1), divisor) || !isPowerOfTwoAbs(divisor))
    return false;
  const u32 magnitude = unsignedAbs(divisor);
  const u32 mask = magnitude - 1;
  if (!rv64::fitsImm12(mask))
    return false;

  Inst *input = remainder->getArg(0);
  const i32 compared = tested->getImm();
  Inst *replacement = nullptr;
  const MachineValueFactQuery query =
      MachineValueFactQuery::forUseSiteI32(function, inst);
  if (compared >= 0 && static_cast<u32>(compared) < magnitude &&
      computeMachineValueFacts(input, query).knownNonNegativeI32()) {
    builder.setInsertBefore(inst);
    builder.setCurrentSourceLocation(inst->sourceLocation);
    Inst *low = builder.emit(MOP_ANDI, TY_I32, input);
    low->setImm(i32FromBits(mask));
    if (compared == 0) {
      replacement = low;
    } else {
      replacement = builder.emit(MOP_XORI, TY_I32, low);
      replacement->setImm(compared);
    }
  } else if (magnitude == 2 && (compared == 1 || compared == -1)) {
    builder.setInsertBefore(inst);
    builder.setCurrentSourceLocation(inst->sourceLocation);
    Inst *zero = function->module->physicalRegister(rv64::ZERO);
    Inst *odd = builder.emit(MOP_ANDI, TY_I32, input);
    odd->setImm(1);
    Inst *rightSign = compared == 1
                          ? builder.emit(MOP_SLT, TY_I32, zero, input)
                          : builder.emit(MOP_SLT, TY_I32, input, zero);
    Inst *equal = builder.emit(MOP_AND, TY_I32, odd, rightSign);
    replacement = builder.emit(MOP_XORI, TY_I32, equal);
    replacement->setImm(1);
  }
  if (!replacement)
    return false;
  site.consumer->setArg(0, replacement);
  return true;
}

bool matchRemTwoDifference(Inst *difference, Inst *&leftInput,
                           Inst *&rightInput) noexcept {
  if (!difference || difference->getOp() != MOP_SUBW ||
      difference->getOperandCount() < 2)
    return false;
  Inst *leftRem = difference->getArg(0);
  Inst *rightRem = difference->getArg(1);
  if (!leftRem || !rightRem || leftRem->getOp() != MOP_REMW ||
      rightRem->getOp() != MOP_REMW || leftRem->getOperandCount() < 2 ||
      rightRem->getOperandCount() < 2 || !leftRem->hasOneUse() ||
      !rightRem->hasOneUse())
    return false;
  i32 leftDivisor = 0;
  i32 rightDivisor = 0;
  if (!matchLi(leftRem->getArg(1), leftDivisor) ||
      (leftDivisor != 2 && leftDivisor != -2) ||
      !matchLi(rightRem->getArg(1), rightDivisor) ||
      (rightDivisor != 2 && rightDivisor != -2))
    return false;
  leftInput = leftRem->getArg(0);
  rightInput = rightRem->getArg(0);
  return leftInput && rightInput;
}

Inst *emitSignedRemTwoNotEqual(Function *function, IRBuilder &builder,
                               Inst *insertBefore, Inst *left, Inst *right) {
  builder.setInsertBefore(insertBefore);
  builder.setCurrentSourceLocation(insertBefore->sourceLocation);
  Inst *zero = function->module->physicalRegister(rv64::ZERO);
  Inst *different = builder.emit(MOP_XOR, TY_I32, left, right);
  Inst *parityDiff = builder.emit(MOP_ANDI, TY_I32, different);
  parityDiff->setImm(1);
  Inst *signDiff = builder.emit(MOP_SLT, TY_I32, different, zero);
  Inst *leftOdd = builder.emit(MOP_ANDI, TY_I32, left);
  leftOdd->setImm(1);
  Inst *differentSignedOdd = builder.emit(MOP_AND, TY_I32, signDiff, leftOdd);
  return builder.emit(MOP_OR, TY_I32, parityDiff, differentSignedOdd);
}

bool tryRemTwoVsRemTwo(Function *function, Inst *inst, IRBuilder &builder) {
  const ConsumerSite site = matchConsumerSite(inst);
  if (!site || !site.tested->hasOneUse())
    return false;
  Inst *left = nullptr;
  Inst *right = nullptr;
  if (!matchRemTwoDifference(site.tested, left, right))
    return false;
  Inst *flag = emitSignedRemTwoNotEqual(function, builder, inst, left, right);
  if (site.isSnez)
    return builder.replace(inst, flag);
  site.consumer->setArg(0, flag);
  return true;
}

} // namespace

std::string_view MachineInstCombinePass::name() const noexcept {
  return "machine-inst-combine";
}

PassResult MachineInstCombinePass::run(Function *function, PassContext &) {
  if (!function || function->isExtern || !function->region ||
      !function->region->first || function->phase != IRPhase::MIR ||
      function->mirPhase != MIRPhase::SSA)
    return PassResult::noChange();

  bool anyChanged = MachineDCE(function);
  bool changed = false;
  do {
    changed = false;
    IRBuilder builder(function->module, function);
    for (BasicBlock *block = function->region->first; block;
         block = block->next()) {
      for (Inst *inst = block->firstInst(); inst;) {
        Inst *next = inst->next();
        if (tryRemTwoVsRemTwo(function, inst, builder) ||
            tryRemPowerOfTwoZeroCompare(inst, builder) ||
            tryRemPowerOfTwoConstantCompare(function, inst, builder)) {
          changed = true;
          anyChanged = true;
        }
        inst = next;
      }
    }
    if (changed)
      MachineDCE(function);
  } while (changed);
  if (!anyChanged)
    return PassResult::noChange();

  PreservedAnalyses preserved = PreservedAnalyses::none();
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
