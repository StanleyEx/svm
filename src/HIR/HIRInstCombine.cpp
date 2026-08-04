#include "HIRPass.h"

#include <optional>
#include <vector>

namespace svm::ir {
namespace {
Inst *foldGlobalLoad(Inst *load, IRBuilder &builder) {
  if (load->getOperandCount() != 1 ||
      (load->getType() != TY_I32 && load->getType() != TY_F32) ||
      load->getMem().elementType != load->getType())
    return nullptr;
  Global *global = nullptr;
  const auto index = [](Inst *address, Global *&global) -> std::optional<u32> {
    Inst *base = getMemoryBase(address);
    if (!base || base->getOp() != OP_GETGLOBAL)
      return std::nullopt;
    global = base->getGlobal();
    if (!global || global->numElements == 0)
      return std::nullopt;
    if (address == base)
      return global->isArray ? std::nullopt : std::optional<u32>(0);
    if (address->getOp() != OP_ARRAYIDX || address->getArg(0) != base)
      return std::nullopt;
    const ArrayPayload &array = address->getArray();
    if (!global->isArray || array.rank == 0 ||
        array.elementType != global->type ||
        address->getOperandCount() != static_cast<u32>(array.rank) + 2)
      return std::nullopt;

    const i32 rawElementSize = typeSizeBytes(global->type);
    if (rawElementSize <= 0)
      return std::nullopt;
    const u32 elementSize = static_cast<u32>(rawElementSize);
    Inst *leading = address->getArg(1);
    if (!leading || leading->isUndefValue() || leading->getOp() != OP_ICONST ||
        leading->getImm() != 0)
      return std::nullopt;

    u64 flatIndex = 0;
    for (u32 dimension = 0; dimension < array.rank; ++dimension) {
      Inst *index = address->getArg(dimension + 2);
      u64 stride = 0;
      if (!index || index->isUndefValue() || index->getOp() != OP_ICONST ||
          index->getImm() < 0 || array.dims[dimension] == 0 ||
          static_cast<u32>(index->getImm()) >= array.dims[dimension] ||
          !arrayIndexStrideBytes(address, dimension + 1, stride) ||
          stride % elementSize != 0)
        return std::nullopt;
      const u64 term = static_cast<u64>(static_cast<u32>(index->getImm())) *
                       (stride / elementSize);
      if (term >= global->numElements ||
          flatIndex > static_cast<u64>(global->numElements - 1) - term)
        return std::nullopt;
      flatIndex += term;
    }
    return static_cast<u32>(flatIndex);
  }(load->getArg(0), global);
  if (!index)
    return nullptr;
  if (!global->isConst ||
      global->origin == Global::GlobalOrigin::StringLiteral ||
      global->type != load->getType() ||
      (global->initSegmentCount != 0 && !global->initSegment))
    return nullptr;

  if (global->initSegmentCount == 0)
    return load->getType() == TY_F32 ? builder.fConst(0.0F) : builder.iConst(0);

  u32 remaining = *index;
  for (u32 segment = 0; segment < global->initSegmentCount; ++segment) {
    const GlobalInitSegment &initialization = global->initSegment[segment];
    if (remaining >= initialization.count) {
      remaining -= initialization.count;
      continue;
    }
    if (!initialization.data)
      return load->getType() == TY_F32 ? builder.fConst(0.0F)
                                       : builder.iConst(0);
    if (load->getType() == TY_F32)
      return builder.fConst(
          static_cast<const f32 *>(initialization.data)[remaining]);
    return builder.iConst(
        static_cast<const i32 *>(initialization.data)[remaining]);
  }
  return nullptr;
}

} // namespace

std::string_view HIRInstCombinePass::name() const noexcept {
  return "hir-inst-combine";
}

PassResult HIRInstCombinePass::run(Function *function, PassContext &) {
  if (!function || function->isExtern || function->phase != IRPhase::HIR)
    return PassResult::noChange();
  bool anyChanged = false;
  IRBuilder builder(function->module, function);
  std::vector<Inst *> worklist;
  forEachInstRecursive(function->region,
                       [&](Inst *inst) { worklist.push_back(inst); });
  do {
    bool needsAnotherIteration = false;
    for (Inst *inst : worklist) {
      if (!inst->parentBlock())
        continue;
      const OpCode op = inst->getOp();
      const bool commutative = op == OP_ADD || op == OP_MUL || op == OP_EQ ||
                               op == OP_NE || op == OP_FADD || op == OP_FMUL ||
                               op == OP_FEQ || op == OP_FNE;
      if (commutative && inst->getOperandCount() == 2 &&
          (isIConst(inst->getArg(0)->getOp()) ||
           isFConst(inst->getArg(0)->getOp())) &&
          !isIConst(inst->getArg(1)->getOp()) &&
          !isFConst(inst->getArg(1)->getOp())) {
        Inst *left = inst->getArg(0);
        inst->setArg(0, inst->getArg(1));
        inst->setArg(1, left);
        anyChanged = true;
      }
      Inst *left = inst->getOperandCount() ? inst->getArg(0) : nullptr;
      Inst *right = inst->getOperandCount() > 1 ? inst->getArg(1) : nullptr;
      Inst *replacement = nullptr;
      if (op == OP_LOAD)
        replacement = foldGlobalLoad(inst, builder);
      else if (isArithmetic(op) || isCompare(op) || isConversion(op))
        replacement = builder.tryFoldConstant(op, inst->getType(), left, right);
      if (!replacement && right && right->getOp() == OP_ICONST) {
        const i32 value = right->getImm();
        if ((op == OP_ADD || op == OP_SUB) && value == 0)
          replacement = left;
        else if ((op == OP_MUL || op == OP_DIV) && value == 1)
          replacement = left;
        else if (op == OP_MUL && value == 0)
          replacement = right;
      }
      if (!replacement && right && left == right && isInt(left->getType())) {
        if (op == OP_SUB || op == OP_NE)
          replacement = builder.iConst(0);
        else if (op == OP_EQ)
          replacement = builder.i1Const(true);
      }
      if (replacement) {
        replaceAllUsesWith(function, inst, replacement);
        inst->eraseFromBlock();
        anyChanged = true;
        needsAnotherIteration = true;
      }
    }
    if (!needsAnotherIteration)
      break;
  } while (true);
  return anyChanged ? PassResult::changedIR() : PassResult::noChange();
}

} // namespace svm::ir
