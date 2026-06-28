#include "IR.h"
#include "MIRPass.h"
#include "RV64.h"

#include <cassert>
#include <limits>

namespace svm::ir {
namespace {

i32 alignUp(i32 value, i32 alignment) noexcept {
  assert(value >= 0 && alignment > 0 && (alignment & (alignment - 1)) == 0);
  const i64 aligned =
      (static_cast<i64>(value) + alignment - 1) & -static_cast<i64>(alignment);
  assert(aligned <= std::numeric_limits<i32>::max());
  return static_cast<i32>(aligned);
}

OpCode resolveFrameOp(OpCode op) noexcept {
  switch (op) {
  case MOP_LW_FRAME:
    return MOP_LW;
  case MOP_SW_FRAME:
    return MOP_SW;
  case MOP_LD_FRAME:
    return MOP_LD;
  case MOP_SD_FRAME:
    return MOP_SD;
  case MOP_FLW_FRAME:
    return MOP_FLW;
  case MOP_FSW_FRAME:
    return MOP_FSW;
  case MOP_ADDI_FRAME:
    return MOP_ADDI;
  default:
    assert(false && "unknown frame pseudo operation");
    return MOP_NOP;
  }
}

void computeFrameLayout(Function *function) {
  if (!function || function->isExtern || !function->region ||
      !function->region->first)
    return;
  assert(function->phase == IRPhase::MIR &&
         function->mirPhase == MIRPhase::PostRegAlloc);

  i32 privateSize = 0;
  for (u32 reg = 0; reg < rv64::kRegisterCount; ++reg)
    if ((function->calleeSaveMask >> reg) & u64{1})
      privateSize += 8;
  if (!function->isLeaf)
    privateSize += 8; // 非叶函数保存返回地址寄存器

  i32 argPassSize = 0;
  for (Function::FrameSlot &slot : function->frameSlots) {
    assert(slot.size > 0 && slot.alignment > 0);
    if (slot.kind == Function::FrameSlot::Kind::ArgPass) {
      argPassSize = alignUp(argPassSize, slot.alignment);
      slot.offset = argPassSize;
      argPassSize += slot.size;
      continue;
    }
    privateSize = alignUp(privateSize, slot.alignment);
    privateSize += slot.size;
    slot.offset = -privateSize;
  }

  UNUSED(argPassSize); // 入参槽位位于调用者栈帧 不计入当前函数私有区域
  privateSize += function->maxCallArgStack;
  function->stackSize = alignUp(privateSize, 16);
}

void fixupStackOffsets(Function *function) {
  if (!function || function->isExtern || !function->region ||
      !function->region->first)
    return;
  assert(function->phase == IRPhase::MIR &&
         function->mirPhase == MIRPhase::PostRegAlloc);

  IRBuilder builder(function->module, function);
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    assert(!block->firstPhi());
    for (Inst *inst = block->firstInst(); inst;) {
      Inst *next = inst->next();
      if (!isMachineFrameOp(inst->getOp())) {
        inst = next;
        continue;
      }

      const i32 slotIndex = inst->getFrameIndex();
      assert(slotIndex >= 0 &&
             static_cast<usize>(slotIndex) < function->frameSlots.size());
      const i64 wideOffset =
          static_cast<i64>(function->frameSlots[slotIndex].offset) +
          function->stackSize;
      assert(wideOffset >= std::numeric_limits<i32>::min() &&
             wideOffset <= std::numeric_limits<i32>::max());
      const i32 offset = static_cast<i32>(wideOffset);
      const OpCode resolved = resolveFrameOp(inst->getOp());

      if (rv64::fitsImm12(offset)) {
        if (isMachineStore(resolved))
          builder.replaceInPlace(inst, resolved, TY_VOID, inst->getArg(0),
                                 inst->getArg(1));
        else
          builder.replaceInPlace(inst, resolved, inst->getType(),
                                 inst->getArg(0));
        inst->setImm(offset);
        inst = next;
        continue;
      }

      // 临时寄存器t0不参与分配 可在寄存器分配后安全承载大偏移地址
      builder.setInsertBefore(inst);
      Inst *sp = function->module->physicalRegister(rv64::SP);
      const i64 highWide = (static_cast<i64>(offset) + 0x800) >> 12;
      assert(highWide >= std::numeric_limits<i32>::min() &&
             highWide <= std::numeric_limits<i32>::max());
      const i32 high = static_cast<i32>(highWide);
      const i32 low = static_cast<i32>(static_cast<i64>(offset) -
                                       (static_cast<i64>(high) << 12));
      assert(rv64::fitsImm12(low));

      Inst *lui = builder.emit(MOP_LUI, TY_I64);
      lui->setImm(high);
      lui->id = rv64::RESERVED_TMP;
      Inst *addi = builder.emit(MOP_ADDI, TY_I64, lui);
      addi->setImm(low);
      addi->id = rv64::RESERVED_TMP;

      if (resolved == MOP_ADDI) {
        builder.replaceInPlace(inst, MOP_ADD, inst->getType(), sp, addi);
      } else {
        Inst *address = builder.emit(MOP_ADD, TY_PTR, sp, addi);
        address->id = rv64::RESERVED_TMP;
        if (isMachineStore(resolved))
          builder.replaceInPlace(inst, resolved, TY_VOID, address,
                                 inst->getArg(1));
        else
          builder.replaceInPlace(inst, resolved, inst->getType(), address);
        inst->setImm(0);
      }
      inst = next;
    }
  }
}

} // namespace

std::string_view ComputeFrameLayoutPass::name() const noexcept {
  return "compute-frame-layout";
}

PassResult ComputeFrameLayoutPass::run(Function *function, PassContext &) {
  computeFrameLayout(function);
  return PassResult::changedIR();
}

std::string_view FixupStackOffsetsPass::name() const noexcept {
  return "fixup-stack-offsets";
}

PassResult FixupStackOffsetsPass::run(Function *function, PassContext &) {
  fixupStackOffsets(function);
  return PassResult::changedIR();
}

} // namespace svm::ir
