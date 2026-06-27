#include "IPRAInfo.h"

namespace svm::ir {
namespace {
const IPRAFunctionUsage kIncomplete{};
} // namespace

const IPRAFunctionUsage &ipraGet(const Function *callee) {
  if (!callee || !callee->ipraInfo)
    return kIncomplete;
  return *static_cast<const IPRAFunctionUsage *>(callee->ipraInfo);
}

u64 ipraCallClobberMask(const Function *callee) {
  const IPRAFunctionUsage &usage = ipraGet(callee);
  return usage.complete ? usage.clobberedGPRMask | usage.clobberedFPRMask
                        : rv64::CALL_CLOBBER_MASK;
}

u64 ipraCallSiteClobberMask(const Inst *call) {
  if (!call || !isMachineCall(call->getOp()))
    return rv64::CALL_CLOBBER_MASK;
  u64 clobbered = ipraCallClobberMask(call->getCallee());
  // Lowering使用完整ABI mask表示未精化的默认上界 只有非默认值才是调用点额外声明
  const u64 declared = call->getRegMask();
  if (declared != rv64::CALL_CLOBBER_MASK)
    clobbered |= declared;
  u32 gprIndex = 0;
  u32 fprIndex = 0;
  for (u32 index = 0; index < call->getOperandCount(); ++index) {
    const Inst *argument = call->getArg(index);
    if (!argument)
      continue;
    if (argument->getType() == TY_F32) {
      if (fprIndex < rv64::kArgumentRegisterCount)
        clobbered |= u64{1} << rv64::FPR_ARG[fprIndex];
      ++fprIndex;
    } else {
      if (gprIndex < rv64::kArgumentRegisterCount)
        clobbered |= u64{1} << rv64::GPR_ARG[gprIndex];
      ++gprIndex;
    }
  }
  return clobbered;
}

void ipraRecord(Function *function, const rv64::PReg *coloring,
                u32 virtualRegisterCount) {
  if (!function)
    return;
  if (!function->ipraInfo)
    function->ipraInfo = function->arena->create<IPRAFunctionUsage>();
  auto *usage = static_cast<IPRAFunctionUsage *>(function->ipraInfo);
  u64 clobbered = 0;
  if (coloring) {
    for (u32 vreg = 0; vreg < virtualRegisterCount; ++vreg) {
      const rv64::PReg reg = coloring[vreg];
      if (reg < rv64::NUM_PREGS && !rv64::isCalleeSaved(reg))
        clobbered |= u64{1} << reg;
    }
  }
  if (!function->isLeaf)
    clobbered |= u64{1} << rv64::RA;
  // 返回寄存器由函数语义必然定义 即使着色数组不包含返回值拷贝也必须建模
  if (!isVoid(function->returnType))
    clobbered |=
        u64{1} << (isFloat(function->returnType) ? rv64::FA0 : rv64::A0);
  if (function->region) {
    for (BasicBlock *block = function->region->first; block;
         block = block->next())
      for (Inst *inst = block->firstInst(); inst; inst = inst->next())
        if (isMachineCall(inst->getOp()))
          clobbered |= ipraCallSiteClobberMask(inst);
  }
  usage->clobberedGPRMask = clobbered & 0x00000000FFFFFFFFULL;
  usage->clobberedFPRMask = clobbered & 0xFFFFFFFF00000000ULL;
  usage->complete = true;
}
} // namespace svm::ir
