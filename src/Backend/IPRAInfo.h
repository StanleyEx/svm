#ifndef BACKEND_IPRAINFO_H
#define BACKEND_IPRAINFO_H

#include "IR.h"
#include "RV64.h"

namespace svm::ir {
struct IPRAFunctionUsage {
  u64 clobberedGPRMask = 0; // 可能破坏的整数寄存器集合
  u64 clobberedFPRMask = 0; // 可能破坏的浮点寄存器集合
  bool complete = false;    // 摘要是否可用于削减干涉
};
const IPRAFunctionUsage &ipraGet(const Function *callee);
void ipraRecord(Function *function, const rv64::PReg *coloring,
                u32 virtualRegisterCount);       // 记录分配后的摘要
u64 ipraCallClobberMask(const Function *callee); // 获取调用的安全破坏上界
// 合并被调破坏, 调用点参数寄存器写入与显式额外破坏
u64 ipraCallSiteClobberMask(const Inst *call);
} // namespace svm::ir

#endif // BACKEND_IPRAINFO_H
