#ifndef BACKEND_VREG_H
#define BACKEND_VREG_H

#include "IR.h"
#include "RV64.h"
#include "ScalarFacts.h"

namespace svm::ir {

struct VRegMetadata {
  u8 spillDepth = 0;
  bool storeConst = false;                  // 是否仅服务于常量存储
  rv64::PReg forcedColor = rv64::NUM_PREGS; // 强制物理颜色或无强制
  ScalarFactBundle scalarFacts;             // Lowering到MIR的稳定标量事实摘要
};

// 分配唯一临时虚拟寄存器编号
void assignNewVReg(Inst *inst, Function *function);
// 压实虚拟寄存器并重建类别表
void renumberVRegs(Function *function);

VRegMetadata queryVRegMetadata(const Function *function, const Inst *def);
void setSpillDepth(Function *function, Inst *def, u8 depth);
void setStoreConst(Function *function, Inst *def, bool value);
void setForcedColor(Function *function, Inst *def, rv64::PReg color);
void attachFactBundle(Function *function, Inst *def,
                      const ScalarFactBundle &bundle);
ScalarFactBundle queryFactBundle(const Function *function, const Inst *def);
// 继承溢出/事实元数据，但不继承强制颜色
void cloneVRegMetadata(Function *function, const Inst *oldDef, Inst *newDef,
                       u8 depthDelta);

} // namespace svm::ir

#endif // BACKEND_VREG_H
