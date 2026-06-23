#ifndef BACKEND_MOVEINFO_H
#define BACKEND_MOVEINFO_H

#include "IR.h"
#include "RV64.h"

namespace svm::ir {

enum class MoveKind : u8 { Normal, ArgCopy, PhiParallelCopy };
using MirMoveKind = MoveKind;

struct MoveInfo {
  MoveKind kind = MoveKind::Normal;          // 拷贝来源
  rv64::PReg preferredReg = rv64::NUM_PREGS; // 可选着色偏好
};
using MirMoveInfo = MoveInfo;

// 标记拷贝启发式
void markMove(Function *function, Inst *copy, MoveKind kind,
              rv64::PReg preferred = rv64::NUM_PREGS);
MoveInfo queryMoveInfo(const Function *function, const Inst *copy);

} // namespace svm::ir

#endif // BACKEND_MOVEINFO_H
