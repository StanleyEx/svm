#include "MoveInfo.h"

#include <unordered_map>

namespace svm::ir {
namespace {
struct MoveInfoTable {
  std::unordered_map<const Inst *, MoveInfo> info; // 拷贝指令侧表
};
} // namespace

void markMove(Function *function, Inst *copy, MoveKind kind,
              rv64::PReg preferred) {
  if (!function || !copy || !isMachineCopy(copy->getOp()))
    return;
  if (!function->mirMoveInfo)
    function->mirMoveInfo = function->arena->create<MoveInfoTable>();
  static_cast<MoveInfoTable *>(function->mirMoveInfo)->info[copy] = {kind,
                                                                     preferred};
}

MoveInfo queryMoveInfo(const Function *function, const Inst *copy) {
  if (!function || !copy || !function->mirMoveInfo)
    return {};
  const auto &info =
      static_cast<const MoveInfoTable *>(function->mirMoveInfo)->info;
  const auto it = info.find(copy);
  return it == info.end() ? MoveInfo{} : it->second;
}

} // namespace svm::ir
