#include "IR.h"
#include "MIRPass.h"
#include "RV64.h"

#include <algorithm>
#include <limits>
#include <string>
#include <unordered_map>
#include <vector>

namespace svm::ir {
namespace {

constexpr u32 kMinJumpTableEntries = 4;
constexpr i64 kMaxJumpTableDensityFactor = 2;

struct SwitchSnapshot {
  std::vector<i32> values;             // 升序case常量
  std::vector<BasicBlock *> targets;   // 与常量一一对应的目标
  BasicBlock *defaultTarget = nullptr; // 默认目标
};

std::vector<CFGEditor::PhiEdgeValue>
snapshotPhiValues(BasicBlock *target, BasicBlock *predecessor) {
  std::vector<CFGEditor::PhiEdgeValue> values;
  for (Inst *phi = target->firstPhi(); phi; phi = phi->next()) {
    Inst *value = CFGEditor::getPhiIncomingValue(phi, predecessor);
    if (!value)
      return {};
    values.push_back({phi, value});
  }
  return values;
}

BasicBlock *
emitMachineLanding(Function *function, IRBuilder &builder, BasicBlock *&anchor,
                   BasicBlock *target,
                   const std::vector<CFGEditor::PhiEdgeValue> &values,
                   const SourceLocation *location) {
  BasicBlock *landing = builder.newBlockAfter(anchor);
  anchor = landing;
  builder.setInsertAtEnd(landing);
  builder.setCurrentSourceLocation(location);
  builder.emit(MOP_J, TY_VOID);
  VERIFY(CFGEditor::rewriteJumpTarget(landing, target));
  VERIFY(CFGEditor::addPhiEdgeValues(function, target, landing, values));
  return landing;
}

BasicBlock *redirectPhiTarget(Function *function, IRBuilder &builder,
                              BasicBlock *&anchor, BasicBlock *dispatch,
                              BasicBlock *target,
                              const SourceLocation *location) {
  std::vector<CFGEditor::PhiEdgeValue> values =
      snapshotPhiValues(target, dispatch);
  VERIFY(!values.empty());
  // 先重定向原switch边 再安装landing->target 始终保持整列Phi对齐
  BasicBlock *landing = builder.newBlockAfter(anchor);
  anchor = landing;
  VERIFY(CFGEditor::redirectEdge(function, dispatch, target, landing));
  builder.setInsertAtEnd(landing);
  builder.setCurrentSourceLocation(location);
  builder.emit(MOP_J, TY_VOID);
  VERIFY(CFGEditor::rewriteJumpTarget(landing, target));
  VERIFY(CFGEditor::addPhiEdgeValues(function, target, landing, values));
  return landing;
}

BasicBlock *mappedTarget(
    BasicBlock *target,
    const std::unordered_map<BasicBlock *, BasicBlock *> &landings) noexcept {
  const auto found = landings.find(target);
  return found == landings.end() ? target : found->second;
}

Inst *materializeCaseValue(IRBuilder &builder, Module *module, i32 value) {
  if (value == 0)
    return module->physicalRegister(rv64::ZERO);
  Inst *constant = builder.emit(MOP_LI, TY_I32);
  constant->setImm(value);
  return constant;
}

const char *makeJumpTableLabel(Function *function, u32 blockID) {
  std::string label = ".LJTI_";
  label += function->name ? function->name : "anon";
  label += '_';
  label += std::to_string(blockID);
  return function->arena->duplicateString(label.c_str());
}

bool lowerSparseSwitch(Function *function, Inst *switchInst, Inst *selector,
                       const SwitchSnapshot &snapshot) {
  BasicBlock *dispatch = switchInst->parentBlock();
  IRBuilder builder(function->module, function);
  builder.setCurrentSourceLocation(switchInst->sourceLocation);

  // 小或稀疏switch直接产出相邻的机器比较块 避免构造大范围跳表
  std::vector<BasicBlock *> tests(snapshot.values.size(), nullptr);
  tests.front() = dispatch;
  BasicBlock *anchor = dispatch;
  for (usize index = 1; index < tests.size(); ++index) {
    anchor = builder.newBlockAfter(anchor);
    tests[index] = anchor;
  }

  std::unordered_map<BasicBlock *, BasicBlock *> landings;
  std::vector<BasicBlock *> uniqueTargets = snapshot.targets;
  uniqueTargets.push_back(snapshot.defaultTarget);
  for (BasicBlock *target : uniqueTargets) {
    if (!target->firstPhi() || landings.count(target))
      continue;
    landings.emplace(target,
                     redirectPhiTarget(function, builder, anchor, dispatch,
                                       target, switchInst->sourceLocation));
  }

  builder.setInsertBefore(switchInst);
  builder.setCurrentSourceLocation(switchInst->sourceLocation);
  Inst *firstValue =
      materializeCaseValue(builder, function->module, snapshot.values.front());
  builder.replaceInPlace(switchInst, MOP_BEQ, TY_VOID, selector, firstValue);
  VERIFY(CFGEditor::rewriteBranchSlot(
      dispatch, true, mappedTarget(snapshot.targets.front(), landings)));
  VERIFY(CFGEditor::rewriteBranchSlot(
      dispatch, false,
      tests.size() == 1 ? mappedTarget(snapshot.defaultTarget, landings)
                        : tests[1]));

  for (usize index = 1; index < tests.size(); ++index) {
    builder.setInsertAtEnd(tests[index]);
    builder.setCurrentSourceLocation(switchInst->sourceLocation);
    Inst *caseValue =
        materializeCaseValue(builder, function->module, snapshot.values[index]);
    builder.emit(MOP_BEQ, TY_VOID, selector, caseValue);
    VERIFY(CFGEditor::rewriteBranchSlot(
        tests[index], true, mappedTarget(snapshot.targets[index], landings)));
    VERIFY(CFGEditor::rewriteBranchSlot(
        tests[index], false,
        index + 1 < tests.size()
            ? tests[index + 1]
            : mappedTarget(snapshot.defaultTarget, landings)));
  }

  VERIFY(computePreds(function));
  return true;
}

bool lowerDenseSwitch(Function *function, Inst *switchInst, Inst *selector,
                      const SwitchSnapshot &snapshot) {
  BasicBlock *dispatch = switchInst->parentBlock();
  BasicBlock *defaultTarget = snapshot.defaultTarget;
  const i32 minimum = snapshot.values.front();
  const i64 range = static_cast<i64>(snapshot.values.back()) - minimum + 1;
  IRBuilder builder(function->module, function);
  builder.setCurrentSourceLocation(switchInst->sourceLocation);

  BasicBlock *tableLookup = builder.newBlockAfter(dispatch);
  BasicBlock *anchor = tableLookup;
  std::unordered_map<BasicBlock *, BasicBlock *> landings;
  for (BasicBlock *target : snapshot.targets) {
    if (target == defaultTarget || !target->firstPhi() ||
        landings.count(target))
      continue;
    landings.emplace(target,
                     redirectPhiTarget(function, builder, anchor, dispatch,
                                       target, switchInst->sourceLocation));
  }

  BasicBlock *tableDefault = defaultTarget;
  const bool tableReachesDefault =
      range > static_cast<i64>(snapshot.values.size()) ||
      std::find(snapshot.targets.begin(), snapshot.targets.end(),
                defaultTarget) != snapshot.targets.end();
  if (tableReachesDefault && defaultTarget->firstPhi()) {
    // 越界仍由dispatch直达default 表内gap经独立landing复制同一边值
    std::vector<CFGEditor::PhiEdgeValue> values =
        snapshotPhiValues(defaultTarget, dispatch);
    VERIFY(!values.empty());
    tableDefault = emitMachineLanding(function, builder, anchor, defaultTarget,
                                      values, switchInst->sourceLocation);
    landings.emplace(defaultTarget, tableDefault);
  }

  std::vector<BasicBlock *> tableTargets(static_cast<usize>(range),
                                         tableDefault);
  for (usize index = 0; index < snapshot.values.size(); ++index) {
    const usize slot =
        static_cast<usize>(static_cast<i64>(snapshot.values[index]) - minimum);
    tableTargets[slot] = mappedTarget(snapshot.targets[index], landings);
  }

  JumpTable *table = function->newJumpTable();
  table->label = makeJumpTableLabel(function, dispatch->id);
  table->configure(function, minimum, defaultTarget, dispatch, tableLookup,
                   tableTargets.data(), static_cast<u32>(tableTargets.size()));

  builder.setInsertBefore(switchInst);
  builder.setCurrentSourceLocation(switchInst->sourceLocation);
  Inst *index = selector;
  if (minimum != 0) {
    const i64 adjustment = -static_cast<i64>(minimum);
    if (rv64::fitsImm12(adjustment)) {
      index = builder.emit(MOP_ADDIW, TY_I32, selector);
      index->setImm(static_cast<i32>(adjustment));
    } else {
      Inst *minimumValue = builder.emit(MOP_LI, TY_I32);
      minimumValue->setImm(minimum);
      index = builder.emit(MOP_SUBW, TY_I32, selector, minimumValue);
    }
  }
  Inst *upperBound = builder.emit(MOP_LI, TY_I32);
  upperBound->setImm(static_cast<i32>(range - 1));
  builder.replaceInPlace(switchInst, MOP_BGTU, TY_VOID, index, upperBound);
  VERIFY(CFGEditor::rewriteBranchSlot(dispatch, true, defaultTarget));
  VERIFY(CFGEditor::rewriteBranchSlot(dispatch, false, tableLookup));

  builder.setInsertAtEnd(tableLookup);
  builder.setCurrentSourceLocation(switchInst->sourceLocation);
  Inst *base = builder.emit(MOP_LA, TY_PTR);
  builder.bindJumpTable(base, table);
  Inst *wideIndex = builder.emit(MOP_SEXT_W, TY_I64, index);
  Inst *offset = builder.emit(MOP_SLLI, TY_I64, wideIndex);
  offset->setImm(2);
  Inst *entryAddress = builder.emit(MOP_ADD, TY_PTR, base, offset);
  Inst *delta = builder.emit(MOP_LW, TY_I64, entryAddress);
  delta->setImm(0);
  Inst *targetAddress = builder.emit(MOP_ADD, TY_PTR, base, delta);
  Inst *dispatchInst = builder.emit(MOP_JT_DISPATCH, TY_VOID, targetAddress);
  builder.bindJumpTable(dispatchInst, table);

  VERIFY(computePreds(function));
  return true;
}

} // namespace

bool lowerSwitchToRV64(Function *function, Inst *switchInst, Inst *selector) {
  if (!function || function->phase != IRPhase::MIR || !switchInst ||
      switchInst->getOp() != OP_SWITCH || !switchInst->parentBlock() ||
      !selector)
    return false;
  const SwitchPayload &payload = switchInst->getSwitch();
  SwitchSnapshot snapshot;
  snapshot.values.reserve(payload.getCaseCount());
  snapshot.targets.reserve(payload.getCaseCount());
  for (u32 index = 0; index < payload.getCaseCount(); ++index) {
    snapshot.values.push_back(payload.getCase(index).getValue());
    snapshot.targets.push_back(payload.getCase(index).getTarget());
  }
  snapshot.defaultTarget = payload.getDefaultTarget();
  if (!snapshot.defaultTarget)
    return false;
  if (snapshot.values.empty()) {
    IRBuilder builder(function->module, function);
    builder.setCurrentSourceLocation(switchInst->sourceLocation);
    builder.replaceInPlace(switchInst, MOP_J, TY_VOID);
    VERIFY(CFGEditor::rewriteJumpTarget(switchInst->parentBlock(),
                                        snapshot.defaultTarget));
    VERIFY(computePreds(function));
    return true;
  }
  const i64 range = static_cast<i64>(snapshot.values.back()) -
                    static_cast<i64>(snapshot.values.front()) + 1;
  const bool dense = snapshot.values.size() >= kMinJumpTableEntries &&
                     range > 0 && range <= std::numeric_limits<i32>::max() &&
                     range <= kMaxJumpTableDensityFactor *
                                  static_cast<i64>(snapshot.values.size());
  return dense ? lowerDenseSwitch(function, switchInst, selector, snapshot)
               : lowerSparseSwitch(function, switchInst, selector, snapshot);
}

} // namespace svm::ir
