#include "MIRPass.h"

#include "Analysis.h"
#include "RV64.h"
#include "VReg.h"

#include <unordered_map>

namespace svm::ir {
namespace {

constexpr i32 kMaxHoistedPerPreheader = 8;
constexpr i32 kMaxScalarLoopInstructions = 192;

bool isLargeIntegerLI(const Inst *inst) noexcept {
  if (!inst || inst->getOp() != MOP_LI)
    return false;
  const IRType type = inst->getType();
  return (type == TY_I32 || type == TY_I64) &&
         !rv64::fitsImm12(inst->getImm64());
}

bool loopAllowsHoist(Loop *loop, std::unordered_map<Loop *, bool> &cache) {
  if (!loop)
    return false;
  const auto cached = cache.find(loop);
  if (cached != cache.end())
    return cached->second;

  i32 instructionCount = 0;
  bool allowed = true;
  for (BasicBlock *block : loop->blocks()) {
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      const OpCode op = inst->getOp();
      ++instructionCount;
      if (op == OP_CALL || op == MOP_CALL || op == OP_LOAD || op == OP_STORE ||
          op == OP_ALLOCA || op == OP_GETPTR || op == OP_ARRAYIDX ||
          op == OP_GETGLOBAL || isMachineLoad(op) || isMachineStore(op) ||
          isMachineFrameOp(op) || isMachineFloat(op) || op == MOP_LA ||
          inst->getType() == TY_F32 || inst->getType() == TY_PTR ||
          instructionCount > kMaxScalarLoopInstructions) {
        allowed = false;
        break;
      }
    }
    if (!allowed)
      break;
  }
  cache.emplace(loop, allowed);
  return allowed;
}

bool allUsesInside(const Inst *definition, const Loop *loop) noexcept {
  if (!definition || !definition->uses() || !loop)
    return false;
  for (const Use *use = definition->uses(); use; use = use->next) {
    if (!use->user || !loop->contains(use->user->parentBlock()))
      return false;
  }
  return true;
}

Loop *chooseTargetLoop(Inst *definition, const LoopInfo &loopInfo,
                       std::unordered_map<Loop *, bool> &cache) {
  if (!definition || !definition->parentBlock())
    return nullptr;
  Loop *inner = loopInfo.getLoopFor(definition->parentBlock());
  if (!inner || !inner->getPreheader() || !allUsesInside(definition, inner) ||
      !loopAllowsHoist(inner, cache))
    return nullptr;

  Loop *target = inner;
  for (Loop *outer = inner->parent(); outer; outer = outer->parent()) {
    if (!outer->getPreheader() || !allUsesInside(definition, outer) ||
        !loopAllowsHoist(outer, cache))
      break;
    target = outer;
  }
  return target;
}

Inst *findLeader(BasicBlock *preheader, i64 value, IRType type) noexcept {
  for (Inst *inst = preheader ? preheader->firstInst() : nullptr; inst;
       inst = inst->next()) {
    if (inst->getOp() == MOP_LI && inst->getType() == type &&
        inst->getImm64() == value)
      return inst;
  }
  return nullptr;
}

bool runConstantHoist(Function *function, const LoopInfo &loopInfo) {
  bool changed = false;
  IRBuilder builder(function->module, function);
  std::unordered_map<Loop *, bool> allowedLoops;
  std::unordered_map<BasicBlock *, i32> hoistedCounts;

  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *inst = block->firstInst(); inst;) {
      Inst *next = inst->next();
      if (!isLargeIntegerLI(inst)) {
        inst = next;
        continue;
      }
      Loop *target = chooseTargetLoop(inst, loopInfo, allowedLoops);
      BasicBlock *preheader = target ? target->getPreheader() : nullptr;
      if (!preheader || !preheader->endsWithTerminator()) {
        inst = next;
        continue;
      }

      if (Inst *leader =
              findLeader(preheader, inst->getImm64(), inst->getType())) {
        if (builder.replace(inst, leader)) {
          changed = true;
          if (!queryFactBundle(function, leader).valid) {
            ScalarFactBundle facts = queryFactBundle(function, inst);
            if (facts.valid) {
              facts.source = FactSource::MetadataClone;
              attachFactBundle(function, leader, facts);
            }
          }
        }
        inst = next;
        continue;
      }
      i32 &count = hoistedCounts[preheader];
      if (count < kMaxHoistedPerPreheader) {
        // 当前IR的跨块move接口刻意拒绝以terminator为锚点
        // 重建等价LI可保持块尾终结符不动 也让Use链和vreg元数据通过统一入口迁移
        builder.setInsertBefore(preheader->terminator());
        builder.setCurrentSourceLocation(inst->sourceLocation);
        Inst *hoisted = builder.emit(MOP_LI, inst->getType());
        hoisted->setImm64(inst->getImm64());
        if (builder.replace(inst, hoisted)) {
          cloneVRegMetadata(function, inst, hoisted, 0);
          ++count;
          changed = true;
        } else
          VERIFY(hoisted->eraseFromBlock());
      }
      inst = next;
    }
  }
  return changed;
}

} // namespace

std::string_view ConstantHoistPass::name() const noexcept {
  return "constant-hoist";
}

PassResult ConstantHoistPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || !function->region ||
      function->phase != IRPhase::MIR || function->mirPhase != MIRPhase::SSA)
    return PassResult::noChange();
  const LoopInfo &loopInfo = context.get<LoopInfoAnalysis>(function).info;
  if (!runConstantHoist(function, loopInfo))
    return PassResult::noChange();
  PreservedAnalyses preserved = PreservedAnalyses::none();
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
