#include "IR.h"
#include "LIRPass.h"

#include <cstdlib>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

bool isLiveRoot(const Inst *inst) noexcept {
  const OpCode op = inst->getOp();
  if (isLIRTerminator(op) || op == OP_STORE || isLocalInitAnchor(op))
    return true;

  // TODO(IPA)
  return op == OP_CALL;
}

void eraseDeadInstructions(Function *function,
                           const std::vector<Inst *> &dead) {
  IRBuilder builder(function->module, function);

  // 先统一断开死集合内部的操作数边 才能删除互相引用或自引用的SSA环
  for (Inst *inst : dead)
    builder.replaceInPlace(inst, inst->getOp(), inst->getType());
  for (Inst *inst : dead)
    if (!inst->eraseFromBlock())
      std::abort();
}

} // namespace

std::string_view DCEPass::name() const noexcept { return "dce"; }

PassResult DCEPass::run(Function *function, PassContext &) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();

  computeUses(function);
  std::unordered_set<Inst *> live;
  std::vector<Inst *> worklist;
  auto mark = [&](Inst *inst) {
    if (inst && inst->parentBlock() && live.insert(inst).second)
      worklist.push_back(inst);
  };

  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      if (isLiveRoot(inst))
        mark(inst);

  while (!worklist.empty()) {
    Inst *inst = worklist.back();
    worklist.pop_back();
    for (u32 index = 0; index < inst->getOperandCount(); ++index)
      mark(inst->getArg(index));
  }

  std::vector<Inst *> dead;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      if (!live.count(phi))
        dead.push_back(phi);
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      if (!live.count(inst))
        dead.push_back(inst);
  }
  if (dead.empty())
    return PassResult::noChange();

  eraseDeadInstructions(function, dead);
  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
