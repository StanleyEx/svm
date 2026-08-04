#include "LIRPass.h"
#include "Utils.h"

#include <limits>
#include <vector>

namespace svm::ir {

namespace {

bool lowerArrayIndices(Function *function) {
  VERIFY(function);
  computeUses(function);
  std::vector<Inst *> worklist;
  forEachInstRecursive(function->region, [&](Inst *instruction) {
    if (instruction->getOp() == OP_ARRAYIDX)
      worklist.push_back(instruction);
  });
  if (worklist.empty())
    return false;

  IRBuilder builder(function->module, function);
  for (Inst *arrayIndex : worklist) {
    if (!arrayIndex->parentBlock())
      continue;
    builder.setInsertBefore(arrayIndex);
    builder.setCurrentSourceLocation(arrayIndex->sourceLocation);

    Inst *replacement = arrayIndex->getArg(0);
    const u32 indexCount = arrayIndex->getOperandCount() - 1;
    for (u32 index = 0; index < indexCount; ++index) {
      Inst *subscript = arrayIndex->getArg(index + 1);
      if (subscript->getOp() == OP_ICONST && !subscript->isUndefValue() &&
          subscript->getImm() == 0)
        continue;
      u64 stride = 0;
      VERIFY(arrayIndexStrideBytes(arrayIndex, index, stride));
      VERIFY(stride != 0 &&
                 stride <= static_cast<u64>(std::numeric_limits<i32>::max()),
             "ARRAYIDX步长溢出");
      replacement =
          builder.emitGetPtr(replacement, subscript, static_cast<i32>(stride));
    }

    replaceAllUsesWith(function, arrayIndex, replacement);
    VERIFY(arrayIndex->eraseFromBlock());
  }
  computeUses(function);
  return true;
}

} // namespace

std::string_view LowerArrayIndexPass::name() const noexcept {
  return "lower-array-index";
}

PassResult LowerArrayIndexPass::run(Function *function, PassContext &) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();
  if (!lowerArrayIndices(function))
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  preserved.preserveAllModuleAnalyses();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
