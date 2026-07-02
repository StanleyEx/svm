#ifndef BACKEND_MIRPASS_H
#define BACKEND_MIRPASS_H

#include "PassManager.h"

#include <cstdio>

namespace svm::ir {

DECLARE_FUNCTION_PASS(LowerToRV64Pass);
DECLARE_FUNCTION_PASS(MachineInstCombinePass);
DECLARE_FUNCTION_PASS(DivByConstPass);
DECLARE_FUNCTION_PASS(ConstantHoistPass);
DECLARE_FUNCTION_PASS(PeepholePass);
DECLARE_FUNCTION_PASS(MachineCSEPass);
DECLARE_FUNCTION_PASS(EliminatePhisPass);
DECLARE_FUNCTION_PASS(IRCAllocPass);
DECLARE_FUNCTION_PASS(ComputeFrameLayoutPass);
DECLARE_FUNCTION_PASS(FixupStackOffsetsPass);
DECLARE_FUNCTION_PASS(LowerCallShufflesPass);
DECLARE_FUNCTION_PASS(PeepholePostRAPass);

class EmitAssembly final : public ModulePass {
public:
  explicit EmitAssembly(FILE *output) noexcept
      : output_(output ? output : stdout) {}
  std::string_view name() const noexcept override;
  PassResult run(Module *module, PassContext &context) override;

private:
  FILE *output_ = stdout;
};

// 供 LowerToRV64Pass 使用
bool lowerSwitchToRV64(Function *function, Inst *switchInst, Inst *selector);

} // namespace svm::ir

#endif // BACKEND_MIRPASS_H
