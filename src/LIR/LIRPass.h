#ifndef LIR_PASS_H
#define LIR_PASS_H

#include "PassManager.h"

#include <cstdio>

namespace svm::ir {

DECLARE_MODULE_PASS(HIRToLIRPass);
DECLARE_MODULE_PASS(AggressiveConstFoldPass);
DECLARE_MODULE_PASS(GlobalMergePass);
DECLARE_MODULE_PASS(DeadArgumentEliminationPass);
DECLARE_MODULE_PASS(DeadFunctionEliminationPass);
DECLARE_MODULE_PASS(GlobalVariableLocalizationPass);
DECLARE_FUNCTION_PASS(Mem2RegPass);
DECLARE_FUNCTION_PASS(ShortCircuitCanonicalizePass);
DECLARE_FUNCTION_PASS(SwitchCanonicalizePass);
DECLARE_FUNCTION_PASS(SCCPPass);
DECLARE_FUNCTION_PASS(SimplifyCFGPass);
DECLARE_FUNCTION_PASS(DCEPass);
DECLARE_FUNCTION_PASS(ADCEPass);
DECLARE_FUNCTION_PASS(GVNPass);
DECLARE_FUNCTION_PASS(GCMPass);
DECLARE_FUNCTION_PASS(LICMPass);
DECLARE_FUNCTION_PASS(JumpThreadingPass);
DECLARE_FUNCTION_PASS(IfConversionPass);
DECLARE_FUNCTION_PASS(SROAPass);

class InlinePass final : public ModulePass {
public:
  explicit InlinePass(i32 instructionThreshold = 256) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Module *module, PassContext &context) override;

private:
  i32 instructionThreshold_ = 256; // 内联的指令数阈值
};

class FunctionSpecializationPass final : public ModulePass {
public:
  explicit FunctionSpecializationPass(
      u32 cloneLimit = 8, u32 cloneInstructionLimit = 2000,
      u32 uniformCallSiteThreshold = 2) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Module *module, PassContext &context) override;

private:
  u32 cloneLimit_ = 8;               // 单次运行最多创建的clone数
  u32 cloneInstructionLimit_ = 2000; // 可复制函数的最大指令数
  u32 uniformCallSiteThreshold_ = 2; // uniform tuple的最少调用点数
};

class InstCombinePass final : public FunctionPass {
public:
  explicit InstCombinePass(bool fastMath = false) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;

private:
  bool fastMath_ = false;
};

class ReassociatePass final : public FunctionPass {
public:
  explicit ReassociatePass(bool fastMath = false) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;

private:
  bool fastMath_ = false;
};

class PrintLLVMIR final : public ModulePass {
public:
  explicit PrintLLVMIR(FILE *output, bool printSource = true) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Module *module, PassContext &context) override;

private:
  FILE *output_ = stdout;
  bool printSource_ = true;
};

} // namespace svm::ir

#endif // LIR_PASS_H
