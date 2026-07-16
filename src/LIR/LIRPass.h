#ifndef LIR_PASS_H
#define LIR_PASS_H

#include "PassManager.h"

#include <cstdio>

namespace svm::ir {

DECLARE_MODULE_PASS(HIRToLIRPass);
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
