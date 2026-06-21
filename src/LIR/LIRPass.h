#ifndef LIR_PASS_H
#define LIR_PASS_H

#include "PassManager.h"

#include <cstdio>

namespace svm::ir {

class HIRToLIRPass final : public ModulePass {
public:
  std::string_view name() const noexcept override;
  PassResult run(Module *module, PassContext &context) override;
};

class Mem2RegPass final : public FunctionPass {
public:
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;
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
