#ifndef HIR_PASS_H
#define HIR_PASS_H

#include "PassManager.h"

#include <cstdio>

namespace svm::ir {

DECLARE_FUNCTION_PASS(HIRInstCombinePass);
DECLARE_FUNCTION_PASS(RaiseToForPass);
DECLARE_FUNCTION_PASS(TCOPass);
DECLARE_FUNCTION_PASS(ModuloUnrollPass);

class PrintHIR final : public ModulePass {
public:
  explicit PrintHIR(FILE *output, bool printSource = true) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Module *module, PassContext &context) override;

private:
  FILE *output_ = stdout;
  bool printSource_ = true;
};

} // namespace svm::ir

#endif // HIR_PASS_H
