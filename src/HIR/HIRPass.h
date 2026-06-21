#ifndef HIR_PASS_H
#define HIR_PASS_H

#include "PassManager.h"

#include <cstdio>

namespace svm::ir {

class HIRInstCombine final : public FunctionPass {
public:
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;
};

class RaiseToFor final : public FunctionPass {
public:
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;
};

class TCO final : public FunctionPass {
public:
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;
};

class ModuloUnroll final : public FunctionPass {
public:
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;
};

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
