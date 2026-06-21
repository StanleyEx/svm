#include "PassManager.h"

#include "DomAnalysis.h"

#include <cassert>
#include <chrono>
#include <variant>

namespace svm::ir {
namespace {

using Clock = std::chrono::steady_clock;

long long elapsedMicros(Clock::time_point start) noexcept {
  return std::chrono::duration_cast<std::chrono::microseconds>(Clock::now() -
                                                               start)
      .count();
}

void noteTiming(PassContext &context, const char *unit, std::string_view pass,
                long long micros) {
  if (DiagnosticEngine *diagnostics = context.diagnostics())
    SVM_NOTE(*diagnostics, SourceLocation{},
             "[PassManager]: %s::%.*s, %lld us.", unit,
             static_cast<int>(pass.size()), pass.data(), micros);
}

[[noreturn]] void failPassManager(DiagnosticEngine *diagnostics,
                                  std::string_view message) {
  if (diagnostics)
    diagnostics->diagEmit(DiagnosticLevel::Fatal, SourceLocation{}, __FILE__,
                          __func__, __LINE__, "%.*s",
                          static_cast<int>(message.size()), message.data());
  std::abort();
}

template <typename Pass>
void validatePass(const Pass *pass, DiagnosticEngine *diagnostics) {
  if (!pass)
    failPassManager(diagnostics, "PassManager不能添加空Pass.");
  if (pass->name().empty())
    failPassManager(diagnostics, "PassManager不能添加无名Pass.");
}

#ifndef NDEBUG
bool verifyDominance(Function *function) {
  if (!function || function->isExtern || !function->region ||
      function->phase != IRPhase::LIR)
    return true;

  BasicBlock *entry = function->region->first;
  if (!entry)
    return true;
  DominatorTree tree;
  if (!tree.build(function) || tree.getDepth(entry) < 0)
    return false;
  std::vector<u8> available(function->instCount, 0);

  for (BasicBlock *block = entry; block; block = block->next()) {
    if (tree.getDepth(block) < 0)
      continue;

    for (Inst *phi = block->firstPhi(); phi; phi = phi->next()) {
      if (phi->id >= available.size())
        return false;
      available[phi->id] = 1;
    }

    auto validUser = [&](Inst *user) {
      if (!user || user->isErased() || user->parentBlock() != block)
        return false;

      for (u32 index = 0; index < user->getOperandCount(); ++index) {
        Inst *definition = user->getArg(index);
        if (!definition || definition->isErased())
          return false;

        BasicBlock *definitionBlock = definition->parentBlock();
        if (!definitionBlock) {
          if (!definition->isUndefValue() && !definition->isPrecoloredDef() &&
              !isConstant(definition->getOp()))
            return false;
          continue;
        }
        if (tree.getDepth(definitionBlock) < 0)
          return false;

        if (user->getOp() == OP_PHI) {
          BasicBlock *incoming = user->getIncomingBlock(index);
          if (!incoming || tree.getDepth(incoming) < 0 ||
              !tree.dominates(definitionBlock, incoming))
            return false;
          continue;
        }

        if (!tree.dominates(definitionBlock, block) ||
            (definitionBlock == block && (definition->id >= available.size() ||
                                          !available[definition->id])))
          return false;
      }
      return true;
    };

    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      if (!validUser(phi))
        return false;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if (!validUser(inst))
        return false;
      if (inst->id >= available.size())
        return false;
      available[inst->id] = 1;
    }
  }
  return true;
}
#endif

} // namespace

void PassContext::invalidate(Function *function,
                             const PreservedAnalyses &preserved) {
  assert(function && function->module == &module_);
  functionAnalyses_.invalidate(function, preserved);
  if (!preserved.preservesAllModuleAnalyses())
    moduleAnalyses_.invalidate(&module_, preserved);
}

void PassContext::invalidate(Module *module, const PreservedAnalyses &preserved,
                             const std::vector<Function *> &affectedFunctions) {
  assert(module == &module_);
  UNUSED(module);
  moduleAnalyses_.invalidate(&module_, preserved);
  if (preserved.preservesAllFunctionAnalyses())
    return;
  if (affectedFunctions.empty()) {
    invalidateAllFunctions(preserved);
    return;
  }
  // affectedFunctions按协议只包含存活函数 这里只将地址作为缓存键
  for (Function *affected : affectedFunctions)
    functionAnalyses_.invalidate(affected, preserved);
}

void PassContext::invalidateModuleAnalyses(const PreservedAnalyses &preserved) {
  if (!preserved.preservesAllModuleAnalyses())
    moduleAnalyses_.invalidate(&module_, preserved);
}

void PassContext::invalidateAllFunctions(const PreservedAnalyses &preserved) {
  for (Function *function = module_.functionHead; function;
       function = function->next)
    if (!function->isExtern)
      functionAnalyses_.invalidate(function, preserved);
}

void PassContext::notifyFunctionTopologyChanged(Function *function) {
  assert(function && function->module == &module_);
  functionAnalyses_.clear(function);
  invalidateModuleAnalyses();
}

struct PassManager::Step {
  using Storage =
      std::variant<std::unique_ptr<ModulePass>, std::unique_ptr<FunctionPass>>;
  explicit Step(std::unique_ptr<ModulePass> pass) : pass(std::move(pass)) {}
  explicit Step(std::unique_ptr<FunctionPass> pass) : pass(std::move(pass)) {}
  std::string_view name() const noexcept {
    return std::visit([](const auto &pass) { return pass->name(); }, pass);
  }
  Storage pass;
};

PassManager::PassManager(DiagnosticEngine *diagnostics)
    : diagnostics_(diagnostics) {
  linkAnalysisManagers(moduleAnalyses_, functionAnalyses_);
}

PassManager::~PassManager() = default;

void PassManager::addPass(std::unique_ptr<ModulePass> pass) {
  if (aborted_)
    return;
  validatePass(pass.get(), diagnostics_);
  steps_.emplace_back(std::move(pass));
}

void PassManager::addPass(std::unique_ptr<FunctionPass> pass) {
  if (aborted_)
    return;
  validatePass(pass.get(), diagnostics_);
  steps_.emplace_back(std::move(pass));
}

bool PassManager::run(Module *module) {
  if (!module)
    return false;
  // 第二次运行先丢弃上一轮缓存 防止历史IR地址持续驻留
  const bool hasPreviousRun = context_.has_value();
  context_.reset();
  if (hasPreviousRun) {
    moduleAnalyses_.clear();
    functionAnalyses_.clear();
  }
  if (!module->diagnostics)
    module->diagnostics = diagnostics_;
  context_.emplace(*module, moduleAnalyses_, functionAnalyses_);
  bool changed = false;

  for (Step &step : steps_) {
    const std::string_view name = step.name();
    if (options_.isDisabled(name))
      continue;
    options_.runPreHooks(name, module);
    PassResult result = std::visit(
        [&](auto &pass) -> PassResult {
          using PassPtr = std::decay_t<decltype(pass)>;
          if constexpr (std::is_same_v<PassPtr, std::unique_ptr<ModulePass>>)
            return runModuleStep(*pass, module, *context_);
          else
            return runFunctionStep(*pass, module, *context_,
                                   options_.hasHooks(name));
        },
        step.pass);
    changed |= result.changed;
    options_.runHooks(name, module, result);
  }
  return changed;
}

PassContext &PassManager::context() {
  if (!context_)
    failPassManager(diagnostics_, "PassManager在run之前请求了PassContext.");
  return *context_;
}

PassResult PassManager::runModuleStep(ModulePass &pass, Module *module,
                                      PassContext &context) {
  const auto start = Clock::now();
  PassResult result = pass.run(module, context);
  if (options_.timePasses())
    noteTiming(context, "module", pass.name(), elapsedMicros(start));

  if (result.changed)
    context.invalidate(module, result.preserved, result.affectedFunctions);
#ifndef NDEBUG
  for (Function *function = module->functionHead; function;
       function = function->next)
    assert(verifyDominance(function));
#endif
  return result;
}

PassResult PassManager::runFunctionStep(FunctionPass &pass, Module *module,
                                        PassContext &context,
                                        bool collectAffectedFunctions) {
  PassResult aggregate = PassResult::noChange();
  const auto sweepStart = Clock::now();
  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (!function->isExtern && function->region &&
        !options_.isBypassed(function)) {
      const IRPhase oldPhase = function->phase;
      const auto start = Clock::now();
      PassResult result = pass.run(function, context);
      if (options_.timePasses())
        noteTiming(context, function->name ? function->name : "<anonymous>",
                   pass.name(), elapsedMicros(start));
      aggregate.preserved.intersect(result.preserved);
      if (result.changed) {
        aggregate.changed = true;
        if (collectAffectedFunctions)
          aggregate.affectedFunctions.push_back(function);
        // 函数扫描期间只失效当前函数 模块分析在扫描完成后统一处理
        functionAnalyses_.invalidate(function, result.preserved);
      }
      if (function->phase != oldPhase)
        functionAnalyses_.clear(function);
#ifndef NDEBUG
      assert(verifyDominance(function));
#endif
    }
  }
  if (aggregate.changed)
    context.invalidateModuleAnalyses(aggregate.preserved);
  if (options_.timePasses())
    noteTiming(context, "function-sweep", pass.name(),
               elapsedMicros(sweepStart));
  return aggregate;
}

} // namespace svm::ir
