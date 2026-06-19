#include "PassManager.h"

#include "DomAnalysis.h"

#include <cassert>
#include <chrono>

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
std::string validatedPassName(const Pass *pass, DiagnosticEngine *diagnostics) {
  if (!pass)
    failPassManager(diagnostics, "PassManager不能添加空Pass.");
  const std::string_view name = pass->name();
  if (name.empty())
    failPassManager(diagnostics, "PassManager不能添加无名Pass.");
  return std::string(name);
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

template <typename Pass>
const char *passValidationError(const Pass *pass, std::string_view registered) {
  if (!pass)
    return "pass factory returned null";
  if (pass->name().empty())
    return "pass factory returned an unnamed pass";
  if (pass->name() != registered)
    return "registered name does not match pass instance name";
  return nullptr;
}

} // namespace

void PassOptions::set(std::string key, std::string value) {
  options_[std::move(key)] = std::move(value);
}

void PassOptions::setInt(std::string key, i32 value) {
  set(std::move(key), std::to_string(value));
}

bool PassOptions::has(std::string_view key) const {
  return options_.find(std::string(key)) != options_.end();
}

std::string PassOptions::getString(std::string_view key,
                                   std::string fallback) const {
  const auto found = options_.find(std::string(key));
  return found == options_.end() ? std::move(fallback) : found->second;
}

i32 PassOptions::getInt(std::string_view key, i32 fallback) const {
  const auto found = options_.find(std::string(key));
  return found == options_.end() ? fallback : std::stoi(found->second);
}

bool PassOptions::getBool(std::string_view key, bool fallback) const {
  const auto found = options_.find(std::string(key));
  if (found == options_.end())
    return fallback;
  return found->second == "1" || found->second == "true";
}

PreservedAnalyses PreservedAnalyses::all() noexcept {
  PreservedAnalyses result;
  result.all_ = true;
  return result;
}

PreservedAnalyses PreservedAnalyses::none() noexcept { return {}; }

void PreservedAnalyses::preserve(const AnalysisKey *key) {
  preserved_.insert(key);
}

bool PreservedAnalyses::preserves(const AnalysisKey *key) const noexcept {
  return all_ || preserved_.find(key) != preserved_.end();
}

void PassContext::invalidate(Function *function,
                             const PreservedAnalyses &preserved) {
  functionAnalyses_.invalidate(function, preserved);
  if (module_ && !preserved.preservesAllModuleAnalyses())
    moduleAnalyses_.invalidate(module_, preserved);
}

void PassContext::invalidate(Module *module, const PreservedAnalyses &preserved,
                             const std::vector<Function *> &affectedFunctions) {
  moduleAnalyses_.invalidate(module, preserved);
  if (preserved.preservesAllFunctionAnalyses())
    return;
  if (affectedFunctions.empty()) {
    invalidateAllFunctions(preserved);
    return;
  }
  for (Function *function : affectedFunctions)
    if (function && !function->isExtern)
      functionAnalyses_.invalidate(function, preserved);
}

void PassContext::invalidateModuleAnalyses(const PreservedAnalyses &preserved) {
  if (module_)
    moduleAnalyses_.invalidate(module_, preserved);
}

void PassContext::invalidateAllFunctions(const PreservedAnalyses &preserved) {
  for (Function *function = module_ ? module_->functionHead : nullptr; function;
       function = function->next)
    if (!function->isExtern)
      functionAnalyses_.invalidate(function, preserved);
}

void PassContext::notifyFunctionErased(Function *function) {
  functionAnalyses_.clear(function);
  invalidateModuleAnalyses();
}

void PassContext::notifyFunctionAdded(Function *function) {
  functionAnalyses_.clear(function);
  invalidateModuleAnalyses();
}

bool PassRegistry::registerPass(PassDescriptor descriptor) {
  if (descriptor.name.empty())
    fail("cannot register a pass with an empty name", descriptor.name);
  const bool validModule = descriptor.kind == PassKind::Module &&
                           descriptor.createModule &&
                           !descriptor.createFunction;
  const bool validFunction = descriptor.kind == PassKind::Function &&
                             descriptor.createFunction &&
                             !descriptor.createModule;
  if (!validModule && !validFunction)
    fail("pass kind and factory do not agree", descriptor.name);
  const std::string name = descriptor.name;
  const bool inserted =
      descriptors().emplace(name, std::move(descriptor)).second;
  if (!inserted)
    fail("duplicate pass registration", name);
  return true;
}

const PassDescriptor *PassRegistry::lookup(std::string_view name) {
  const auto found = descriptors().find(std::string(name));
  return found == descriptors().end() ? nullptr : &found->second;
}

std::unique_ptr<FunctionPass>
PassRegistry::createFunction(std::string_view name,
                             const PassOptions &options) {
  const PassDescriptor *descriptor = lookup(name);
  if (!descriptor || descriptor->kind != PassKind::Function ||
      !descriptor->createFunction || descriptor->createModule)
    fail("not a registered function pass", name);
  std::unique_ptr<FunctionPass> pass = descriptor->createFunction(options);
  if (const char *reason = passValidationError(pass.get(), name))
    fail(reason, name);
  return pass;
}

std::unique_ptr<ModulePass>
PassRegistry::createModule(std::string_view name, const PassOptions &options) {
  const PassDescriptor *descriptor = lookup(name);
  if (!descriptor || descriptor->kind != PassKind::Module ||
      !descriptor->createModule || descriptor->createFunction)
    fail("not a registered module pass", name);
  std::unique_ptr<ModulePass> pass = descriptor->createModule(options);
  if (const char *reason = passValidationError(pass.get(), name))
    fail(reason, name);
  return pass;
}

[[noreturn]] void PassRegistry::fail(const char *reason,
                                     std::string_view name) {
  std::fprintf(stderr, "[PassRegistry] fatal: %s: '%.*s'\n", reason,
               static_cast<int>(name.size()), name.data());
  std::abort();
}

std::unordered_map<std::string, PassDescriptor> &PassRegistry::descriptors() {
  static std::unordered_map<std::string, PassDescriptor> value;
  return value;
}

struct PassManager::Step {
  std::string name;                       // 插桩使用的Pass
  PassKind kind = PassKind::Function;     // Pass运行层级
  std::unique_ptr<ModulePass> module;     // 模块Pass实例
  std::unique_ptr<FunctionPass> function; // 函数Pass实例
};

struct PassManager::Instrumentation {
  explicit Instrumentation(const PassOptions &options)
      : disable(options.getString("disable-pass")),
        filterFunction(options.getString("filter-function")),
        stopBefore(options.getString("stop-before")),
        stopAfter(options.getString("stop-after")),
        printBefore(options.getString("print-before")),
        printAfter(options.getString("print-after")),
        timePasses(options.getBool("time-passes")) {}

  bool enabled(std::string_view pass) const noexcept {
    return disable.empty() || disable != pass;
  }

  bool filterMatches(const Function *function) const noexcept {
    return filterFunction.empty() ||
           (function && function->name && filterFunction == function->name);
  }

  std::string disable;        // 禁用的Pass
  std::string filterFunction; // 插桩限定的函数名
  std::string stopBefore;     // 执行前停止的Pass
  std::string stopAfter;      // 执行后停止的Pass
  std::string printBefore;    // 执行前打印的Pass
  std::string printAfter;     // 执行后打印的Pass
  bool timePasses = false;    // 是否统计Pass时间
};

PassManager::PassManager(DiagnosticEngine *diagnostics)
    : diagnostics_(diagnostics) {
  functionAnalyses_.linkModuleAnalyses(&moduleAnalyses_);
  moduleAnalyses_.linkFunctionAnalyses(&functionAnalyses_);
}

PassManager::~PassManager() = default;

void PassManager::addPass(std::unique_ptr<ModulePass> pass) {
  std::string name = validatedPassName(pass.get(), diagnostics_);
  steps_.push_back(
      {std::move(name), PassKind::Module, std::move(pass), nullptr});
}

void PassManager::addPass(std::unique_ptr<FunctionPass> pass) {
  std::string name = validatedPassName(pass.get(), diagnostics_);
  steps_.push_back(
      {std::move(name), PassKind::Function, nullptr, std::move(pass)});
}

void PassManager::addPass(std::string_view name) {
  const PassDescriptor *descriptor = PassRegistry::lookup(name);
  if (!descriptor)
    failPassManager(diagnostics_,
                    "PassManager找不到'" + std::string(name) + "'Pass.");
  if (descriptor->kind == PassKind::Module)
    addPass(PassRegistry::createModule(name, options_));
  else
    addPass(PassRegistry::createFunction(name, options_));
}

bool PassManager::run(Module *module) {
  if (!module)
    return false;
  if (!diagnostics_)
    diagnostics_ = module->diagnostics;
  else if (!module->diagnostics)
    module->diagnostics = diagnostics_;
  moduleAnalyses_.linkDiagnostics(diagnostics_);
  functionAnalyses_.linkDiagnostics(diagnostics_);
  context_ = std::make_unique<PassContext>(
      module, moduleAnalyses_, functionAnalyses_, options_, output_);
  Instrumentation instrumentation(options_);
  bool changed = false;
  halted_ = false;

  for (Step &step : steps_) {
    if (halted_)
      break;
    if (!instrumentation.enabled(step.name))
      continue;
    if (!instrumentation.stopBefore.empty() &&
        instrumentation.stopBefore == step.name) {
      halted_ = true;
      break;
    }
    changed |= step.kind == PassKind::Module
                   ? runModuleStep(step, module, *context_, instrumentation)
                   : runFunctionStep(step, module, *context_, instrumentation);
  }
  return changed;
}

PassContext &PassManager::context() {
  if (!context_)
    failPassManager(diagnostics_, "PassManager在run之前请求了PassContext.");
  return *context_;
}

void PassManager::maybePrint(Module *module, std::string_view selected,
                             std::string_view pass, const char *tag) const {
  if (printHook_ && !selected.empty() && selected == pass)
    printHook_(module, tag);
}

bool PassManager::runModuleStep(Step &step, Module *module,
                                PassContext &context,
                                const Instrumentation &instrumentation) {
  maybePrint(module, instrumentation.printBefore, step.name,
             "before-module-pass");
  std::vector<std::pair<Function *, IRPhase>> oldPhases;
  for (Function *function = module->functionHead; function;
       function = function->next)
    if (!function->isExtern)
      oldPhases.emplace_back(function, function->phase);

  const auto start = Clock::now();
  PassResult result = step.module->run(module, context);
  if (instrumentation.timePasses)
    noteTiming(context, "module", step.name, elapsedMicros(start));

  if (result.changed)
    context.invalidate(module, result.preserved, result.affectedFunctions);
  for (const auto &[function, oldPhase] : oldPhases)
    if (function->phase != oldPhase)
      functionAnalyses_.clear(function);
#ifndef NDEBUG
  for (Function *function = module->functionHead; function;
       function = function->next)
    assert(verifyDominance(function));
#endif
  maybePrint(module, instrumentation.printAfter, step.name,
             "after-module-pass");
  if (!instrumentation.stopAfter.empty() &&
      instrumentation.stopAfter == step.name)
    halted_ = true;
  return result.changed;
}

bool PassManager::runFunctionStep(Step &step, Module *module,
                                  PassContext &context,
                                  const Instrumentation &instrumentation) {
  bool changed = false;
  const auto sweepStart = Clock::now();
  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (!function->isExtern && function->region) {
      const bool selected = instrumentation.filterMatches(function);
      if (selected)
        maybePrint(module, instrumentation.printBefore, step.name,
                   "before-function-pass");
      const IRPhase oldPhase = function->phase;
      const auto start = Clock::now();
      PassResult result = step.function->run(function, context);
      if (instrumentation.timePasses)
        noteTiming(context, function->name ? function->name : "<anonymous>",
                   step.name, elapsedMicros(start));
      if (result.changed) {
        changed = true;
        context.invalidate(function, result.preserved);
      }
      if (function->phase != oldPhase)
        functionAnalyses_.clear(function);
#ifndef NDEBUG
      assert(verifyDominance(function));
#endif
      if (selected)
        maybePrint(module, instrumentation.printAfter, step.name,
                   "after-function-pass");
      if (!instrumentation.stopAfter.empty() &&
          instrumentation.stopAfter == step.name && selected) {
        halted_ = true;
        break;
      }
    }
  }
  if (instrumentation.timePasses)
    noteTiming(context, "function-sweep", step.name, elapsedMicros(sweepStart));
  return changed;
}

} // namespace svm::ir
