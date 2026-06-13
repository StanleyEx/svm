#ifndef PASS_MANAGER_H
#define PASS_MANAGER_H

#include "DiagnosticEngine.h"
#include "IR.h"

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <string>
#include <string_view>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace svm::ir {
class PassOptions {
public:
  void set(std::string key, std::string value) {
    options_[std::move(key)] = std::move(value);
  }
  void setInt(std::string key, i32 value) {
    set(std::move(key), std::to_string(value));
  }
  bool has(std::string_view key) const {
    return options_.find(std::string(key)) != options_.end();
  }
  std::string getString(std::string_view key, std::string fallback = {}) const {
    auto found = options_.find(std::string(key));
    return found == options_.end() ? std::move(fallback) : found->second;
  }
  i32 getInt(std::string_view key, i32 fallback = 0) const {
    auto found = options_.find(std::string(key));
    return found == options_.end() ? fallback : std::stoi(found->second);
  }
  bool getBool(std::string_view key, bool fallback = false) const {
    auto found = options_.find(std::string(key));
    if (found == options_.end())
      return fallback;
    return found->second == "1" || found->second == "true";
  }

private:
  std::unordered_map<std::string, std::string> options_;
};

struct AnalysisKey {};

class PreservedAnalyses {
public:
  static PreservedAnalyses all() noexcept {
    PreservedAnalyses result;
    result.all_ = true;
    return result;
  }
  static PreservedAnalyses none() noexcept { return {}; }

  template <typename Analysis> void preserve() { preserve(Analysis::ID()); }
  void preserve(const AnalysisKey *key) { preserved_.insert(key); }
  template <typename Analysis> bool preserves() const noexcept {
    return preserves(Analysis::ID());
  }
  bool preserves(const AnalysisKey *key) const noexcept {
    return all_ || preserved_.find(key) != preserved_.end();
  }

  void preserveCFGAnalyses() noexcept { cfg_ = true; }
  void preserveSSAForm() noexcept { ssa_ = true; }
  void preserveUseDef() noexcept { useDef_ = true; }
  void preserveAllFunctionAnalyses() noexcept { allFunctions_ = true; }
  void preserveAllModuleAnalyses() noexcept { allModules_ = true; }

  bool preservesAll() const noexcept { return all_; }
  bool preservesCFGAnalyses() const noexcept { return all_ || cfg_; }
  bool preservesSSAForm() const noexcept { return all_ || ssa_; }
  bool preservesUseDef() const noexcept { return all_ || useDef_; }
  bool preservesAllFunctionAnalyses() const noexcept {
    return all_ || allFunctions_;
  }
  bool preservesAllModuleAnalyses() const noexcept {
    return all_ || allModules_;
  }

private:
  bool all_ = false;
  bool cfg_ = false;
  bool ssa_ = false;
  bool useDef_ = false;
  bool allFunctions_ = false;
  bool allModules_ = false;
  std::unordered_set<const AnalysisKey *> preserved_; // 显式保留的分析
};

struct PassResult {
  bool changed = false;                                   // 是否修改了IR
  PreservedAnalyses preserved = PreservedAnalyses::all(); // 保留的分析
  std::vector<Function *> affectedFunctions; // Module Pass影响的函数

  static PassResult noChange() noexcept { return {}; }
  static PassResult
  changedIR(PreservedAnalyses analyses = PreservedAnalyses::none()) noexcept {
    return {true, std::move(analyses), {}};
  }
};

namespace detail {
template <typename Pass>
std::unique_ptr<Pass> makePass(const PassOptions &options) {
  if constexpr (std::is_constructible_v<Pass, const PassOptions &>)
    return std::make_unique<Pass>(options);
  else
    return std::make_unique<Pass>();
}

template <typename Result, typename Unit, typename = void>
struct HasInvalidate : std::false_type {};

template <typename Result, typename Unit>
struct HasInvalidate<
    Result, Unit,
    std::void_t<decltype(std::declval<Result &>().invalidate(
        std::declval<Unit *>(), std::declval<const PreservedAnalyses &>()))>>
    : std::true_type {};

} // namespace detail

template <typename Unit> class AnalysisManager {
  class ResultConcept {
  public:
    virtual ~ResultConcept() = default;
    virtual bool invalidate(Unit *unit, const PreservedAnalyses &preserved) = 0;
  };

  template <typename Analysis> class ResultModel final : public ResultConcept {
  public:
    using Result = typename Analysis::Result;

    template <typename Value>
    explicit ResultModel(Value &&value) : value_(std::forward<Value>(value)) {}

    bool invalidate(Unit *unit, const PreservedAnalyses &preserved) override {
      if constexpr (detail::HasInvalidate<Result, Unit>::value)
        return value_.invalidate(unit, preserved);
      else
        return !preserved.preserves(Analysis::ID());
    }

    Result value_; // 缓存的分析结果
  };

  struct InProgress {
    Unit *unit = nullptr;             // 正在分析的IR单元
    const AnalysisKey *key = nullptr; // 正在构建的分析
  };

public:
  AnalysisManager() = default;
  AnalysisManager(const AnalysisManager &) = delete;
  AnalysisManager &operator=(const AnalysisManager &) = delete;

  void linkModuleAnalyses(AnalysisManager<Module> *analyses) noexcept {
    moduleAnalyses_ = analyses;
  }
  void linkFunctionAnalyses(AnalysisManager<Function> *analyses) noexcept {
    functionAnalyses_ = analyses;
  }
  void linkDiagnostics(DiagnosticEngine *diagnostics) noexcept {
    diagnostics_ = diagnostics;
  }

  AnalysisManager<Module> *moduleAnalyses() const noexcept {
    return moduleAnalyses_;
  }
  AnalysisManager<Function> *functionAnalyses() const noexcept {
    return functionAnalyses_;
  }

  template <typename Analysis>
  typename Analysis::Result &getResult(Unit *unit) {
    if (!unit)
      std::abort();
    if (auto *cached = getCachedResult<Analysis>(unit))
      return *cached;

    const AnalysisKey *key = Analysis::ID();
    for (const InProgress &entry : building_) {
      if (entry.unit == unit && entry.key == key) {
        if (diagnostics_)
          SVM_FATAL(*diagnostics_, SourceLocation{},
                    "AnalysisManager检测到循环分析依赖.");
        std::abort();
      }
    }

    building_.push_back({unit, key});
    Analysis analysis;
    auto model =
        std::make_unique<ResultModel<Analysis>>(analysis.run(unit, *this));
    building_.pop_back();
    auto *result = &model->value_;
    cache_[unit].emplace(key, std::move(model));
    return *result;
  }

  template <typename Analysis>
  typename Analysis::Result *getCachedResult(Unit *unit) noexcept {
    auto unitIt = cache_.find(unit);
    if (unitIt == cache_.end())
      return nullptr;
    auto resultIt = unitIt->second.find(Analysis::ID());
    if (resultIt == unitIt->second.end())
      return nullptr;
    return &static_cast<ResultModel<Analysis> *>(resultIt->second.get())
                ->value_;
  }

  void invalidate(Unit *unit, const PreservedAnalyses &preserved) {
    if (!unit || preserved.preservesAll())
      return;
    auto found = cache_.find(unit);
    if (found == cache_.end())
      return;
    for (auto it = found->second.begin(); it != found->second.end();) {
      if (it->second->invalidate(unit, preserved))
        it = found->second.erase(it);
      else
        ++it;
    }
    if (found->second.empty())
      cache_.erase(found);
  }
  void clear(Unit *unit) { cache_.erase(unit); }
  void clear() noexcept { cache_.clear(); }

private:
  using UnitCache =
      std::unordered_map<const AnalysisKey *, std::unique_ptr<ResultConcept>>;
  std::unordered_map<Unit *, UnitCache> cache_;       // 按IR单元保存分析结果
  std::vector<InProgress> building_;                  // 分析递归构建栈
  AnalysisManager<Module> *moduleAnalyses_ = nullptr; // 跨层模块分析
  AnalysisManager<Function> *functionAnalyses_ = nullptr; // 跨层函数分析
  DiagnosticEngine *diagnostics_ = nullptr;
};

using ModuleAnalysisManager = AnalysisManager<Module>;
using FunctionAnalysisManager = AnalysisManager<Function>;

class PassContext {
public:
  PassContext(Module *module, ModuleAnalysisManager &moduleAnalyses,
              FunctionAnalysisManager &functionAnalyses,
              const PassOptions &options, FILE *output) noexcept
      : module_(module), moduleAnalyses_(moduleAnalyses),
        functionAnalyses_(functionAnalyses), options_(options),
        output_(output ? output : stdout) {}

  Arena *arena() const noexcept { return module_ ? module_->arena : nullptr; }
  Module *module() const noexcept { return module_; }
  ModuleAnalysisManager &moduleAnalyses() noexcept { return moduleAnalyses_; }
  FunctionAnalysisManager &functionAnalyses() noexcept {
    return functionAnalyses_;
  }
  const PassOptions &options() const noexcept { return options_; }
  FILE *output() const noexcept { return output_; }
  DiagnosticEngine *diagnostics() const noexcept {
    return module_ ? module_->diagnostics : nullptr;
  }

  template <typename Analysis> typename Analysis::Result &get(Module *module) {
    return moduleAnalyses_.getResult<Analysis>(module);
  }
  template <typename Analysis>
  typename Analysis::Result &get(Function *function) {
    return functionAnalyses_.getResult<Analysis>(function);
  }
  template <typename Analysis>
  typename Analysis::Result *getCached(Module *module) noexcept {
    return moduleAnalyses_.getCachedResult<Analysis>(module);
  }
  template <typename Analysis>
  typename Analysis::Result *getCached(Function *function) noexcept {
    return functionAnalyses_.getCachedResult<Analysis>(function);
  }

  void invalidate(Function *function, const PreservedAnalyses &preserved) {
    functionAnalyses_.invalidate(function, preserved);
    if (module_ && !preserved.preservesAllModuleAnalyses())
      moduleAnalyses_.invalidate(module_, preserved);
  }
  void invalidate(Module *module, const PreservedAnalyses &preserved,
                  const std::vector<Function *> &affectedFunctions = {}) {
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
  void invalidateModuleAnalyses(
      const PreservedAnalyses &preserved = PreservedAnalyses::none()) {
    if (module_)
      moduleAnalyses_.invalidate(module_, preserved);
  }
  void invalidateAllFunctions(
      const PreservedAnalyses &preserved = PreservedAnalyses::none()) {
    for (Function *function = module_ ? module_->functionHead : nullptr;
         function; function = function->next) {
      if (!function->isExtern)
        functionAnalyses_.invalidate(function, preserved);
    }
  }
  void notifyFunctionErased(Function *function) {
    functionAnalyses_.clear(function);
    invalidateModuleAnalyses();
  }
  void notifyFunctionAdded(Function *function) {
    functionAnalyses_.clear(function);
    invalidateModuleAnalyses();
  }

private:
  Module *module_ = nullptr;                  // 当前模块
  ModuleAnalysisManager &moduleAnalyses_;     // 模块分析管理器
  FunctionAnalysisManager &functionAnalyses_; // 函数分析管理器
  const PassOptions &options_;                // 当前流水线参数
  FILE *output_ = stdout;                     // 非拥有Pass输出流
};

class ModulePass {
public:
  virtual ~ModulePass() = default;
  virtual PassResult run(Module *module, PassContext &context) = 0;
  virtual std::string_view name() const noexcept = 0;
};

class FunctionPass {
public:
  virtual ~FunctionPass() = default;
  virtual PassResult run(Function *function, PassContext &context) = 0;
  virtual std::string_view name() const noexcept = 0;
};

enum class PassKind : u8 { Module, Function };

struct PassDescriptor {
  using ModuleFactory = std::unique_ptr<ModulePass> (*)(const PassOptions &);
  using FunctionFactory =
      std::unique_ptr<FunctionPass> (*)(const PassOptions &);

  std::string name;                         // Pass注册名
  PassKind kind = PassKind::Function;       // Pass运行层级
  ModuleFactory createModule = nullptr;     // 模块Pass工厂
  FunctionFactory createFunction = nullptr; // 函数Pass工厂
};

class PassRegistry {
public:
  static bool registerPass(PassDescriptor descriptor) {
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
    auto [_, inserted] = descriptors().emplace(name, std::move(descriptor));
    if (!inserted)
      fail("duplicate pass registration", name);
    return true;
  }
  static const PassDescriptor *lookup(std::string_view name) {
    auto found = descriptors().find(std::string(name));
    return found == descriptors().end() ? nullptr : &found->second;
  }
  static std::unique_ptr<FunctionPass>
  createFunction(std::string_view name, const PassOptions &options) {
    const PassDescriptor *descriptor = lookup(name);
    if (!descriptor || descriptor->kind != PassKind::Function ||
        !descriptor->createFunction || descriptor->createModule)
      fail("not a registered function pass", name);
    std::unique_ptr<FunctionPass> pass = descriptor->createFunction(options);
    validateInstance(pass.get(), name);
    return pass;
  }
  static std::unique_ptr<ModulePass> createModule(std::string_view name,
                                                  const PassOptions &options) {
    const PassDescriptor *descriptor = lookup(name);
    if (!descriptor || descriptor->kind != PassKind::Module ||
        !descriptor->createModule || descriptor->createFunction)
      fail("not a registered module pass", name);
    std::unique_ptr<ModulePass> pass = descriptor->createModule(options);
    validateInstance(pass.get(), name);
    return pass;
  }

private:
  [[noreturn]] static void fail(const char *reason, std::string_view name) {
    std::fprintf(stderr, "[PassRegistry] fatal: %s: '%.*s'\n", reason,
                 static_cast<int>(name.size()), name.data());
    std::abort();
  }
  template <typename Pass>
  static void validateInstance(const Pass *pass, std::string_view registered) {
    if (!pass)
      fail("pass factory returned null", registered);
    const std::string_view actual = pass->name();
    if (actual.empty())
      fail("pass factory returned an unnamed pass", registered);
    if (actual != registered)
      fail("registered name does not match pass instance name", registered);
  }
  static std::unordered_map<std::string, PassDescriptor> &descriptors() {
    static std::unordered_map<std::string, PassDescriptor> value;
    return value;
  }
};

class PassManager {
public:
  using PrintHook = void (*)(Module *, const char *);

  explicit PassManager(DiagnosticEngine *diagnostics = nullptr)
      : diagnostics_(diagnostics) {
    functionAnalyses_.linkModuleAnalyses(&moduleAnalyses_);
    moduleAnalyses_.linkFunctionAnalyses(&functionAnalyses_);
  }

  template <typename Pass, typename... Args> void addPass(Args &&...args) {
    static_assert(std::is_base_of_v<ModulePass, Pass> ||
                  std::is_base_of_v<FunctionPass, Pass>);
    addPass(std::make_unique<Pass>(std::forward<Args>(args)...));
  }

  void addPass(std::unique_ptr<ModulePass> pass) {
    std::string name = validatedName(pass.get());
    steps_.push_back(
        {std::move(name), PassKind::Module, std::move(pass), nullptr});
  }
  void addPass(std::unique_ptr<FunctionPass> pass) {
    std::string name = validatedName(pass.get());
    steps_.push_back(
        {std::move(name), PassKind::Function, nullptr, std::move(pass)});
  }

  void addPass(std::string_view name) {
    const PassDescriptor *descriptor = PassRegistry::lookup(name);
    if (!descriptor)
      fatal("PassManager找不到名为'%.*s'的Pass.", static_cast<int>(name.size()),
            name.data());
    if (descriptor->kind == PassKind::Module)
      addPass(PassRegistry::createModule(name, options_));
    else
      addPass(PassRegistry::createFunction(name, options_));
  }

  bool run(Module *module) {
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
      changed |=
          step.kind == PassKind::Module
              ? runModuleStep(step, module, *context_, instrumentation)
              : runFunctionStep(step, module, *context_, instrumentation);
    }
    return changed;
  }

  void setPrintHook(PrintHook hook) noexcept { printHook_ = hook; }
  void setOutput(FILE *output) noexcept { output_ = output ? output : stdout; }
  bool halted() const noexcept { return halted_; }
  PassContext &context() {
    if (!context_)
      fatal("PassManager在run之前请求了PassContext.");
    return *context_;
  }
  ModuleAnalysisManager &moduleAnalyses() noexcept { return moduleAnalyses_; }
  FunctionAnalysisManager &functionAnalyses() noexcept {
    return functionAnalyses_;
  }
  PassOptions &options() noexcept { return options_; }
  const PassOptions &options() const noexcept { return options_; }

private:
  struct Step {
    std::string name;                       // 插桩使用的Pass
    PassKind kind = PassKind::Function;     // Pass运行层级
    std::unique_ptr<ModulePass> module;     // 模块Pass实例
    std::unique_ptr<FunctionPass> function; // 函数Pass实例
  };

  struct Instrumentation {
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
    bool timePasses = false;
  };

  using Clock = std::chrono::steady_clock;

  template <typename Pass> std::string validatedName(const Pass *pass) {
    if (!pass)
      fatal("PassManager不能添加空Pass.");
    const std::string_view name = pass->name();
    if (name.empty())
      fatal("PassManager不能添加无名Pass.");
    return std::string(name);
  }

  template <typename... Args>
  [[noreturn]] void fatal(const char *format, Args... args) const {
    if (diagnostics_)
      diagnostics_->diagEmit(DiagnosticLevel::Fatal, SourceLocation{}, __FILE__,
                             __func__, __LINE__, format, args...);
    std::abort();
  }

  void maybePrint(Module *module, std::string_view selected,
                  std::string_view pass, const char *tag) const {
    if (printHook_ && !selected.empty() && selected == pass)
      printHook_(module, tag);
  }

  static long long elapsedMicros(Clock::time_point start) noexcept {
    return std::chrono::duration_cast<std::chrono::microseconds>(Clock::now() -
                                                                 start)
        .count();
  }

  static void noteTiming(PassContext &context, const char *unit,
                         std::string_view pass, long long micros) {
    if (DiagnosticEngine *diagnostics = context.diagnostics())
      SVM_NOTE(*diagnostics, SourceLocation{},
               "[PassManager]: %s::%.*s, %lld us.", unit,
               static_cast<int>(pass.size()), pass.data(), micros);
  }

  bool runModuleStep(Step &step, Module *module, PassContext &context,
                     const Instrumentation &instrumentation) {
    maybePrint(module, instrumentation.printBefore, step.name,
               "before-module-pass");
    std::vector<std::pair<Function *, IRPhase>> oldPhases;
    for (Function *function = module->functionHead; function;
         function = function->next) {
      if (!function->isExtern)
        oldPhases.emplace_back(function, function->phase);
    }
    const auto start = Clock::now();
    PassResult result = step.module->run(module, context);
    if (instrumentation.timePasses)
      noteTiming(context, "module", step.name, elapsedMicros(start));

    if (result.changed)
      context.invalidate(module, result.preserved, result.affectedFunctions);
    for (const auto &[function, oldPhase] : oldPhases)
      if (function->phase != oldPhase)
        functionAnalyses_.clear(function);
    maybePrint(module, instrumentation.printAfter, step.name,
               "after-module-pass");
    if (!instrumentation.stopAfter.empty() &&
        instrumentation.stopAfter == step.name)
      halted_ = true;
    return result.changed;
  }

  bool runFunctionStep(Step &step, Module *module, PassContext &context,
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
      noteTiming(context, "function-sweep", step.name,
                 elapsedMicros(sweepStart));
    return changed;
  }

  std::vector<Step> steps_;
  ModuleAnalysisManager moduleAnalyses_;     // 模块分析缓存
  FunctionAnalysisManager functionAnalyses_; // 函数分析缓存
  PassOptions options_;                      // 流水线Pass参数
  std::unique_ptr<PassContext> context_;     // 最近一次运行的上下文
  PrintHook printHook_ = nullptr;            // IR打印回调
  FILE *output_ = stdout;                    // 非拥有Pass输出流
  DiagnosticEngine *diagnostics_ = nullptr;  // 非拥有统一诊断通道
  bool halted_ = false;                      // 是否命中停止插桩
};

} // namespace svm::ir

#define SVM_PM_CONCAT_IMPL(Left, Right) Left##Right
#define SVM_PM_CONCAT(Left, Right) SVM_PM_CONCAT_IMPL(Left, Right)

#define SVM_REGISTER_FUNCTION_PASS(Name, Class)                                \
  namespace {                                                                  \
  [[maybe_unused]] const bool SVM_PM_CONCAT(registeredFunctionPass_,           \
                                            __LINE__) =                        \
      ::svm::ir::PassRegistry::registerPass(                                   \
          {Name, ::svm::ir::PassKind::Function, nullptr,                       \
           [](const ::svm::ir::PassOptions &options)                           \
               -> std::unique_ptr<::svm::ir::FunctionPass> {                   \
             return ::svm::ir::detail::makePass<Class>(options);               \
           }});                                                                \
  }

#define SVM_REGISTER_MODULE_PASS(Name, Class)                                  \
  namespace {                                                                  \
  [[maybe_unused]] const bool SVM_PM_CONCAT(registeredModulePass_, __LINE__) = \
      ::svm::ir::PassRegistry::registerPass(                                   \
          {Name, ::svm::ir::PassKind::Module,                                  \
           [](const ::svm::ir::PassOptions &options)                           \
               -> std::unique_ptr<::svm::ir::ModulePass> {                     \
             return ::svm::ir::detail::makePass<Class>(options);               \
           },                                                                  \
           nullptr});                                                          \
  }

#endif // PASS_MANAGER_H
