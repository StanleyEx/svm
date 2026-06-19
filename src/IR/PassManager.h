#ifndef PASS_MANAGER_H
#define PASS_MANAGER_H

#include "DiagnosticEngine.h"
#include "IR.h"

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
  void set(std::string key, std::string value);
  void setInt(std::string key, i32 value);
  bool has(std::string_view key) const;
  std::string getString(std::string_view key, std::string fallback = {}) const;
  i32 getInt(std::string_view key, i32 fallback = 0) const;
  bool getBool(std::string_view key, bool fallback = false) const;

private:
  std::unordered_map<std::string, std::string> options_;
};

struct AnalysisKey {};

class PreservedAnalyses {
public:
  static PreservedAnalyses all() noexcept;
  static PreservedAnalyses none() noexcept;

  template <typename Analysis> void preserve() { preserve(Analysis::ID()); }
  void preserve(const AnalysisKey *key);
  template <typename Analysis> bool preserves() const noexcept {
    return preserves(Analysis::ID());
  }
  bool preserves(const AnalysisKey *key) const noexcept;

  void preserveCFGAnalyses() noexcept { cfg_ = true; }
  void preserveSSAForm() noexcept { ssa_ = true; }
  void preserveAllFunctionAnalyses() noexcept { allFunctions_ = true; }
  void preserveAllModuleAnalyses() noexcept { allModules_ = true; }

  bool preservesAll() const noexcept { return all_; }
  bool preservesCFGAnalyses() const noexcept { return all_ || cfg_; }
  bool preservesSSAForm() const noexcept { return all_ || ssa_; }
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

template <typename Analysis, typename Unit, typename = void>
struct HasInvalidate : std::false_type {};

template <typename Analysis, typename Unit>
struct HasInvalidate<
    Analysis, Unit,
    std::void_t<decltype(std::declval<const Analysis &>().invalidate(
        std::declval<Unit *>(), std::declval<const PreservedAnalyses &>()))>>
    : std::true_type {};
} // namespace detail

// Analysis对象同时持有分析, 结果数据和失效规则
// 需提供静态ID(), run(Unit *, AnalysisManager &)以及可选的const invalidate()
// Manager只负责按需默认构造Analysis, 触发run(), 缓存对象生命周期
// 并依据PreservedAnalyses删除缓存 公开查询统一返回const Analysis引用或指针
// Pass不能改写缓存中的派生事实 CFG变化只能通过失效流程反映到分析
template <typename Unit> class AnalysisManager {
  class AnalysisConcept {
  public:
    virtual ~AnalysisConcept() = default;
    virtual bool invalidate(Unit *unit, const PreservedAnalyses &preserved) = 0;
  };

  template <typename Analysis>
  class AnalysisModel final : public AnalysisConcept {
  public:
    explicit AnalysisModel(Analysis analysis) : value_(std::move(analysis)) {}

    bool invalidate(Unit *unit, const PreservedAnalyses &preserved) override {
      if constexpr (detail::HasInvalidate<Analysis, Unit>::value)
        return value_.invalidate(unit, preserved);
      else
        return !preserved.preserves(Analysis::ID());
    } // 按分析规则判断失效

    Analysis value_; // 缓存的分析对象
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

  template <typename Analysis> const Analysis &getResult(Unit *unit) {
    if (!unit)
      std::abort();
    if (auto *cached = getCachedResult<Analysis>(unit))
      return *cached;

    const AnalysisKey *key = Analysis::ID();
    for (const InProgress &entry : building_) {
      if (entry.unit == unit && entry.key == key) {
        if (diagnostics_)
          SVM_FATAL(*diagnostics_, SourceLocation{},
                    "AnalysisManager检测到分析循环依赖.");
        std::abort();
      }
    }

    building_.push_back({unit, key});
    Analysis analysis;
    analysis.run(unit, *this);
    auto model = std::make_unique<AnalysisModel<Analysis>>(std::move(analysis));
    building_.pop_back();
    const Analysis *result = &model->value_;
    cache_[unit].emplace(key, std::move(model));
    return *result;
  }

  template <typename Analysis>
  const Analysis *getCachedResult(Unit *unit) const noexcept {
    const auto unitIt = cache_.find(unit);
    if (unitIt == cache_.end())
      return nullptr;
    const auto resultIt = unitIt->second.find(Analysis::ID());
    if (resultIt == unitIt->second.end())
      return nullptr;
    return &static_cast<const AnalysisModel<Analysis> *>(resultIt->second.get())
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
      std::unordered_map<const AnalysisKey *, std::unique_ptr<AnalysisConcept>>;
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

  template <typename Analysis> const Analysis &get(Module *module) {
    return moduleAnalyses_.getResult<Analysis>(module);
  }
  template <typename Analysis> const Analysis &get(Function *function) {
    return functionAnalyses_.getResult<Analysis>(function);
  }
  template <typename Analysis>
  const Analysis *getCached(Module *module) const noexcept {
    return moduleAnalyses_.getCachedResult<Analysis>(module);
  }
  template <typename Analysis>
  const Analysis *getCached(Function *function) const noexcept {
    return functionAnalyses_.getCachedResult<Analysis>(function);
  }

  void invalidate(Function *function, const PreservedAnalyses &preserved);
  void invalidate(Module *module, const PreservedAnalyses &preserved,
                  const std::vector<Function *> &affectedFunctions = {});
  void invalidateModuleAnalyses(
      const PreservedAnalyses &preserved = PreservedAnalyses::none());
  void invalidateAllFunctions(
      const PreservedAnalyses &preserved = PreservedAnalyses::none());
  void notifyFunctionErased(Function *function);
  void notifyFunctionAdded(Function *function);

private:
  Module *module_ = nullptr;
  ModuleAnalysisManager &moduleAnalyses_;
  FunctionAnalysisManager &functionAnalyses_;
  const PassOptions &options_;
  FILE *output_ = stdout;
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
  static bool registerPass(PassDescriptor descriptor);
  static const PassDescriptor *lookup(std::string_view name);
  static std::unique_ptr<FunctionPass>
  createFunction(std::string_view name, const PassOptions &options);
  static std::unique_ptr<ModulePass> createModule(std::string_view name,
                                                  const PassOptions &options);

private:
  [[noreturn]] static void fail(const char *reason, std::string_view name);
  static std::unordered_map<std::string, PassDescriptor> &
  descriptors(); // 返回全局注册表
};

class PassManager {
public:
  using PrintHook = void (*)(Module *, const char *);

  explicit PassManager(DiagnosticEngine *diagnostics = nullptr);
  ~PassManager();

  template <typename Pass, typename... Args> void addPass(Args &&...args) {
    static_assert(std::is_base_of_v<ModulePass, Pass> ||
                  std::is_base_of_v<FunctionPass, Pass>);
    addPass(std::make_unique<Pass>(std::forward<Args>(args)...));
  }

  void addPass(std::unique_ptr<ModulePass> pass);
  void addPass(std::unique_ptr<FunctionPass> pass);
  void addPass(std::string_view name);
  bool run(Module *module);

  void setPrintHook(PrintHook hook) noexcept { printHook_ = hook; }
  void setOutput(FILE *output) noexcept { output_ = output ? output : stdout; }
  bool halted() const noexcept { return halted_; }
  PassContext &context(); // 读取最近一次运行上下文
  ModuleAnalysisManager &moduleAnalyses() noexcept { return moduleAnalyses_; }
  FunctionAnalysisManager &functionAnalyses() noexcept {
    return functionAnalyses_;
  }
  PassOptions &options() noexcept { return options_; }
  const PassOptions &options() const noexcept { return options_; }

private:
  struct Step;            // Pass执行步骤
  struct Instrumentation; // 流水线插桩参数

  void maybePrint(Module *module, std::string_view selected,
                  std::string_view pass, const char *tag) const;
  bool runModuleStep(Step &step, Module *module, PassContext &context,
                     const Instrumentation &instrumentation);
  bool runFunctionStep(Step &step, Module *module, PassContext &context,
                       const Instrumentation &instrumentation);

  std::vector<Step> steps_;                  // 顺序Pass流水线
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
