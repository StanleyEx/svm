#ifndef PASS_MANAGER_H
#define PASS_MANAGER_H

#include "DiagnosticEngine.h"
#include "IR.h"

#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>

namespace svm::ir {
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
  void preserve(const AnalysisKey *key) {
    if (all_)
      return;
    if (!preservesKey(key))
      preserved_.push_back(key);
  }
  template <typename Analysis> bool preserves() const noexcept {
    return preserves(Analysis::ID());
  }
  bool preserves(const AnalysisKey *key) const noexcept {
    return all_ || preservesKey(key);
  }

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

  // 聚合多个IR单元的结果时 只保留每个结果共同承诺有效的分析
  void intersect(const PreservedAnalyses &other) {
    if (other.all_)
      return;
    if (all_) {
      *this = other;
      return;
    }

    cfg_ = cfg_ && other.cfg_;
    ssa_ = ssa_ && other.ssa_;
    allFunctions_ = allFunctions_ && other.allFunctions_;
    allModules_ = allModules_ && other.allModules_;
    preserved_.erase(std::remove_if(preserved_.begin(), preserved_.end(),
                                    [&](const AnalysisKey *key) {
                                      return !other.preservesKey(key);
                                    }),
                     preserved_.end());
  }

private:
  bool preservesKey(const AnalysisKey *key) const noexcept {
    return std::find(preserved_.begin(), preserved_.end(), key) !=
           preserved_.end();
  }

  bool all_ = false;
  bool cfg_ = false;
  bool ssa_ = false;
  bool allFunctions_ = false;
  bool allModules_ = false;
  // 显式保留的分析通常不超过数项 连续存储比节点式哈希表更紧凑
  std::vector<const AnalysisKey *> preserved_;
};

struct PassResult {
  bool changed = false;                                   // 是否修改了IR
  PreservedAnalyses preserved = PreservedAnalyses::all(); // 保留的分析
  // 仅记录Pass返回时仍属于Module的函数 删除函数需显式通知拓扑变化
  std::vector<Function *> affectedFunctions; // 实际影响的存活函数

  static PassResult noChange() noexcept { return {}; }
  static PassResult
  changedIR(PreservedAnalyses analyses = PreservedAnalyses::none()) noexcept {
    return {true, std::move(analyses), {}};
  }
};

// PipelineOptions只描述PassManager的调度策略 Pass私有参数由构造函数接收
class PipelineOptions {
public:
  using Hook = std::function<void(Module *, const PassResult &)>;
  using PreHook = std::function<void(Module *)>;

  void addDisablePass(std::string_view name) {
    appendUnique(disabledPasses_, name);
  }
  void addBypassFunction(std::string_view functionName) {
    appendUnique(bypassedFunctions_, functionName);
  }
  void setTimePasses(bool enable) noexcept { timePasses_ = enable; }
  void hook(std::string_view passName, Hook callback) {
    if (callback)
      hooks_.emplace_back(std::string(passName), std::move(callback));
  }
  void hookPre(std::string_view passName, PreHook callback) {
    if (callback)
      preHooks_.emplace_back(std::string(passName), std::move(callback));
  }
  bool timePasses() const noexcept { return timePasses_; }

private:
  friend class PassManager;

  template <typename Names>
  static auto lowerBound(Names &names, std::string_view name) noexcept {
    return std::lower_bound(
        names.begin(), names.end(), name,
        [](const std::string &candidate, std::string_view selected) {
          return std::string_view(candidate) < selected;
        });
  }
  static bool contains(const std::vector<std::string> &names,
                       std::string_view name) noexcept {
    const auto found = lowerBound(names, name);
    return found != names.end() && std::string_view(*found) == name;
  }
  static void appendUnique(std::vector<std::string> &names,
                           std::string_view name) {
    const auto insertion = lowerBound(names, name);
    if (insertion == names.end() || std::string_view(*insertion) != name)
      names.emplace(insertion, name);
  }
  bool isDisabled(std::string_view passName) const noexcept {
    return contains(disabledPasses_, passName);
  }
  bool isBypassed(const Function *function) const noexcept {
    return function && function->name &&
           contains(bypassedFunctions_, std::string_view(function->name));
  }
  void runPreHooks(std::string_view passName, Module *module) const {
    for (const auto &[selected, callback] : preHooks_)
      if (selected == passName)
        callback(module);
  }
  void runHooks(std::string_view passName, Module *module,
                const PassResult &result) const {
    for (const auto &[selected, callback] : hooks_)
      if (selected == passName)
        callback(module, result);
  }
  bool hasHooks(std::string_view passName) const noexcept {
    for (const auto &entry : hooks_)
      if (entry.first == passName)
        return true;
    return false;
  }

  std::vector<std::string> disabledPasses_;
  std::vector<std::string> bypassedFunctions_;
  bool timePasses_ = false;
  std::vector<std::pair<std::string, Hook>> hooks_;
  std::vector<std::pair<std::string, PreHook>> preHooks_;
};

namespace detail {
inline DiagnosticEngine *diagnosticsFor(Module *module) noexcept {
  return module ? module->diagnostics : nullptr;
}

inline DiagnosticEngine *diagnosticsFor(Function *function) noexcept {
  return function && function->module ? function->module->diagnostics : nullptr;
}

template <typename Analysis, typename Unit, typename = void>
struct HasMutableInvalidate : std::false_type {};

template <typename Analysis, typename Unit>
struct HasMutableInvalidate<
    Analysis, Unit,
    std::void_t<decltype(static_cast<bool (Analysis::*)(
                             Unit *, const PreservedAnalyses &)>(
        &Analysis::invalidate))>> : std::true_type {};

template <typename Analysis, typename Unit, typename = void>
struct HasConstInvalidate : std::false_type {};

template <typename Analysis, typename Unit>
struct HasConstInvalidate<
    Analysis, Unit,
    std::void_t<decltype(static_cast<bool (Analysis::*)(
                             Unit *, const PreservedAnalyses &) const>(
        &Analysis::invalidate))>> : std::true_type {};

// 自定义失效必须使用精确签名 避免传值或错误返回类型被静默接受
template <typename Analysis, typename Unit>
struct HasInvalidate
    : std::bool_constant<HasMutableInvalidate<Analysis, Unit>::value ||
                         HasConstInvalidate<Analysis, Unit>::value> {};

template <typename Analysis, typename = void>
struct HasNamedInvalidate : std::false_type {};

template <typename Analysis>
struct HasNamedInvalidate<Analysis,
                          std::void_t<decltype(&Analysis::invalidate)>>
    : std::true_type {};

template <typename Analysis, typename Unit, typename = void>
struct HasCallableInvalidate : std::false_type {};

template <typename Analysis, typename Unit>
struct HasCallableInvalidate<
    Analysis, Unit,
    std::void_t<decltype(std::declval<Analysis &>().invalidate(
        std::declval<Unit *>(), std::declval<const PreservedAnalyses &>()))>>
    : std::true_type {};

template <typename Analysis, typename Unit>
struct HasMalformedInvalidate
    : std::bool_constant<!HasInvalidate<Analysis, Unit>::value &&
                         (HasNamedInvalidate<Analysis>::value ||
                          HasCallableInvalidate<Analysis, Unit>::value)> {};
} // namespace detail

// Analysis对象同时持有分析, 结果数据和失效规则
// 需提供静态ID(), run(Unit *, AnalysisManager &)以及可选的invalidate()
// AM只负责按需默认构造Analysis, 触发run(), 缓存对象生命周期
// 并依据PreservedAnalyses删除缓存 公开查询统一返回const Analysis引用或指针
// Pass不能改写缓存中的派生事实 CFG变化只能通过失效流程反映到分析
template <typename Unit> class AnalysisManager {
  static_assert(std::is_same_v<Unit, Module> || std::is_same_v<Unit, Function>,
                "AnalysisManager只支持Module或Function IR结构");

  using LinkedUnit =
      std::conditional_t<std::is_same_v<Unit, Module>, Function, Module>;
  class AnalysisConcept {
  public:
    virtual ~AnalysisConcept() = default;
    virtual bool invalidate(Unit *unit, const PreservedAnalyses &preserved) = 0;
  };

  template <typename Analysis>
  class AnalysisModel final : public AnalysisConcept {
  public:
    static_assert(!detail::HasMalformedInvalidate<Analysis, Unit>::value,
                  "Analysis::invalidate必须声明为bool invalidate(Unit *, const "
                  "PreservedAnalyses &), 也可以是const成员函数.");
    explicit AnalysisModel(Analysis analysis) : value_(std::move(analysis)) {}

    bool invalidate(Unit *unit, const PreservedAnalyses &preserved) override {
      if constexpr (detail::HasInvalidate<Analysis, Unit>::value)
        return value_.invalidate(unit, preserved);
      else
        return !preserved.preserves(Analysis::ID());
    }

    Analysis value_;
  };

  struct InProgress {
    Unit *unit = nullptr;             // 正在分析的IR单元
    const AnalysisKey *key = nullptr; // 正在构建的分析
  };

  // 分析构建状态必须在run()或结果入缓存抛出时同样出栈
  class BuildingGuard {
  public:
    explicit BuildingGuard(std::vector<InProgress> &building) noexcept
        : building_(building) {}
    ~BuildingGuard() noexcept { building_.pop_back(); }

    BuildingGuard(const BuildingGuard &) = delete;
    BuildingGuard &operator=(const BuildingGuard &) = delete;

  private:
    std::vector<InProgress> &building_; // 需在作用域退出时回滚的构建栈
  };

public:
  AnalysisManager() = default;
  AnalysisManager(const AnalysisManager &) = delete;
  AnalysisManager &operator=(const AnalysisManager &) = delete;

  // 每个管理器只链接相反IR层级 分析构建可据此按需查询跨层依赖
  template <typename U = Unit,
            std::enable_if_t<std::is_same_v<U, Module>, int> = 0>
  void linkFunctionAM(AnalysisManager<Function> *analyses) noexcept {
    linkedAnalyses_ = analyses;
  }
  template <typename U = Unit,
            std::enable_if_t<std::is_same_v<U, Function>, int> = 0>
  void linkModuleAM(AnalysisManager<Module> *analyses) noexcept {
    linkedAnalyses_ = analyses;
  }
  template <typename U = Unit,
            std::enable_if_t<std::is_same_v<U, Module>, int> = 0>
  AnalysisManager<Function> *functionLink() const noexcept {
    return linkedAnalyses_;
  }
  template <typename U = Unit,
            std::enable_if_t<std::is_same_v<U, Function>, int> = 0>
  AnalysisManager<Module> *moduleLink() const noexcept {
    return linkedAnalyses_;
  }

  template <typename Analysis> const Analysis &getResult(Unit *unit) {
    if (!unit)
      std::abort();
    if (auto *cached = getCachedResult<Analysis>(unit))
      return *cached;

    const AnalysisKey *key = Analysis::ID();
    for (const InProgress &entry : building_) {
      if (entry.unit == unit && entry.key == key) {
        if (DiagnosticEngine *diagnostics = detail::diagnosticsFor(unit))
          SVM_FATAL(*diagnostics, SourceLocation{},
                    "AnalysisManager检测到分析循环依赖.");
        std::abort();
      }
    }

    building_.push_back({unit, key});
    [[maybe_unused]] const BuildingGuard guard(building_);
    Analysis analysis;
    analysis.run(unit, *this);
    auto model = std::make_unique<AnalysisModel<Analysis>>(std::move(analysis));
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
  bool hasResults(Unit *unit) const noexcept {
    return cache_.find(unit) != cache_.end();
  }

private:
  using UnitCache =
      std::unordered_map<const AnalysisKey *, std::unique_ptr<AnalysisConcept>>;
  std::unordered_map<Unit *, UnitCache> cache_; // 按IR单元保存分析结果
  std::vector<InProgress> building_;            // 分析递归构建栈
  AnalysisManager<LinkedUnit> *linkedAnalyses_ = nullptr; // 相反层级分析缓存
};

using ModuleAnalysisManager = AnalysisManager<Module>;
using FunctionAnalysisManager = AnalysisManager<Function>;

// 建立双向跨层查询关系 链接不转移AnalysisManager所有权
inline void linkAnalysisManagers(ModuleAnalysisManager &moduleAnalyses,
                                 FunctionAnalysisManager &functionAnalyses) {
  moduleAnalyses.linkFunctionAM(&functionAnalyses);
  functionAnalyses.linkModuleAM(&moduleAnalyses);
}

class PassContext {
public:
  PassContext(Module &module, ModuleAnalysisManager &moduleAnalyses,
              FunctionAnalysisManager &functionAnalyses) noexcept
      : module_(module), moduleAnalyses_(moduleAnalyses),
        functionAnalyses_(functionAnalyses) {}

  Arena *arena() const noexcept { return module_.arena; }
  Module *module() const noexcept { return &module_; }
  ModuleAnalysisManager &moduleAnalyses() noexcept { return moduleAnalyses_; }
  FunctionAnalysisManager &functionAnalyses() noexcept {
    return functionAnalyses_;
  }
  DiagnosticEngine *diagnostics() const noexcept { return module_.diagnostics; }

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
  // Function必须仍然有效 在摘链前或插入Module后立即调用
  void notifyFunctionTopologyChanged(Function *function);

private:
  Module &module_;                            // 当前运行且始终有效的模块
  ModuleAnalysisManager &moduleAnalyses_;     // 模块分析缓存
  FunctionAnalysisManager &functionAnalyses_; // 函数分析缓存
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

#define DECLARE_MODULE_PASS(PassName)                                          \
  class PassName final : public ModulePass {                                   \
  public:                                                                      \
    std::string_view name() const noexcept override;                           \
    PassResult run(Module *module, PassContext &context) override;             \
  }

#define DECLARE_FUNCTION_PASS(PassName)                                        \
  class PassName final : public FunctionPass {                                 \
  public:                                                                      \
    std::string_view name() const noexcept override;                           \
    PassResult run(Function *function, PassContext &context) override;         \
  }

class PassManager {
public:
  explicit PassManager(DiagnosticEngine *diagnostics = nullptr);
  ~PassManager();

  template <typename Pass, typename... Args> void addPass(Args &&...args) {
    static_assert(std::is_base_of_v<ModulePass, Pass> ||
                      std::is_base_of_v<FunctionPass, Pass>,
                  "Pass必须继承ModulePass或FunctionPass.");
    addPass(std::make_unique<Pass>(std::forward<Args>(args)...));
  }

  bool run(Module *module);

  PassContext &context(); // 读取最近一次运行上下文
  ModuleAnalysisManager &moduleAnalyses() noexcept { return moduleAnalyses_; }
  FunctionAnalysisManager &functionAnalyses() noexcept {
    return functionAnalyses_;
  }
  PipelineOptions &options() noexcept { return options_; }
  const PipelineOptions &options() const noexcept { return options_; }

private:
  struct Step; // Pass执行步骤

  void addPass(std::unique_ptr<ModulePass> pass);
  void addPass(std::unique_ptr<FunctionPass> pass);
  PassResult runModuleStep(ModulePass &pass, Module *module,
                           PassContext &context);
  PassResult runFunctionStep(FunctionPass &pass, Module *module,
                             PassContext &context,
                             bool collectAffectedFunctions);

  std::vector<Step> steps_;                  // 顺序Pass流水线
  ModuleAnalysisManager moduleAnalyses_;     // 模块分析缓存
  FunctionAnalysisManager functionAnalyses_; // 函数分析缓存
  PipelineOptions options_;                  // 流水线调度选项
  std::optional<PassContext> context_;       // 最近一次运行的内联上下文
  DiagnosticEngine *diagnostics_ = nullptr;  // 非拥有诊断通道
};

} // namespace svm::ir

#endif // PASS_MANAGER_H
