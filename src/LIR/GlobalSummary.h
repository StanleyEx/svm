#ifndef LIR_GLOBAL_SUMMARY_H
#define LIR_GLOBAL_SUMMARY_H

#include "CallGraph.h"
#include "PassManager.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace svm::ir {

struct EffectSummary {
  enum FlagBits : u8 {
    F_NO_READ_GLOBAL = 1u << 0,  // 不读取全局对象
    F_NO_WRITE_GLOBAL = 1u << 1, // 不写入全局对象
    F_NO_READ_PARAM = 1u << 2,   // 不读取指针形参指向的内存
    F_NO_WRITE_PARAM = 1u << 3,  // 不写入指针形参指向的内存
    F_NO_RECURSE = 1u << 4,      // 传递调用图中不存在递归
    F_NO_EXTERNAL = 1u << 5,     // 不产生外部可见副作用
    F_NO_INF_LOOP = 1u << 6,     // 可保守认为会终止
    F_NO_ESCAPE_PARAM = 1u << 7, // 指针形参均不逃逸
    F_ALL_OPTIMISTIC = 0xFFu,    // 全部最乐观性质
  };
  u8 flags = 0;                              // F_NO_* 性质位
  u16 readsParamMask = 0;                    // 被读的前 16 个形参槽
  u16 writesParamMask = 0;                   // 被写的前 16 个形参槽
  u16 escapesParamMask = 0;                  // 可能逃逸的前 16 个形参槽
  std::unordered_set<Global *> readGlobals;  // 精确读取的全局集合
  std::unordered_set<Global *> writeGlobals; // 精确写入的全局集合
  bool readsUnknownGlobal = false;           // 是否可能读取任意全局
  bool writesUnknownGlobal = false;          // 是否可能写入任意全局
  bool readsUnknownParam = false;            // 是否可能读取未表示的形参槽
  bool writesUnknownParam = false;           // 是否可能写入未表示的形参槽
  bool escapesUnknownParam = false;          // 是否可能逃逸未表示的形参槽
  bool noTrap = false;                       // 所有可达执行都不会触发trap

  // 查询全部过程间乐观性质
  bool isPure() const noexcept { return flags == F_ALL_OPTIMISTIC; }
  // 查询是否没有外部可见写副作用
  bool isReadOnly() const noexcept {
    constexpr u8 mask = F_NO_WRITE_GLOBAL | F_NO_WRITE_PARAM | F_NO_EXTERNAL;
    return (flags & mask) == mask;
  }
  bool readsNoMemory() const noexcept {
    constexpr u8 mask = F_NO_READ_GLOBAL | F_NO_READ_PARAM;
    return (flags & mask) == mask;
  }
  bool writesNoMemory() const noexcept {
    constexpr u8 mask = F_NO_WRITE_GLOBAL | F_NO_WRITE_PARAM;
    return (flags & mask) == mask;
  }
  // 查询可复用调用结果性质
  bool isReadNoneNoSideEffect() const noexcept {
    return readsNoMemory() && writesNoMemory() && (flags & F_NO_EXTERNAL);
  }
  // 查询调用能否新增动态执行
  bool isSpeculatable() const noexcept {
    return isReadNoneNoSideEffect() && (flags & F_NO_INF_LOOP) && noTrap;
  }
  // 查询可见副作用
  bool maySide() const noexcept { return !isReadOnly(); }
  // 查询形参槽读取
  bool readsParam(i32 index) const noexcept {
    return index >= 16 ? readsUnknownParam
                       : index >= 0 && (readsParamMask &
                                        static_cast<u16>(u16{1} << index));
  }
  // 查询形参槽写入
  bool writesParam(i32 index) const noexcept {
    return index >= 16 ? writesUnknownParam
                       : index >= 0 && (writesParamMask &
                                        static_cast<u16>(u16{1} << index));
  }
  // 查询形参槽逃逸
  bool escapesParam(i32 index) const noexcept {
    return index >= 16 ? escapesUnknownParam
                       : index >= 0 && (escapesParamMask &
                                        static_cast<u16>(u16{1} << index));
  }
  // 查询全局读取
  bool readsGlobal(Global *global) const noexcept {
    return readsUnknownGlobal || readGlobals.count(global) != 0;
  }
  // 查询全局写入
  bool writesGlobal(Global *global) const noexcept {
    return writesUnknownGlobal || writeGlobals.count(global) != 0;
  }
};

enum class ExecBoundKind : u8 {
  Never,       // 从 main 不可达
  Const,       // 不超过记录上限的常量上界
  OverCap,     // 有限但超过记录上限
  UnknownMany, // 无法静态界定
};

struct ExecBound {
  ExecBoundKind kind = ExecBoundKind::Never; // 上界分类
  u32 n = 0;                                 // Const 分类的值

  // 不可达
  bool isNever() const noexcept { return kind == ExecBoundKind::Never; }
  // 常量上界
  bool isConst() const noexcept { return kind == ExecBoundKind::Const; }
  // 超限
  bool isOverCap() const noexcept { return kind == ExecBoundKind::OverCap; }
  // 未知执行次数
  bool isUnknownMany() const noexcept {
    return kind == ExecBoundKind::UnknownMany;
  }
  // 最多执行一次
  bool isOnce() const noexcept {
    return kind == ExecBoundKind::Const && n == 1;
  }
  // 查询常量范围
  bool isConstInRange(u32 low, u32 high) const noexcept {
    return kind == ExecBoundKind::Const && n >= low && n <= high;
  }
  static ExecBound never() noexcept { return {ExecBoundKind::Never, 0}; }
  static ExecBound constN(u32 value) noexcept {
    return {ExecBoundKind::Const, value};
  }
  static ExecBound overCap() noexcept { return {ExecBoundKind::OverCap, 0}; }
  static ExecBound unknownMany() noexcept {
    return {ExecBoundKind::UnknownMany, 0};
  }
};

struct CallSiteSummary {
  Function *caller = nullptr;
  Function *callee = nullptr;
  Inst *call = nullptr;
  bool reachable = false; // 调用者是否从 main 可达
  u32 loopDepth = 0;      // 调用点循环嵌套深度
};

struct ExecSummary {
  bool reachableFromEntry = false;
  bool recursiveSCC = false;              // 是否位于递归 SCC
  u32 directCallSiteCount = 0;            // 指向本函数的调用点数
  u32 nonLoopCallSiteCount = 0;           // 其中非循环调用点数
  u32 knownCallerCount = 0;               // 不同内部调用者数量
  ExecBound maxExec = ExecBound::never(); // 执行次数上界
};

struct CallSiteLocalInfo {
  Function *callee = nullptr; // 直接被调函数
  Inst *call = nullptr;       // 调用指令
  u32 lexicalLoopDepth = 0;   // 词法循环深度
  std::vector<Inst *> args;   // 与调用操作数对齐的实参
};

struct LocalMemoryEffects {
  u16 readsParamMask = 0;                    // 本地读取的形参槽
  u16 writesParamMask = 0;                   // 本地写入的形参槽
  u16 escapesParamMask = 0;                  // 本地逃逸的形参槽
  std::unordered_set<Global *> readGlobals;  // 本地读取的全局
  std::unordered_set<Global *> writeGlobals; // 本地写入的全局
  bool readsUnknownParam = false;            // 读取未表示的高位形参
  bool writesUnknownParam = false;           // 写入未表示的高位形参
  bool escapesUnknownParam = false;          // 逃逸未表示的高位形参
  bool readsUnknownRoot = false;             // 读地址根无法归约
  bool writesUnknownRoot = false;            // 写地址根无法归约
};

struct LocalFunctionSummary {
  Function *function = nullptr;
  bool isExternal = false;              // 是否为外部声明
  bool hasBody = false;                 // 是否具有可扫描函数体
  u32 instCount = 0;                    // 递归区域中的指令数
  u32 blockCount = 0;                   // 递归区域中的基本块数
  u32 callCount = 0;                    // 调用指令数
  bool mayNotTerminateLocally = false;  // 本地是否含潜在循环
  bool mayTrapLocally = false;          // 本地是否含未证安全的trap点
  std::vector<CallSiteLocalInfo> calls; // 调用点明细
  LocalMemoryEffects localMem;          // 本地内存行为
  EffectSummary localEffect;            // 不含内部 callee 闭包的摘要
};

using FunctionSummaryMap =
    std::unordered_map<const Function *, LocalFunctionSummary>;

struct GlobalSummaryResult {
  static constexpr u32 kExecCap = 4; // 精确记录的执行次数上限

  Module *module = nullptr;
  Function *entryPoint = nullptr;
  CallGraph callGraph;
  FunctionSummaryMap locals;                                   // 本地摘要
  std::unordered_map<const Function *, EffectSummary> effects; // 副作用闭包
  std::unordered_map<Function *, ExecSummary> fnExec;          // 函数执行事实
  std::unordered_map<Inst *, CallSiteSummary> callSites;       // 调用点执行事实

  const CallGraph &graph() const noexcept { return callGraph; }
  CGNode *nodeOf(const Function *function) const noexcept {
    return callGraph.findNode(function);
  }
  Function *getEntryPoint() const noexcept { return entryPoint; }
  const EffectSummary &effectOf(const Function *function) const;
  const EffectSummary &calleeEffect(const Function *callee) const;
  ExecBound execOf(const Function *function) const noexcept;
  const ExecSummary *execSummary(const Function *function) const noexcept;
  const CallSiteSummary *callSiteSummary(const Inst *call) const noexcept;
};

// 未知调用的最坏摘要
const EffectSummary &conservativeEffectSummary();
// 查询运行时摘要
const EffectSummary &externalEffectSummary(const Function *callee);
// 查询 callee 摘要
const EffectSummary &effectSummaryForCallee(
    const Function *callee,
    const std::unordered_map<const Function *, EffectSummary> *effects);

// 单遍收集本地摘要

FunctionSummaryMap collectLocalSummaries(Module *module);
void buildCallGraphFromLocals(Module *module, const FunctionSummaryMap &locals,
                              CallGraph &graph);
std::unordered_map<const Function *, EffectSummary>
solveModuleEffects(Module *module, const FunctionSummaryMap &locals,
                   const CallGraph &graph);
void populateExecutionSummaries(Module *module,
                                const FunctionSummaryMap &locals,
                                const CallGraph &graph,
                                ModuleAnalysisManager &manager,
                                GlobalSummaryResult &result);

namespace global_summary_detail {

enum class PointerRootKind : u8 {
  Unknown, // 无法静态归约
  Alloca,  // 栈局部对象
  Global,  // 模块全局对象
  Param    // 函数指针形参
};

struct PointerRoot {
  PointerRootKind kind = PointerRootKind::Unknown; // 根类别
  Inst *allocaDef = nullptr;                       // Alloca 根定义
  Global *global = nullptr;                        // Global 根对象
  i32 paramIndex = -1;                             // Param 根槽位
};

PointerRoot resolvePointerRoot(Inst *pointer); // 归约过程间摘要所需指针根

} // namespace global_summary_detail

} // namespace svm::ir

#endif // LIR_GLOBAL_SUMMARY_H
