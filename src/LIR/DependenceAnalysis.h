#ifndef LIR_DEPENDENCE_ANALYSIS_H
#define LIR_DEPENDENCE_ANALYSIS_H

#include "Alias.h"
#include "DependenceSolver.h"
#include "DomAnalysis.h"
#include "SCEV.h"

#include <optional>
#include <unordered_map>
#include <vector>

namespace svm::ir {

enum class AccessBuildStatus : u8 {
  Exact,              // 访问已完整建模
  UnknownRoot,        // 无法取得稳定对象根
  NonAffine,          // 地址含非仿射项
  MissingNoWrap,      // 标量i32数学整数语义未获证明
  UnsupportedWidth,   // 访问宽度无法建模
  BudgetExceeded,     // 访问表达式超过构建预算
  ArithmeticOverflow, // checked-i64线性化溢出
};

enum class MemoryAccessKind : u8 {
  Read,  // 只读访问
  Write, // 写访问
};

struct LoopCoefficient {
  const Loop *loop = nullptr; // 规范迭代号所属循环
  i64 coefficient = 0;        // 规范迭代号系数
};

struct InvariantAtom {
  const SCEVExpr *expression = nullptr; // 循环不变SCEV身份
  IRType type = TY_I32;                 // 原子结果类型
  i64 coefficient = 0;                  // 规范化系数
};

struct AffineExpr {
  i64 constant = 0;                   // 常量项
  std::vector<LoopCoefficient> loops; // 规范迭代号项
  std::vector<InvariantAtom> symbols; // 循环不变原子项
  MathBounds bounds;                  // 已证明的数学整数边界
};

struct LinearByteFunction {
  Inst *root = nullptr;               // 抽象内存对象根
  i64 constant = 0;                   // 相对根的常量字节偏移
  std::vector<LoopCoefficient> loops; // 字节单位循环系数
  std::vector<InvariantAtom> symbols; // 字节单位不变量系数
  NoWrapInfo noWrap;                  // pointer-width字节表达式无回绕证明
};

struct StructuredSubscripts {
  IRType elementType = TY_VOID;    // 数组元素类型
  std::vector<u32> dims;           // 各坐标合法范围 0表示形参未知首维
  std::vector<u32> strides;        // 各坐标字节步幅
  std::vector<AffineExpr> indices; // 各维仿射下标
};

struct AffineAccess {
  Inst *memoryInst = nullptr;                              // load/store指令
  Inst *address = nullptr;                                 // 地址SSA值
  MemoryAccessKind kind = MemoryAccessKind::Read;          // 读写角色
  u32 widthBytes = 0;                                      // 访问宽度
  LinearByteFunction bytes;                                // byte-linear主模型
  std::optional<StructuredSubscripts> shape;               // 已证单射的结构模型
  AccessBuildStatus status = AccessBuildStatus::NonAffine; // 构建状态

  // 判断访问模型是否完整精确
  bool exact() const noexcept { return status == AccessBuildStatus::Exact; }
};

struct AffineAccessBudget {
  u32 maxExpressionNodes = 256; // 单访问最多遍历的SCEV节点数
  u32 maxAddressDepth = 32;     // 地址链最大深度
};

enum class DependenceKind : u8 {
  Flow,   // write到read
  Anti,   // read到write
  Output, // write到write
  Input,  // read到read
};

enum class ProgramOrder : u8 {
  Before,   // source静态语句先执行
  After,    // source静态语句后执行
  Same,     // static self-pair
  Unordered // CFG中没有可证静态先后
};

enum class DependenceProofKind : u8 {
  None,          // 没有排除证明
  ObjectNoAlias, // 对象级AA证明
  ZIV,           // 常量地址证明
  SIV,           // 单变量证明
  GCD,           // 最大公约数证明
  Banerjee,      // 有界Banerjee证明
};

enum class DependenceRejectReason : u8 {
  None,                     // 未发生建模拒绝
  InvalidAccess,            // 不是受支持的load/store
  UnknownRoot,              // 无稳定对象根
  NonAffine,                // 地址不是仿射式
  MissingNoWrap,            // 标量i32无回绕证明缺失
  UnsupportedWidth,         // 宽度或对齐合同不支持
  AccessBudgetExceeded,     // 单循环访问数超预算
  PairBudgetExceeded,       // 单循环访问对超预算
  DirectionBudgetExceeded,  // 方向枚举深度超预算
  ExpressionBudgetExceeded, // 单地址表达式超预算
  ScopeMismatch,            // scope不是两访问公共循环
  ProgramOrderUnknown,      // 同迭代静态先后不可证
  MayAlias,                 // 不同对象根仍可能别名
  SymbolicTerm,             // 不变量或局部循环项未抵消
  OpaqueCall,               // 循环含未知内存效果调用
  ArithmeticOverflow,       // checked-i64推理溢出
  SolverInvalid,            // 纯整数求解输入非法
};

using DirectionVectorSet = std::vector<DirectionVector>;

struct DependenceResult {
  Inst *source = nullptr;                              // 较早动态访问的静态指令
  Inst *sink = nullptr;                                // 较晚动态访问的静态指令
  DependenceStatus status = DependenceStatus::Unknown; // No/May/Unknown三态
  DependenceKind kind = DependenceKind::Input;         // 规范化读写类型
  DirectionVectorSet possible;                         // 可能方向向量集合
  std::vector<std::optional<i64>> distances;           // sink-source精确距离
  std::vector<std::optional<u64>> distanceMultiples;   // 非零距离的整除约束
  std::vector<const Loop *> loops;                     // 方向分量对应循环
  DependenceProofKind proof = DependenceProofKind::None;        // 最强排除证明
  DependenceRejectReason reject = DependenceRejectReason::None; // Unknown原因
  bool selfPair = false;                        // 是否static self-pair
  ProgramOrder order = ProgramOrder::Unordered; // 同迭代语句顺序
};

struct DependenceBudget {
  u32 maxAccessesPerLoop = 128; // 单循环最多内存访问数
  u32 maxPairsPerLoop = 8192;   // 单循环最多static pair数
  u32 maxDirectionDepth = 3;    // 最多枚举的方向维数
  AffineAccessBudget access;    // 单访问表达式预算
};

class DependenceInfo {
public:
  DependenceInfo() = default;

  // 查询并缓存单条load/store的仿射访问模型
  const AffineAccess &getAccess(Inst *memoryInst) const;
  // 查询一个已按动态执行顺序定向的访问对
  DependenceResult dependence(Inst *source, Inst *sink, const Loop *scope,
                              ProgramOrder order, bool selfPair = false) const;
  // 统一枚举scope内所有static pair和self-pair
  std::vector<DependenceResult> getDependences(const Loop *scope,
                                               bool includeInput = false) const;
  // 返回当前可观测预算
  const DependenceBudget &budget() const noexcept { return budget_; }

private:
  struct PairKey {
    Inst *source = nullptr;                       // 定向source
    Inst *sink = nullptr;                         // 定向sink
    const Loop *scope = nullptr;                  // 查询scope
    ProgramOrder order = ProgramOrder::Unordered; // 同迭代顺序
    bool selfPair = false;                        // self-pair标记

    bool operator==(const PairKey &other) const noexcept;
  };

  struct PairKeyHash {
    usize operator()(const PairKey &key) const noexcept;
  };

  friend struct DependenceAnalysis;

  void build(Function *function, const SCEV *scev, const LoopInfo *loops,
             const AliasInfo *alias, const DominatorTree *dominators,
             DependenceBudget budget = {}) noexcept;

  // 返回访问所在的完整外到内循环链
  std::vector<const Loop *> loopNestFor(const Inst *instruction) const;

  // 返回两访问从scope开始的公共循环链
  std::vector<const Loop *> commonNest(Inst *first, Inst *second,
                                       const Loop *scope) const;

  // 判定同迭代静态语句顺序
  ProgramOrder programOrder(Inst *first, Inst *second) const noexcept;

  // 执行未缓存的定向访问对求解
  DependenceResult solvePair(Inst *source, Inst *sink, const Loop *scope,
                             ProgramOrder order, bool selfPair) const;

  Function *function_ = nullptr;
  const SCEV *scev_ = nullptr;
  const LoopInfo *loops_ = nullptr;
  const AliasInfo *alias_ = nullptr;
  const DominatorTree *dominators_ = nullptr;
  // 观测复杂度预算
  DependenceBudget budget_;
  // 访问缓存
  mutable std::unordered_map<Inst *, AffineAccess> accessCache_;
  // 定向访问对缓存
  mutable std::unordered_map<PairKey, DependenceResult, PairKeyHash> pairCache_;
};

} // namespace svm::ir

#endif // LIR_DEPENDENCE_ANALYSIS_H
