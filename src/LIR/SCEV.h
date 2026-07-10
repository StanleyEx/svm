#ifndef LIR_SCEV_H
#define LIR_SCEV_H

#include "DomAnalysis.h"
#include "IR.h"
#include "LoopInfo.h"
#include "PassManager.h"
#include "PredicateContext.h"
#include "ScalarFacts.h"

#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace svm::ir {

struct SCEVExpr {
  enum Kind : u8 {
    K_CONSTANT, // 编译期常量
    K_UNKNOWN,  // 不可分析的 SSA 值
    K_ADDREC,   // 加法递推 {base,+,step}<loop>
    K_ADD,      // 规范化多元加法
    K_MUL,      // 规范化多元乘法
    K_SDIV,     // 有符号除法
    K_SREM,     // 有符号取余
  };

  struct CstData {
    i64 v = 0; // K_CONSTANT 的常量值
  };
  struct UnkData {
    Inst *val = nullptr; // K_UNKNOWN 对应的 SSA 值
  };
  struct AddRecData {
    SCEVExpr *base = nullptr; // 迭代零的初值
    SCEVExpr *step = nullptr; // 每轮增量
    Loop *loop = nullptr;     // 递推所属循环
  };
  struct NAryData {
    std::vector<SCEVExpr *> ops; // K_ADD/K_MUL 的操作数
  };
  struct BinData {
    SCEVExpr *lhs = nullptr; // K_SDIV/K_SREM 左操作数
    SCEVExpr *rhs = nullptr; // K_SDIV/K_SREM 右操作数
  };

  Kind kind = K_UNKNOWN; // 节点种类
  IRType ty = TY_I32;    // 表达式结果类型
  bool nsw = false;      // 已证明有符号 i32 不回绕
  CstData cst;           // 常量载荷
  UnkData unk;           // 未知值载荷
  AddRecData addRec;     // 递推载荷
  NAryData nary;         // 多元运算载荷
  BinData bin;           // 二元运算载荷

  bool isLoopInvariant(const Loop *loop) const; // 循环不变量判断
  bool isConstant() const noexcept { return kind == K_CONSTANT; }
  bool isZero() const noexcept { return isConstant() && cst.v == 0; }
  bool isOne() const noexcept { return isConstant() && cst.v == 1; }
  bool structurallyEquals(const SCEVExpr *other) const noexcept;
  bool containsAddRecOf(const Loop *loop) const; // 查询是否包含指定递推
};

/// i32 回绕值域查询参数
struct RangeQuery {
  BasicBlock *contextBlock = nullptr;                 // 查询发生的基本块
  const PredicateContext *predicateContext = nullptr; // 显式路径事实
  u32 maxDepth = 64;                                  // 递归深度上限
};

/// 数学整数域边界查询参数
struct MathQuery {
  BasicBlock *contextBlock = nullptr;
  const PredicateContext *predicateContext = nullptr;
  u32 maxDepth = 64;
};

/// 同余事实查询参数
struct CongruenceQuery {
  BasicBlock *contextBlock = nullptr;
  const PredicateContext *predicateContext = nullptr;
  u32 maxDepth = 64;
  ArithmeticDomain domain = ArithmeticDomain::I32Wrapping; // 算术语义域
  u64 maxMod = u64{1} << 32;                               // 模数复杂度上限
};

class SCEV {
public:
  SCEV() = default;
  ~SCEV() = default;
  SCEV(SCEV &&) noexcept = default;
  SCEV &operator=(SCEV &&) noexcept = default;
  SCEV(const SCEV &) = delete;
  SCEV &operator=(const SCEV &) = delete;

  void build(Function *function, FunctionAnalysisManager &manager);

  SCEVExpr *getSCEV(Inst *value) const;

  // 入环后的精确 BTC 或未知值
  SCEVExpr *getBackedgeTakenCount(const Loop *loop) const;
  // 正常量迭代次数 否则 -1
  i64 getConstantTripCount(const Loop *loop) const;
  // 无旁路出口闭式值
  SCEVExpr *getExitValue(Inst *value, const Loop *loop) const;

  SCEVExpr *getConstant(i64 value, IRType type) const;
  SCEVExpr *getUnknown(Inst *value) const;
  SCEVExpr *getAddRecExpr(SCEVExpr *base, SCEVExpr *step, Loop *loop) const;
  SCEVExpr *getAddExpr(SCEVExpr *left, SCEVExpr *right) const;
  SCEVExpr *getMulExpr(SCEVExpr *left, SCEVExpr *right) const;
  SCEVExpr *getSDivExpr(SCEVExpr *left, SCEVExpr *right) const;
  SCEVExpr *getSRemExpr(SCEVExpr *left, SCEVExpr *right) const;

  I32Range getI32Range(SCEVExpr *expr, const RangeQuery &query = {}) const;
  I32Range getI32Range(Inst *value, const RangeQuery &query = {}) const;
  MathBounds getSignedDeltaBounds(SCEVExpr *left, SCEVExpr *right,
                                  const MathQuery &query = {}) const;

  Congruence getCongruence(SCEVExpr *expr,
                           const CongruenceQuery &query = {}) const;
  Congruence getCongruence(Inst *value,
                           const CongruenceQuery &query = {}) const;
  bool satisfiesCongruence(SCEVExpr *expr, u64 mod, i64 rem,
                           const CongruenceQuery &query = {}) const;
  bool satisfiesCongruence(Inst *value, u64 mod, i64 rem,
                           const CongruenceQuery &query = {}) const;
  KnownBool evaluatePredicate(Inst *predicate,
                              const PredicateQuery &query = {}) const;

  bool isSafeToExpand(SCEVExpr *expr, BasicBlock *insertBlock) const;

private:
  friend class SCEVExpander;

  // 既有值复用计划
  struct ExpansionReuse {
    Inst *value = nullptr;      // 可复用的既有 SSA 值
    SCEVExpr *offset = nullptr; // 需要补加的循环不变量
  };

  Function *function_ = nullptr;
  const LoopInfo *loopInfo_ = nullptr;
  const DominatorTree *dominatorTree_ = nullptr;

  // SCEV 表达式所有权
  mutable std::vector<std::unique_ptr<SCEVExpr>> expressions_;
  // SSA 到表达式缓存
  mutable std::unordered_map<Inst *, SCEVExpr *> cache_;
  // 循环 BTC 缓存
  mutable std::unordered_map<const Loop *, SCEVExpr *> btcCache_;
  // 表达式到原 SSA
  mutable std::unordered_map<SCEVExpr *, Inst *> exprToInst_;
  // 无上下文值域缓存
  mutable std::unordered_map<SCEVExpr *, I32Range> rangeCache_;
  // 同余缓存
  mutable std::unordered_map<SCEVExpr *, Congruence> congruenceCache_;
  // 无回绕递归保护
  mutable std::unordered_set<SCEVExpr *> noWrapProving_;

  // 按操作码创建表达式
  SCEVExpr *createSCEV(Inst *value) const;
  // 识别循环递推 Phi
  SCEVExpr *createNodeForPhi(Inst *phi) const;
  // 计算回边次数
  SCEVExpr *computeBTC(const Loop *loop) const;
  // 写入无回绕证明
  void setNoWrap(SCEVExpr *expr) const noexcept;
  // 证明递推
  void proveAndSetAddRecNoWrap(SCEVExpr *expr) const noexcept;
  // 无回绕证明
  bool proveAddRecNoSignedWrap(SCEVExpr *base, SCEVExpr *step,
                               const Loop *loop) const noexcept;

  MathBounds proveMathBoundsNoWrap(SCEVExpr *expr,
                                   const MathQuery &query) const;
  // 数学边界递归
  bool computeNoWrap(SCEVExpr *expr, const MathQuery &query,
                     MathBounds &mathRange, NoWrapSource &source,
                     u32 depth) const;
  // 闭式代入
  SCEVExpr *evaluateAtIteration(SCEVExpr *expr, SCEVExpr *iteration,
                                const Loop *loop) const;
  // 合并同类项
  SCEVExpr *buildAddCanonical(SCEVExpr *left, SCEVExpr *right) const;
  // 规范化取负
  SCEVExpr *getNegExpr(SCEVExpr *expr) const;

  I32Range computeI32Range(SCEVExpr *expr, const RangeQuery &query, u32 depth,
                           std::unordered_set<SCEVExpr *> &onStack) const;
  I32Range computeAddRecI32Range(SCEVExpr *expr, const RangeQuery &query,
                                 u32 depth,
                                 std::unordered_set<SCEVExpr *> &onStack) const;
  Congruence computeCongruence(SCEVExpr *expr, const CongruenceQuery &query,
                               u32 depth,
                               std::unordered_set<SCEVExpr *> &onStack) const;
  // 机器域裁剪
  Congruence restrictToDomain(Congruence value, ArithmeticDomain domain,
                              bool expressionIsNSW) const;

  // 统一物化预检
  static bool canExpandAt(const SCEV *scev, const Function *function,
                          SCEVExpr *expr, BasicBlock *insertBlock,
                          Inst *insertBefore);
  // 查找可复用的既有值
  static ExpansionReuse
  findExpansionReuse(const SCEV *scev, const Function *function, SCEVExpr *expr,
                     BasicBlock *insertBlock, Inst *insertBefore);

  // 分配拥有节点
  SCEVExpr *allocExpr(SCEVExpr::Kind kind, IRType type) const;
};

class SCEVExpander {
public:
  explicit SCEVExpander(Function *function, const SCEV *scev = nullptr);
  Inst *expandCodeFor(SCEVExpr *expr, Inst *insertBefore);

private:
  const SCEV *scev_ = nullptr;
  IRBuilder builder_;
  std::unordered_map<SCEVExpr *, Inst *> expanded_; // 物化缓存

  Inst *expand(SCEVExpr *expr, Inst *insertBefore);
};

} // namespace svm::ir

#endif // LIR_SCEV_H
