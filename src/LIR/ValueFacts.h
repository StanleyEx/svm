#ifndef LIR_VALUE_FACTS_H
#define LIR_VALUE_FACTS_H

/// @file ValueFacts.h
/// @brief 组合 SCEV, 谓词上下文与局部 SSA 传递规则的 i32 值域信息

#include "PredicateContext.h"

#include <unordered_map>
#include <unordered_set>

namespace svm::ir {

class DominatorTree;
class Inst;
class SCEV;

struct ValueFactQuery {
  BasicBlock *contextBlock = nullptr;                 // 查询所在的 CFG 块
  const PredicateContext *predicateContext = nullptr; // 调用方提供的边/路径事实
  bool useNonLoopPhi = true;                          // 是否展开非循环 Phi
  bool useLocalExpr = true; // 是否执行局部表达式传递规则
};

class ValueFactOracle {
public:
  ValueFactOracle(const SCEV *scev, const DominatorTree *dominatorTree) noexcept
      : scev_(scev), builder_(dominatorTree) {}

  /// 查询 SSA 值在给定上下文中的 i32 环形值集合
  I32Range getI32Range(Inst *value, const ValueFactQuery &query = {});

private:
  /// 递归查询的结果和环检测或预算降级标记
  struct RangeResult {
    I32Range range = I32Range::unknown(); // 推导出的值集合
    bool tainted = false; // 结果含有仅对当前递归栈有效的保守占位
  };

  /// 无显式 PredicateContext 时可缓存的查询键
  struct MemoKey {
    const Inst *value = nullptr;              // SSA 值身份
    const BasicBlock *contextBlock = nullptr; // 块敏感上下文身份
    u32 flags = 0;                            // ValueFactQuery 的布尔开关

    /// 比较两个查询键是否表示同一语义查询
    bool operator==(const MemoKey &other) const noexcept {
      return value == other.value && contextBlock == other.contextBlock &&
             flags == other.flags;
    }
  };

  /// MemoKey 的指针与标志混合哈希
  struct MemoKeyHash {
    /// 计算稳定的无符号哈希值
    usize operator()(const MemoKey &key) const noexcept;
  };

  const SCEV *scev_ = nullptr;
  PredicateContextBuilder builder_;
  std::unordered_map<MemoKey, I32Range, MemoKeyHash> memo_; // 短寿命记忆缓存
  using QueryMemo = std::unordered_map<Inst *, I32Range>;   // 单次同上下文缓存

  /// 递归值域查询核心
  RangeResult rangeImpl(Inst *value, const ValueFactQuery &query,
                        std::unordered_set<Inst *> &visited,
                        QueryMemo &queryMemo);
  /// 合流普通 Phi 的各个输入值域
  RangeResult rangePhi(Inst *phi, const ValueFactQuery &query,
                       std::unordered_set<Inst *> &visited);
  /// 查询非 Phi 指令的事实并执行局部传递规则
  RangeResult rangeExpr(Inst *value, const ValueFactQuery &query,
                        std::unordered_set<Inst *> &visited,
                        QueryMemo &queryMemo);
};

} // namespace svm::ir

#endif // LIR_VALUE_FACTS_H
