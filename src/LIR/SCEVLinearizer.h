#ifndef LIR_SCEV_LINEARIZER_H
#define LIR_SCEV_LINEARIZER_H

#include "SCEV.h"

#include <vector>

namespace svm::ir {

enum class SCEVLinearizeStatus : u8 {
  Exact,              // 表达式已完整线性化
  InvalidExpression,  // 表达式结构无效
  BudgetExceeded,     // 节点或深度预算耗尽
  ArithmeticOverflow, // 常量运算溢出
};

struct SCEVLinearTerm {
  SCEVExpr *atom = nullptr; // 不透明非恒定原子
  i64 coefficient = 0;      // 规范化系数
};

struct SCEVLinearForm {
  // 常量项
  i64 constant = 0;
  // 按原子身份合并的非零项
  std::vector<SCEVLinearTerm> terms;
  // 构建状态
  SCEVLinearizeStatus status = SCEVLinearizeStatus::InvalidExpression;
  // 已消费的表达式节点数
  u32 nodesVisited = 0;

  // 判断表达式是否完整线性化
  bool exact() const noexcept { return status == SCEVLinearizeStatus::Exact; }
};

class SCEVLinearizer {
public:
  explicit SCEVLinearizer(u32 maxNodes = 256, u32 maxDepth = 64) noexcept;

  SCEVLinearForm linearize(SCEVExpr *expression, i64 scale = 1) const;

private:
  u32 maxNodes_ = 256; // 最多消费的表达式节点数
  u32 maxDepth_ = 64;  // 根深度为零的最大递归深度
};

} // namespace svm::ir

#endif // LIR_SCEV_LINEARIZER_H
