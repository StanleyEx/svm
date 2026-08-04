#ifndef LIR_DEPENDENCE_SOLVER_H
#define LIR_DEPENDENCE_SOLVER_H

#include "Utils.h"

#include <optional>
#include <vector>

namespace svm::ir {

enum class DependenceStatus : u8 {
  NoDependence,  // 已证明访问不可能重叠
  MayDependence, // 模型有效但仍存在可能方向
  Unknown,       // 输入或有界整数推理合同失败
};

// source迭代号和sink的相对大小关系
enum class DependenceDirection : u8 {
  Less,
  Equal,
  Greater,
};

enum class DependenceProof : u8 {
  None,     // 未形成排除证明
  ZIV,      // 常量地址排除
  SIV,      // 单变量距离或整除排除
  GCD,      // GCD整除性排除
  Banerjee, // 有界方向Banerjee排除
};

enum class DependenceSolverFailure : u8 {
  None,                    // 求解器合同未失败
  InvalidProblem,          // 维度或迭代域输入非法
  ArithmeticOverflow,      // checked-i64中间结果不可承载
  DirectionBudgetExceeded, // 方向向量枚举超过预算
};

using DirectionVector = std::vector<DependenceDirection>;

struct AffineEquationSide {
  i64 constant = 0;              // 地址常量项
  std::vector<i64> coefficients; // 按外到内顺序的迭代号系数
};

struct DependenceProblem {
  AffineEquationSide source;                  // source地址函数
  AffineEquationSide sink;                    // sink地址函数
  std::vector<i64> localCoefficients;         // 非公共存在量的有符号系数
  std::vector<std::optional<i64>> tripCounts; // 各维正迭代次数
  bool allowEqualIterations = true;           // 是否允许同一迭代向量
  u32 maxDirectionDepth = 3;                  // 方向枚举深度预算
};

struct DependenceSolution {
  // 求解结果
  DependenceStatus status = DependenceStatus::Unknown;
  // 最强排除证明
  DependenceProof proof = DependenceProof::None;
  // Unknown原因
  DependenceSolverFailure failure = DependenceSolverFailure::None;
  // 可能方向向量上集
  std::vector<DirectionVector> directions;
  // sink-source距离
  std::vector<std::optional<i64>> distances;
  // 非零sink-source距离必须是该值的倍数
  std::vector<std::optional<u64>> distanceMultiples;
};

// 求解两个仿射地址在原字典序调度中的可能重叠
DependenceSolution solveDependence(const DependenceProblem &problem);

// 判断方向向量是否保持原字典序调度
bool isForwardDirection(const DirectionVector &direction,
                        bool allowAllEqual = true) noexcept;

} // namespace svm::ir

#endif // LIR_DEPENDENCE_SOLVER_H
