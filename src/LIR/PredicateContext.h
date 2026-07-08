#ifndef LIR_PREDICATE_CONTEXT_H
#define LIR_PREDICATE_CONTEXT_H

/// @file PredicateContext.h
/// @brief LIR 路径谓词事实及其 CFG 采集器

#include "ScalarFacts.h"

#include <optional>
#include <unordered_map>
#include <vector>

namespace svm::ir {

class BasicBlock;
class DominatorTree;
class Inst;
class SCEV;

/// 单条同余事实: value  ==  rem (mod mod)
struct ModFact {
  Inst *value = nullptr; // 事实对应的 SSA 值
  u64 mod = 1;           // 模数, <=1 表示无信息
  i64 rem = 0;           // 规范化余数
};

/// 单条同模不等事实: value % mod != forbiddenRemainder
struct ModDisequalityFact {
  Inst *value = nullptr;      // 事实对应的 SSA 值
  u64 mod = 1;                // 模数, <=1 表示无信息
  i64 forbiddenRemainder = 0; // 被排除的规范化余数
};

/// 单条 i32 环形区间事实
struct RangeFact {
  Inst *value = nullptr;                // 事实对应的 SSA 值
  I32Range range = I32Range::unknown(); // 值域约束
};

/// 同一值和模数下的不等事实汇总结果
struct ModExclusionSummary {
  u64 mod = 1;                     // 汇总使用的模数
  bool preciseSmallMod = false;    // mod<=64 时使用精确位集
  u64 forbiddenBits = 0;           // 第 r 位表示余数 r 被排除
  std::vector<i64> largeForbidden; // 大模数的稀疏排除列表

  // 查询余数是否已被排除
  bool forbids(i64 rem) const noexcept;
  // 查询唯一允许余数
  std::optional<i64> soleAllowedResidue() const noexcept;
};

/// 短寿命的块/边敏感谓词事实集合
struct PredicateContext {
  std::vector<ModFact> congruences;              // 同余事实列表
  std::vector<ModDisequalityFact> disequalities; // 同模不等事实列表
  std::vector<RangeFact> ranges;                 // 值域事实列表
  bool unreachable = false;                      // 事实合取是否已矛盾

  // 追加同余事实
  void addCongruence(Inst *value, u64 mod, i64 rem);
  // 追加同模不等事实
  void addDisequality(Inst *value, u64 mod, i64 forbidden);
  // 追加值域事实
  void addRange(Inst *value, I32Range range);
  // 拼接另一份事实
  void appendFrom(const PredicateContext &source);

  // 查询路径矛盾
  bool isUnreachable() const noexcept { return unreachable; }
  // 查询值的合取同余
  Congruence getCongruenceFor(Inst *value) const;
  // 查询值的交集区间
  I32Range getRangeFor(Inst *value) const;
  // 汇总同模不等事实
  ModExclusionSummary getModExclusionsFor(Inst *value, u64 mod) const;
};

/// SCEV 谓词查询的上下文参数.
struct PredicateQuery {
  // 所在块
  BasicBlock *contextBlock = nullptr;
  // 显式边事实
  const PredicateContext *predicateContext = nullptr;
  // 同余语义域
  ArithmeticDomain congruenceDomain = ArithmeticDomain::I32Wrapping;
};

/// 从一条 CFG 边提取可安全表达的一元谓词事实
PredicateContext buildEdgeContext(const SCEV *scev, BasicBlock *pred,
                                  BasicBlock *succ);

/// 沿唯一前驱链回溯并拼接边事实
PredicateContext buildUniquePredPathContext(const SCEV *scev, BasicBlock *from,
                                            BasicBlock *stop, i32 maxEdges);

/// 将回边输入投影为下一轮循环头 Phi 的事实
PredicateContext buildLoopHeaderIncomingContext(
    const SCEV *scev, BasicBlock *pred, BasicBlock *header,
    const PredicateContext &pathContext, const DominatorTree &dominators);

/// 支配事实缓存与边事实采集器
class PredicateContextBuilder {
public:
  explicit PredicateContextBuilder(const DominatorTree *dominatorTree) noexcept
      : dominatorTree_(dominatorTree) {}

  const PredicateContext &buildBlockContext(BasicBlock *contextBlock);
  // 按值叠加边事实
  PredicateContext withEdgeFact(const PredicateContext &base, BasicBlock *pred,
                                BasicBlock *succ);

private:
  const DominatorTree *dominatorTree_ = nullptr;
  std::unordered_map<const BasicBlock *, PredicateContext> blockCache_;
};

} // namespace svm::ir

#endif // LIR_PREDICATE_CONTEXT_H
