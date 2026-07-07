#include "Analysis.h"
#include "LIRPass.h"

#include <algorithm>
#include <cassert>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

struct ReassocRank {
  u32 loopDepth = 0; // 定义所在块的循环深度
  u32 classRank = 0; // 叶子优先级
  u64 stableId = 0;  // 确定性指令编号
};

bool rankLess(const ReassocRank &left, const ReassocRank &right) noexcept {
  if (left.loopDepth != right.loopDepth)
    return left.loopDepth < right.loopDepth;
  if (left.classRank != right.classRank)
    return left.classRank < right.classRank;
  return left.stableId < right.stableId;
}

u32 classRankOf(const Inst *inst) noexcept {
  if (inst->isUndefValue())
    return 0;
  switch (inst->getOp()) {
  case OP_PARAM:
  case OP_GETGLOBAL:
  case OP_ALLOCA:
    return 0;
  default:
    return 1;
  }
}

ReassocRank computeRank(Inst *inst, const LoopInfo *loops) noexcept {
  const BasicBlock *block = inst->parentBlock();
  return {block && loops ? static_cast<u32>(loops->getLoopDepth(block)) : 0,
          classRankOf(inst), inst->id};
}

struct IntDomain {
  using Coeff = i32;

  static Coeff add(Coeff left, Coeff right) noexcept {
    return i32AddWrap(left, right);
  }
  static Coeff neg(Coeff value) noexcept { return i32NegWrap(value); }
  static Coeff mul(Coeff left, Coeff right) noexcept {
    return i32MulWrap(left, right);
  }
  static Coeff zero() noexcept { return 0; }
  static Coeff one() noexcept { return 1; }
  static bool isZero(Coeff value) noexcept { return value == 0; }
  static bool isOne(Coeff value) noexcept { return value == 1; }
  static bool isNegOne(Coeff value) noexcept { return value == -1; }
  static IRType type() noexcept { return TY_I32; }
  static OpCode addOp() noexcept { return OP_ADD; }
  static OpCode subOp() noexcept { return OP_SUB; }
  static OpCode mulOp() noexcept { return OP_MUL; }
  static OpCode negOp() noexcept { return OP_NEG; }
  static bool isConst(const Inst *inst) noexcept {
    return inst->getOp() == OP_ICONST;
  }
  static Coeff constValue(const Inst *inst) noexcept { return inst->getImm(); }
  static bool constEquals(const Inst *inst, Coeff value) noexcept {
    return inst->getOp() == OP_ICONST && inst->getImm() == value;
  }
  static Inst *emitConst(IRBuilder &builder, Coeff value) {
    return builder.iConst(value);
  }
};

struct FloatDomain {
  using Coeff = f32;

  static Coeff add(Coeff left, Coeff right) noexcept { return left + right; }
  static Coeff neg(Coeff value) noexcept { return -value; }
  static Coeff mul(Coeff left, Coeff right) noexcept { return left * right; }
  static Coeff zero() noexcept { return 0.0F; }
  static Coeff one() noexcept { return 1.0F; }
  static bool isZero(Coeff value) noexcept { return value == 0.0F; }
  static bool isOne(Coeff value) noexcept { return value == 1.0F; }
  static bool isNegOne(Coeff value) noexcept { return value == -1.0F; }
  static IRType type() noexcept { return TY_F32; }
  static OpCode addOp() noexcept { return OP_FADD; }
  static OpCode subOp() noexcept { return OP_FSUB; }
  static OpCode mulOp() noexcept { return OP_FMUL; }
  static OpCode negOp() noexcept { return OP_FNEG; }
  static bool isConst(const Inst *inst) noexcept {
    return inst->getOp() == OP_FCONST;
  }
  static Coeff constValue(const Inst *inst) noexcept { return inst->getFimm(); }
  static bool constEquals(const Inst *inst, Coeff value) noexcept {
    return inst->getOp() == OP_FCONST && inst->getFimm() == value;
  }
  static Inst *emitConst(IRBuilder &builder, Coeff value) {
    return builder.fConst(value);
  }
};

struct ReassociateBudget {
  u32 maxChainTerms = 4096;          // 单根最多展开项数
  u32 maxNewNodesPerRoot = 256;      // 单根净增长上限
  u32 maxNewNodesPerFunction = 4096; // 单函数净增长上限
  u32 newNodesInFunction = 0;        // 已计入的新增节点
};

void eraseDeadChain(std::vector<Inst *> dead) {
  bool progress = true;
  while (progress) {
    progress = false;
    for (Inst *&inst : dead) {
      if (!inst || inst->isErased() || !inst->parentBlock() || inst->hasUses())
        continue;
      VERIFY(inst->eraseFromBlock(), "dead reassociation node must erase");
      inst = nullptr;
      progress = true;
    }
  }
}

template <typename Domain> class AddReassociator {
public:
  using Coeff = typename Domain::Coeff;

  AddReassociator(Function *function, IRBuilder &builder, const LoopInfo *loops,
                  ReassociateBudget &budget) noexcept
      : function_(function), builder_(builder), loops_(loops), budget_(budget) {
  }

  bool run(Inst *root) {
    if (root->hasNoUses())
      return false;
    reset();
    if (flatten(root))
      return false;

    for (Inst *base : baseOrder_) {
      const Coeff coefficient = coefficients_.at(base);
      if (Domain::isZero(coefficient))
        continue;
      terms_.push_back(Term{
          base, coefficient, computeRank(base, loops_), false, nullptr, {}});
    }

    std::vector<Inst *> factoredBases;
    factorCommonBases(factoredBases);
    std::stable_sort(terms_.begin(), terms_.end(),
                     [](const Term &left, const Term &right) {
                       return rankLess(left.rank, right.rank);
                     });
    if (matchesCanonical(root))
      return false;

    const u32 newNodes = estimateNewNodes();
    const u32 removable =
        static_cast<u32>(consumed_.size() + factoredBases.size() + 1);
    if (!budgetAllows(newNodes, removable))
      return false;

    builder_.setInsertBefore(root);
    const u32 before = function_->instCount;
    Inst *replacement = rebuild();
    if (!replacement || replacement == root)
      return false;
    replaceAllUsesWith(function_, root, replacement);

    std::vector<Inst *> dead = consumed_;
    dead.insert(dead.end(), factoredBases.begin(), factoredBases.end());
    dead.push_back(root);
    eraseDeadChain(std::move(dead));
    if (function_->instCount > before)
      budget_.newNodesInFunction += function_->instCount - before;
    return true;
  }

private:
  struct Term {
    Inst *base = nullptr;                       // 普通项基底
    Coeff coefficient = Domain::one();          // 普通项系数
    ReassocRank rank;                           // 用于项排序的键
    bool synthesized = false;                   // 是否为合成公因子项
    Inst *factor = nullptr;                     // 合成项公共因子
    std::vector<std::pair<Inst *, bool>> inner; // 合成项内层值及负号
  };

  void reset() {
    terms_.clear();
    coefficients_.clear();
    baseOrder_.clear();
    consumed_.clear();
    descended_.clear();
    constantSum_ = Domain::zero();
  }

  bool budgetAllows(u32 newNodes, u32 removable) const noexcept {
    return newNodes <= removable ||
           (newNodes <= budget_.maxNewNodesPerRoot &&
            newNodes <= budget_.maxNewNodesPerFunction -
                            std::min(budget_.newNodesInFunction,
                                     budget_.maxNewNodesPerFunction));
  }

  bool flatten(Inst *root) {
    const OpCode addOp = Domain::addOp();
    const OpCode subOp = Domain::subOp();
    const OpCode negOp = Domain::negOp();
    const OpCode mulOp = Domain::mulOp();
    std::vector<std::pair<Inst *, Coeff>> stack{{root, Domain::one()}};

    while (!stack.empty()) {
      const auto [node, coefficient] = stack.back();
      stack.pop_back();
      if (Domain::isZero(coefficient))
        continue;

      const bool isRoot = node == root;
      const bool mayDescend = isRoot || node->hasOneUse();
      const bool fresh = descended_.insert(node).second;
      const OpCode op = node->getOp();
      if (mayDescend && fresh && op == addOp && node->getOperandCount() == 2) {
        if (!isRoot)
          consumed_.push_back(node);
        stack.emplace_back(node->getArg(0), coefficient);
        stack.emplace_back(node->getArg(1), coefficient);
        continue;
      }
      if (mayDescend && fresh && op == subOp && node->getOperandCount() == 2) {
        if (!isRoot)
          consumed_.push_back(node);
        stack.emplace_back(node->getArg(0), coefficient);
        stack.emplace_back(node->getArg(1), Domain::neg(coefficient));
        continue;
      }
      if (mayDescend && fresh && op == negOp && node->getOperandCount() == 1) {
        if (!isRoot)
          consumed_.push_back(node);
        stack.emplace_back(node->getArg(0), Domain::neg(coefficient));
        continue;
      }
      if (Domain::isConst(node)) {
        constantSum_ = Domain::add(
            constantSum_, Domain::mul(coefficient, Domain::constValue(node)));
        continue;
      }
      if (mayDescend && fresh && op == mulOp && node->getOperandCount() == 2) {
        Inst *value = nullptr;
        Coeff scale = Domain::one();
        if (Domain::isConst(node->getArg(1))) {
          value = node->getArg(0);
          scale = Domain::constValue(node->getArg(1));
        } else if (Domain::isConst(node->getArg(0))) {
          value = node->getArg(1);
          scale = Domain::constValue(node->getArg(0));
        }
        if (value) {
          consumed_.push_back(node);
          stack.emplace_back(value, Domain::mul(coefficient, scale));
          continue;
        }
      }

      const auto found = coefficients_.find(node);
      if (found == coefficients_.end()) {
        coefficients_.emplace(node, coefficient);
        baseOrder_.push_back(node);
        if (coefficients_.size() > budget_.maxChainTerms)
          return true;
      } else {
        found->second = Domain::add(found->second, coefficient);
      }
    }
    return false;
  }

  // 识别可提取乘法项
  bool isFactorable(const Term &term, Inst *&left,
                    Inst *&right) const noexcept {
    if (term.synthesized || !term.base ||
        (!Domain::isOne(term.coefficient) &&
         !Domain::isNegOne(term.coefficient)) ||
        term.base->getOp() != Domain::mulOp() ||
        term.base->getOperandCount() != 2 || !term.base->hasOneUse())
      return false;
    left = term.base->getArg(0);
    right = term.base->getArg(1);
    return !Domain::isConst(left) && !Domain::isConst(right);
  }

  // 提取至少两个项共享的非常量因子
  void factorCommonBases(std::vector<Inst *> &factoredBases) {
    for (;;) {
      std::unordered_map<Inst *, std::vector<u32>> byFactor;
      for (u32 index = 0; index < terms_.size(); ++index) {
        Inst *left = nullptr;
        Inst *right = nullptr;
        if (!isFactorable(terms_[index], left, right))
          continue;
        byFactor[left].push_back(index);
        if (right != left)
          byFactor[right].push_back(index);
      }

      Inst *best = nullptr;
      usize bestCount = 0;
      ReassocRank bestRank;
      for (const auto &[factor, group] : byFactor) {
        if (group.size() < 2)
          continue;
        const ReassocRank rank = computeRank(factor, loops_);
        if (!best || group.size() > bestCount ||
            (group.size() == bestCount && rankLess(rank, bestRank))) {
          best = factor;
          bestCount = group.size();
          bestRank = rank;
        }
      }
      if (!best)
        return;

      Term synthesized;
      synthesized.synthesized = true;
      synthesized.factor = best;
      synthesized.rank = bestRank;
      std::vector<bool> dropped(terms_.size(), false);
      for (u32 index : byFactor.at(best)) {
        if (dropped[index])
          continue;
        dropped[index] = true;
        Term &term = terms_[index];
        Inst *left = term.base->getArg(0);
        Inst *right = term.base->getArg(1);
        Inst *other = left == best ? right : left;
        synthesized.inner.emplace_back(other,
                                       Domain::isNegOne(term.coefficient));
        factoredBases.push_back(term.base);
      }

      std::vector<Term> remaining;
      remaining.reserve(terms_.size() - bestCount + 1);
      for (u32 index = 0; index < terms_.size(); ++index)
        if (!dropped[index])
          remaining.push_back(std::move(terms_[index]));
      remaining.push_back(std::move(synthesized));
      terms_ = std::move(remaining);
    }
  }

  // 比较单项形态
  bool matchesTermValue(Inst *inst, const Term &term) const noexcept {
    if (Domain::isOne(term.coefficient) || Domain::isNegOne(term.coefficient))
      return inst == term.base;
    if (inst->getOp() != Domain::mulOp() || inst->getOperandCount() != 2)
      return false;
    return (inst->getArg(0) == term.base &&
            Domain::constEquals(inst->getArg(1), term.coefficient)) ||
           (inst->getArg(1) == term.base &&
            Domain::constEquals(inst->getArg(0), term.coefficient));
  }

  // 检查确定性左深规范形
  bool matchesCanonical(Inst *root) const {
    for (const Term &term : terms_)
      if (term.synthesized)
        return false;

    const bool hasConstant = !Domain::isZero(constantSum_);
    const u32 itemCount =
        static_cast<u32>(terms_.size()) + (hasConstant ? 1U : 0U);
    if (itemCount == 0)
      return false;

    Inst *node = root;
    for (u32 item = itemCount - 1; item >= 1; --item) {
      const bool constantItem = hasConstant && item == terms_.size();
      if (constantItem) {
        if (node->getOp() != Domain::addOp() || node->getOperandCount() != 2 ||
            !Domain::constEquals(node->getArg(1), constantSum_))
          return false;
      } else {
        const Term &term = terms_[item];
        const OpCode expected = Domain::isNegOne(term.coefficient)
                                    ? Domain::subOp()
                                    : Domain::addOp();
        if (node->getOp() != expected || node->getOperandCount() != 2 ||
            !matchesTermValue(node->getArg(1), term))
          return false;
      }
      node = node->getArg(0);
    }

    if (terms_.empty())
      return Domain::constEquals(node, constantSum_);
    const Term &first = terms_.front();
    if (Domain::isNegOne(first.coefficient))
      return node->getOp() == Domain::negOp() && node->getOperandCount() == 1 &&
             node->getArg(0) == first.base;
    return matchesTermValue(node, first);
  }

  // 估算完整重建节点数
  u32 estimateNewNodes() const noexcept {
    const bool hasConstant = !Domain::isZero(constantSum_);
    const u32 itemCount =
        static_cast<u32>(terms_.size()) + (hasConstant ? 1U : 0U);
    u32 count = itemCount == 0 ? 0 : itemCount - 1;
    for (const Term &term : terms_) {
      if (term.synthesized)
        count += static_cast<u32>(term.inner.size());
      else if (!Domain::isOne(term.coefficient) &&
               !Domain::isNegOne(term.coefficient))
        ++count;
    }
    if (!terms_.empty() && Domain::isNegOne(terms_.front().coefficient))
      ++count;
    return count;
  }

  // 物化公因子合成项
  Inst *materializeFactor(const Term &term) {
    std::vector<std::pair<Inst *, bool>> inner = term.inner;
    std::stable_sort(inner.begin(), inner.end(),
                     [&](const auto &left, const auto &right) {
                       return rankLess(computeRank(left.first, loops_),
                                       computeRank(right.first, loops_));
                     });
    Inst *sum = nullptr;
    for (const auto &[value, negative] : inner) {
      if (!sum)
        sum = negative ? builder_.emit(Domain::negOp(), Domain::type(), value)
                       : value;
      else
        sum = builder_.emit(negative ? Domain::subOp() : Domain::addOp(),
                            Domain::type(), sum, value);
    }
    assert(sum);
    return builder_.emit(Domain::mulOp(), Domain::type(), term.factor, sum);
  }

  // 按Rank重建规范左深树
  Inst *rebuild() {
    Inst *accumulator = nullptr;
    for (const Term &term : terms_) {
      Inst *value = nullptr;
      bool subtract = false;
      if (term.synthesized) {
        value = materializeFactor(term);
      } else if (Domain::isOne(term.coefficient)) {
        value = term.base;
      } else if (Domain::isNegOne(term.coefficient)) {
        value = term.base;
        subtract = true;
      } else {
        value = builder_.emit(Domain::mulOp(), Domain::type(), term.base,
                              Domain::emitConst(builder_, term.coefficient));
      }

      if (!accumulator)
        accumulator =
            subtract ? builder_.emit(Domain::negOp(), Domain::type(), value)
                     : value;
      else
        accumulator =
            builder_.emit(subtract ? Domain::subOp() : Domain::addOp(),
                          Domain::type(), accumulator, value);
    }
    if (!Domain::isZero(constantSum_) || !accumulator) {
      Inst *constant = Domain::emitConst(builder_, constantSum_);
      accumulator = accumulator ? builder_.emit(Domain::addOp(), Domain::type(),
                                                accumulator, constant)
                                : constant;
    }
    return accumulator;
  }

  Function *function_ = nullptr;
  IRBuilder &builder_;
  const LoopInfo *loops_ = nullptr;
  ReassociateBudget &budget_;                      // 共享预算
  std::vector<Term> terms_;                        // 规约后的项
  std::unordered_map<Inst *, Coeff> coefficients_; // 基底到系数
  std::vector<Inst *> baseOrder_;                  // 基底首次出现顺序
  std::vector<Inst *> consumed_;                   // 展平后可删除节点
  std::unordered_set<Inst *> descended_;           // 已下钻节点
  Coeff constantSum_ = Domain::zero();             // 聚合常量
};

template <typename Domain> class MulReassociator {
public:
  using Coeff = typename Domain::Coeff;

  MulReassociator(Function *function, IRBuilder &builder, const LoopInfo *loops,
                  ReassociateBudget &budget) noexcept
      : function_(function), builder_(builder), loops_(loops), budget_(budget) {
  }

  bool run(Inst *root) {
    if (root->hasNoUses())
      return false;
    factors_.clear();
    consumed_.clear();
    descended_.clear();
    constantProduct_ = Domain::one();
    if (flatten(root))
      return false;
    if (Domain::isZero(constantProduct_))
      return commit(root, Domain::emitConst(builder_, Domain::zero()));

    std::stable_sort(factors_.begin(), factors_.end(),
                     [](const Factor &left, const Factor &right) {
                       return rankLess(left.rank, right.rank);
                     });
    if (matchesCanonical(root))
      return false;

    const u32 itemCount = static_cast<u32>(factors_.size()) +
                          (Domain::isOne(constantProduct_) ? 0U : 1U);
    const u32 newNodes = itemCount == 0 ? 0 : itemCount - 1;
    const u32 removable = static_cast<u32>(consumed_.size() + 1);
    if (!budgetAllows(newNodes, removable))
      return false;

    builder_.setInsertBefore(root);
    const u32 before = function_->instCount;
    const bool changed = commit(root, rebuild());
    if (changed && function_->instCount > before)
      budget_.newNodesInFunction += function_->instCount - before;
    return changed;
  }

private:
  struct Factor {
    Inst *value = nullptr; // 因子值
    ReassocRank rank;      // 因子排序键
  };

  bool budgetAllows(u32 newNodes, u32 removable) const noexcept {
    return newNodes <= removable ||
           (newNodes <= budget_.maxNewNodesPerRoot &&
            newNodes <= budget_.maxNewNodesPerFunction -
                            std::min(budget_.newNodesInFunction,
                                     budget_.maxNewNodesPerFunction));
  }

  bool flatten(Inst *root) {
    std::vector<Inst *> stack{root};
    while (!stack.empty()) {
      Inst *node = stack.back();
      stack.pop_back();
      const bool isRoot = node == root;
      const bool mayDescend = isRoot || node->hasOneUse();
      const bool fresh = descended_.insert(node).second;
      if (mayDescend && fresh && node->getOp() == Domain::mulOp() &&
          node->getOperandCount() == 2) {
        if (!isRoot)
          consumed_.push_back(node);
        stack.push_back(node->getArg(0));
        stack.push_back(node->getArg(1));
        continue;
      }
      if (Domain::isConst(node)) {
        constantProduct_ =
            Domain::mul(constantProduct_, Domain::constValue(node));
        continue;
      }
      factors_.push_back(Factor{node, computeRank(node, loops_)});
      if (factors_.size() > budget_.maxChainTerms)
        return true;
    }
    return false;
  }

  // 检查确定性左深规范形
  bool matchesCanonical(Inst *root) const {
    const bool hasConstant = !Domain::isOne(constantProduct_);
    const u32 itemCount =
        static_cast<u32>(factors_.size()) + (hasConstant ? 1U : 0U);
    if (itemCount == 0)
      return false;
    Inst *node = root;
    for (u32 item = itemCount - 1; item >= 1; --item) {
      if (node->getOp() != Domain::mulOp() || node->getOperandCount() != 2)
        return false;
      const bool constantItem = hasConstant && item == factors_.size();
      if (constantItem) {
        if (!Domain::constEquals(node->getArg(1), constantProduct_))
          return false;
      } else if (node->getArg(1) != factors_[item].value) {
        return false;
      }
      node = node->getArg(0);
    }
    return factors_.empty() ? Domain::constEquals(node, constantProduct_)
                            : node == factors_.front().value;
  }

  // 重建规范乘法链
  Inst *rebuild() {
    Inst *accumulator = nullptr;
    for (const Factor &factor : factors_)
      accumulator = accumulator ? builder_.emit(Domain::mulOp(), Domain::type(),
                                                accumulator, factor.value)
                                : factor.value;
    if (!Domain::isOne(constantProduct_) || !accumulator) {
      Inst *constant = Domain::emitConst(builder_, constantProduct_);
      accumulator = accumulator ? builder_.emit(Domain::mulOp(), Domain::type(),
                                                accumulator, constant)
                                : constant;
    }
    return accumulator;
  }

  // 提交替换并清理旧链
  bool commit(Inst *root, Inst *replacement) {
    if (!replacement || replacement == root)
      return false;
    replaceAllUsesWith(function_, root, replacement);
    std::vector<Inst *> dead = consumed_;
    dead.push_back(root);
    eraseDeadChain(std::move(dead));
    return true;
  }

  Function *function_ = nullptr;
  IRBuilder &builder_;
  const LoopInfo *loops_ = nullptr;
  ReassociateBudget &budget_;
  std::vector<Factor> factors_;
  std::vector<Inst *> consumed_;
  std::unordered_set<Inst *> descended_;
  Coeff constantProduct_ = Domain::one();
};

bool isAddFamily(OpCode op, bool fastMath) noexcept {
  return op == OP_ADD || op == OP_SUB ||
         (fastMath && (op == OP_FADD || op == OP_FSUB));
}

bool isMulFamily(OpCode op, bool fastMath) noexcept {
  return op == OP_MUL || (fastMath && op == OP_FMUL);
}

bool isInnerSameFamily(Inst *inst, bool fastMath) noexcept {
  if (!inst->hasOneUse())
    return false;
  Inst *user = inst->uses()->user;
  return (isAddFamily(inst->getOp(), fastMath) &&
          isAddFamily(user->getOp(), fastMath)) ||
         (isMulFamily(inst->getOp(), fastMath) &&
          isMulFamily(user->getOp(), fastMath));
}

bool reassociate(Function *function, PassContext &context, bool fastMath) {
  assert(function && function->phase == IRPhase::LIR);
  computeUses(function);
  const LoopInfo &loops = context.get<LoopInfoAnalysis>(function).info;
  IRBuilder builder(function->module, function);
  ReassociateBudget budget;
  AddReassociator<IntDomain> integerAdd(function, builder, &loops, budget);
  MulReassociator<IntDomain> integerMul(function, builder, &loops, budget);
  AddReassociator<FloatDomain> floatAdd(function, builder, &loops, budget);
  MulReassociator<FloatDomain> floatMul(function, builder, &loops, budget);
  bool changed = false;

  for (BasicBlock *block : computeRPO(function)) {
    for (Inst *inst = block->firstInst(); inst;) {
      Inst *next = inst->next();
      const OpCode op = inst->getOp();
      if (!isInnerSameFamily(inst, fastMath)) {
        if (op == OP_ADD || op == OP_SUB)
          changed |= integerAdd.run(inst);
        else if (op == OP_MUL)
          changed |= integerMul.run(inst);
        else if (fastMath && (op == OP_FADD || op == OP_FSUB))
          changed |= floatAdd.run(inst);
        else if (fastMath && op == OP_FMUL)
          changed |= floatMul.run(inst);
      }
      inst = next;
    }
  }
  return changed;
}

} // namespace

ReassociatePass::ReassociatePass(bool fastMath) noexcept
    : fastMath_(fastMath) {}

std::string_view ReassociatePass::name() const noexcept {
  return "reassociate";
}

PassResult ReassociatePass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();
  if (!reassociate(function, context, fastMath_))
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
