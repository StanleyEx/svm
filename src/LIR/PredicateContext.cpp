/// @file PredicateContext.cpp
/// @brief 路径事实归一化, 汇总与 CFG 提取实现

#include "PredicateContext.h"
#include "DomAnalysis.h"
#include "IR.h"
#include "SCEV.h"

#include <algorithm>
#include <cassert>
#include <limits>
#include <unordered_set>

namespace svm::ir {
namespace {

constexpr u64 MaxSupportedModulus = u64{1} << 63;

bool supportsModulus(u64 modulus) noexcept {
  return modulus > 1 && modulus <= MaxSupportedModulus;
}

bool congruenceImpliesResidue(const Congruence &congruence, u64 modulus,
                              i64 residue) noexcept {
  if (!supportsModulus(modulus) || congruence.isUnknown() || !congruence.valid)
    return false;
  if (congruence.isConstant())
    return floorMod(congruence.rem, modulus) == floorMod(residue, modulus);
  return congruence.mod % modulus == 0 &&
         floorMod(congruence.rem, modulus) == floorMod(residue, modulus);
}

bool isIntValue(const Inst *value) noexcept {
  return value && (value->getType() == TY_I1 || value->getType() == TY_I32);
}

Inst *terminatorOf(BasicBlock *block) noexcept {
  return block && block->endsWithTerminator() ? block->terminator() : nullptr;
}

std::optional<i32> constantOf(const Inst *value) noexcept {
  return value && value->getOp() == OP_ICONST
             ? std::optional<i32>{value->getImm()}
             : std::nullopt;
}

void applyCompareFact(PredicateContext &context, Inst *compare,
                      bool takenIsTrue) {
  if (!compare || !isIntCompare(compare->getOp()) ||
      compare->getOperandCount() != 2)
    return;

  OpCode op =
      takenIsTrue ? compare->getOp() : invertIntCompare(compare->getOp());
  Inst *left = compare->getArg(0);
  Inst *right = compare->getArg(1);
  Inst *value = nullptr;
  std::optional<i32> constant;
  if (const auto rightConstant = constantOf(right)) {
    value = left;
    constant = rightConstant;
  } else if (const auto leftConstant = constantOf(left)) {
    value = right;
    constant = leftConstant;
    op = swapCompareOperands(op);
  }
  if (!value || !constant || !isIntValue(value))
    return;

  const i64 bound = *constant;
  constexpr i64 I32Min = std::numeric_limits<i32>::min();
  constexpr i64 I32Max = std::numeric_limits<i32>::max();
  switch (op) {
  case OP_LT:
    context.addRange(value, I32Range::fromSigned(I32Min, bound - 1));
    break;
  case OP_LE:
    context.addRange(value, I32Range::fromSigned(I32Min, bound));
    break;
  case OP_GT:
    context.addRange(value, I32Range::fromSigned(bound + 1, I32Max));
    break;
  case OP_GE:
    context.addRange(value, I32Range::fromSigned(bound, I32Max));
    break;
  case OP_EQ:
    context.addRange(value, I32Range::constant(*constant));
    break;
  case OP_NE:
    context.addRange(value, I32Range::notEqual(*constant));
    break;
  default:
    break;
  }
}

bool peelAdditiveConstant(Inst *value, Inst *&base, i64 &offset) noexcept {
  base = value;
  offset = 0;
  if (!value)
    return false;
  if ((value->getOp() != OP_ADD && value->getOp() != OP_SUB) ||
      value->getOperandCount() != 2)
    return true;

  Inst *left = value->getArg(0);
  Inst *right = value->getArg(1);
  if (left && right && right->getOp() == OP_ICONST &&
      left->getOp() != OP_ICONST) {
    base = left;
    const i64 constant = right->getImm();
    offset = value->getOp() == OP_ADD ? constant : -constant;
    return true;
  }
  if (value->getOp() == OP_ADD && left && right && left->getOp() == OP_ICONST &&
      right->getOp() != OP_ICONST) {
    base = right;
    offset = left->getImm();
  }
  return true;
}

void addRangeFromShiftedRemainderSign(PredicateContext &context, Inst *base,
                                      i64 offset, i64 remainder) {
  if (!base || remainder == 0)
    return;

  // 余数和偏移都来自 i32 常量 在 i64 中始终可表示
  const i64 shiftedBound = remainder - offset;
  if (remainder > 0) {
    if (shiftedBound > std::numeric_limits<i32>::max())
      return;
    context.addRange(
        base, I32Range::fromSigned(
                  std::max<i64>(shiftedBound, std::numeric_limits<i32>::min()),
                  std::numeric_limits<i32>::max()));
    return;
  }
  if (shiftedBound < std::numeric_limits<i32>::min())
    return;
  context.addRange(
      base, I32Range::fromSigned(
                std::numeric_limits<i32>::min(),
                std::min<i64>(shiftedBound, std::numeric_limits<i32>::max())));
}

bool provesShiftNoWrap(const SCEV *scev, Inst *base, i64 offset) {
  if (!base)
    return false;
  if (offset == 0)
    return true;
  if (!scev)
    return false;
  const auto bounds = scev->getI32Range(base, RangeQuery{}).signedBounds();
  if (!bounds)
    return false;
  const i64 minimum = static_cast<i64>(bounds->min) + offset;
  const i64 maximum = static_cast<i64>(bounds->max) + offset;
  return minimum >= std::numeric_limits<i32>::min() &&
         maximum <= std::numeric_limits<i32>::max();
}

void collectFactsFromCondition(const SCEV *scev, Inst *condition, bool holds,
                               PredicateContext &context) {
  if (!condition)
    return;

  // 保持独立边与路径提取同缓存构造器的结果一致
  while (condition->getOp() == OP_LNOT && condition->getOperandCount() == 1) {
    condition = condition->getArg(0);
    holds = !holds;
    if (!condition)
      return;
  }

  const OpCode op = condition->getOp();
  if ((op == OP_EQ || op == OP_NE) && condition->getOperandCount() == 2) {
    applyCompareFact(context, condition, holds);
    Inst *left = condition->getArg(0);
    Inst *right = condition->getArg(1);
    const bool equalityHolds = op == OP_EQ ? holds : !holds;
    for (u32 side = 0; side < 2; ++side) {
      Inst *modulo = side == 0 ? left : right;
      Inst *constant = side == 0 ? right : left;
      Inst *divisorValue = modulo && modulo->getOperandCount() == 2
                               ? modulo->getArg(1)
                               : nullptr;
      if (!modulo || !constant || modulo->getOp() != OP_MOD || !divisorValue ||
          divisorValue->getOp() != OP_ICONST || constant->getOp() != OP_ICONST)
        continue;

      const i64 divisor = divisorValue->getImm();
      const i64 remainder = constant->getImm();
      const u64 modulus = unsignedMagnitude(divisor);
      if (!supportsModulus(modulus) || unsignedMagnitude(remainder) >= modulus)
        continue;

      Inst *dividend = modulo->getArg(0);
      Inst *base = nullptr;
      i64 offset = 0;
      if (!peelAdditiveConstant(dividend, base, offset) || !base)
        continue;
      const i64 wanted = floorMod(remainder, modulus);
      const i64 baseWanted = floorMod(wanted - offset, modulus);
      const bool shifted = base != dividend;
      const bool shiftNoWrap = shifted && provesShiftNoWrap(scev, base, offset);
      const bool canProjectCongruence =
          shifted && (isI32WrappingInvariantModulus(modulus) || shiftNoWrap);
      if (equalityHolds) {
        // 条件直接约束运行时被除数 该事实与被除数的构造是否回绕无关
        // 始终可以保留
        context.addCongruence(dividend, modulus, wanted);
        addRangeFromShiftedRemainderSign(context, dividend, 0, remainder);

        // i32 回绕只保持 2^k 同余 任意模数的平移必须另有无回绕证明
        if (canProjectCongruence)
          context.addCongruence(base, modulus, baseWanted);
        // 余数符号约束回绕后的被除数
        // 只有数学平移不回绕时才能反推基值的有符号范围
        if (shiftNoWrap)
          addRangeFromShiftedRemainderSign(context, base, offset, remainder);
      } else if (remainder == 0) {
        if (modulus == 2) {
          context.addCongruence(dividend, modulus, 1);
          if (canProjectCongruence)
            context.addCongruence(base, modulus, floorMod(1 - offset, modulus));
        } else {
          context.addDisequality(dividend, modulus, wanted);
          if (canProjectCongruence)
            context.addDisequality(base, modulus, baseWanted);
        }
      } else if (scev) {
        const I32Range range = scev->getI32Range(dividend, RangeQuery{});
        const auto bounds = range.signedBounds();
        const bool signMatches =
            (remainder > 0 && bounds && bounds->min >= 0) ||
            (remainder < 0 && bounds && bounds->max <= 0);
        if (signMatches) {
          context.addDisequality(dividend, modulus, wanted);
          if (canProjectCongruence)
            context.addDisequality(base, modulus, baseWanted);
        }
      }
      return;
    }
    return;
  }

  if (op == OP_LT || op == OP_LE || op == OP_GT || op == OP_GE)
    applyCompareFact(context, condition, holds);
}

i32 uniquePhiIncomingIndex(Inst *phi, BasicBlock *pred) noexcept {
  if (!phi || phi->getOp() != OP_PHI || !pred)
    return -1;
  i32 found = -1;
  for (u32 index = 0; index < phi->getOperandCount(); ++index) {
    if (phi->getIncomingBlock(index) != pred)
      continue;
    if (found >= 0)
      return -1;
    found = static_cast<i32>(index);
  }
  return found;
}

Inst *uniquePhiIncomingForBlock(Inst *phi, BasicBlock *pred) noexcept {
  const i32 index = uniquePhiIncomingIndex(phi, pred);
  return index >= 0 ? phi->getArg(static_cast<u32>(index)) : nullptr;
}

Inst *peelSingleIncomingPhis(Inst *value) noexcept {
  const auto incoming = [](Inst *candidate) noexcept {
    return candidate && candidate->getOp() == OP_PHI &&
                   candidate->getOperandCount() == 1
               ? candidate->getArg(0)
               : nullptr;
  };
  Inst *const start = value;
  Inst *slow = value;
  Inst *fast = value;
  while (Inst *next = incoming(value)) {
    value = next;
    slow = incoming(slow);
    fast = incoming(fast);
    if (fast)
      fast = incoming(fast);
    if (slow && fast && slow == fast)
      return start;
  }
  return value;
}

void appendExceptValues(PredicateContext &destination,
                        const PredicateContext &source,
                        const std::unordered_set<Inst *> &blocked) {
  for (const ModFact &fact : source.congruences)
    if (!blocked.count(fact.value))
      destination.addCongruence(fact.value, fact.mod, fact.rem);
  for (const ModDisequalityFact &fact : source.disequalities)
    if (!blocked.count(fact.value))
      destination.addDisequality(fact.value, fact.mod, fact.forbiddenRemainder);
  for (const RangeFact &fact : source.ranges)
    if (!blocked.count(fact.value))
      destination.addRange(fact.value, fact.range);
}

} // namespace

bool ModExclusionSummary::forbids(i64 rem) const noexcept {
  if (!supportsModulus(mod))
    return false;
  const i64 normalized = floorMod(rem, mod);
  if (preciseSmallMod)
    return (forbiddenBits & (u64{1} << static_cast<u64>(normalized))) != 0;
  return std::find(largeForbidden.begin(), largeForbidden.end(), normalized) !=
         largeForbidden.end();
}

std::optional<i64> ModExclusionSummary::soleAllowedResidue() const noexcept {
  if (!preciseSmallMod || mod < 2 || mod > 64)
    return std::nullopt;
  const u64 mask =
      mod == 64 ? std::numeric_limits<u64>::max() : (u64{1} << mod) - 1;
  const u64 allowed = mask & ~forbiddenBits;
  if (allowed == 0 || (allowed & (allowed - 1)) != 0)
    return std::nullopt;
  for (u64 residue = 0; residue < mod; ++residue)
    if (((allowed >> residue) & 1U) != 0)
      return static_cast<i64>(residue);
  return std::nullopt;
}

void PredicateContext::addCongruence(Inst *value, u64 mod, i64 rem) {
  if (!value || !supportsModulus(mod))
    return;
  const Congruence incoming = Congruence::modulo(mod, rem);
  Congruence combined = incoming;
  for (const ModFact &fact : congruences) {
    if (fact.value != value)
      continue;
    const Congruence current = Congruence::modulo(fact.mod, fact.rem);
    if (conjoinCongruence(incoming, current).contradiction) {
      unreachable = true;
      return;
    }
    combined = conjoinCongruence(combined, current).value;
  }
  for (const ModDisequalityFact &fact : disequalities)
    if (fact.value == value &&
        congruenceImpliesResidue(combined, fact.mod, fact.forbiddenRemainder)) {
      unreachable = true;
      return;
    }
  congruences.push_back({value, mod, floorMod(rem, mod)});
}

void PredicateContext::addDisequality(Inst *value, u64 mod, i64 forbidden) {
  if (!value || !supportsModulus(mod))
    return;
  const i64 normalized = floorMod(forbidden, mod);
  if (congruenceImpliesResidue(getCongruenceFor(value), mod, normalized)) {
    unreachable = true;
    return;
  }
  disequalities.push_back({value, mod, normalized});
  if (mod <= 64) {
    const ModExclusionSummary summary = getModExclusionsFor(value, mod);
    const u64 allResidues =
        mod == 64 ? std::numeric_limits<u64>::max() : (u64{1} << mod) - 1;
    if (summary.forbiddenBits == allResidues)
      unreachable = true;
  }
}

void PredicateContext::addRange(Inst *value, I32Range range) {
  if (!value || range.isUnknown())
    return;
  if (range.isEmpty()) {
    unreachable = true;
    return;
  }
  for (const RangeFact &fact : ranges) {
    if (fact.value != value || fact.range.isUnknown())
      continue;
    if (fact.range.intersectWith(range).isEmpty()) {
      unreachable = true;
      return;
    }
  }
  ranges.push_back({value, range});
}

void PredicateContext::appendFrom(const PredicateContext &source) {
  congruences.reserve(congruences.size() + source.congruences.size());
  disequalities.reserve(disequalities.size() + source.disequalities.size());
  ranges.reserve(ranges.size() + source.ranges.size());
  for (const ModFact &fact : source.congruences)
    addCongruence(fact.value, fact.mod, fact.rem);
  for (const ModDisequalityFact &fact : source.disequalities)
    addDisequality(fact.value, fact.mod, fact.forbiddenRemainder);
  for (const RangeFact &fact : source.ranges)
    addRange(fact.value, fact.range);
  unreachable = unreachable || source.unreachable;
}

Congruence PredicateContext::getCongruenceFor(Inst *value) const {
  if (!value || unreachable)
    return Congruence::unknown();
  Congruence result = Congruence::unknown();
  for (const ModFact &fact : congruences) {
    if (fact.value != value)
      continue;
    const Congruence current = Congruence::modulo(fact.mod, fact.rem);
    const CongruenceConjunction conjunction =
        conjoinCongruence(result, current);
    if (conjunction.contradiction)
      return Congruence::unknown();
    result = conjunction.value;
  }
  return result;
}

I32Range PredicateContext::getRangeFor(Inst *value) const {
  if (unreachable)
    return I32Range::empty();
  if (!value)
    return I32Range::full();
  I32Range result = I32Range::full();
  for (const RangeFact &fact : ranges)
    if (fact.value == value && !fact.range.isUnknown())
      result = result.intersectWith(fact.range);
  return result;
}

ModExclusionSummary PredicateContext::getModExclusionsFor(Inst *value,
                                                          u64 mod) const {
  ModExclusionSummary result;
  if (!value || !supportsModulus(mod))
    return result;
  result.mod = mod;
  result.preciseSmallMod = mod <= 64;

  for (const ModDisequalityFact &fact : disequalities) {
    if (fact.value != value || fact.mod != mod)
      continue;
    const i64 normalized = floorMod(fact.forbiddenRemainder, mod);
    if (result.preciseSmallMod) {
      result.forbiddenBits |= u64{1} << static_cast<u64>(normalized);
    } else if (std::find(result.largeForbidden.begin(),
                         result.largeForbidden.end(),
                         normalized) == result.largeForbidden.end()) {
      result.largeForbidden.push_back(normalized);
    }
  }
  return result;
}

const PredicateContext &
PredicateContextBuilder::buildBlockContext(BasicBlock *contextBlock) {
  if (const auto found = blockCache_.find(contextBlock);
      found != blockCache_.end())
    return found->second;

  PredicateContext context;
  if (dominatorTree_ && contextBlock) {
    for (BasicBlock *block = contextBlock; block;) {
      BasicBlock *idom = dominatorTree_->getIDom(block);
      if (!idom || idom == block)
        break;
      Inst *terminator = terminatorOf(idom);
      if (terminator && terminator->getOp() == OP_BR) {
        BasicBlock *trueBlock = terminator->getBr().trueBB;
        BasicBlock *falseBlock = terminator->getBr().falseBB;
        const auto edgeDominates = [&](BasicBlock *successor) noexcept {
          if (!successor || !dominatorTree_->dominates(successor, contextBlock))
            return false;
          bool hasController = false;
          for (u32 index = 0; index < successor->getPredecessorCount();
               ++index) {
            BasicBlock *predecessor = successor->getPredecessor(index);
            if (predecessor == idom)
              hasController = true;
            else if (!dominatorTree_->dominates(successor, predecessor))
              return false;
          }
          return hasController;
        };
        const bool trueDominates = edgeDominates(trueBlock);
        const bool falseDominates = edgeDominates(falseBlock);
        if (trueDominates != falseDominates)
          collectFactsFromCondition(nullptr, terminator->getArg(0),
                                    trueDominates, context);
      }
      block = idom;
    }
  }

  const auto inserted = blockCache_.emplace(contextBlock, std::move(context));
  assert(inserted.second);
  return inserted.first->second;
}

PredicateContext
PredicateContextBuilder::withEdgeFact(const PredicateContext &base,
                                      BasicBlock *pred, BasicBlock *succ) {
  PredicateContext context = base;
  Inst *terminator = terminatorOf(pred);
  if (terminator && terminator->getOp() == OP_BR) {
    BasicBlock *trueBlock = terminator->getBr().trueBB;
    BasicBlock *falseBlock = terminator->getBr().falseBB;
    if ((succ == trueBlock) != (succ == falseBlock))
      collectFactsFromCondition(nullptr, terminator->getArg(0),
                                succ == trueBlock, context);
  }
  return context;
}

PredicateContext buildEdgeContext(const SCEV *scev, BasicBlock *pred,
                                  BasicBlock *succ) {
  PredicateContext context;
  if (!pred || !succ || !pred->endsWithTerminator())
    return context;
  Inst *terminator = pred->terminator();
  if (terminator->getOp() != OP_BR)
    return context;

  BasicBlock *trueBlock = terminator->getBr().trueBB;
  BasicBlock *falseBlock = terminator->getBr().falseBB;
  const bool trueEdge = trueBlock == succ;
  const bool falseEdge = falseBlock == succ;
  if (trueEdge == falseEdge)
    return context;
  collectFactsFromCondition(scev, terminator->getArg(0), trueEdge, context);
  return context;
}

PredicateContext buildUniquePredPathContext(const SCEV *scev, BasicBlock *from,
                                            BasicBlock *stop, i32 maxEdges) {
  PredicateContext context;
  if (!from || !stop || maxEdges <= 0)
    return context;

  BasicBlock *current = from;
  i32 usedEdges = 0;
  while (current && current != stop && usedEdges < maxEdges) {
    if (current->getPredecessorCount() != 1)
      break;
    BasicBlock *pred = current->getPredecessor(0);
    if (!pred)
      break;
    context.appendFrom(buildEdgeContext(scev, pred, current));
    ++usedEdges;
    if (pred == stop)
      break;
    current = pred;
  }
  return context;
}

PredicateContext buildLoopHeaderIncomingContext(
    const SCEV *scev, BasicBlock *pred, BasicBlock *header,
    const PredicateContext &pathContext, const DominatorTree &dominators) {
  PredicateContext result;
  if (!scev || !pred || !header)
    return result;

  // 回边上的路径事实描述本轮动态值 只能用来投影下一轮 Header Phi
  std::unordered_set<Inst *> loopLocalValues;
  const auto recordLoopLocal = [&](Inst *value) {
    BasicBlock *definition = value ? value->parentBlock() : nullptr;
    if (definition && dominators.dominates(header, definition))
      loopLocalValues.insert(value);
  };
  for (const ModFact &fact : pathContext.congruences)
    recordLoopLocal(fact.value);
  for (const ModDisequalityFact &fact : pathContext.disequalities)
    recordLoopLocal(fact.value);
  for (const RangeFact &fact : pathContext.ranges)
    recordLoopLocal(fact.value);
  appendExceptValues(result, pathContext, loopLocalValues);

  // Condition 的单入边 Phi 与本轮输入等价 仅用于分析回边值
  PredicateContext queryContext = pathContext;
  for (const ModFact &fact : pathContext.congruences) {
    Inst *value = peelSingleIncomingPhis(fact.value);
    if (value != fact.value)
      queryContext.addCongruence(value, fact.mod, fact.rem);
  }
  for (const ModDisequalityFact &fact : pathContext.disequalities) {
    Inst *value = peelSingleIncomingPhis(fact.value);
    if (value != fact.value)
      queryContext.addDisequality(value, fact.mod, fact.forbiddenRemainder);
  }
  for (const RangeFact &fact : pathContext.ranges) {
    Inst *value = peelSingleIncomingPhis(fact.value);
    if (value != fact.value)
      queryContext.addRange(value, fact.range);
  }

  CongruenceQuery query;
  query.contextBlock = pred;
  query.predicateContext = &queryContext;
  query.domain = ArithmeticDomain::I32Wrapping;
  RangeQuery rangeQuery;
  rangeQuery.contextBlock = pred;
  rangeQuery.predicateContext = &queryContext;
  for (Inst *phi = header->firstPhi(); phi; phi = phi->next()) {
    Inst *incoming = uniquePhiIncomingForBlock(phi, pred);
    if (!incoming)
      continue;
    const Congruence congruence = scev->getCongruence(incoming, query);
    if (congruence.isConstant())
      result.addCongruence(phi, u64{1} << 32, congruence.rem);
    else if (congruence.isModulo())
      result.addCongruence(phi, congruence.mod, congruence.rem);
    result.addRange(phi, scev->getI32Range(incoming, rangeQuery));
  }
  return result;
}

} // namespace svm::ir
