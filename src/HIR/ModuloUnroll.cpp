#include "DeepCopy.h"
#include "HIRPass.h"

#include <algorithm>
#include <iterator>
#include <limits>
#include <numeric>
#include <optional>
#include <vector>

namespace svm::ir {
namespace {

constexpr i32 kMaxUnroll = 8;       // 最大展开倍数
constexpr usize kMaxExpanded = 250; // 主体加尾循环的总代码预算

usize countInstructions(Region *region) noexcept {
  usize count = 0;
  forEachInstRecursive(region, [&](Inst *) { ++count; });
  return count;
}

struct IntRange {
  i64 minimum = 0; // 表达式可能的最小值
  i64 maximum = 0; // 表达式可能的最大值
};

enum class ExpressionSign : u8 {
  NonNegative, // 表达式在整个循环范围内恒非负
  NonPositive, // 表达式在整个循环范围内恒非正
};

bool fitsI32(const IntRange &range) noexcept {
  return range.minimum >= std::numeric_limits<i32>::min() &&
         range.maximum <= std::numeric_limits<i32>::max();
}

template <typename IsIV>
bool analyzePolynomial(Inst *value, const IsIV &isIV, const IntRange &ivRange,
                       bool &usesIV, IntRange &result, u32 depth = 0) {
  if (!value || value->getType() != TY_I32 || depth > 32)
    return false;
  if (isIV(value)) {
    usesIV = true;
    result = ivRange;
    return true;
  }
  if (value->getOp() == OP_ICONST) {
    result = {value->getImm(), value->getImm()};
    return true;
  }
  if (value->getOp() == OP_NEG) {
    if (value->getOperandCount() != 1)
      return false;
    IntRange operand;
    if (!analyzePolynomial(value->getArg(0), isIV, ivRange, usesIV, operand,
                           depth + 1))
      return false;
    result = {-operand.maximum, -operand.minimum};
    return fitsI32(result);
  }
  if ((value->getOp() != OP_ADD && value->getOp() != OP_SUB &&
       value->getOp() != OP_MUL) ||
      value->getOperandCount() != 2)
    return false;

  IntRange left;
  IntRange right;
  if (!analyzePolynomial(value->getArg(0), isIV, ivRange, usesIV, left,
                         depth + 1) ||
      !analyzePolynomial(value->getArg(1), isIV, ivRange, usesIV, right,
                         depth + 1))
    return false;
  if (value->getOp() == OP_ADD) {
    result = {left.minimum + right.minimum, left.maximum + right.maximum};
  } else if (value->getOp() == OP_SUB) {
    result = {left.minimum - right.maximum, left.maximum - right.minimum};
  } else {
    const i64 products[] = {
        left.minimum * right.minimum, left.minimum * right.maximum,
        left.maximum * right.minimum, left.maximum * right.maximum};
    result = {*std::min_element(std::begin(products), std::end(products)),
              *std::max_element(std::begin(products), std::end(products))};
  }
  return fitsI32(result);
}

bool classifySign(const IntRange &range, ExpressionSign &sign) noexcept {
  if (range.minimum >= 0) {
    sign = ExpressionSign::NonNegative;
    return true;
  }
  if (range.maximum <= 0) {
    sign = ExpressionSign::NonPositive;
    return true;
  }
  return false;
}

IntRange phaseRange(const IntRange &ivRange, i64 phase) noexcept {
  return {phase, std::max(phase, ivRange.maximum)};
}

i32 normalizeModulo(i64 value, i32 modulus) noexcept {
  i64 remainder = value % modulus;
  if (remainder < 0)
    remainder += modulus;
  return static_cast<i32>(remainder);
}

template <typename IsIV>
bool evaluateModulo(Inst *value, const IsIV &isIV, i64 ivResidue, i32 modulus,
                    i32 &result, u32 depth = 0) {
  if (!value || value->getType() != TY_I32 || depth > 32)
    return false;
  if (isIV(value)) {
    result = normalizeModulo(ivResidue, modulus);
    return true;
  }
  if (value->getOp() == OP_ICONST) {
    result = normalizeModulo(value->getImm(), modulus);
    return true;
  }
  if (value->getOp() == OP_NEG) {
    if (value->getOperandCount() != 1 ||
        !evaluateModulo(value->getArg(0), isIV, ivResidue, modulus, result,
                        depth + 1))
      return false;
    result = normalizeModulo(-static_cast<i64>(result), modulus);
    return true;
  }
  if ((value->getOp() != OP_ADD && value->getOp() != OP_SUB &&
       value->getOp() != OP_MUL) ||
      value->getOperandCount() != 2)
    return false;

  i32 left = 0;
  i32 right = 0;
  if (!evaluateModulo(value->getArg(0), isIV, ivResidue, modulus, left,
                      depth + 1) ||
      !evaluateModulo(value->getArg(1), isIV, ivResidue, modulus, right,
                      depth + 1))
    return false;
  const i64 combined = value->getOp() == OP_ADD ? static_cast<i64>(left) + right
                       : value->getOp() == OP_SUB
                           ? static_cast<i64>(left) - right
                           : static_cast<i64>(left) * right;
  result = normalizeModulo(combined, modulus);
  return true;
}

template <typename IsIV>
std::optional<i32> foldedModuloForPhase(Inst *value, const IsIV &isIV,
                                        const IntRange &ivRange, i64 phase,
                                        i32 modulus) {
  bool usesIV = false;
  IntRange expressionRange;
  if (!analyzePolynomial(value, isIV, phaseRange(ivRange, phase), usesIV,
                         expressionRange) ||
      !usesIV)
    return std::nullopt;
  i32 residue = 0;
  if (!evaluateModulo(value, isIV, phase, modulus, residue))
    return std::nullopt;
  if (residue == 0)
    return 0;
  ExpressionSign sign = ExpressionSign::NonNegative;
  if (!classifySign(expressionRange, sign))
    return std::nullopt;
  return sign == ExpressionSign::NonPositive ? residue - modulus : residue;
}

bool singleBlockRegion(Region *region) noexcept {
  return region && region->first && region->first == region->last &&
         region->first->endsWithTerminator();
}

bool yieldRegion(Region *region) noexcept {
  return singleBlockRegion(region) &&
         region->first->lastInst()->getOp() == OP_YIELD;
}

bool clonableRegion(Region *region) noexcept {
  if (!singleBlockRegion(region))
    return false;
  bool valid = true;
  forEachInst(region->first, [&](Inst *inst) {
    if (!valid)
      return;
    const OpCode op = inst->getOp();
    const bool supported =
        isArithmetic(op) || isCompare(op) || isConversion(op) ||
        isMemoryOp(op) || isStructuredControl(op) || isLocalInitAnchor(op) ||
        op == OP_LNOT || op == OP_CALL || op == OP_YIELD || op == OP_BREAK ||
        op == OP_CONTINUE || op == OP_SELECT;
    if (!supported) {
      valid = false;
      return;
    }

    if (op == OP_IF)
      valid = clonableRegion(inst->getScf().r[0]) &&
              (!inst->getScf().r[1] || clonableRegion(inst->getScf().r[1]));
    else if (op == OP_WHILE)
      valid = yieldRegion(inst->getScf().r[0]) &&
              clonableRegion(inst->getScf().r[0]) &&
              clonableRegion(inst->getScf().r[1]);
    else if (op == OP_FOR)
      valid = clonableRegion(inst->getBody());
  });
  return valid;
}

bool hasAliasingIVAccess(Inst *inst, Inst *ivAddress) noexcept {
  if (inst->getOp() == OP_LOAD) {
    Inst *address = inst->getOperandCount() == 1 ? inst->getArg(0) : nullptr;
    return address != ivAddress && mayAlias(getMemoryBase(address), ivAddress);
  }
  if (inst->getOp() == OP_STORE || isLocalInitAnchor(inst->getOp())) {
    Inst *address = inst->getOperandCount() ? inst->getArg(0) : nullptr;
    return address != ivAddress && mayAlias(getMemoryBase(address), ivAddress);
  }
  if (inst->getOp() == OP_FOR) {
    Inst *address = inst->getOperandCount() == 3 ? inst->getArg(2) : nullptr;
    return address != ivAddress && mayAlias(getMemoryBase(address), ivAddress);
  }
  return false;
}

Inst *constantStart(Inst *loop, Inst *ivAddress) noexcept {
  for (Inst *inst = loop->previous(); inst; inst = inst->previous()) {
    if (inst->getOp() == OP_CALL || isStructuredControl(inst->getOp()))
      return nullptr;
    if (inst->getOp() != OP_STORE)
      continue;
    Inst *destination = inst->getArg(0);
    if (destination == ivAddress)
      return inst->getArg(1)->getOp() == OP_ICONST ? inst->getArg(1) : nullptr;
    if (mayAlias(getMemoryBase(destination), ivAddress))
      return nullptr;
  }
  return nullptr;
}

std::optional<i32> constantI32Value(Inst *value) noexcept {
  if (!value || value->getType() != TY_I32)
    return std::nullopt;
  if (value->getOp() == OP_ICONST)
    return value->getImm();
  if (value->getOp() != OP_LOAD || value->getOperandCount() != 1)
    return std::nullopt;
  Inst *address = value->getArg(0);
  if (!address || address->getOp() != OP_GETGLOBAL)
    return std::nullopt;
  Global *global = address->getGlobal();
  if (!global || !global->isConst || global->isArray || global->type != TY_I32)
    return std::nullopt;
  if (!global->initSegmentCount || !global->initSegment[0].data)
    return 0;
  return *static_cast<const i32 *>(global->initSegment[0].data);
}

struct Plan {
  Inst *loop = nullptr;      // 待展开循环
  Inst *ivAddress = nullptr; // 归纳变量地址
  i32 start = 0;             // 常量起点
  i32 factor = 0;            // 展开倍数
  IntRange ivRange;          // 原循环全部可能执行的IV范围
};

bool analyze(Inst *loop, Plan &plan) {
  if (!loop || loop->getOp() != OP_FOR || loop->getOperandCount() != 3 ||
      !yieldRegion(loop->getBody()) || !clonableRegion(loop->getBody()))
    return false;
  Inst *step = loop->getArg(1);
  Inst *ivAddress = loop->getArg(2);
  if (step->getOp() != OP_ICONST || step->getImm() != 1 ||
      (ivAddress->getOp() != OP_ALLOCA && ivAddress->getOp() != OP_GETGLOBAL))
    return false;
  Inst *start = constantStart(loop, ivAddress);
  Inst *stop = loop->getArg(0);
  if (!start || start->getImm() < 0 || stop->getType() != TY_I32)
    return false;
  const std::optional<i32> stopValue = constantI32Value(stop);
  if (stopValue && *stopValue <= start->getImm())
    return false;
  if (start->getImm() == std::numeric_limits<i32>::max())
    return false;
  const IntRange ivRange = {
      start->getImm(),
      stopValue ? static_cast<i64>(*stopValue) - 1
                : static_cast<i64>(std::numeric_limits<i32>::max()) - 1};

  bool unsafe = false;
  bool containsCall = false;
  i32 factor = 0;
  forEachInstRecursive(loop->getBody(), [&](Inst *inst) {
    if ((inst->getOp() == OP_BREAK || inst->getOp() == OP_CONTINUE) &&
        getEnclosingLoop(inst) == loop)
      unsafe = true;
    containsCall |= inst->getOp() == OP_CALL;
    for (u32 index = 0; index < inst->getOperandCount(); ++index)
      if (inst->getArg(index) == ivAddress &&
          !(inst->getOp() == OP_LOAD && index == 0))
        unsafe = true;
    unsafe |= hasAliasingIVAccess(inst, ivAddress);

    if (inst->getOp() != OP_MOD || inst->getOperandCount() != 2 ||
        inst->getArg(1)->getOp() != OP_ICONST)
      return;
    Inst *dividend = inst->getArg(0);
    const i32 modulus = inst->getArg(1)->getImm();
    bool usesIV = false;
    IntRange expressionRange;
    auto isIV = [&](Inst *value) {
      return value->getOp() == OP_LOAD && value->getOperandCount() == 1 &&
             value->getArg(0) == ivAddress;
    };
    if (modulus < 2 || modulus > kMaxUnroll ||
        !analyzePolynomial(dividend, isIV, ivRange, usesIV, expressionRange) ||
        !usesIV)
      return;
    bool foldable = false;
    for (i32 phase = 0; phase < modulus && !foldable; ++phase) {
      const i64 phaseValue = static_cast<i64>(start->getImm()) + phase;
      if (phaseValue <= ivRange.maximum)
        foldable =
            foldedModuloForPhase(dividend, isIV, ivRange, phaseValue, modulus)
                .has_value();
    }
    if (!foldable)
      return;
    factor =
        factor == 0 ? modulus : factor / std::gcd(factor, modulus) * modulus;
  });
  if (containsCall) {
    if (ivAddress->getOp() != OP_ALLOCA) {
      unsafe = true;
    } else {
      for (const Use *use = ivAddress->uses(); use; use = use->next) {
        const Inst *user = use->user;
        const bool privateUse =
            user && ((user->getOp() == OP_LOAD && use->argNo == 0) ||
                     (user->getOp() == OP_STORE && use->argNo == 0) ||
                     (user->getOp() == OP_FOR && use->argNo == 2));
        if (!privateUse) {
          unsafe = true;
          break;
        }
      }
    }
  }
  if (unsafe || factor < 2 || factor > kMaxUnroll ||
      (stopValue && static_cast<i64>(*stopValue) - start->getImm() < factor))
    return false;
  const usize bodyCount = countInstructions(loop->getBody());
  if (bodyCount > (kMaxExpanded - static_cast<usize>(factor) - 6) /
                      static_cast<usize>(factor + 1))
    return false;
  plan = Plan{loop, ivAddress, start->getImm(), factor, ivRange};
  return true;
}

Region *buildExpandedBody(Function *function, Region *oldBody, const Plan &plan,
                          Region *parent, IRBuilder &builder) {
  Region *newBody = builder.newRegion(nullptr, parent);
  BasicBlock *merged = builder.newBlockAtEnd(newBody);
  builder.setInsertAtEnd(merged);
  Inst *base = builder.emitLoad(plan.ivAddress, TY_I32);
  for (i32 copyIndex = 0; copyIndex < plan.factor; ++copyIndex) {
    Inst *ivValue = copyIndex == 0 ? base
                                   : builder.emit(OP_ADD, TY_I32, base,
                                                  builder.iConst(copyIndex));
    DeepCopy bodyCopy(function);
    RegionCloneConfig cloneConfig;
    const i64 phase = static_cast<i64>(plan.start) + copyIndex;
    // 在创建克隆外壳前直接映射IV读取和可折叠Modulo 避免先克隆再扫描删除
    cloneConfig.remapValueBeforeClone = [&](Inst *source) -> Inst * {
      auto isIVLoad = [&](Inst *value) {
        return value->getOp() == OP_LOAD && value->getOperandCount() == 1 &&
               value->getArg(0) == plan.ivAddress;
      };
      if (isIVLoad(source))
        return ivValue;
      if (source->getOp() != OP_MOD || source->getOperandCount() != 2 ||
          source->getArg(1)->getOp() != OP_ICONST)
        return nullptr;
      const i32 modulus = source->getArg(1)->getImm();
      if (modulus < 2 || plan.factor % modulus != 0)
        return nullptr;
      const std::optional<i32> folded = foldedModuloForPhase(
          source->getArg(0), isIVLoad, plan.ivRange, phase, modulus);
      return folded ? builder.iConst(*folded) : nullptr;
    };
    Region *copy = bodyCopy.copyRegion(oldBody, cloneConfig).region;
    assert(copy);
    copy->parent = newBody;
    bodyCopy.flattenRegionIntoBlock(copy, merged, false);
    builder.setInsertAtEnd(merged);
    copy->owner = nullptr;
    copy->parent = nullptr;
  }
  builder.setInsertAtEnd(merged);
  builder.emitYield();
  return newBody;
}

void transform(Function *function, const Plan &plan) {
  Inst *loop = plan.loop;
  Region *oldBody = loop->getBody();
  Region *parent = loop->parentBlock()->parentRegion;
  Inst *stop = loop->getArg(0);
  IRBuilder builder(function->module, function);

  // 动态上界可能小于起点 只在原循环至少执行一次时计算安全的trip
  builder.setInsertBefore(loop);
  builder.setCurrentSourceLocation(loop->sourceLocation);
  Inst *start = builder.iConst(plan.start);
  Inst *hasIterations = builder.emit(OP_LT, TY_I1, start, stop);
  Region *thenRegion = builder.newRegion(nullptr, parent);
  BasicBlock *thenBlock = builder.newBlockAtEnd(thenRegion);
  builder.setInsertAtEnd(thenBlock);

  Inst *trip = builder.emit(OP_SUB, TY_I32, stop, start);
  Inst *remainder =
      builder.emit(OP_MOD, TY_I32, trip, builder.iConst(plan.factor));
  Inst *newStop = builder.emit(OP_SUB, TY_I32, stop, remainder);

  Region *newBody =
      buildExpandedBody(function, oldBody, plan, thenRegion, builder);
  builder.setInsertAtEnd(thenBlock);
  builder.emitFor(newStop, builder.iConst(plan.factor), plan.ivAddress,
                  newBody);

  DeepCopy epilogueCopy(function);
  Region *epilogueBody = epilogueCopy.copyRegion(oldBody).region;
  assert(epilogueBody);
  epilogueBody->parent = thenRegion;
  builder.setInsertAtEnd(thenBlock);
  builder.emitStore(plan.ivAddress, newStop, TY_I32);
  builder.emitFor(stop, builder.iConst(1), plan.ivAddress, epilogueBody);
  builder.emitYield();

  builder.setInsertBefore(loop);
  builder.emitIf(hasIterations, thenRegion);
  VERIFY(loop->eraseFromBlock());
  VERIFY(builder.eraseRegionContents(oldBody));
}

} // namespace

std::string_view ModuloUnroll::name() const noexcept { return "modulo-unroll"; }

PassResult ModuloUnroll::run(Function *function, PassContext &) {
  if (!function || function->isExtern || function->phase != IRPhase::HIR ||
      !function->region)
    return PassResult::noChange();
  bool changed = false;
  for (;;) {
    std::vector<Inst *> loops;
    forEachInstRecursive(function->region, [&](Inst *inst) {
      if (inst->getOp() == OP_FOR)
        loops.push_back(inst);
    });
    bool localChange = false;
    for (auto it = loops.rbegin(); it != loops.rend(); ++it) {
      Plan plan;
      if ((*it)->parentBlock() && analyze(*it, plan)) {
        transform(function, plan);
        localChange = true;
        changed = true;
        break;
      }
    }
    if (!localChange)
      break;
  }
  return changed ? PassResult::changedIR() : PassResult::noChange();
}

} // namespace svm::ir
