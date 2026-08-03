#include "Analysis.h"
#include "LIRPass.h"
#include "LoopShape.h"
#include "Utils.h"

#include <functional>
#include <optional>
#include <unordered_map>
#include <vector>

namespace svm::ir {
namespace {

constexpr i32 kUnknownCoefficient = 1000000;
constexpr i32 kMaxTransformsPerFunction = 32;

struct RepeatReductionPlan {
  CountedLoopShape shape;       // 已验证的外层counted loop
  Inst *base = nullptr;         // reduction零轮初值
  Inst *first = nullptr;        // 执行首轮后的reduction值
  Inst *tripCount = nullptr;    // 动态重复次数R
  std::vector<Inst *> exitPhis; // 需要改写latch incoming的LCSSA Phi
};

std::vector<Loop *> collectLoopsPostorder(const LoopInfo &loops) {
  std::vector<Loop *> result;
  const std::function<void(Loop *)> collect = [&](Loop *loop) {
    for (Loop *child : loop->children())
      collect(child);
    result.push_back(loop);
  };
  for (Loop *loop : loops.topLevelLoops())
    collect(loop);
  return result;
}

bool entersForPositiveBound(const CountedLoopShape &shape, const SCEV &scev) {
  RangeQuery query;
  query.contextBlock = shape.preheader;
  const auto bounds =
      scev.getI32Range(shape.latchTest.boundValue, query).signedBounds();
  return bounds && bounds->min >= 1;
}

bool hasSupportedEffects(const Loop *loop) noexcept {
  for (BasicBlock *block : loop->blocks()) {
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      const OpCode op = inst->getOp();
      const bool supported =
          isArithmetic(op) || isUnaryArithmetic(op) || isCompare(op) ||
          isConversion(op) || isAddressingOp(op) || op == OP_LOAD ||
          op == OP_SELECT || op == OP_BR || op == OP_JMP || op == OP_SWITCH;
      if (!supported)
        return false;
    }
  }
  return true;
}

bool controlIVIsOnlyControl(const CountedLoopShape &shape) noexcept {
  for (const Use *use = shape.iv.phi->uses(); use; use = use->next) {
    if (!use->user || !use->user->parentBlock() ||
        !shape.loop->contains(use->user->parentBlock()))
      continue;
    if (use->user != shape.iv.stepInst)
      return false;
  }
  for (const Use *use = shape.iv.stepInst->uses(); use; use = use->next) {
    Inst *user = use->user;
    if (user != shape.iv.phi && user != shape.latchTest.comparison)
      return false;
  }
  return true;
}

bool proveUnitCoefficient(const Loop *loop, Inst *seed, Inst *value) {
  if (!loop || !seed || !value)
    return false;
  std::vector<Inst *> nodes;
  for (BasicBlock *block : loop->blocks()) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      nodes.push_back(phi);
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      nodes.push_back(inst);
  }

  std::unordered_map<Inst *, i32> coefficients;
  for (Inst *node : nodes)
    coefficients.emplace(node, kUnknownCoefficient);
  coefficients[seed] = 1;
  const auto coefficientOf = [&](Inst *operand, i32 &coefficient) {
    if (!operand) {
      coefficient = 0;
      return true;
    }
    if (operand == seed) {
      coefficient = 1;
      return true;
    }
    if (!operand->parentBlock() || !loop->contains(operand->parentBlock())) {
      coefficient = 0;
      return true;
    }
    const auto found = coefficients.find(operand);
    if (found == coefficients.end() || found->second == kUnknownCoefficient)
      return false;
    coefficient = found->second;
    return true;
  };

  bool invalid = false;
  bool changed = true;
  for (usize round = 0; round < nodes.size() + 4 && changed && !invalid;
       ++round) {
    changed = false;
    for (Inst *node : nodes) {
      if (node == seed)
        continue;
      i32 coefficient = kUnknownCoefficient;
      bool known = true;
      switch (node->getOp()) {
      case OP_PHI: {
        bool haveKnown = false;
        coefficient = 0;
        for (u32 index = 0; index < node->getOperandCount(); ++index) {
          i32 incoming = 0;
          if (!coefficientOf(node->getArg(index), incoming)) {
            known = false;
            continue;
          }
          if (!haveKnown) {
            coefficient = incoming;
            haveKnown = true;
          } else if (coefficient != incoming) {
            invalid = true;
            break;
          }
        }
        known = haveKnown;
        break;
      }
      case OP_ADD:
      case OP_SUB: {
        i32 left = 0;
        i32 right = 0;
        known = coefficientOf(node->getArg(0), left) &&
                coefficientOf(node->getArg(1), right);
        if (known)
          coefficient = node->getOp() == OP_ADD ? left + right : left - right;
        break;
      }
      case OP_NEG: {
        i32 operand = 0;
        known = coefficientOf(node->getArg(0), operand);
        if (known)
          coefficient = -operand;
        break;
      }
      default:
        coefficient = 0;
        for (u32 index = 0; index < node->getOperandCount(); ++index) {
          i32 operand = 0;
          if (!coefficientOf(node->getArg(index), operand)) {
            known = false;
            continue;
          }
          if (operand != 0) {
            invalid = true;
            break;
          }
        }
        break;
      }
      if (invalid || !known || coefficient == kUnknownCoefficient)
        continue;
      if (coefficient < -1 || coefficient > 1) {
        invalid = true;
        break;
      }
      i32 &stored = coefficients[node];
      if (stored != coefficient) {
        stored = coefficient;
        changed = true;
      }
    }
  }
  i32 result = 0;
  return !invalid && coefficientOf(value, result) && result == 1;
}

bool collectExclusiveLiveOuts(const CountedLoopShape &shape, Inst *first,
                              std::vector<Inst *> &exitPhis) {
  for (BasicBlock *block : shape.loop->blocks()) {
    bool valid = true;
    forEachOp(block, [&](Inst *definition) {
      if (!valid || isVoid(definition->getType()))
        return;
      for (const Use *use = definition->uses(); use; use = use->next) {
        Inst *user = use->user;
        BasicBlock *userBlock = user ? user->parentBlock() : nullptr;
        if (!userBlock || shape.loop->contains(userBlock))
          continue;
        const bool isTarget = definition == first && user->getOp() == OP_PHI &&
                              userBlock == shape.exit &&
                              user->getIncomingBlock(use->argNo) == shape.latch;
        if (!isTarget) {
          valid = false;
          break;
        }
        exitPhis.push_back(user);
      }
    });
    if (!valid)
      return false;
  }
  return !exitPhis.empty();
}

std::optional<RepeatReductionPlan>
buildPlan(Loop *loop, const LoopShapeInfo &shapes, const SCEV &scev) {
  LoopShapeQuery query;
  query.requireLatchCompareInLatch = true;
  auto shape = shapes.getCountedLoop(loop, query);
  if (!shape || shape->iv.step != 1 || shape->iv.updateOp != OP_ADD ||
      shape->latchTest.canonicalPredicate != OP_LT ||
      shape->headerPhis.size() != 2 || loop->exitingBlocks().size() != 1 ||
      loop->exitingBlocks().front() != shape->latch || !shape->iv.baseSCEV ||
      !shape->iv.baseSCEV->isConstant() || shape->iv.baseSCEV->cst.v != 0 ||
      !shape->latchTest.boundValue ||
      shape->latchTest.boundValue->getType() != TY_I32 ||
      !entersForPositiveBound(*shape, scev) || !hasSupportedEffects(loop) ||
      !controlIVIsOnlyControl(*shape))
    return std::nullopt;

  const HeaderPhiShape *reduction = nullptr;
  for (const HeaderPhiShape &headerPhi : shape->headerPhis)
    if (!headerPhi.isControlIV)
      reduction = &headerPhi;
  if (!reduction || !reduction->phi || reduction->phi->getType() != TY_I32 ||
      !reduction->preheaderValue || !reduction->latchValue ||
      !proveUnitCoefficient(loop, reduction->phi, reduction->latchValue))
    return std::nullopt;

  RepeatReductionPlan plan;
  plan.shape = *shape;
  plan.base = reduction->preheaderValue;
  plan.first = reduction->latchValue;
  plan.tripCount = shape->latchTest.boundValue;
  if (!collectExclusiveLiveOuts(*shape, plan.first, plan.exitPhis))
    return std::nullopt;
  return plan;
}

void commitPlan(Function *function, const RepeatReductionPlan &plan) {
  IRBuilder builder(function->module, function);
  builder.setInsertBefore(plan.shape.latch->terminator());
  Inst *delta = builder.emit(OP_SUB, TY_I32, plan.first, plan.base);
  Inst *scaled = builder.emit(OP_MUL, TY_I32, delta, plan.tripCount);
  Inst *finalValue = builder.emit(OP_ADD, TY_I32, plan.base, scaled);
  std::vector<CFGEditor::PhiEdgeValue> values;
  values.reserve(plan.exitPhis.size());
  for (Inst *phi : plan.exitPhis)
    values.push_back({phi, finalValue});
  VERIFY(CFGEditor::setPhiEdgeValues(function, plan.shape.exit,
                                     plan.shape.latch, values));
  VERIFY(CFGEditor::foldTerminatorToJump(function, plan.shape.latch,
                                         plan.shape.exit));
  VERIFY(computePreds(function));
  computeUses(function);
}

} // namespace

std::string_view InvariantRepeatReductionPass::name() const noexcept {
  return "invariant-repeat-reduction";
}

PassResult InvariantRepeatReductionPass::run(Function *function,
                                             PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first || !computePreds(function))
    return PassResult::noChange();
  computeUses(function);
  FunctionAnalysisManager &analyses = context.functionAnalyses();
#ifndef NDEBUG
  VERIFY(verifyLoopSimplify(function, analyses));
  VERIFY(verifyLCSSA(function, analyses));
#endif

  i32 transformed = 0;
  while (transformed < kMaxTransformsPerFunction) {
    const LoopInfo &loops = analyses.getResult<LoopInfoAnalysis>(function).info;
    const LoopShapeInfo &shapes =
        analyses.getResult<LoopShapeAnalysis>(function).info;
    const SCEV &scev = analyses.getResult<SCEVAnalysis>(function).info;
    std::optional<RepeatReductionPlan> selected;
    for (Loop *loop : collectLoopsPostorder(loops)) {
      selected = buildPlan(loop, shapes, scev);
      if (selected)
        break;
    }
    if (!selected)
      break;
    commitPlan(function, *selected);
    ++transformed;
    UNUSED(repairLoopForm(function, context));
  }

  if (transformed == 0)
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
