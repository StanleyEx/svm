#include "IR.h"
#include "LIRPass.h"

#include <cassert>
#include <cmath>
#include <limits>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

enum class LatticeState : u8 {
  Top,      // 尚无信息 乐观
  Constant, // 已知为唯一常量
  Bottom,   // 已知不是唯一常量
};

struct LatticeValue {
  LatticeState state = LatticeState::Top;
  Inst *constant = nullptr; // Constant状态对应的常量

  bool isTop() const noexcept { return state == LatticeState::Top; }
  bool isConstant() const noexcept { return state == LatticeState::Constant; }
  bool isBottom() const noexcept { return state == LatticeState::Bottom; }
  static LatticeValue top() noexcept { return {}; }
  static LatticeValue bottom() noexcept {
    return {LatticeState::Bottom, nullptr};
  }
  static LatticeValue fromConstant(Inst *value) noexcept {
    return {LatticeState::Constant, value};
  }
  bool operator==(const LatticeValue &other) const noexcept {
    return state == other.state && constant == other.constant;
  }
  bool operator!=(const LatticeValue &other) const noexcept {
    return !(*this == other);
  }
};

using CFGEdge = std::pair<BasicBlock *, BasicBlock *>;

class SCCPSolver {
public:
  explicit SCCPSolver(Function *function) noexcept
      : function_(function), builder_(function->module, function) {}

  bool run(bool &cfgChanged) {
    if (!function_->region || !function_->region->first)
      return false;
    computeUses(function_);
    analyze();
    return rewrite(cfgChanged);
  }

private:
  void analyze() {
    BasicBlock *entry = function_->region->first;
    reachableBlocks_.insert(entry);
    forEachOp(entry, [&](Inst *inst) { visit(inst); });

    for (;;) {
      while (!cfgWorklist_.empty() || !ssaWorklist_.empty()) {
        while (!cfgWorklist_.empty()) {
          const CFGEdge edge = cfgWorklist_.back();
          cfgWorklist_.pop_back();
          processEdge(edge);
        }
        while (!ssaWorklist_.empty()) {
          Inst *inst = ssaWorklist_.back();
          ssaWorklist_.pop_back();
          if (inst && inst->parentBlock() && isReachable(inst->parentBlock()))
            visit(inst);
        }
      }
      if (!resolveUnknownControlFlow())
        break;
    }
  }

  // 不动点后保守激活未决Top条件的边
  bool resolveUnknownControlFlow() {
    bool queued = false;
    for (BasicBlock *block = function_->region->first; block;
         block = block->next()) {
      if (!isReachable(block) || !block->endsWithTerminator())
        continue;
      Inst *terminator = block->terminator();
      if (terminator->getOp() != OP_BR && terminator->getOp() != OP_SWITCH)
        continue;
      if (!valueOf(terminator->getArg(0)).isTop())
        continue;
      forEachSuccessor(terminator, [&](BasicBlock *successor) {
        if (isExecutable(block, successor))
          return;
        cfgWorklist_.emplace_back(block, successor);
        queued = true;
      });
    }
    return queued;
  }

  // 激活新边并重算后继Phi
  void processEdge(const CFGEdge &edge) {
    if (!edge.first || !edge.second || !executableEdges_.insert(edge).second)
      return;
    if (reachableBlocks_.insert(edge.second).second) {
      forEachOp(edge.second, [&](Inst *inst) { visit(inst); });
      return;
    }
    forEachPhi(edge.second, [&](Inst *phi) { visit(phi); });
  }

  // 更新单条指令格值或传播终结符边
  void visit(Inst *inst) {
    assert(inst && inst->parentBlock());
    if (isLIRTerminator(inst->getOp())) {
      visitTerminator(inst);
      return;
    }
    if (inst->getType() == TY_VOID)
      return;

    const LatticeValue oldValue = valueOf(inst);
    const LatticeValue newValue = evaluate(inst);
    if (oldValue == newValue)
      return;
    assert(
        (!oldValue.isBottom() ||                          // Bottom状态不可逆
         !(oldValue.isConstant() && newValue.isTop())) && // 从Top或Constant下降
        "SCCP 格值必须单调下降");
    values_[inst] = newValue;
    for (const Use *use = inst->uses(); use; use = use->next)
      ssaWorklist_.push_back(use->user);
  }

  // 按当前条件格值激活后继边
  void visitTerminator(Inst *terminator) {
    BasicBlock *block = terminator->parentBlock();
    switch (terminator->getOp()) {
    case OP_JMP:
      cfgWorklist_.emplace_back(block, terminator->getJumpTarget());
      return;
    case OP_BR: {
      const LatticeValue condition = valueOf(terminator->getArg(0));
      if (condition.isConstant()) {
        cfgWorklist_.emplace_back(block, condition.constant->getImm() != 0
                                             ? terminator->getBr().trueBB
                                             : terminator->getBr().falseBB);
      } else if (condition.isBottom()) {
        cfgWorklist_.emplace_back(block, terminator->getBr().trueBB);
        cfgWorklist_.emplace_back(block, terminator->getBr().falseBB);
      }
      return;
    }
    case OP_SWITCH: {
      const LatticeValue selector = valueOf(terminator->getArg(0));
      if (selector.isConstant()) {
        cfgWorklist_.emplace_back(
            block, switchTarget(terminator, selector.constant->getImm()));
      } else if (selector.isBottom()) {
        forEachSuccessor(terminator, [&](BasicBlock *successor) {
          cfgWorklist_.emplace_back(block, successor);
        });
      }
      return;
    }
    case OP_RET:
    case OP_UNREACHABLE:
      return;
    default:
      return;
    }
  }

  LatticeValue evaluate(Inst *inst) {
    const OpCode op = inst->getOp();
    if (op == OP_PHI)
      return evaluatePhi(inst);
    if (isBinaryArithmetic(op))
      return evaluateBinary(inst);
    if (isUnaryArithmetic(op))
      return evaluateUnary(inst);
    if (isCompare(op))
      return evaluateCompare(inst);
    if (isConversion(op))
      return evaluateConversion(inst);
    if (op == OP_SELECT)
      return evaluateSelect(inst);
    return LatticeValue::bottom();
  }
  // 只合流可执行入边
  LatticeValue evaluatePhi(Inst *phi) const {
    LatticeValue result = LatticeValue::top();
    BasicBlock *block = phi->parentBlock();
    for (u32 index = 0; index < phi->getOperandCount(); ++index) {
      BasicBlock *predecessor = phi->getIncomingBlock(index);
      if (!isExecutable(predecessor, block))
        continue;
      result = meet(result, valueOf(phi->getArg(index)));
      if (result.isBottom())
        break;
    }
    return result;
  }
  LatticeValue evaluateBinary(Inst *inst) {
    const LatticeValue left = valueOf(inst->getArg(0));
    const LatticeValue right = valueOf(inst->getArg(1));
    if (left.isTop() || right.isTop())
      return LatticeValue::top();
    if (left.isBottom() || right.isBottom())
      return LatticeValue::bottom();
    return foldBinary(inst->getOp(), left.constant, right.constant);
  }
  LatticeValue evaluateUnary(Inst *inst) {
    const LatticeValue operand = valueOf(inst->getArg(0));
    if (operand.isTop())
      return LatticeValue::top();
    if (operand.isBottom())
      return LatticeValue::bottom();
    switch (inst->getOp()) {
    case OP_NEG:
      return LatticeValue::fromConstant(
          builder_.iConst(i32NegWrap(operand.constant->getImm())));
    case OP_FNEG:
      return LatticeValue::fromConstant(
          builder_.fConst(-operand.constant->getFimm()));
    case OP_LNOT:
      return LatticeValue::fromConstant(
          builder_.i1Const(operand.constant->getImm() == 0));
    default:
      return LatticeValue::bottom();
    }
  }
  LatticeValue evaluateCompare(Inst *inst) {
    const LatticeValue left = valueOf(inst->getArg(0));
    const LatticeValue right = valueOf(inst->getArg(1));
    // TODO(SCEV)
    if (left.isTop() || right.isTop())
      return LatticeValue::top();
    if (left.isBottom() || right.isBottom())
      return LatticeValue::bottom();

    bool result = false;
    switch (inst->getOp()) {
    case OP_EQ:
      result = left.constant->getImm() == right.constant->getImm();
      break;
    case OP_NE:
      result = left.constant->getImm() != right.constant->getImm();
      break;
    case OP_LT:
      result = left.constant->getImm() < right.constant->getImm();
      break;
    case OP_LE:
      result = left.constant->getImm() <= right.constant->getImm();
      break;
    case OP_GT:
      result = left.constant->getImm() > right.constant->getImm();
      break;
    case OP_GE:
      result = left.constant->getImm() >= right.constant->getImm();
      break;
    case OP_FEQ:
      result = left.constant->getFimm() == right.constant->getFimm();
      break;
    case OP_FNE:
      result = left.constant->getFimm() != right.constant->getFimm();
      break;
    case OP_FLT:
      result = left.constant->getFimm() < right.constant->getFimm();
      break;
    case OP_FLE:
      result = left.constant->getFimm() <= right.constant->getFimm();
      break;
    case OP_FGT:
      result = left.constant->getFimm() > right.constant->getFimm();
      break;
    case OP_FGE:
      result = left.constant->getFimm() >= right.constant->getFimm();
      break;
    default:
      return LatticeValue::bottom();
    }
    return LatticeValue::fromConstant(builder_.i1Const(result));
  }
  LatticeValue evaluateConversion(Inst *inst) {
    const LatticeValue operand = valueOf(inst->getArg(0));
    if (operand.isTop())
      return LatticeValue::top();
    if (operand.isBottom())
      return LatticeValue::bottom();
    switch (inst->getOp()) {
    case OP_I2F:
      return LatticeValue::fromConstant(
          builder_.fConst(static_cast<f32>(operand.constant->getImm())));
    case OP_F2I: {
      const f32 value = operand.constant->getFimm();
      if (!canConvertToI32(value))
        return LatticeValue::bottom();
      return LatticeValue::fromConstant(builder_.iConst(
          static_cast<i32>(std::trunc(static_cast<f64>(value)))));
    }
    case OP_ZEXT:
      return LatticeValue::fromConstant(
          builder_.iConst(operand.constant->getImm() != 0 ? 1 : 0));
    default:
      return LatticeValue::bottom();
    }
  }
  LatticeValue evaluateSelect(Inst *inst) const {
    const LatticeValue condition = valueOf(inst->getArg(0));
    const LatticeValue trueValue = valueOf(inst->getArg(1));
    const LatticeValue falseValue = valueOf(inst->getArg(2));
    if (condition.isConstant())
      return condition.constant->getImm() != 0 ? trueValue : falseValue;
    if (inst->getArg(1) == inst->getArg(2))
      return trueValue;
    if (condition.isTop() && (trueValue.isTop() || falseValue.isTop()))
      return LatticeValue::top();
    return meet(trueValue, falseValue);
  }
  LatticeValue foldBinary(OpCode op, Inst *left, Inst *right) {
    if (op >= OP_ADD && op <= OP_MOD) {
      const i32 lhs = left->getImm();
      const i32 rhs = right->getImm();
      switch (op) {
      case OP_ADD:
        return LatticeValue::fromConstant(
            builder_.iConst(i32AddWrap(lhs, rhs)));
      case OP_SUB:
        return LatticeValue::fromConstant(
            builder_.iConst(i32SubWrap(lhs, rhs)));
      case OP_MUL:
        return LatticeValue::fromConstant(
            builder_.iConst(i32MulWrap(lhs, rhs)));
      case OP_DIV:
        if (rhs == 0 || (lhs == std::numeric_limits<i32>::min() && rhs == -1))
          return LatticeValue::bottom();
        return LatticeValue::fromConstant(builder_.iConst(lhs / rhs));
      case OP_MOD:
        if (rhs == 0)
          return LatticeValue::bottom();
        if (lhs == std::numeric_limits<i32>::min() && rhs == -1)
          return LatticeValue::fromConstant(builder_.iConst(0));
        return LatticeValue::fromConstant(builder_.iConst(lhs % rhs));
      default:
        break;
      }
    }
    if (op >= OP_FADD && op <= OP_FDIV) {
      const f32 lhs = left->getFimm();
      const f32 rhs = right->getFimm();
      switch (op) {
      case OP_FADD:
        return LatticeValue::fromConstant(builder_.fConst(lhs + rhs));
      case OP_FSUB:
        return LatticeValue::fromConstant(builder_.fConst(lhs - rhs));
      case OP_FMUL:
        return LatticeValue::fromConstant(builder_.fConst(lhs * rhs));
      case OP_FDIV:
        return LatticeValue::fromConstant(builder_.fConst(lhs / rhs));
      default:
        break;
      }
    }
    return LatticeValue::bottom();
  }
  // 值的当前格状态
  LatticeValue valueOf(Inst *inst) const {
    if (!inst || inst->isUndefValue())
      return LatticeValue::top();
    if (inst->getOp() == OP_ICONST || inst->getOp() == OP_FCONST)
      return LatticeValue::fromConstant(inst);
    if (!inst->parentBlock())
      return LatticeValue::bottom();
    const auto found = values_.find(inst);
    return found == values_.end() ? LatticeValue::top() : found->second;
  }
  // Phi格合流
  static LatticeValue meet(LatticeValue left, LatticeValue right) noexcept {
    if (left.isTop())
      return right;
    if (right.isTop())
      return left;
    if (left.isBottom() || right.isBottom())
      return LatticeValue::bottom();
    return left.constant == right.constant ? left : LatticeValue::bottom();
  }

  // 常量case目标
  BasicBlock *switchTarget(Inst *switchInst, i32 value) const noexcept {
    const SwitchPayload &payload = switchInst->getSwitch();
    u32 first = 0;
    u32 last = payload.getCaseCount();
    while (first < last) {
      const u32 middle = first + (last - first) / 2;
      const i32 candidate = payload.getCase(middle).getValue();
      if (candidate < value)
        first = middle + 1;
      else
        last = middle;
    }
    if (first < payload.getCaseCount() &&
        payload.getCase(first).getValue() == value)
      return payload.getCase(first).getTarget();
    return payload.getDefaultTarget();
  }

  // 边是否已激活
  bool isExecutable(BasicBlock *predecessor, BasicBlock *successor) const {
    return executableEdges_.count({predecessor, successor}) != 0;
  }

  // 块是否已由可执行边激活
  bool isReachable(BasicBlock *block) const {
    return reachableBlocks_.count(block) != 0;
  }

  // 常量替换 终结符折叠 死块清理
  bool rewrite(bool &cfgChanged) {
    bool changed = false;
    std::vector<std::pair<Inst *, Inst *>> replacements;
    for (BasicBlock *block = function_->region->first; block;
         block = block->next()) {
      if (!isReachable(block))
        continue;
      forEachOp(block, [&](Inst *inst) {
        if (isLIRTerminator(inst->getOp()))
          return;
        const LatticeValue value = valueOf(inst);
        if (value.isConstant() && value.constant != inst)
          replacements.emplace_back(inst, value.constant);
      });
    }
    for (const auto &[inst, constant] : replacements) {
      if (inst->parentBlock() && builder_.replace(inst, constant))
        changed = true;
    }

    for (BasicBlock *block = function_->region->first; block;
         block = block->next()) {
      if (!isReachable(block) || !block->endsWithTerminator())
        continue;
      Inst *terminator = block->terminator();
      BasicBlock *target = nullptr;
      const LatticeValue selector = terminator->getOperandCount() != 0
                                        ? valueOf(terminator->getArg(0))
                                        : LatticeValue::top();
      if (terminator->getOp() == OP_BR && selector.isConstant()) {
        target = selector.constant->getImm() != 0 ? terminator->getBr().trueBB
                                                  : terminator->getBr().falseBB;
      } else if (terminator->getOp() == OP_SWITCH && selector.isConstant()) {
        target = switchTarget(terminator, selector.constant->getImm());
      }
      if (target && CFGEditor::foldTerminatorToJump(function_, block, target)) {
        changed = true;
        cfgChanged = true;
      }
    }

    if (cleanupDeadBlocks(function_)) {
      changed = true;
      cfgChanged = true;
    }
    if (cfgChanged)
      VERIFY(computePreds(function_));
    return changed;
  }

  struct CFGEdgeHash {
    usize operator()(const CFGEdge &edge) const noexcept {
      auto first = reinterpret_cast<uintptr>(edge.first);
      auto second = reinterpret_cast<uintptr>(edge.second);
      return std::hash<uintptr>{}(first ^
                                  (second + (first << 6) + (first >> 2)));
    }
  };

  Function *function_ = nullptr;
  IRBuilder builder_;
  std::unordered_map<Inst *, LatticeValue> values_;          // SSA值格状态
  std::unordered_set<CFGEdge, CFGEdgeHash> executableEdges_; // 可执行边集合
  std::unordered_set<BasicBlock *> reachableBlocks_;         // 已激活块集合
  std::vector<CFGEdge> cfgWorklist_;                         // 待激活CFG边
  std::vector<Inst *> ssaWorklist_;                          // 待重算SSA用户
};

} // namespace

std::string_view SCCPPass::name() const noexcept { return "sccp"; }

PassResult SCCPPass::run(Function *function, PassContext &) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();

  bool cfgChanged = false;
  if (!SCCPSolver(function).run(cfgChanged))
    return PassResult::noChange();

  PreservedAnalyses preserved;
  preserved.preserveSSAForm();
  if (!cfgChanged)
    preserved.preserveCFGAnalyses();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
