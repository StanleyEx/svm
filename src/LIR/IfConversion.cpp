#include "Analysis.h"
#include "LIRPass.h"

#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

constexpr u32 kMaxCandidatesPerRound = 256;

struct Candidate {
  BasicBlock *head = nullptr;      // 条件分支块
  BasicBlock *join = nullptr;      // 公共汇合块
  BasicBlock *firstArm = nullptr;  // 第一个被绕过的分支臂
  BasicBlock *secondArm = nullptr; // 第二个被绕过的分支臂
  Inst *terminator = nullptr;      // 原条件终结符
  Inst *condition = nullptr;       // Select条件
  Inst *phi = nullptr;             // 被替换的唯一Phi
  Inst *trueValue = nullptr;       // 真边值
  Inst *falseValue = nullptr;      // 假边值
  Inst *moved = nullptr;           // 至多一条投机搬运指令
  IRType type = TY_VOID;           // Select结果类型
};

Inst *incomingFrom(Inst *phi, BasicBlock *predecessor) noexcept {
  if (!phi || phi->getOp() != OP_PHI || !predecessor)
    return nullptr;
  return CFGEditor::getPhiIncomingValue(phi, predecessor);
}

bool isConstant(Inst *value, i32 expected) noexcept {
  return value && value->getOp() == OP_ICONST && value->getImm() == expected;
}

bool isSpeculatableArmOp(OpCode op) noexcept {
  switch (op) {
  case OP_ADD:
  case OP_SUB:
  case OP_NEG:
  case OP_EQ:
  case OP_NE:
  case OP_LT:
  case OP_LE:
  case OP_GT:
  case OP_GE:
  case OP_LNOT:
  case OP_ZEXT:
  case OP_SELECT:
    return true;
  default:
    return false;
  }
}

bool isArm(BasicBlock *arm, BasicBlock *head, BasicBlock *join) noexcept {
  if (!arm || arm == head || arm == join || arm->firstPhi() ||
      arm->getPredecessorCount() != 1 || arm->getPredecessor(0) != head)
    return false;
  Inst *terminator = arm->terminator();
  return terminator && terminator->getOp() == OP_JMP &&
         terminator->getJumpTarget() == join;
}

bool sameIncomingPair(BasicBlock *join, BasicBlock *truePredecessor,
                      BasicBlock *falsePredecessor) noexcept {
  if (!join || join->getPredecessorCount() != 2 ||
      truePredecessor == falsePredecessor)
    return false;
  BasicBlock *first = join->getPredecessor(0);
  BasicBlock *second = join->getPredecessor(1);
  return (first == truePredecessor && second == falsePredecessor) ||
         (first == falsePredecessor && second == truePredecessor);
}

bool collectMovedInstruction(const Candidate &candidate,
                             Inst *&moved) noexcept {
  moved = nullptr;
  u32 count = 0;
  BasicBlock *arms[] = {candidate.firstArm, candidate.secondArm};
  for (BasicBlock *arm : arms) {
    if (!arm)
      continue;
    Inst *terminator = arm->terminator();
    u32 perArm = 0;
    for (Inst *inst = arm->firstInst(); inst && inst != terminator;
         inst = inst->next()) {
      if (!isSpeculatableArmOp(inst->getOp()) ||
          (inst->getType() != TY_I1 && inst->getType() != TY_I32) ||
          ++perArm > 1 || ++count > 1)
        return false;
      moved = inst;
    }
  }
  return true;
}

bool hasLocalUsesOnly(Inst *value, BasicBlock *join) noexcept {
  if (!value)
    return true;
  for (const Use *use = value->uses(); use; use = use->next) {
    Inst *user = use->user;
    if (!user)
      return false;
    if (user->parentBlock() == value->parentBlock())
      continue;
    if (user->getOp() == OP_PHI && user->parentBlock() == join)
      continue;
    return false;
  }
  return true;
}

bool isProfitable(const Candidate &candidate) noexcept {
  bool conditionalUpdate = false;
  Inst *moved = candidate.moved;
  if (moved && (moved->getOp() == OP_ADD || moved->getOp() == OP_SUB) &&
      moved->hasOneUse()) {
    Inst *base = candidate.trueValue == moved    ? candidate.falseValue
                 : candidate.falseValue == moved ? candidate.trueValue
                                                 : nullptr;
    if (base) {
      conditionalUpdate =
          moved->getOp() == OP_ADD
              ? moved->getArg(0) == base || moved->getArg(1) == base
              : moved->getArg(0) == base;
    }
  }

  const bool cheapConstantArm =
      isConstant(candidate.trueValue, 0) ||
      isConstant(candidate.falseValue, 0) ||
      (candidate.type == TY_I1 && (isConstant(candidate.trueValue, 1) ||
                                   isConstant(candidate.falseValue, 1)));
  return conditionalUpdate || cheapConstantArm;
}

bool conflicts(const Candidate &candidate,
               const std::unordered_set<BasicBlock *> &reserved) noexcept {
  if (reserved.count(candidate.head) || reserved.count(candidate.join) ||
      (candidate.firstArm && reserved.count(candidate.firstArm)) ||
      (candidate.secondArm && reserved.count(candidate.secondArm)))
    return true;

  auto definedInReserved = [&](Inst *value) {
    return value && value->parentBlock() &&
           reserved.count(value->parentBlock()) != 0;
  };
  if (definedInReserved(candidate.condition) ||
      definedInReserved(candidate.trueValue) ||
      definedInReserved(candidate.falseValue))
    return true;
  if (candidate.moved)
    for (u32 index = 0; index < candidate.moved->getOperandCount(); ++index)
      if (definedInReserved(candidate.moved->getArg(index)))
        return true;
  return false;
}

void reserve(const Candidate &candidate,
             std::unordered_set<BasicBlock *> &reserved) {
  reserved.insert(candidate.head);
  reserved.insert(candidate.join);
  if (candidate.firstArm)
    reserved.insert(candidate.firstArm);
  if (candidate.secondArm)
    reserved.insert(candidate.secondArm);
}

bool collectCandidate(BasicBlock *head, const DominatorTree &dominators,
                      const PostDominatorTree &postDominators,
                      const LoopInfo &loops, Candidate &candidate) {
  Inst *branch = head ? head->terminator() : nullptr;
  if (!branch || branch->getOp() != OP_BR)
    return false;
  Inst *condition = branch->getArg(0);
  BasicBlock *trueBlock = branch->getBr().trueBB;
  BasicBlock *falseBlock = branch->getBr().falseBB;
  if (!condition || condition->getType() != TY_I1 || trueBlock == falseBlock)
    return false;

  Loop *loop = loops.getLoopFor(head);
  if (!loop || loops.isLoopHeader(head) ||
      dominators.dominates(trueBlock, head) ||
      dominators.dominates(falseBlock, head) || !condition->parentBlock() ||
      !loop->contains(condition->parentBlock()))
    return false;

  BasicBlock *join = nullptr;
  BasicBlock *firstArm = nullptr;
  BasicBlock *secondArm = nullptr;
  if (isArm(falseBlock, head, trueBlock)) {
    join = trueBlock;
    firstArm = falseBlock;
  } else if (isArm(trueBlock, head, falseBlock)) {
    join = falseBlock;
    firstArm = trueBlock;
  } else {
    BasicBlock *trueJoin = nullptr;
    if (successorCount(trueBlock) == 1)
      forEachSuccessor(trueBlock,
                       [&](BasicBlock *successor) { trueJoin = successor; });
    if (trueJoin && isArm(trueBlock, head, trueJoin) &&
        isArm(falseBlock, head, trueJoin)) {
      join = trueJoin;
      firstArm = trueBlock;
      secondArm = falseBlock;
    }
  }
  if (!join || join == head || loops.getLoopFor(join) != loop ||
      loops.getLoopFor(firstArm) != loop ||
      (secondArm && loops.getLoopFor(secondArm) != loop) ||
      !postDominators.postDominates(join, head) ||
      !dominators.dominates(head, join))
    return false;

  BasicBlock *truePredecessor = trueBlock == join ? head : trueBlock;
  BasicBlock *falsePredecessor = falseBlock == join ? head : falseBlock;
  if (!sameIncomingPair(join, truePredecessor, falsePredecessor) ||
      !join->firstPhi() || join->firstPhi() != join->lastPhi())
    return false;

  Inst *phi = join->firstPhi();
  IRType type = phi->getType();
  if (phi->getOperandCount() != 2 || (type != TY_I1 && type != TY_I32))
    return false;
  Inst *trueValue = incomingFrom(phi, truePredecessor);
  Inst *falseValue = incomingFrom(phi, falsePredecessor);
  if (!trueValue || !falseValue || trueValue->getType() != type ||
      falseValue->getType() != type)
    return false;

  candidate = {head, join,      firstArm,   secondArm, branch, condition,
               phi,  trueValue, falseValue, nullptr,   type};
  if (!collectMovedInstruction(candidate, candidate.moved) ||
      !hasLocalUsesOnly(candidate.moved, join))
    return false;

  auto availableAtHead = [&](Inst *value) {
    return value && (!value->parentBlock() || value == candidate.moved ||
                     dominators.dominates(value->parentBlock(), head));
  };
  if (!availableAtHead(trueValue) || !availableAtHead(falseValue))
    return false;
  if (candidate.moved)
    for (u32 index = 0; index < candidate.moved->getOperandCount(); ++index)
      if (!availableAtHead(candidate.moved->getArg(index)))
        return false;
  return isProfitable(candidate);
}

bool runIfConversion(Function *function, PassContext &context) {
  if (!computePreds(function))
    return false;
  bool changed = false;
  FunctionAnalysisManager &analyses = context.functionAnalyses();
  while (true) {
    const DominatorTree &dominators = context.get<DomAnalysis>(function).tree;
    const PostDominatorTree &postDominators =
        context.get<PostDomAnalysis>(function).tree;
    const LoopInfo &loops = context.get<LoopInfoAnalysis>(function).info;

    std::vector<Candidate> batch;
    std::unordered_set<BasicBlock *> reserved;
    for (BasicBlock *head : computeRPO(function)) {
      if (batch.size() >= kMaxCandidatesPerRound)
        break;
      Candidate candidate;
      if (!collectCandidate(head, dominators, postDominators, loops,
                            candidate) ||
          conflicts(candidate, reserved))
        continue;
      reserve(candidate, reserved);
      batch.push_back(candidate);
    }
    if (batch.empty())
      break;

    IRBuilder builder(function->module, function);
    for (const Candidate &candidate : batch) {
      if (candidate.moved)
        candidate.moved->moveBefore(candidate.terminator);
      builder.setInsertBefore(candidate.terminator);
      Inst *arguments[] = {candidate.condition, candidate.trueValue,
                           candidate.falseValue};
      Inst *select = builder.emitN(OP_SELECT, candidate.type, arguments, 3);
      replaceAllUsesWith(function, candidate.phi, select);
      VERIFY(candidate.phi->eraseFromBlock());
      UNUSED(builder.replaceWithJump(candidate.terminator, candidate.join));
    }

    changed = true;
    if (!cleanupDeadBlocks(function))
      VERIFY(computePreds(function), "IfConversion转换后CFG错误");
    analyses.clear(function);
  }
  return changed;
}

} // namespace

std::string_view IfConversionPass::name() const noexcept {
  return "if-conversion";
}

PassResult IfConversionPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();
  return runIfConversion(function, context) ? PassResult::changedIR()
                                            : PassResult::noChange();
}

} // namespace svm::ir
