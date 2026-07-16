#include "Analysis.h"
#include "LIRPass.h"
#include "MemDep.h"

#include <functional>
#include <limits>
#include <vector>

namespace svm::ir {
namespace {

struct AddRecView {
  SCEVExpr *recurrence = nullptr; // 地址中的唯一循环递推
  SCEVExpr *base = nullptr;       // 合并外层不变量后的零迭代地址
};

bool isInvariant(Inst *value, const Loop *loop) noexcept {
  return !value || !value->parentBlock() ||
         !loop->contains(value->parentBlock());
}

bool isSafePureInstruction(Inst *inst,
                           const GlobalSummaryResult *summary) noexcept {
  const OpCode op = inst->getOp();
  if (isBinaryArithmetic(op)) {
    if (op != OP_DIV && op != OP_MOD)
      return true;
    Inst *divisor = inst->getArg(1);
    return divisor->getOp() == OP_ICONST && divisor->getImm() != 0;
  }
  if (isUnaryArithmetic(op) || isCompare(op) || isConversion(op) ||
      isAddressingOp(op) || op == OP_SELECT)
    return true;
  if (op != OP_CALL || !summary || !inst->getCallee())
    return false;
  return summary->calleeEffect(inst->getCallee()).isSpeculatable();
}

bool sameConcreteRoot(const PointerInfo &left,
                      const PointerInfo &right) noexcept {
  if (!left.root || !right.root || left.kind != right.kind ||
      (left.kind != PointerKind::Alloca && left.kind != PointerKind::Global))
    return false;
  if (left.root == right.root)
    return true;
  return left.kind == PointerKind::Global &&
         left.root->getOp() == OP_GETGLOBAL &&
         right.root->getOp() == OP_GETGLOBAL &&
         left.root->getGlobal() == right.root->getGlobal();
}

bool hasBoundedObject(const PointerInfo &pointer) noexcept {
  return pointer.objectSize && *pointer.objectSize != 0 &&
         *pointer.objectSize <=
             static_cast<u64>(std::numeric_limits<i64>::max());
}

AddRecView extractAddRec(const SCEV &scev, SCEVExpr *expression,
                         const Loop *loop) {
  if (!expression)
    return {};
  if (expression->kind == SCEVExpr::K_ADDREC)
    return expression->addRec.loop == loop
               ? AddRecView{expression, expression->addRec.base}
               : AddRecView{};
  if (expression->kind != SCEVExpr::K_ADD)
    return {};

  SCEVExpr *recurrence = nullptr;
  SCEVExpr *base = nullptr;
  for (SCEVExpr *operand : expression->nary.ops) {
    if (operand->kind == SCEVExpr::K_ADDREC && operand->addRec.loop == loop) {
      if (recurrence)
        return {};
      recurrence = operand;
      base = operand->addRec.base;
      continue;
    }
    if (!operand->isLoopInvariant(loop))
      return {};
    base = base ? scev.getAddExpr(base, operand) : operand;
  }
  return recurrence ? AddRecView{recurrence, base} : AddRecView{};
}

bool proveAffineNoAlias(Inst *load, Inst *store, const Loop *loop,
                        const AliasInfo &aliases, const SCEV &scev) {
  const MemoryLocation loaded = MemoryLocation::fromMemoryInstruction(load);
  const MemoryLocation stored = MemoryLocation::fromMemoryInstruction(store);
  if (!loaded.pointer || !stored.pointer || !loaded.accessSize ||
      !stored.accessSize || *loaded.accessSize == 0 ||
      *stored.accessSize == 0 ||
      *loaded.accessSize > static_cast<u64>(std::numeric_limits<i64>::max()) ||
      *stored.accessSize > static_cast<u64>(std::numeric_limits<i64>::max()))
    return false;

  const PointerInfo loadInfo = aliases.info(loaded.pointer);
  const PointerInfo storeInfo = aliases.info(stored.pointer);
  if (!sameConcreteRoot(loadInfo, storeInfo) || !hasBoundedObject(loadInfo))
    return false;

  SCEVExpr *loadExpression = scev.getSCEV(loaded.pointer);
  SCEVExpr *storeExpression = scev.getSCEV(stored.pointer);
  if (!loadExpression || !loadExpression->isLoopInvariant(loop))
    return false;
  const AddRecView storeRec = extractAddRec(scev, storeExpression, loop);
  if (!storeRec.recurrence || !storeRec.base ||
      !storeRec.recurrence->addRec.step ||
      !storeRec.recurrence->addRec.step->isConstant() ||
      !storeRec.recurrence->nsw)
    return false;

  MathQuery query;
  query.contextBlock = store->parentBlock();
  const MathBounds initialDelta =
      scev.getSignedDeltaBounds(storeRec.base, loadExpression, query);
  if (!initialDelta.valid)
    return false;

  const i64 step = storeRec.recurrence->addRec.step->cst.v;
  const i64 loadSize = static_cast<i64>(*loaded.accessSize);
  const i64 storeSize = static_cast<i64>(*stored.accessSize);
  return (step >= 0 && initialDelta.min >= loadSize) ||
         (step <= 0 && initialDelta.max <= -storeSize);
}

bool hasClobberAfterAffineRefinement(Inst *load, const Loop *loop,
                                     const AliasInfo &aliases, const SCEV &scev,
                                     const GlobalSummaryResult *summary) {
  const MemoryLocation loaded = MemoryLocation::fromMemoryInstruction(load);
  for (BasicBlock *block : loop->blocks()) {
    AliasQuery query;
    query.contextBlock = block;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if (inst->getOp() == OP_STORE) {
        const AliasResult result = aliases.alias(
            MemoryLocation::fromMemoryInstruction(inst), loaded, query);
        if (result != AliasResult::NoAlias &&
            !proveAffineNoAlias(load, inst, loop, aliases, scev))
          return true;
      } else if (inst->getOp() == OP_CALL || inst->getOp() == MOP_CALL) {
        const bool mayWrite =
            summary ? aliases.mayWriteMemory(
                          inst, loaded,
                          summary->calleeEffect(inst->getCallee()), query)
                    : aliases.mayWriteMemory(inst, loaded, query);
        if (mayWrite)
          return true;
      }
    }
  }
  return false;
}

bool canHoistLoad(Inst *load, const Loop *loop, const AliasInfo &aliases,
                  const SCEV &scev, const MemDepOracle &memory,
                  const GlobalSummaryResult *summary) {
  Inst *address = load->getArg(0);
  if (!isInvariant(address, loop))
    return false;
  const MemoryLocation location = MemoryLocation::fromMemoryInstruction(load);
  if (memory.hasClobberInLoop(location, loop) &&
      hasClobberAfterAffineRefinement(load, loop, aliases, scev, summary))
    return false;
  AliasQuery query;
  query.contextBlock = loop->getPreheader();
  return aliases.isDereferenceable(location, query) ||
         load->parentBlock() == loop->header();
}

bool processLoop(Loop *loop, const AliasInfo &aliases, const SCEV &scev,
                 const MemDepOracle &memory,
                 const GlobalSummaryResult *summary) {
  BasicBlock *preheader = loop->getPreheader();
  if (!preheader || !preheader->terminator())
    return false;

  bool changed = false;
  bool roundChanged = false;
  do {
    roundChanged = false;
    for (BasicBlock *block : loop->blocks()) {
      for (Inst *inst = block->firstInst(); inst;) {
        Inst *next = inst->next();
        if (isVoid(inst->getType()) || isTerminator(inst->getOp()) ||
            inst->getOp() == OP_PHI) {
          inst = next;
          continue;
        }

        bool operandsInvariant = true;
        for (u32 index = 0; index < inst->getOperandCount(); ++index)
          if (!isInvariant(inst->getArg(index), loop)) {
            operandsInvariant = false;
            break;
          }
        if (operandsInvariant &&
            (isSafePureInstruction(inst, summary) ||
             (inst->getOp() == OP_LOAD &&
              canHoistLoad(inst, loop, aliases, scev, memory, summary)))) {
          inst->moveBefore(preheader->terminator());
          roundChanged = changed = true;
        }
        inst = next;
      }
    }
  } while (roundChanged);
  return changed;
}

bool runLICM(Function *function, PassContext &context) {
  const LoopInfo &loops = context.get<LoopInfoAnalysis>(function).info;
  if (loops.topLevelLoops().empty())
    return false;
  const SCEV &scev = context.get<SCEVAnalysis>(function).info;
  const AliasInfo &aliases = context.get<AliasAnalysis>(function).info;
  const GlobalSummaryResult *summary =
      function->module
          ? &context.get<GlobalSummaryAnalysis>(function->module).result
          : nullptr;
  const MemDepOracle memory(&aliases, summary);

  std::vector<Loop *> postorder;
  std::function<void(Loop *)> collect = [&](Loop *loop) {
    for (Loop *child : loop->children())
      collect(child);
    postorder.push_back(loop);
  };
  for (Loop *loop : loops.topLevelLoops())
    collect(loop);

  bool changed = false;
  for (Loop *loop : postorder)
    changed |= processLoop(loop, aliases, scev, memory, summary);
  return changed;
}

} // namespace

std::string_view LICMPass::name() const noexcept { return "licm"; }

PassResult LICMPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();
  if (!runLICM(function, context))
    return PassResult::noChange();

  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  preserved.preserve<SCEVAnalysis>();
  preserved.preserve<AliasAnalysis>();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
