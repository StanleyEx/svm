#include "Analysis.h"
#include "DeepCopy.h"
#include "IR.h"
#include "LIRPass.h"
#include "LoopMutator.h"
#include "LoopShape.h"
#include "PressureOracle.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <vector>

namespace svm::ir {
namespace {

struct LoopUnrollMetrics {
  i32 controlIVIndex = -1;      // 控制IV在Header Phi中的位置
  i32 bodyInstructions = 0;     // 循环体活指令数
  bool compact = true;          // 是否仅由Header和Latch组成
  bool hasInternalExit = false; // 是否存在非Latch退出边
};

LoopUnrollMetrics computeMetrics(const CountedLoopShape &shape) {
  LoopUnrollMetrics result;
  for (usize index = 0; index < shape.headerPhis.size(); ++index)
    if (shape.headerPhis[index].isControlIV)
      result.controlIVIndex = static_cast<i32>(index);
  VERIFY(result.controlIVIndex >= 0, "找不到控制IV");

  for (BasicBlock *block : shape.loop->blocks()) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      ++result.bodyInstructions;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      result.bodyInstructions = static_cast<i32>(
          std::min<i64>(std::numeric_limits<i32>::max(),
                        static_cast<i64>(result.bodyInstructions) +
                            estimateArrayIndexLoweringCost(inst).instructions));
    if (block != shape.header && block != shape.latch)
      result.compact = false;
    forEachSuccessor(block, [&](BasicBlock *successor) {
      if (successor == shape.exit && block != shape.latch)
        result.hasInternalExit = true;
    });
  }
  return result;
}

std::vector<BasicBlock *> collectLoopBlocks(Function *function,
                                            const Loop *loop) {
  std::vector<BasicBlock *> result;
  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    if (loop->contains(block))
      result.push_back(block);
  return result;
}

// 循环Preheader的位置关系
enum class LoopEntryKind : u8 {
  OutsideAnyLoop,  // 不属于任何循环
  InsideOuterBody, // 位于外层循环体
  IsOuterHeader,   // 本身是外层Header
};

LoopEntryKind classifyLoopEntry(const CountedLoopShape &shape,
                                const LoopInfo &loops) {
  Loop *owner = loops.getLoopFor(shape.preheader);
  if (!owner)
    return LoopEntryKind::OutsideAnyLoop;
  return owner->header() == shape.preheader ? LoopEntryKind::IsOuterHeader
                                            : LoopEntryKind::InsideOuterBody;
}

bool preheaderCanRedirectLoopEntry(const CountedLoopShape &shape) {
  Inst *terminator = shape.preheader->terminator();
  if (!terminator)
    return false;
  if (terminator->getOp() == OP_JMP)
    return terminator->getJumpTarget() == shape.header;
  if (terminator->getOp() != OP_BR)
    return false;
  const BrPayload &branch = terminator->getBr();
  return (branch.trueBB == shape.header &&
          (branch.falseBB == shape.exit || branch.falseBB == shape.header)) ||
         (branch.falseBB == shape.header &&
          (branch.trueBB == shape.exit || branch.trueBB == shape.header));
}

bool canFullyUnroll(const CountedLoopShape &shape,
                    const LoopUnrollMetrics &metrics, i32 tripLimit,
                    i32 instructionLimit) {
  const i64 tripCount = shape.constantTripCount;
  if (tripCount <= 0 || tripCount > tripLimit || metrics.hasInternalExit ||
      !shape.loop->children().empty())
    return false;
  return tripCount * static_cast<i64>(metrics.bodyInstructions) <=
         instructionLimit;
}

bool canBranchFreePartiallyUnroll(const CountedLoopShape &shape,
                                  const LoopUnrollMetrics &metrics,
                                  const LoopInfo &loops, i32 factor,
                                  i32 bodyLimit, i32 fullTripLimit) {
  const i64 tripCount = shape.constantTripCount;
  if (factor != 2 || metrics.bodyInstructions > bodyLimit ||
      !(tripCount < 0 || tripCount > fullTripLimit) || !metrics.compact ||
      metrics.hasInternalExit || shape.header == shape.latch ||
      shape.headerPhis.size() != 1 || !shape.backedgeTakenCount ||
      shape.backedgeTakenCount->kind == SCEVExpr::K_UNKNOWN ||
      classifyLoopEntry(shape, loops) != LoopEntryKind::OutsideAnyLoop)
    return false;
  if (shape.backedgeTakenCount->isConstant() &&
      (shape.backedgeTakenCount->cst.v < 0 ||
       shape.backedgeTakenCount->cst.v >
           static_cast<i64>(std::numeric_limits<i32>::max()) - 1))
    return false;
  return preheaderCanRedirectLoopEntry(shape);
}

bool canBranchedPartiallyUnroll(const CountedLoopShape &shape,
                                const LoopUnrollMetrics &metrics, i32 factor,
                                i32 bodyLimit, i32 fullTripLimit) {
  const i64 tripCount = shape.constantTripCount;
  return factor >= 2 && metrics.bodyInstructions <= bodyLimit &&
         (tripCount < 0 || tripCount > fullTripLimit);
}

bool fullyUnroll(Function *function, const CountedLoopShape &shape,
                 i32 tripCount) {
  VERIFY(function && tripCount >= 1);
  IRBuilder builder(function->module, function);
  BasicBlock *header = shape.header;
  BasicBlock *latch = shape.latch;
  BasicBlock *exit = shape.exit;
  const std::vector<BasicBlock *> loopBlocks =
      collectLoopBlocks(function, shape.loop);
  if (loopBlocks.empty())
    return false;

  std::vector<BasicBlock *> originalBlocks;
  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    originalBlocks.push_back(block);

  IterationChain chain =
      cloneLoopIterations(function, shape, loopBlocks, tripCount - 1);
  if (!chain.empty()) {
    VERIFY(computePreds(function));

    // clone helper已镜像每代退出Phi 重接边只移除中间退出列并保留末代列
    VERIFY(CFGEditor::redirectEdge(function, latch, exit, chain.firstHeader(),
                                   {}));
    VERIFY(
        CFGEditor::foldTerminatorToJump(function, latch, chain.firstHeader()));
    for (i32 index = 0; index + 1 < static_cast<i32>(chain.size()); ++index) {
      BasicBlock *clonedLatch = chain.mapAt(index)->translateBlock(latch);
      BasicBlock *nextHeader = chain.mapAt(index + 1)->translateBlock(header);
      VERIFY(
          CFGEditor::redirectEdge(function, clonedLatch, exit, nextHeader, {}));
      VERIFY(
          CFGEditor::foldTerminatorToJump(function, clonedLatch, nextHeader));
    }

    BasicBlock *lastLatch = chain.lastLatch();
    VERIFY(CFGEditor::foldTerminatorToJump(function, lastLatch, exit));

    for (BasicBlock *block : originalBlocks) {
      if (shape.loop->contains(block))
        continue;
      forEachOp(block, [&](Inst *inst) {
        if (block == exit && inst->getOp() == OP_PHI)
          return;
        for (u32 index = 0; index < inst->getOperandCount(); ++index) {
          Inst *operand = inst->getArg(index);
          BasicBlock *definition = operand ? operand->parentBlock() : nullptr;
          if (!definition || !shape.loop->contains(definition))
            continue;
          Inst *translated = chain.lastMap()->translate(operand);
          if (translated != operand)
            inst->setArg(index, translated);
        }
      });
    }
  } else {
    builder.replaceWithJump(latch->terminator(), exit);
  }

  for (const HeaderPhiShape &headerPhi : shape.headerPhis) {
    if (headerPhi.phi->hasUses())
      replaceAllUsesWith(function, headerPhi.phi, headerPhi.preheaderValue);
    VERIFY(headerPhi.phi->eraseFromBlock());
  }
  VERIFY(computePreds(function));
  computeUses(function);
  return true;
}

bool branchFreePartiallyUnroll(Function *function,
                               const CountedLoopShape &shape,
                               const LoopUnrollMetrics &metrics,
                               const SCEV *scev) {
  constexpr i32 factor = 2;
  VERIFY(function && scev);
  IRBuilder builder(function->module, function);

  SCEVExpr *one = scev->getConstant(1, TY_I32);
  SCEVExpr *factorValue = scev->getConstant(factor, TY_I32);
  SCEVExpr *tripCount = scev->getAddExpr(shape.backedgeTakenCount, one);
  // 主循环执行(tripCount / 2) * 2次 至多一次余数迭代由remainder路径承担
  SCEVExpr *mainTripCount =
      scev->getMulExpr(scev->getSDivExpr(tripCount, factorValue), factorValue);
  SCEVExpr *newBound = scev->getAddExpr(
      shape.iv.baseSCEV, scev->getMulExpr(shape.iv.stepSCEV, mainTripCount));

  Inst *preheaderTerminator = shape.preheader->terminator();
  SCEVExpander expander(function, scev);
  Inst *newBoundValue = expander.expandCodeFor(newBound, preheaderTerminator);
  Inst *mainTripCountValue =
      expander.expandCodeFor(mainTripCount, preheaderTerminator);
  if (!newBoundValue || !mainTripCountValue)
    return false;
  const i32 doubledStep = i32MulWrap(static_cast<i32>(shape.iv.step), factor);
  Inst *newStep = builder.iConst(doubledStep);

  BasicBlock *secondPreheader = builder.newBlockAfter(shape.preheader);
  // secondPreheader还要分流主循环与余数路径 不能直接充当严格preheader
  // 单独建立只跳向Header的mainLanding 保持主循环的Dedicated Preheader
  BasicBlock *mainLanding = builder.newBlockAfter(secondPreheader);
  BasicBlock *secondBody = builder.newBlockAfter(shape.header);
  BasicBlock *remainderCheck = builder.newBlockAfter(shape.latch);
  BasicBlock *remainder = builder.newBlockAfter(remainderCheck);
  DeepCopy secondBodyCopy(function);

  builder.setInsertAtEnd(mainLanding);
  builder.emitJump(shape.header);

  const auto cloneHeaderBody = [&](DeepCopy &copier, BasicBlock *destination,
                                   BasicBlock *successor) {
    BlockCloneConfig config;
    config.createBlock = [destination](BasicBlock *, BasicBlock *) {
      return destination;
    };
    config.decideInst = [&](BasicBlock *, Inst *source, bool isPhi) {
      if (isPhi)
        return copier.hasInstMapping(source) ? CloneInstAction::SkipMapped
                                             : CloneInstAction::SkipUnmapped;
      if (isTerminator(source->getOp()))
        return CloneInstAction::SkipUnmapped;
      return copier.hasInstMapping(source) ? CloneInstAction::SkipMapped
                                           : CloneInstAction::Clone;
    };
    // DeepCopy要求跳过源终结符时同时给出克隆块的补尾目标
    config.skippedTerminatorTarget = [successor](Inst *) { return successor; };
    const std::vector<ClonedBlockPair> cloned =
        copier.copyBlocks({shape.header}, config);
    return cloned.size() == 1 && cloned.front().source == shape.header &&
           cloned.front().clone == destination &&
           destination->endsWithTerminator() &&
           destination->terminator()->getOp() == OP_JMP &&
           destination->terminator()->getJumpTarget() == successor;
  };

  builder.setInsertAtEnd(secondBody);
  VERIFY(shape.iv.updateOp == OP_ADD || shape.iv.updateOp == OP_SUB,
         "非仿射IV更新");
  Inst *middle = builder.emit(shape.iv.updateOp, TY_I32, shape.iv.phi,
                              shape.iv.stepConstant);
  for (const HeaderPhiShape &headerPhi : shape.headerPhis) {
    Inst *entry =
        headerPhi.phi == shape.iv.phi
            ? middle
            : (headerPhiKeepsInitialValue(headerPhi) ? headerPhi.preheaderValue
                                                     : headerPhi.latchValue);
    secondBodyCopy.mapInst(headerPhi.phi, entry);
  }
  VERIFY(cloneHeaderBody(secondBodyCopy, secondBody, shape.latch));

  std::vector<CFGEditor::PhiEdgeValue> latchValues;
  for (Inst *phi = shape.latch->firstPhi(); phi; phi = phi->next()) {
    Inst *value = CFGEditor::getPhiIncomingValue(phi, shape.header);
    if (value)
      latchValues.push_back({phi, secondBodyCopy.translate(value)});
  }
  VERIFY(CFGEditor::moveAndSetPhiEdgeValues(function, shape.latch, shape.header,
                                            secondBody, latchValues));
  builder.replaceWithJump(shape.header->terminator(), secondBody);

  shape.iv.stepInst->setArg(static_cast<u32>(shape.iv.stepConstantArgIndex),
                            newStep);
  shape.latchTest.comparison->setArg(
      static_cast<u32>(shape.latchTest.boundArgIndex), newBoundValue);

  std::vector<CFGEditor::PhiEdgeValue> headerLatchValues;
  for (const HeaderPhiShape &headerPhi : shape.headerPhis) {
    if (headerPhi.phi == shape.iv.phi)
      continue;
    Inst *lastValue = headerPhiKeepsInitialValue(headerPhi)
                          ? headerPhi.preheaderValue
                          : headerPhi.latchValue;
    headerLatchValues.push_back(
        {headerPhi.phi, secondBodyCopy.translate(lastValue)});
  }
  if (!headerLatchValues.empty())
    VERIFY(CFGEditor::setPhiEdgeValues(function, shape.header, shape.latch,
                                       headerLatchValues));

  builder.setInsertAtEnd(secondPreheader);
  Inst *hasMainIterations =
      builder.emit(OP_GT, TY_I1, mainTripCountValue, builder.iConst(0));
  // 有成对迭代时经专用入口进入主循环 否则直接执行至多一次余数迭代
  builder.emitBranch(hasMainIterations, mainLanding, remainder);
  // Header的外部入口已从旧preheader迁至mainLanding Phi边必须同步迁移
  VERIFY(CFGEditor::moveAndSetPhiEdgeValues(function, shape.header,
                                            shape.preheader, mainLanding));

  Inst *entryTerminator = shape.preheader->terminator();
  if (entryTerminator->getOp() == OP_JMP) {
    VERIFY(CFGEditor::rewriteJumpTarget(shape.preheader, secondPreheader));
  } else {
    VERIFY(entryTerminator->getOp() == OP_BR);
    const bool trueEnters = entryTerminator->getBr().trueBB == shape.header;
    const bool falseEnters = entryTerminator->getBr().falseBB == shape.header;
    if (trueEnters)
      VERIFY(
          CFGEditor::rewriteBranchSlot(shape.preheader, true, secondPreheader));
    if (falseEnters)
      VERIFY(CFGEditor::rewriteBranchSlot(shape.preheader, false,
                                          secondPreheader));
    VERIFY(trueEnters || falseEnters);
  }

  std::vector<std::pair<Inst *, Inst *>> oldExitValues;
  for (Inst *phi = shape.exit->firstPhi(); phi; phi = phi->next()) {
    Inst *value = CFGEditor::getPhiIncomingValue(phi, shape.latch);
    if (value)
      oldExitValues.push_back({phi, value});
  }

  // 主循环退出先到remainderCheck该块是主循环的直接exit
  // 所有流向余数或旧exit的循环内值都必须先在这里形成LCSSA闭包
  VERIFY(CFGEditor::rewriteBranchSlot(
      shape.latch, !shape.latchTest.continueOnTrue, remainderCheck));
  VERIFY(
      CFGEditor::addPhiEdgeValues(function, remainderCheck, shape.latch, {}));
  std::vector<std::pair<Inst *, Inst *>> exitClosures;
  const auto closeAtRemainderCheck = [&](Inst *value) -> Inst * {
    VERIFY(value && !isVoid(value->getType()));
    for (const auto &[source, closure] : exitClosures)
      if (source == value)
        return closure;
    Inst *closure = builder.emitPhi(value->getType(), remainderCheck,
                                    builder.makeUndef(value->getType()));
    VERIFY(CFGEditor::setPhiEdgeValues(function, remainderCheck, shape.latch,
                                       {{closure, value}}));
    exitClosures.push_back({value, closure});
    return closure;
  };

  std::vector<Inst *> mainExitClosures(shape.headerPhis.size(), nullptr);
  for (usize index = 0; index < shape.headerPhis.size(); ++index) {
    const HeaderPhiShape &headerPhi = shape.headerPhis[index];
    Inst *lastValue = headerPhiKeepsInitialValue(headerPhi)
                          ? headerPhi.preheaderValue
                          : headerPhi.latchValue;
    Inst *mainExitValue = headerPhi.phi == shape.iv.phi
                              ? shape.iv.stepInst
                              : secondBodyCopy.translate(lastValue);
    mainExitClosures[index] = closeAtRemainderCheck(mainExitValue);
  }

  std::vector<CFGEditor::PhiEdgeValue> noRemainderValues;
  for (const auto &[phi, value] : oldExitValues)
    noRemainderValues.push_back(
        {phi, closeAtRemainderCheck(secondBodyCopy.translate(value))});

  builder.setInsertAtEnd(remainderCheck);
  Inst *closedMainIV =
      mainExitClosures[static_cast<usize>(metrics.controlIVIndex)];
  Inst *remainderCondition =
      shape.latchTest.testedIsLHS
          ? builder.emit(shape.latchTest.comparison->getOp(), TY_I1,
                         closedMainIV, shape.latchTest.boundValue)
          : builder.emit(shape.latchTest.comparison->getOp(), TY_I1,
                         shape.latchTest.boundValue, closedMainIV);
  builder.emitBranch(remainderCondition, remainder, shape.exit);
  VERIFY(CFGEditor::moveAndSetPhiEdgeValues(function, shape.exit, shape.latch,
                                            remainderCheck, noRemainderValues));

  VERIFY(CFGEditor::addPhiEdgeValues(function, remainder, secondPreheader, {}));
  VERIFY(CFGEditor::addPhiEdgeValues(function, remainder, remainderCheck, {}));

  DeepCopy remainderCopy(function);
  std::vector<Inst *> remainderPhis(shape.headerPhis.size(), nullptr);
  for (usize index = 0; index < shape.headerPhis.size(); ++index) {
    const HeaderPhiShape &headerPhi = shape.headerPhis[index];
    Inst *phi = builder.emitPhi(headerPhi.phi->getType(), remainder,
                                builder.makeUndef(headerPhi.phi->getType()));
    VERIFY(CFGEditor::setPhiEdgeValues(function, remainder, secondPreheader,
                                       {{phi, headerPhi.preheaderValue}}));
    VERIFY(CFGEditor::setPhiEdgeValues(function, remainder, remainderCheck,
                                       {{phi, mainExitClosures[index]}}));
    remainderPhis[index] = phi;
    remainderCopy.mapInst(headerPhi.phi, phi);
  }

  VERIFY(cloneHeaderBody(remainderCopy, remainder, shape.exit));
  builder.setInsertBefore(remainder->terminator());
  Inst *remainderIV = remainderPhis[static_cast<usize>(metrics.controlIVIndex)];
  Inst *remainderNext = builder.emit(shape.iv.updateOp, TY_I32, remainderIV,
                                     shape.iv.stepConstant);
  remainderCopy.mapInst(shape.iv.stepInst, remainderNext);

  std::vector<CFGEditor::PhiEdgeValue> remainderExitValues;
  for (const auto &[phi, value] : oldExitValues)
    remainderExitValues.push_back({phi, remainderCopy.translate(value)});
  VERIFY(CFGEditor::addPhiEdgeValues(function, shape.exit, remainder,
                                     remainderExitValues));

  VERIFY(computePreds(function));
  computeUses(function);
  return true;
}

bool branchedPartiallyUnroll(Function *function, const CountedLoopShape &shape,
                             i32 factor) {
  VERIFY(function && factor >= 2);
  BasicBlock *header = shape.header;
  BasicBlock *latch = shape.latch;
  const std::vector<BasicBlock *> loopBlocks =
      collectLoopBlocks(function, shape.loop);
  if (loopBlocks.empty())
    return false;

  IterationChain chain =
      cloneLoopIterations(function, shape, loopBlocks, factor - 1);
  VERIFY(!chain.empty());
  // 仅串接各代continue边 退出边和对应Phi值由clone helper原样保留
  VERIFY(CFGEditor::rewriteBranchSlot(latch, shape.latchTest.continueOnTrue,
                                      chain.firstHeader()));
  for (i32 index = 0; index + 1 < static_cast<i32>(chain.size()); ++index) {
    BasicBlock *clonedLatch = chain.mapAt(index)->translateBlock(latch);
    BasicBlock *nextHeader = chain.mapAt(index + 1)->translateBlock(header);
    VERIFY(CFGEditor::rewriteBranchSlot(
        clonedLatch, shape.latchTest.continueOnTrue, nextHeader));
  }

  BasicBlock *lastLatch = chain.lastLatch();
  VERIFY(CFGEditor::rewriteBranchSlot(lastLatch, shape.latchTest.continueOnTrue,
                                      header));
  std::vector<CFGEditor::PhiEdgeValue> headerValues;
  for (Inst *phi = header->firstPhi(); phi; phi = phi->next()) {
    Inst *value = CFGEditor::getPhiIncomingValue(phi, latch);
    if (value)
      headerValues.push_back({phi, chain.lastMap()->translate(value)});
  }
  VERIFY(CFGEditor::moveAndSetPhiEdgeValues(function, header, latch, lastLatch,
                                            headerValues));

  VERIFY(computePreds(function));
  computeUses(function);
  return true;
}

bool isStaticMaterializationCandidate(const CountedLoopShape &shape) {
  const auto smallSourceGlobal = [](Global *global) {
    return global && global->origin == Global::GlobalOrigin::SourceGlobal &&
           !global->isConst &&
           (global->type == TY_I32 || global->type == TY_F32) &&
           global->totalSizeBytes <= 4096;
  };
  const auto smallLocalArray = [](Inst *root) {
    if (!root || root->getOp() != OP_ALLOCA)
      return false;
    const MemPayload &memory = root->getMem();
    return memory.paramIdx < 0 &&
           (memory.elementType == TY_I32 || memory.elementType == TY_F32) &&
           memory.totalSizeBytes > 0 && memory.totalSizeBytes <= 4096;
  };

  std::function<bool(Inst *, i32)> valueUsesOnlyIVAndConstants =
      [&](Inst *value, i32 depth) {
        if (!value || depth > 32)
          return false;
        if (value == shape.iv.phi)
          return true;
        const OpCode op = value->getOp();
        if (op == OP_ICONST || op == OP_FCONST)
          return true;
        if (op == OP_NEG || op == OP_FNEG || op == OP_ZEXT || op == OP_I2F ||
            op == OP_F2I)
          return valueUsesOnlyIVAndConstants(value->getArg(0), depth + 1);
        if (!isBinaryArithmetic(op) && !isCompare(op))
          return false;
        for (u32 index = 0; index < value->getOperandCount(); ++index)
          if (!valueUsesOnlyIVAndConstants(value->getArg(index), depth + 1))
            return false;
        return true;
      };

  std::function<Inst *(Inst *, i32)> addressRoot = [&](Inst *address,
                                                       i32 depth) -> Inst * {
    if (!address || depth > 32)
      return nullptr;
    if (address->getOp() == OP_GETGLOBAL || address->getOp() == OP_ALLOCA)
      return address;
    if (address->getOp() == OP_GETPTR) {
      if (!valueUsesOnlyIVAndConstants(address->getArg(1), 0))
        return nullptr;
      return addressRoot(address->getArg(0), depth + 1);
    }
    if (address->getOp() != OP_ARRAYIDX)
      return nullptr;
    for (u32 index = 1; index < address->getOperandCount(); ++index)
      if (!valueUsesOnlyIVAndConstants(address->getArg(index), 0))
        return nullptr;
    return addressRoot(address->getArg(0), depth + 1);
  };

  Inst *localRoot = nullptr;
  bool localCandidate = true;
  bool sawLocalAccess = false;
  bool sawGlobalStore = false;
  for (BasicBlock *block : shape.loop->blocks()) {
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if (inst->getOp() == OP_CALL || inst->getOp() == MOP_CALL)
        return false;
      if (inst->getOp() != OP_LOAD && inst->getOp() != OP_STORE)
        continue;
      Inst *root = addressRoot(inst->getArg(0), 0);
      const bool storeValueIsStatic =
          inst->getOp() != OP_STORE ||
          valueUsesOnlyIVAndConstants(inst->getArg(1), 0);
      if (inst->getOp() == OP_STORE && storeValueIsStatic && root &&
          root->getOp() == OP_GETGLOBAL && smallSourceGlobal(root->getGlobal()))
        sawGlobalStore = true;
      if (!smallLocalArray(root) || !storeValueIsStatic ||
          (localRoot && localRoot != root)) {
        localCandidate = false;
        continue;
      }
      localRoot = root;
      sawLocalAccess = true;
    }
  }
  return sawGlobalStore || (localCandidate && sawLocalAccess);
}

i32 saturatingGrowth(i64 value) noexcept {
  if (value <= 0)
    return 0;
  return value > std::numeric_limits<i32>::max()
             ? std::numeric_limits<i32>::max()
             : static_cast<i32>(value);
}

i32 runLoopUnroll(Function *function, PassContext &context,
                  i32 maxFullTripCount, i32 maxFullInstructions,
                  i32 partialFactor, i32 maxPartialBodyInstructions,
                  i32 maxFunctionInstructions) {
  FunctionAnalysisManager &analyses = context.functionAnalyses();
  PressureOracle oracle(function->module);
  const GlobalSummaryResult &summary =
      context.get<GlobalSummaryAnalysis>(function->module).result;
  const bool isExecuteOnce = summary.execOf(function).isOnce();
  i32 transformed = 0;

  while (true) {
    const LoopInfo &loops = analyses.getResult<LoopInfoAnalysis>(function).info;
    const SCEV &scev = analyses.getResult<SCEVAnalysis>(function).info;
    const LoopShapeInfo &shapes =
        analyses.getResult<LoopShapeAnalysis>(function).info;

    std::vector<Loop *> worklist;
    const std::function<void(Loop *)> collectPostorder = [&](Loop *loop) {
      for (Loop *child : loop->children())
        collectPostorder(child);
      worklist.push_back(loop);
    };
    for (Loop *loop : loops.topLevelLoops())
      collectPostorder(loop);

    bool changed = false;
    for (Loop *loop : worklist) {
      LoopShapeQuery query;
      query.requireLatchContinueOnTrue = true;
      query.requireLatchCompareInLatch = true;
      std::optional<CountedLoopShape> candidate =
          shapes.getCountedLoop(loop, query);
      if (!candidate)
        continue;
      const CountedLoopShape &shape = *candidate;
      const LoopUnrollMetrics metrics = computeMetrics(shape);

      i32 fullTripLimit = maxFullTripCount;
      i32 fullInstructionLimit = maxFullInstructions;
      if (isExecuteOnce && isStaticMaterializationCandidate(shape)) {
        fullTripLimit = std::max(fullTripLimit, i32{256});
        fullInstructionLimit = std::max(fullInstructionLimit, i32{8192});
      }

      bool applied = false;
      i32 addedInstructions = 0;
      if (canFullyUnroll(shape, metrics, fullTripLimit, fullInstructionLimit)) {
        addedInstructions =
            saturatingGrowth((shape.constantTripCount - 1) *
                             static_cast<i64>(metrics.bodyInstructions));
        const GrowthHint growth = oracle.hint(function, addedInstructions);
        if (growth.functionAfter > maxFunctionInstructions)
          continue;
        if (!isExecuteOnce && (growth.overall == PressureLevel::High ||
                               growth.overall == PressureLevel::UnknownLarge))
          continue;
        applied = fullyUnroll(function, shape,
                              static_cast<i32>(shape.constantTripCount));
      } else if (canBranchedPartiallyUnroll(shape, metrics, partialFactor,
                                            maxPartialBodyInstructions,
                                            fullTripLimit)) {
        addedInstructions =
            saturatingGrowth(static_cast<i64>(partialFactor - 1) *
                             static_cast<i64>(metrics.bodyInstructions));
        const GrowthHint growth = oracle.hint(function, addedInstructions);
        if (growth.functionAfter > maxFunctionInstructions ||
            growth.overall == PressureLevel::High ||
            growth.overall == PressureLevel::UnknownLarge)
          continue;

        if (canBranchFreePartiallyUnroll(shape, metrics, loops, partialFactor,
                                         maxPartialBodyInstructions,
                                         fullTripLimit))
          applied = branchFreePartiallyUnroll(function, shape, metrics, &scev);
        if (!applied)
          applied = branchedPartiallyUnroll(function, shape, partialFactor);
      }

      if (!applied)
        continue;
      oracle.recordApplied(function, addedInstructions);
      analyses.clear(function);
      ++transformed;
      changed = true;
      break;
    }
    if (!changed)
      break;
  }
  return transformed;
}

} // namespace

LoopUnrollPass::LoopUnrollPass(i32 maxFullTripCount, i32 maxFullInstructions,
                               i32 partialFactor,
                               i32 maxPartialBodyInstructions,
                               i32 maxFunctionInstructions) noexcept
    : maxFullTripCount_(std::max(maxFullTripCount, i32{0})),
      maxFullInstructions_(std::max(maxFullInstructions, i32{0})),
      partialFactor_(std::max(partialFactor, i32{2})),
      maxPartialBodyInstructions_(std::max(maxPartialBodyInstructions, i32{0})),
      maxFunctionInstructions_(std::max(maxFunctionInstructions, i32{0})) {}

std::string_view LoopUnrollPass::name() const noexcept { return "loop-unroll"; }

PassResult LoopUnrollPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first ||
      maxFunctionInstructions_ == 0)
    return PassResult::noChange();
  if (!computePreds(function))
    return PassResult::noChange();
  computeUses(function);
  return runLoopUnroll(function, context, maxFullTripCount_,
                       maxFullInstructions_, partialFactor_,
                       maxPartialBodyInstructions_,
                       maxFunctionInstructions_) > 0
             ? PassResult::changedIR()
             : PassResult::noChange();
}

} // namespace svm::ir
