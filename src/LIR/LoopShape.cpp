#include "LoopShape.h"
#include "Analysis.h"
#include "Utils.h"

#include <unordered_set>
#include <utility>

namespace svm::ir {
namespace {

void setReject(LoopShapeReject &reject, const char *reason) noexcept {
  reject.stableReason = reason;
}

bool detectMaterializedUpdate(Inst *phi, Inst *next, BasicBlock *latch,
                              ControlIVShape &iv) {
  if (!phi || !next || next->parentBlock() != latch)
    return false;
  const OpCode op = next->getOp();
  if (op != OP_ADD && op != OP_SUB)
    return false;

  Inst *constant = nullptr;
  i32 constantIndex = -1;
  if (op == OP_ADD) {
    if (next->getArg(0) == phi && next->getArg(1)->getOp() == OP_ICONST) {
      constant = next->getArg(1);
      constantIndex = 1;
    } else if (next->getArg(1) == phi &&
               next->getArg(0)->getOp() == OP_ICONST) {
      constant = next->getArg(0);
      constantIndex = 0;
    }
  } else if (next->getArg(0) == phi && next->getArg(1)->getOp() == OP_ICONST) {
    constant = next->getArg(1);
    constantIndex = 1;
  }
  if (!constant)
    return false;

  const i64 materializedStep = op == OP_ADD
                                   ? static_cast<i64>(constant->getImm())
                                   : -static_cast<i64>(constant->getImm());
  if (materializedStep != iv.step)
    return false;

  iv.stepInst = next;
  iv.stepConstant = constant;
  iv.stepConstantArgIndex = constantIndex;
  iv.updateOp = op;
  return true;
}

} // namespace

std::optional<NormalizedLoopPredicate>
analyzeLoopPredicate(const SCEV *scev, const Loop *loop, Inst *branch,
                     SCEVExpr *wanted, BasicBlock *continueTarget,
                     BasicBlock *expectedExit, LoopShapeReject *reject) {
  const auto fail =
      [&](const char *reason) -> std::optional<NormalizedLoopPredicate> {
    if (reject)
      reject->stableReason = reason;
    return std::nullopt;
  };

  if (!scev || !loop)
    return fail("SCEV或循环无效");
  if (!branch || branch->getOp() != OP_BR || branch->getOperandCount() != 1)
    return fail("循环没有分支");
  if (!continueTarget)
    return fail("循环分支没有继续目标");

  const bool trueContinues = branch->getBr().trueBB == continueTarget;
  const bool falseContinues = branch->getBr().falseBB == continueTarget;
  if (trueContinues == falseContinues)
    return fail("循环分支目标错误");
  BasicBlock *exitTarget =
      trueContinues ? branch->getBr().falseBB : branch->getBr().trueBB;
  if (expectedExit && exitTarget != expectedExit)
    return fail("循环真假分支exit目标不匹配");

  Inst *comparison = branch->getArg(0);
  if (!comparison || !isIntCompare(comparison->getOp()) ||
      comparison->getOperandCount() != 2)
    return fail("循环谓词非整数比较");
  SCEVExpr *left = scev->getSCEV(comparison->getArg(0));
  SCEVExpr *right = scev->getSCEV(comparison->getArg(1));
  if (!left || !right)
    return fail("循环谓词比较操作数的SCEV缺失");

  bool testedIsLHS = true;
  SCEVExpr *tested = nullptr;
  Inst *boundValue = nullptr;
  SCEVExpr *bound = nullptr;
  const auto selectSide = [&](bool leftIsTested) {
    testedIsLHS = leftIsTested;
    tested = leftIsTested ? left : right;
    boundValue = comparison->getArg(leftIsTested ? 1U : 0U);
    bound = leftIsTested ? right : left;
  };

  // 指定递推时精确匹配 否则只接受一侧递推另一侧循环不变的比较
  if (wanted) {
    if (left->structurallyEquals(wanted) && right->isLoopInvariant(loop))
      selectSide(true);
    else if (right->structurallyEquals(wanted) && left->isLoopInvariant(loop))
      selectSide(false);
    else
      return fail("循环谓词指定递推侧不匹配");
  } else if (left->containsAddRecOf(loop) && right->isLoopInvariant(loop)) {
    selectSide(true);
  } else if (right->containsAddRecOf(loop) && left->isLoopInvariant(loop)) {
    selectSide(false);
  } else {
    return fail("循环谓词递推与边界不匹配");
  }

  OpCode predicate = testedIsLHS ? comparison->getOp()
                                 : swapCompareOperands(comparison->getOp());
  if (!trueContinues)
    predicate = invertIntCompare(predicate);
  if (!isIntCompare(predicate))
    return fail("循环谓词比较类型不支持");

  NormalizedLoopPredicate result;
  result.comparison = comparison;
  result.testedSCEV = tested;
  result.boundValue = boundValue;
  result.boundSCEV = bound;
  result.canonicalPredicate = predicate;
  result.testedIsLHS = testedIsLHS;
  result.continueOnTrue = trueContinues;
  result.boundArgIndex = testedIsLHS ? 1 : 0;
  result.exitTarget = exitTarget;
  if (reject)
    reject->stableReason = "ok";
  return result;
}

void LoopShapeInfo::build(const SCEV *scev, const LoopInfo *loopInfo) noexcept {
  scev_ = scev;
  loopInfo_ = loopInfo;
  byLoop_.clear();
  phiTransfers_.clear();
}

bool LoopShapeInfo::buildBaseShape(Loop *loop, CountedLoopShape &shape,
                                   LoopShapeReject &reject) const {
  const auto fail = [&](const char *reason) {
    setReject(reject, reason);
    return false;
  };

  if (!loop || !loop->header() || !scev_)
    return fail("循环或header无效");
  if (loop->latches().size() != 1)
    return fail("循环存在多个latch");
  if (loop->exitingBlocks().size() == 0)
    return fail("循环存在多个exiting");

  shape.loop = loop;
  shape.header = loop->header();
  shape.latch = loop->latches().front();
  shape.preheader = loop->getPreheader();
  if (!shape.preheader)
    return fail("循环缺少Preheader");

  std::unordered_set<BasicBlock *> exits(loop->exitBlocks().begin(),
                                         loop->exitBlocks().end());
  if (exits.empty())
    return fail("循环没有exit");
  if (exits.size() != 1)
    return fail("循环存在多个exit");
  BasicBlock *uniqueExit = *exits.begin();

  bool sawHeaderPhi = false;
  bool headerPhiIncomingMismatch = false;
  forEachPhi(shape.header, [&](Inst *phi) {
    sawHeaderPhi = true;
    if (phi->getOperandCount() != 2) {
      headerPhiIncomingMismatch = true;
      return;
    }

    HeaderPhiShape current;
    current.phi = phi;
    bool seenPreheader = false;
    bool seenLatch = false;
    for (u32 index = 0; index < phi->getOperandCount(); ++index) {
      BasicBlock *incoming = phi->getIncomingBlock(index);
      if (incoming == shape.preheader) {
        if (seenPreheader) {
          headerPhiIncomingMismatch = true;
          return;
        }
        seenPreheader = true;
        current.preheaderValue = phi->getArg(index);
      } else if (incoming == shape.latch) {
        if (seenLatch) {
          headerPhiIncomingMismatch = true;
          return;
        }
        seenLatch = true;
        current.latchValue = phi->getArg(index);
      } else {
        headerPhiIncomingMismatch = true;
        return;
      }
    }
    if (!seenPreheader || !seenLatch) {
      headerPhiIncomingMismatch = true;
      return;
    }
    shape.headerPhis.push_back(current);
  });
  if (!sawHeaderPhi)
    return fail("header没有Phi");
  if (headerPhiIncomingMismatch)
    return fail("header Phi来边不匹配");

  if (!shape.latch || !shape.latch->endsWithTerminator() ||
      shape.latch->terminator()->getOp() != OP_BR)
    return fail("latch终结指令不是分支");

  struct Candidate {
    usize phiIndex = 0;                // Header Phi索引
    SCEVExpr *addRec = nullptr;        // 候选递推
    NormalizedLoopPredicate predicate; // 候选latch条件
  };
  std::vector<Candidate> candidates;
  // 控制IV由latch实际比较的post-increment值决定 避免猜测任意AddRec
  for (usize index = 0; index < shape.headerPhis.size(); ++index) {
    HeaderPhiShape &phi = shape.headerPhis[index];
    SCEVExpr *addRec = scev_->getSCEV(phi.phi);
    if (!addRec || addRec->kind != SCEVExpr::K_ADDREC ||
        addRec->addRec.loop != loop || !addRec->addRec.step ||
        addRec->addRec.step->isZero())
      continue;
    SCEVExpr *postIncrement = scev_->getSCEV(phi.latchValue);
    auto predicate =
        analyzeLoopPredicate(scev_, loop, shape.latch->terminator(),
                             postIncrement, shape.header, uniqueExit);
    if (predicate)
      candidates.push_back({index, addRec, *predicate});
  }
  if (candidates.empty())
    return fail("无法识别latch分支谓词");
  if (candidates.size() != 1)
    return fail("检测到多个控制IV");

  const Candidate &candidate = candidates.front();
  HeaderPhiShape &controlPhi = shape.headerPhis[candidate.phiIndex];
  controlPhi.isControlIV = true;
  shape.latchTest = candidate.predicate;
  shape.exit = candidate.predicate.exitTarget;

  shape.iv.phi = controlPhi.phi;
  shape.iv.baseSCEV = candidate.addRec->addRec.base;
  shape.iv.stepSCEV = candidate.addRec->addRec.step;
  if (!shape.iv.stepSCEV || !shape.iv.stepSCEV->isConstant())
    return fail("IV步长不是常量");
  shape.iv.step = shape.iv.stepSCEV->cst.v;
  if (shape.iv.step == 0)
    return fail("IV步长为零");
  if (!detectMaterializedUpdate(shape.iv.phi, controlPhi.latchValue,
                                shape.latch, shape.iv))
    return fail("无更新指令或更新指令不在latch");

  shape.backedgeTakenCount = scev_->getBackedgeTakenCount(loop);
  shape.constantTripCount = scev_->getConstantTripCount(loop);
  setReject(reject, "ok");
  return true;
}

const LoopShapeInfo::CacheEntry &LoopShapeInfo::baseShapeOf(Loop *loop) const {
  if (const auto found = byLoop_.find(loop); found != byLoop_.end())
    return found->second;

  CacheEntry entry;
  CountedLoopShape shape;
  if (buildBaseShape(loop, shape, entry.reject))
    entry.shape = std::move(shape);
  return byLoop_.emplace(loop, std::move(entry)).first->second;
}

std::optional<CountedLoopShape>
LoopShapeInfo::getCountedLoop(Loop *loop, const LoopShapeQuery &query,
                              LoopShapeReject *reject) const {
  LoopShapeReject local;
  LoopShapeReject &resultReject = reject ? *reject : local;
  resultReject = LoopShapeReject{};

  const CacheEntry &base = baseShapeOf(loop);
  if (!base.shape) {
    resultReject = base.reject;
    return std::nullopt;
  }
  CountedLoopShape result = *base.shape;
  if (query.requireLatchContinueOnTrue && !result.latchTest.continueOnTrue) {
    setReject(resultReject, "latch继续条件不为true分支");
    return std::nullopt;
  }
  if (query.requireLatchCompareInLatch &&
      result.latchTest.comparison->parentBlock() != result.latch) {
    setReject(resultReject, "latch比较指令不在latch中");
    return std::nullopt;
  }
  setReject(resultReject, "ok");
  return result;
}

std::optional<HeaderPhiTransferInfo>
LoopShapeInfo::getHeaderPhiTransfer(Inst *phi) const {
  if (const auto found = phiTransfers_.find(phi); found != phiTransfers_.end())
    return found->second;

  const auto memo = [&](std::optional<HeaderPhiTransferInfo> result) {
    phiTransfers_.emplace(phi, result);
    return result;
  };
  if (!phi || phi->getOp() != OP_PHI || phi->getType() != TY_I32 || !scev_ ||
      !loopInfo_)
    return memo(std::nullopt);

  BasicBlock *header = phi->parentBlock();
  Loop *loop = loopInfo_->getLoopFor(header);
  if (!loop || loop->header() != header)
    return memo(std::nullopt);

  HeaderPhiTransferInfo info;
  info.loop = loop;
  info.header = header;
  info.phi = phi;
  SCEVExpr *phiSCEV = scev_->getSCEV(phi);
  SCEVExpr *negativePhi =
      scev_->getMulExpr(phiSCEV, scev_->getConstant(-1, phiSCEV->ty));

  const auto classifyIncoming = [&](BasicBlock *predecessor,
                                    Inst *incomingValue) {
    HeaderPhiIncomingTransfer transfer;
    transfer.predecessor = predecessor;
    transfer.incomingValue = incomingValue;
    SCEVExpr *delta =
        scev_->getAddExpr(scev_->getSCEV(incomingValue), negativePhi);
    if (delta->isConstant()) {
      transfer.kind = HeaderPhiIncomingKind::SelfDelta;
      transfer.delta = delta->cst.v;
    }
    return transfer;
  };

  // incoming-phi消去共同递推后若为常量 即得到该CFG边的局部增量
  for (u32 index = 0; index < phi->getOperandCount(); ++index) {
    BasicBlock *predecessor = phi->getIncomingBlock(index);
    Inst *incomingValue = phi->getArg(index);
    if (!predecessor || !incomingValue)
      return memo(std::nullopt);

    HeaderPhiIncomingTransfer transfer =
        classifyIncoming(predecessor, incomingValue);
    info.hasNonzeroSelfDelta |=
        transfer.kind == HeaderPhiIncomingKind::SelfDelta &&
        transfer.delta != 0;

    // 唯一Latch会用中间Phi合并原回边值
    // 仅下钻这一层 便可保留条件自增与不变边的局部递推事实
    if (transfer.kind == HeaderPhiIncomingKind::Reset &&
        loop->latches().size() == 1 && predecessor == loop->latches().front() &&
        incomingValue->getOp() == OP_PHI &&
        incomingValue->parentBlock() == predecessor &&
        incomingValue->getOperandCount() ==
            predecessor->getPredecessorCount()) {
      bool validMerge = true;
      bool hasMergedSelfDelta = false;
      for (u32 mergedIndex = 0; mergedIndex < incomingValue->getOperandCount();
           ++mergedIndex) {
        BasicBlock *mergedPredecessor =
            incomingValue->getIncomingBlock(mergedIndex);
        Inst *mergedValue = incomingValue->getArg(mergedIndex);
        if (!mergedPredecessor || !mergedValue ||
            !loop->contains(mergedPredecessor)) {
          validMerge = false;
          break;
        }
        HeaderPhiIncomingTransfer merged =
            classifyIncoming(mergedPredecessor, mergedValue);
        hasMergedSelfDelta |= merged.kind == HeaderPhiIncomingKind::SelfDelta &&
                              merged.delta != 0;
        transfer.mergedIncoming.push_back(std::move(merged));
      }
      if (!validMerge || !hasMergedSelfDelta)
        transfer.mergedIncoming.clear();
      else
        info.hasNonzeroSelfDelta = true;
    }
    info.incoming.push_back(transfer);
  }
  if (!info.hasNonzeroSelfDelta)
    return memo(std::nullopt);
  return memo(std::move(info));
}

void LoopShapeAnalysis::run(Function *function,
                            FunctionAnalysisManager &manager) {
  VERIFY(function && function->phase == IRPhase::LIR);
  const SCEV &scev = manager.getResult<SCEVAnalysis>(function).info;
  const LoopInfo &loopInfo = manager.getResult<LoopInfoAnalysis>(function).info;
  info.build(&scev, &loopInfo);
}

bool LoopShapeAnalysis::invalidate(Function *function,
                                   const PreservedAnalyses &preserved) const {
  UNUSED(function);
  if (!preserved.preserves(ID()) || !preserved.preservesSSAForm() ||
      !preserved.preserves<SCEVAnalysis>())
    return true;
  return !(preserved.preservesCFGAnalyses() ||
           (preserved.preserves<DomAnalysis>() &&
            preserved.preserves<LoopInfoAnalysis>()));
}

} // namespace svm::ir
