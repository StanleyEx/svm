#include "Analysis.h"
#include "LIRPass.h"
#include "LSRAddress.h"
#include "LoopShape.h"
#include "Utils.h"

#include <algorithm>
#include <map>
#include <tuple>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

using namespace lsr_address;

bool fitsTargetMemoryOffset(i64 value) noexcept {
  return value >= -2048 && value <= 2047;
}

i32 useCount(Inst *inst) noexcept {
  i32 count = 0;
  for (const Use *use = inst ? inst->uses() : nullptr; use; use = use->next)
    ++count;
  return count;
}

Inst *emitScaledOffset(IRBuilder &builder, Inst *scalar, i64 coefficient,
                       i64 constant, Inst *insertBefore) {
  if (!scalar || !insertBefore || !fitsI32(coefficient) || !fitsI32(constant))
    return nullptr;
  builder.setInsertBefore(insertBefore);
  Inst *offset = scalar;
  if (coefficient != 1)
    offset = builder.emit(OP_MUL, TY_I32, scalar,
                          builder.iConst(static_cast<i32>(coefficient)));
  if (constant != 0) {
    builder.setInsertBefore(insertBefore);
    offset = builder.emit(OP_ADD, TY_I32, offset,
                          builder.iConst(static_cast<i32>(constant)));
  }
  return offset;
}

Inst *emitAddressForScalar(IRBuilder &builder, Inst *root, Inst *scalar,
                           i64 coefficient, i64 constant, Inst *insertBefore) {
  Inst *offset =
      emitScaledOffset(builder, scalar, coefficient, constant, insertBefore);
  if (!root || !offset)
    return nullptr;
  builder.setInsertBefore(insertBefore);
  Inst *pointer = builder.emitGetPtr(root, offset);
  pointer->setStride(1);
  return pointer;
}

Inst *emitPointerStep(IRBuilder &builder, Inst *pointer, i64 step,
                      Inst *insertBefore) {
  if (!pointer || !insertBefore || !fitsI32(step))
    return nullptr;
  if (step == 0)
    return pointer;
  builder.setInsertBefore(insertBefore);
  Inst *next =
      builder.emitGetPtr(pointer, builder.iConst(static_cast<i32>(step)));
  next->setStride(1);
  return next;
}

struct LSRUse {
  AddressEvolution evolution; // 分类器提供的地址事实
  i32 useCount = 0;           // 原 GETPTR 使用次数
};

struct CanonicalGroup {
  Loop *loop = nullptr;       // 递推所属循环
  i64 step = 0;               // 共同字节步长
  std::vector<LSRUse *> uses; // 同 root/step 候选
};

struct EdgeGroup {
  Loop *loop = nullptr;       // Phi 所属循环
  Inst *root = nullptr;       // 共同指针根
  Inst *phi = nullptr;        // 共同标量 Phi
  i64 coefficient = 0;        // 共同字节系数
  std::vector<LSRUse *> uses; // 不同常量偏移候选
};

struct RewritePlan {
  std::vector<LSRUse> uses;                    // 全部已分类候选
  std::unordered_set<Inst *> originalGetPtrs;  // 原 GETPTR 集合
  std::vector<CanonicalGroup> canonicalGroups; // 标准递推组
  std::vector<EdgeGroup> edgeGroups;           // 边局部递推组
};

struct EdgeRewritePlan {
  HeaderPhiTransferInfo transfer;              // 逐边标量传递事实
  i64 minimum = 0;                             // 代表地址常量
  std::vector<std::pair<LSRUse *, i64>> lanes; // 可复用的常量偏移
};

struct CanonicalReuseQuery {
  Loop *loop = nullptr;     // 目标循环
  Inst *root = nullptr;     // 指针根
  i64 step = 0;             // 地址步长
  SCEVExpr *base = nullptr; // 第零次迭代地址
};

using CFGEdge = std::pair<BasicBlock *, BasicBlock *>;

constexpr i32 kMaxRecurrencesPerLoop = 8;
constexpr i32 kMaxEdgeRecurrencesPerLoop = 8;
constexpr i32 kMaxRowRecurrencesPerOuter = 8;

bool shouldBuildLanes(
    const std::vector<std::pair<LSRUse *, i64>> &lanes) noexcept {
  if (lanes.empty())
    return false;
  i32 benefit = 0;
  i32 cost = 3;
  for (const auto &[use, offset] : lanes) {
    benefit += 2 + use->useCount;
    cost += offset != 0 ? 1 : 0;
  }
  if (lanes.size() > 1)
    benefit += static_cast<i32>(lanes.size() - 1);
  return benefit >= cost;
}

std::optional<EdgeRewritePlan> planEdgeRewrite(const EdgeGroup &group,
                                               const LoopShapeInfo &loopShape) {
  if (group.uses.empty())
    return std::nullopt;
  i64 minimum = group.uses.front()->evolution.edgeLocal.constant;
  for (LSRUse *use : group.uses)
    minimum = std::min(minimum, use->evolution.edgeLocal.constant);

  std::vector<std::pair<LSRUse *, i64>> lanes;
  for (LSRUse *use : group.uses) {
    i64 offset = 0;
    if (checkedSub(use->evolution.edgeLocal.constant, minimum, offset) &&
        fitsI32(offset))
      lanes.push_back({use, offset});
  }
  auto transfer = loopShape.getHeaderPhiTransfer(group.phi);
  if (lanes.empty() || !transfer || !transfer->hasNonzeroSelfDelta ||
      !transfer->header ||
      transfer->header->getPredecessorCount() != group.phi->getOperandCount() ||
      transfer->incoming.size() != group.phi->getOperandCount())
    return std::nullopt;
  const auto validLeaf = [&](const HeaderPhiIncomingTransfer &incoming) {
    if (!incoming.predecessor || !incoming.predecessor->endsWithTerminator())
      return false;
    if (incoming.kind == HeaderPhiIncomingKind::SelfDelta) {
      i64 step = 0;
      return checkedMul(group.coefficient, incoming.delta, step) &&
             fitsI32(step);
    }
    return incoming.incomingValue && fitsI32(group.coefficient) &&
           fitsI32(minimum);
  };
  for (const HeaderPhiIncomingTransfer &incoming : transfer->incoming) {
    if (!validLeaf(incoming))
      return std::nullopt;
    if (!incoming.mergedIncoming.empty()) {
      if (incoming.kind != HeaderPhiIncomingKind::Reset ||
          !incoming.incomingValue ||
          incoming.incomingValue->getOp() != OP_PHI ||
          incoming.incomingValue->parentBlock() != incoming.predecessor ||
          incoming.mergedIncoming.size() !=
              incoming.incomingValue->getOperandCount() ||
          incoming.mergedIncoming.size() !=
              incoming.predecessor->getPredecessorCount())
        return std::nullopt;
      for (const HeaderPhiIncomingTransfer &merged : incoming.mergedIncoming)
        if (!validLeaf(merged))
          return std::nullopt;
    }
  }
  return EdgeRewritePlan{std::move(*transfer), minimum, std::move(lanes)};
}

std::optional<CanonicalReuseQuery>
planCanonicalReuse(const EdgeGroup &group, const EdgeRewritePlan &plan,
                   const SCEV &scev) {
  BasicBlock *preheader = group.loop ? group.loop->getPreheader() : nullptr;
  BasicBlock *latch = group.loop && group.loop->latches().size() == 1
                          ? group.loop->latches().front()
                          : nullptr;
  Inst *initial = nullptr;
  i64 step = 0;
  bool hasStep = false;
  for (const HeaderPhiIncomingTransfer &incoming : plan.transfer.incoming) {
    if (incoming.kind == HeaderPhiIncomingKind::Reset &&
        incoming.predecessor == preheader)
      initial = incoming.incomingValue;
    if (incoming.kind == HeaderPhiIncomingKind::SelfDelta &&
        incoming.predecessor == latch && incoming.delta != 0)
      hasStep = checkedMul(group.coefficient, incoming.delta, step);
  }
  if (!initial || !hasStep)
    return std::nullopt;
  SCEVExpr *index = scev.getSCEV(initial);
  SCEVExpr *base = scev.getAddExpr(
      scev.getSCEV(group.root),
      scev.getMulExpr(index, scev.getConstant(group.coefficient, index->ty)));
  if (plan.minimum != 0)
    base = scev.getAddExpr(base, scev.getConstant(plan.minimum, index->ty));
  return CanonicalReuseQuery{group.loop, group.root, step, base};
}

class Rewriter {
public:
  Rewriter(Function *function, const SCEV *scev, const LoopShapeInfo *loopShape,
           ExpansionSession &session,
           const std::unordered_set<Inst *> &originalGetPtrs,
           const std::vector<CFGEdge> &failedResetEdges) noexcept
      : function_(function), builder_(function->module, function), scev_(scev),
        loopShape_(loopShape), session_(session),
        originalGetPtrs_(originalGetPtrs), failedResetEdges_(failedResetEdges) {
  }

  // 聚合同root/step的标准AddRec lane
  void rewriteCanonicalGroup(CanonicalGroup &group) {
    std::vector<u8> used(group.uses.size(), 0);
    for (usize seed = 0; seed < group.uses.size(); ++seed) {
      if (used[seed])
        continue;

      struct RawLane {
        LSRUse *use = nullptr; // 候选地址
        i64 delta = 0;         // 相对 seed 初值偏移
      };
      std::vector<RawLane> raw{{group.uses[seed], 0}};
      SCEVExpr *seedBase = group.uses[seed]->evolution.canonical.base;
      for (usize index = seed + 1; index < group.uses.size(); ++index) {
        if (used[index])
          continue;
        const MathBounds delta = scev_->getSignedDeltaBounds(
            group.uses[index]->evolution.canonical.base, seedBase);
        if (delta.valid && delta.min == delta.max && fitsI32(delta.min))
          raw.push_back({group.uses[index], delta.min});
      }
      std::stable_sort(raw.begin(), raw.end(),
                       [](const RawLane &left, const RawLane &right) {
                         return left.delta < right.delta;
                       });

      const auto markSeed = [&](const auto &lanes) {
        for (const auto &[use, offset] : lanes) {
          UNUSED(offset);
          if (use == group.uses[seed]) {
            used[seed] = 1;
            break;
          }
        }
      };

      for (usize first = 0; first < raw.size();) {
        usize bestLast = first;
        usize bestRepresentative = first;
        for (usize last = first; last < raw.size(); ++last) {
          bool found = false;
          for (usize representative = first; representative <= last;
               ++representative) {
            if (fitsTargetMemoryOffset(raw[first].delta -
                                       raw[representative].delta) &&
                fitsTargetMemoryOffset(raw[last].delta -
                                       raw[representative].delta)) {
              found = true;
              bestRepresentative = representative;
              break;
            }
          }
          if (!found)
            break;
          bestLast = last;
        }

        const i64 representativeDelta = raw[bestRepresentative].delta;
        LSRUse *representativeUse = raw[bestRepresentative].use;
        SCEVExpr *representativeBase =
            representativeUse->evolution.canonical.base;
        std::vector<std::pair<LSRUse *, i64>> lanes;
        const usize end = bestLast + 1;
        for (usize index = first; index < end; ++index)
          lanes.push_back(
              {raw[index].use, raw[index].delta - representativeDelta});
        std::sort(lanes.begin(), lanes.end(),
                  [](const auto &left, const auto &right) {
                    if (left.second != right.second)
                      return left.second < right.second;
                    return left.first->evolution.getPtr->id <
                           right.first->evolution.getPtr->id;
                  });

        if (!shouldBuildLanes(lanes) ||
            pointerPerLoop_[group.loop] >= kMaxRecurrencesPerLoop) {
          markSeed(lanes);
          first = end;
          continue;
        }
        Inst *phi = buildRecurrence(group.loop, representativeBase, group.step);
        if (!phi) {
          markSeed(lanes);
          first = end;
          continue;
        }
        ++pointerPerLoop_[group.loop];
        canonicalPointers_[std::make_tuple(group.loop,
                                           representativeUse->evolution.root,
                                           group.step)]
            .push_back({representativeBase, phi});
        for (const auto &[use, offset] : lanes)
          applyToUse(phi, use->evolution.getPtr, offset);

        for (usize index = seed; index < group.uses.size(); ++index) {
          if (used[index])
            continue;
          for (const auto &[use, offset] : lanes) {
            UNUSED(offset);
            if (use == group.uses[index]) {
              used[index] = 1;
              break;
            }
          }
        }
        first = end;
      }
    }
  }

  // 改写非规范header Phi的边局部地址组
  void rewriteEdgeGroup(EdgeGroup &group) {
    if (edgePerLoop_[group.loop] >= kMaxEdgeRecurrencesPerLoop)
      return;
    auto plan = planEdgeRewrite(group, *loopShape_);
    if (!plan)
      return;

    Inst *phi = nullptr;
    bool reusedCanonical = false;
    if (auto reuse = planCanonicalReuse(group, *plan, *scev_)) {
      const auto found = canonicalPointers_.find(
          std::make_tuple(reuse->loop, reuse->root, reuse->step));
      if (found != canonicalPointers_.end()) {
        for (const auto &[candidateBase, candidatePhi] : found->second) {
          const MathBounds delta =
              scev_->getSignedDeltaBounds(candidateBase, reuse->base);
          if (delta.valid && delta.min == 0 && delta.max == 0) {
            phi = candidatePhi;
            reusedCanonical = true;
            break;
          }
        }
      }
    }
    if (!phi)
      phi = buildEdgeRecurrence(group.root, group.coefficient, plan->minimum,
                                plan->transfer);
    if (!phi)
      return;
    if (!reusedCanonical)
      ++edgePerLoop_[group.loop];

    std::sort(plan->lanes.begin(), plan->lanes.end(),
              [](const auto &left, const auto &right) {
                if (left.second != right.second)
                  return left.second < right.second;
                return left.first->evolution.getPtr->id <
                       right.first->evolution.getPtr->id;
              });
    for (const auto &[use, offset] : plan->lanes)
      applyToUse(phi, use->evolution.getPtr, offset);
  }

  // 批量RAUW并删除已经失去使用的旧GETPTR
  bool commit() {
    if (replacements_.empty())
      return false;
    for (const Replacement &replacement : replacements_)
      replaceAllUsesWith(function_, replacement.from, replacement.to);
    for (const Replacement &replacement : replacements_)
      if (replacement.from->hasNoUses())
        VERIFY(replacement.from->eraseFromBlock());
    return true;
  }

private:
  struct Replacement {
    Inst *from = nullptr; // 原 GETPTR
    Inst *to = nullptr;   // 新递推值
  };

  // 查询物化结果是否依赖本轮待删除候选
  bool dependsOnOriginal(Inst *root) const {
    std::unordered_set<Inst *> visited;
    std::vector<Inst *> worklist;
    if (root)
      worklist.push_back(root);
    while (!worklist.empty()) {
      Inst *value = worklist.back();
      worklist.pop_back();
      if (!value || !visited.insert(value).second)
        continue;
      if (originalGetPtrs_.count(value))
        return true;
      for (u32 index = 0; index < value->getOperandCount(); ++index)
        worklist.push_back(value->getArg(index));
    }
    return false;
  }

  // 构建标准preheader/header/latch pointer recurrence
  Inst *buildRecurrence(Loop *loop, SCEVExpr *base, i64 step) {
    if (!loop || !base || !fitsI32(step) || loop->latches().size() != 1)
      return nullptr;
    BasicBlock *preheader = loop->getPreheader();
    BasicBlock *header = loop->header();
    BasicBlock *latch = loop->latches().front();
    if (!preheader || !header || !preheader->endsWithTerminator() ||
        !latch->endsWithTerminator())
      return nullptr;
    for (u32 index = 0; index < header->getPredecessorCount(); ++index) {
      BasicBlock *predecessor = header->getPredecessor(index);
      if (predecessor != preheader && predecessor != latch)
        return nullptr;
    }
    if (session_.dependsOnAny(base, originalGetPtrs_))
      return nullptr;

    ensureRowBaseAvailable(loop, base);
    Inst *initial = session_.expandCodeFor(base, preheader->terminator());
    if (!initial || dependsOnOriginal(initial))
      return nullptr;
    Inst *phi = builder_.emitPhi(TY_PTR, header, builder_.makeUndef(TY_PTR));
    Inst *next = emitPointerStep(builder_, phi, step, latch->terminator());
    if (!next)
      return nullptr;
    VERIFY(CFGEditor::setPhiEdgeValues(function_, header, preheader,
                                       {{phi, initial}}));
    VERIFY(
        CFGEditor::setPhiEdgeValues(function_, header, latch, {{phi, next}}));
    session_.registerAvailableAddRec(base, scev_->getConstant(step, TY_I32),
                                     loop, phi);
    return phi;
  }

  // 按需建立包围内层循环的外层row-base递推
  void ensureRowBaseAvailable(Loop *inner, SCEVExpr *base) {
    BasicBlock *innerPreheader = inner ? inner->getPreheader() : nullptr;
    if (!innerPreheader || session_.hasAvailableFor(base, innerPreheader))
      return;
    const auto recurrence = findAddRecurrence(scev_, base);
    if (!recurrence)
      return;
    Loop *outer = recurrence->loop;
    if (!outer || outer == inner || !outer->contains(innerPreheader) ||
        outer->latches().size() != 1 || !outer->getPreheader() ||
        !recurrence->step->isConstant() || !fitsI32(recurrence->step->cst.v) ||
        !recurrence->base->isLoopInvariant(outer) ||
        !scev_->isSafeToExpand(recurrence->base, outer->getPreheader()) ||
        session_.dependsOnAny(recurrence->base, originalGetPtrs_) ||
        rowPerOuter_[outer] >= kMaxRowRecurrencesPerOuter)
      return;

    BasicBlock *preheader = outer->getPreheader();
    BasicBlock *latch = outer->latches().front();
    if (!preheader->endsWithTerminator() || !latch->endsWithTerminator())
      return;
    ensureRowBaseAvailable(outer, recurrence->base);
    Inst *initial =
        session_.expandCodeFor(recurrence->base, preheader->terminator());
    if (!initial || dependsOnOriginal(initial))
      return;
    Inst *phi =
        builder_.emitPhi(TY_PTR, outer->header(), builder_.makeUndef(TY_PTR));
    Inst *next = emitPointerStep(builder_, phi, recurrence->step->cst.v,
                                 latch->terminator());
    if (!next)
      return;
    VERIFY(CFGEditor::setPhiEdgeValues(function_, outer->header(), preheader,
                                       {{phi, initial}}));
    VERIFY(CFGEditor::setPhiEdgeValues(function_, outer->header(), latch,
                                       {{phi, next}}));
    session_.registerAvailableAddRec(recurrence->base, recurrence->step, outer,
                                     phi);
    ++rowPerOuter_[outer];
  }

  // 按HeaderPhiTransfer逐边建立pointer Phi
  Inst *buildEdgeRecurrence(Inst *root, i64 coefficient, i64 constant,
                            const HeaderPhiTransferInfo &transfer) {
    struct LeafPlan {
      BasicBlock *predecessor = nullptr; // incoming 边
      bool useStep = false;              // 是否由 pointer Phi 自增
      i64 step = 0;                      // pointer 字节步长
      Inst *scalar = nullptr;            // Reset 边标量值
    };
    struct IncomingPlan {
      BasicBlock *predecessor = nullptr; // Header直接前驱
      std::optional<LeafPlan> direct;    // 普通边的传入方案
      std::vector<LeafPlan> merged;      // Single Latch内原回边方案
    };
    const auto makeLeaf = [&](const HeaderPhiIncomingTransfer &incoming,
                              BasicBlock *target) -> std::optional<LeafPlan> {
      if (incoming.kind == HeaderPhiIncomingKind::SelfDelta) {
        i64 step = 0;
        VERIFY(checkedMul(coefficient, incoming.delta, step) && fitsI32(step));
        return LeafPlan{incoming.predecessor, true, step, nullptr};
      }
      // Reset地址只能放在专属边块 条件前驱上投机物化会放大热路径成本
      const CFGEdge edge{incoming.predecessor, target};
      if (successorCount(incoming.predecessor) > 1 ||
          std::find(failedResetEdges_.begin(), failedResetEdges_.end(), edge) !=
              failedResetEdges_.end())
        return std::nullopt;
      return LeafPlan{incoming.predecessor, false, 0, incoming.incomingValue};
    };

    std::vector<IncomingPlan> plans;
    plans.reserve(transfer.incoming.size());
    for (const HeaderPhiIncomingTransfer &incoming : transfer.incoming) {
      IncomingPlan plan;
      plan.predecessor = incoming.predecessor;
      if (incoming.mergedIncoming.empty()) {
        plan.direct = makeLeaf(incoming, transfer.header);
        if (!plan.direct)
          return nullptr;
      } else {
        plan.merged.reserve(incoming.mergedIncoming.size());
        for (const HeaderPhiIncomingTransfer &merged :
             incoming.mergedIncoming) {
          std::optional<LeafPlan> leaf = makeLeaf(merged, incoming.predecessor);
          if (!leaf)
            return nullptr;
          plan.merged.push_back(*leaf);
        }
      }
      plans.push_back(std::move(plan));
    }

    Inst *phi =
        builder_.emitPhi(TY_PTR, transfer.header, builder_.makeUndef(TY_PTR));
    const auto emitLeaf = [&](const LeafPlan &plan) {
      return plan.useStep
                 ? emitPointerStep(builder_, phi, plan.step,
                                   plan.predecessor->terminator())
                 : emitAddressForScalar(builder_, root, plan.scalar,
                                        coefficient, constant,
                                        plan.predecessor->terminator());
    };
    for (const IncomingPlan &plan : plans) {
      Inst *incoming = nullptr;
      if (plan.direct) {
        incoming = emitLeaf(*plan.direct);
      } else {
        Inst *mergedPhi = builder_.emitPhi(TY_PTR, plan.predecessor,
                                           builder_.makeUndef(TY_PTR));
        for (const LeafPlan &leaf : plan.merged) {
          Inst *mergedValue = emitLeaf(leaf);
          VERIFY(mergedValue != nullptr);
          VERIFY(CFGEditor::setPhiEdgeValues(function_, plan.predecessor,
                                             leaf.predecessor,
                                             {{mergedPhi, mergedValue}}));
        }
        incoming = mergedPhi;
      }
      VERIFY(incoming != nullptr);
      VERIFY(CFGEditor::setPhiEdgeValues(function_, transfer.header,
                                         plan.predecessor, {{phi, incoming}}));
    }
    return phi;
  }

  // 用代表递推或其常量偏移替换单条地址
  void applyToUse(Inst *representative, Inst *getPtr, i64 offset) {
    if (offset == 0) {
      if (representative != getPtr)
        replacements_.push_back({getPtr, representative});
      return;
    }
    builder_.setInsertBefore(getPtr);
    Inst *replacement = builder_.emitGetPtr(
        representative, builder_.iConst(static_cast<i32>(offset)));
    replacement->setStride(1);
    replacements_.push_back({getPtr, replacement});
  }

  Function *function_ = nullptr;
  IRBuilder builder_;
  const SCEV *scev_ = nullptr;
  const LoopShapeInfo *loopShape_ = nullptr;
  ExpansionSession &session_;                         // 本轮递推复用会话
  const std::unordered_set<Inst *> &originalGetPtrs_; // 原候选集合
  const std::vector<CFGEdge> &failedResetEdges_;      // 未能拆分的Reset边
  std::vector<Replacement> replacements_;             // 延迟提交替换
  std::map<Loop *, i32> pointerPerLoop_;              // 标准递推压力预算
  std::map<Loop *, i32> edgePerLoop_;                 // 边局部递推压力预算
  std::map<Loop *, i32> rowPerOuter_;                 // 外层 row 递推压力预算
  std::map<std::tuple<Loop *, Inst *, i64>,
           std::vector<std::pair<SCEVExpr *, Inst *>>>
      canonicalPointers_; // 可供退出地址复用的标准递推
};

bool collectRewritePlan(Function *function, PassContext &context,
                        RewritePlan &plan) {
  plan = {};
  const LoopInfo &loopInfo = context.get<LoopInfoAnalysis>(function).info;
  const DominatorTree &dominatorTree = context.get<DomAnalysis>(function).tree;
  const AliasInfo &aliasInfo = context.get<AliasAnalysis>(function).info;
  const SCEV &scev = context.get<SCEVAnalysis>(function).info;
  const LoopShapeInfo &loopShape =
      context.get<LoopShapeAnalysis>(function).info;

  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if (inst->getOp() != OP_GETPTR)
        continue;
      auto evolution = classifyAddressEvolution(
          &scev, &loopInfo, inst, &loopShape, &aliasInfo, &dominatorTree);
      if (evolution)
        plan.uses.push_back({*evolution, useCount(inst)});
    }
  }
  if (plan.uses.empty())
    return false;

  for (const LSRUse &use : plan.uses)
    plan.originalGetPtrs.insert(use.evolution.getPtr);

  std::map<std::tuple<Loop *, Inst *, i64>, usize> canonicalIndex;
  std::map<std::tuple<Inst *, Inst *, i64>, usize> edgeIndex;
  for (LSRUse &use : plan.uses) {
    if (use.evolution.kind == AddressEvolutionKind::CanonicalAddRec) {
      const i64 step = use.evolution.canonical.step->cst.v;
      const auto key = std::make_tuple(use.evolution.canonical.loop,
                                       use.evolution.root, step);
      auto [position, inserted] =
          canonicalIndex.emplace(key, plan.canonicalGroups.size());
      if (inserted)
        plan.canonicalGroups.push_back(
            {use.evolution.canonical.loop, step, {}});
      plan.canonicalGroups[position->second].uses.push_back(&use);
    } else if (use.evolution.kind == AddressEvolutionKind::EdgeLocalPhi) {
      const EdgeLocalAddressEvolution &edge = use.evolution.edgeLocal;
      const auto key = std::make_tuple(edge.root, edge.phi, edge.coefficient);
      auto [position, inserted] =
          edgeIndex.emplace(key, plan.edgeGroups.size());
      if (inserted)
        plan.edgeGroups.push_back(
            {edge.loop, edge.root, edge.phi, edge.coefficient, {}});
      plan.edgeGroups[position->second].uses.push_back(&use);
    }
  }
  return true;
}

std::vector<CFGEdge> collectResetCriticalEdges(const RewritePlan &rewritePlan,
                                               const LoopShapeInfo &loopShape,
                                               const SCEV &scev) {
  std::vector<CFGEdge> edges;
  std::map<Loop *, i32> requiredPerLoop;
  for (const EdgeGroup &group : rewritePlan.edgeGroups) {
    if (requiredPerLoop[group.loop] >= kMaxEdgeRecurrencesPerLoop)
      continue;
    auto plan = planEdgeRewrite(group, loopShape);
    if (!plan)
      continue;

    bool mayReuseCanonical = false;
    if (auto reuse = planCanonicalReuse(group, *plan, scev))
      for (const CanonicalGroup &canonical : rewritePlan.canonicalGroups)
        if (canonical.loop == reuse->loop && canonical.step == reuse->step)
          for (LSRUse *use : canonical.uses) {
            const MathBounds delta = scev.getSignedDeltaBounds(
                use->evolution.canonical.base, reuse->base);
            if (use->evolution.root == reuse->root && delta.valid &&
                delta.min == 0 && delta.max == 0) {
              mayReuseCanonical = true;
              break;
            }
          }
    requiredPerLoop[group.loop] += mayReuseCanonical ? 0 : 1;

    const auto collectReset = [&](const HeaderPhiIncomingTransfer &incoming,
                                  BasicBlock *target) {
      if (incoming.kind != HeaderPhiIncomingKind::Reset ||
          successorCount(incoming.predecessor) <= 1)
        return;
      const CFGEdge edge{incoming.predecessor, target};
      if (std::find(edges.begin(), edges.end(), edge) == edges.end())
        edges.push_back(edge);
    };
    for (const HeaderPhiIncomingTransfer &incoming : plan->transfer.incoming) {
      if (incoming.mergedIncoming.empty()) {
        collectReset(incoming, plan->transfer.header);
        continue;
      }
      for (const HeaderPhiIncomingTransfer &merged : incoming.mergedIncoming)
        collectReset(merged, incoming.predecessor);
    }
  }
  return edges;
}

bool runLSR(Function *function, PassContext &context, bool &changedCFG) {
  changedCFG = false;
  RewritePlan plan;
  if (!collectRewritePlan(function, context, plan))
    return false;

  const LoopShapeInfo &initialLoopShape =
      context.get<LoopShapeAnalysis>(function).info;
  const SCEV &initialSCEV = context.get<SCEVAnalysis>(function).info;
  const std::vector<CFGEdge> resetEdges =
      collectResetCriticalEdges(plan, initialLoopShape, initialSCEV);
  std::vector<CFGEdge> failedResetEdges;
  for (const CFGEdge &edge : resetEdges) {
    if (CFGEditor::splitCriticalEdge(function, edge.first, edge.second))
      changedCFG = true;
    else
      failedResetEdges.push_back(edge);
  }
  if (changedCFG) {
    context.functionAnalyses().clear(function);
    (void)collectRewritePlan(function, context, plan);
  }

  const SCEV &scev = context.get<SCEVAnalysis>(function).info;
  const LoopShapeInfo &loopShape =
      context.get<LoopShapeAnalysis>(function).info;
  ExpansionSession session(function, &scev);
  Rewriter rewriter(function, &scev, &loopShape, session, plan.originalGetPtrs,
                    failedResetEdges);
  for (CanonicalGroup &group : plan.canonicalGroups)
    rewriter.rewriteCanonicalGroup(group);
  for (EdgeGroup &group : plan.edgeGroups)
    rewriter.rewriteEdgeGroup(group);
  const bool rewritten = rewriter.commit();
  if (rewritten || changedCFG)
    // 外部地址候选可能复用循环内 pointer Phi, 统一重新封闭其出口使用
    (void)formLCSSA(function, context.functionAnalyses());
  return rewritten || changedCFG;
}

} // namespace

std::string_view LSRPass::name() const noexcept { return "lsr"; }

PassResult LSRPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();
  bool changedCFG = false;
  if (!runLSR(function, context, changedCFG))
    return PassResult::noChange();
  PreservedAnalyses preserved;
  if (!changedCFG)
    preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
