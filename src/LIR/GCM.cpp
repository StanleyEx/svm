#include "Analysis.h"
#include "LIRPass.h"

#include <limits>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

bool isSafeToSpeculate(const Inst *inst) noexcept {
  const OpCode op = inst->getOp();
  if (op != OP_DIV && op != OP_MOD)
    return true;
  const Inst *divisor = inst->getArg(1);
  return divisor->getOp() == OP_ICONST && divisor->getImm() != 0;
}

bool isMovable(Inst *inst, const GlobalSummaryResult *effects) noexcept {
  if (!inst || !inst->parentBlock() || isVoid(inst->getType()))
    return false;

  const OpCode op = inst->getOp();
  if (op == OP_PHI || isTerminator(op) || isMachineOp(op))
    return false;
  if (isArithmetic(op) || isUnaryArithmetic(op) || isCompare(op) ||
      isConversion(op) || isAddressingOp(op) || op == OP_SELECT)
    return isSafeToSpeculate(inst);
  if (op == OP_LOAD)
    return true;
  return op == OP_CALL && effects &&
         effects->calleeEffect(inst->getCallee()).isSpeculatable();
}

BasicBlock *useBlock(const Use *use) noexcept {
  if (!use || !use->user)
    return nullptr;
  if (use->user->getOp() == OP_PHI)
    return use->user->getIncomingBlock(use->argNo);
  return use->user->parentBlock();
}

bool usesValue(const Inst *user, const Inst *value) noexcept {
  for (u32 index = 0; index < user->getOperandCount(); ++index)
    if (user->getArg(index) == value)
      return true;
  return false;
}

struct ScheduleInfo {
  BasicBlock *original = nullptr; // 输入IR中的所属块
  BasicBlock *early = nullptr;    // 操作数允许的最早块
  BasicBlock *late = nullptr;     // 全部使用点的支配树LCA
  BasicBlock *best = nullptr;     // 代价最低的最终计划块
  bool candidate = false;         // 是否参与本轮调度
  bool earlyDone = false;         // 是否已经求得early
  bool lateDone = false;          // 是否已经求得late和best
  bool visitingEarly = false;     // schedule-early递归栈标记
  bool visitingLate = false;      // schedule-late递归栈标记
};

class GCMScheduler {
public:
  GCMScheduler(Function *function, const DominatorTree &dominators,
               const LoopInfo &loops, const AliasInfo &aliases,
               const GlobalSummaryResult *effects) noexcept
      : function_(function), dominators_(dominators), loops_(loops),
        aliases_(aliases), effects_(effects), entry_(function->region->first) {}
  bool run();

private:
  i32 loopDepth(BasicBlock *block) const noexcept; // 循环嵌套深度
  i32 domDepth(BasicBlock *block) const noexcept;  // 支配树深度
  i32 rpoIndex(BasicBlock *block) const noexcept;  // 稳定RPO编号
  bool isCandidate(Inst *inst) const noexcept;     // 候选集合成员
  // 求支配树LCA
  BasicBlock *domLCA(BasicBlock *left, BasicBlock *right) const noexcept;
  BasicBlock *scheduleEarly(Inst *inst);
  BasicBlock *scheduleLate(Inst *inst);
  BasicBlock *chooseBest(Inst *inst, BasicBlock *early, BasicBlock *late,
                         BasicBlock *original);
  // 比较块代价
  bool betterBlock(BasicBlock *candidate, BasicBlock *current,
                   BasicBlock *original) const noexcept;
  // 检查指令是否可能与目标内存冲突
  bool mayClobber(Inst *inst, const MemoryLocation &location) const;
  // 检查控制流走廊内是否存在内存写冲突
  bool corridorHasClobber(const MemoryLocation &location, BasicBlock *top,
                          BasicBlock *bottom) const;
  // 查询Load在目标点可解引用
  bool isLoadDerefSafe(Inst *load, BasicBlock *at) const;
  // 将不自洽计划退回原块
  void demoteInvalidPlans();
  // 排序依赖图
  std::vector<Inst *>
  buildTopologicalOrder(const std::vector<Inst *> &nodes) const;
  // 在目标块内放置跨块指令
  void placeMover(Inst *inst);
  // 收缩留在原块的活跃区间
  bool placeSameBlock(Inst *inst);

  Function *function_ = nullptr;
  const DominatorTree &dominators_;
  const LoopInfo &loops_;
  const AliasInfo &aliases_;
  const GlobalSummaryResult *effects_ = nullptr;
  BasicBlock *entry_ = nullptr;                       // 可达CFG入口
  std::unordered_map<BasicBlock *, i32> rpoIndices_;  // 块到RPO编号
  std::unordered_map<Inst *, ScheduleInfo> schedule_; // 指令调度状态
  std::vector<Inst *> candidates_;                    // 稳定候选序列

  static constexpr u32 kMaxRegionChecks = 64;    // 单条Load的走廊查询预算
  static constexpr u32 kMaxSameBlockScan = 4096; // 单次块内扫描预算
  static constexpr usize kMaxInstsForLoadMotion = 8000;  // Load移动指令阈值
  static constexpr usize kMaxBlocksForLoadMotion = 1200; // Load移动块阈值
};

i32 GCMScheduler::loopDepth(BasicBlock *block) const noexcept {
  return loops_.getLoopDepth(block);
}

i32 GCMScheduler::domDepth(BasicBlock *block) const noexcept {
  return dominators_.getDepth(block);
}

i32 GCMScheduler::rpoIndex(BasicBlock *block) const noexcept {
  const auto found = rpoIndices_.find(block);
  return found == rpoIndices_.end() ? std::numeric_limits<i32>::max()
                                    : found->second;
}

bool GCMScheduler::isCandidate(Inst *inst) const noexcept {
  const auto found = schedule_.find(inst);
  return found != schedule_.end() && found->second.candidate;
}

BasicBlock *GCMScheduler::domLCA(BasicBlock *left,
                                 BasicBlock *right) const noexcept {
  if (!left)
    return right;
  if (!right)
    return left;

  i32 leftDepth = domDepth(left);
  i32 rightDepth = domDepth(right);
  if (leftDepth < 0)
    return right;
  if (rightDepth < 0)
    return left;
  while (leftDepth > rightDepth) {
    left = dominators_.getIDom(left);
    --leftDepth;
  }
  while (rightDepth > leftDepth) {
    right = dominators_.getIDom(right);
    --rightDepth;
  }
  while (left != right) {
    left = dominators_.getIDom(left);
    right = dominators_.getIDom(right);
    if (!left || !right)
      return nullptr;
  }
  return left;
}

BasicBlock *GCMScheduler::scheduleEarly(Inst *inst) {
  ScheduleInfo &info = schedule_.at(inst);
  if (info.earlyDone)
    return info.early;
  if (info.visitingEarly)
    return info.original;
  info.visitingEarly = true;

  // SSA操作数的定义块位于同一条支配链 最深者就是最早合法块
  BasicBlock *early = entry_;
  for (u32 index = 0; index < inst->getOperandCount(); ++index) {
    Inst *operand = inst->getArg(index);
    BasicBlock *operandBlock =
        isCandidate(operand) ? scheduleEarly(operand) : operand->parentBlock();
    if (operandBlock && domDepth(operandBlock) > domDepth(early))
      early = operandBlock;
  }
  info.early = early;
  info.earlyDone = true;
  info.visitingEarly = false;
  return early;
}

BasicBlock *GCMScheduler::scheduleLate(Inst *inst) {
  ScheduleInfo &info = schedule_.at(inst);
  if (info.lateDone)
    return info.late;
  if (info.visitingLate)
    return info.late;
  info.visitingLate = true;

  BasicBlock *late = nullptr;
  for (const Use *use = inst->uses(); use; use = use->next) {
    Inst *user = use->user;
    BasicBlock *block = nullptr;
    if (isCandidate(user)) {
      UNUSED(scheduleLate(user));
      block = schedule_.at(user).best;
    } else {
      // 处理不可移动指令及 Phi 使用点
      // Phi在incoming边上取值 使用位置是对应前驱而不是Phi块
      block = useBlock(use);
    }
    if (block)
      late = domLCA(late, block);
  }

  info.late = late;
  info.best = chooseBest(inst, info.early, late, info.original);
  info.lateDone = true;
  info.visitingLate = false;
  return late;
}

BasicBlock *GCMScheduler::chooseBest(Inst *inst, BasicBlock *early,
                                     BasicBlock *late, BasicBlock *original) {
  if (!early || !late || !dominators_.dominates(early, late))
    return original;

  const bool isLoad = inst->getOp() == OP_LOAD;
  const MemoryLocation location =
      isLoad ? MemoryLocation::fromMemoryInstruction(inst) : MemoryLocation{};
  BasicBlock *best = original;
  u32 regionChecks = 0;
  bool hoistBlocked = false;
  // [early, late]是单条支配链 先按循环深度, 再按支配深度择优
  for (BasicBlock *block = late; block; block = dominators_.getIDom(block)) {
    if (!dominators_.dominates(early, block))
      break;

    bool legal = true;
    if (isLoad && block != original) {
      if (dominators_.dominates(original, block)) {
        legal = regionChecks++ < kMaxRegionChecks &&
                !corridorHasClobber(location, original, block);
      } else if (hoistBlocked || !isLoadDerefSafe(inst, block) ||
                 regionChecks++ >= kMaxRegionChecks ||
                 corridorHasClobber(location, block, original)) {
        legal = false;
        hoistBlocked = true;
      }
    }
    if (legal && betterBlock(block, best, original))
      best = block;
  }
  return best;
}

bool GCMScheduler::betterBlock(BasicBlock *candidate, BasicBlock *current,
                               BasicBlock *original) const noexcept {
  if (candidate == current)
    return false;
  const i32 candidateLoopDepth = loopDepth(candidate);
  const i32 currentLoopDepth = loopDepth(current);
  if (candidateLoopDepth != currentLoopDepth)
    return candidateLoopDepth < currentLoopDepth;
  const i32 candidateDomDepth = domDepth(candidate);
  const i32 currentDomDepth = domDepth(current);
  if (candidateDomDepth != currentDomDepth)
    return candidateDomDepth > currentDomDepth;
  if (candidate == original)
    return true;
  if (current == original)
    return false;
  return rpoIndex(candidate) < rpoIndex(current);
}

bool GCMScheduler::mayClobber(Inst *inst,
                              const MemoryLocation &location) const {
  const OpCode op = inst->getOp();
  if (op == OP_STORE) {
    return aliases_.alias(MemoryLocation::fromMemoryInstruction(inst),
                          location) != AliasResult::NoAlias;
  }
  if (isLocalInitAnchor(op))
    return inst->getOperandCount() == 0 ||
           aliases_.alias(inst->getArg(0), location.pointer) !=
               AliasResult::NoAlias;
  if (op != OP_CALL)
    return false;
  if (!effects_)
    return true;
  return aliases_.mayWriteMemory(inst, location,
                                 effects_->calleeEffect(inst->getCallee()));
}

bool GCMScheduler::corridorHasClobber(const MemoryLocation &location,
                                      BasicBlock *top,
                                      BasicBlock *bottom) const {
  std::unordered_set<BasicBlock *> reachableFromTop;
  std::unordered_set<BasicBlock *> reachingBottom;
  // 两次泛洪的交集包含top到底部的全部路径 也会自然包含循环回边
  std::vector<BasicBlock *> worklist{top};
  reachableFromTop.insert(top);
  while (!worklist.empty()) {
    BasicBlock *block = worklist.back();
    worklist.pop_back();
    forEachSuccessor(block, [&](BasicBlock *successor) {
      if (reachableFromTop.insert(successor).second)
        worklist.push_back(successor);
    });
  }

  worklist.push_back(bottom);
  reachingBottom.insert(bottom);
  while (!worklist.empty()) {
    BasicBlock *block = worklist.back();
    worklist.pop_back();
    for (u32 index = 0; index < block->getPredecessorCount(); ++index) {
      BasicBlock *predecessor = block->getPredecessor(index);
      if (predecessor && reachingBottom.insert(predecessor).second)
        worklist.push_back(predecessor);
    }
  }

  for (BasicBlock *block : reachableFromTop) {
    if (!reachingBottom.count(block))
      continue;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      if (mayClobber(inst, location))
        return true;
  }
  return false;
}

bool GCMScheduler::isLoadDerefSafe(Inst *load, BasicBlock *at) const {
  AliasQuery query;
  query.contextBlock = at;
  return aliases_.isDereferenceable(MemoryLocation::fromMemoryInstruction(load),
                                    query);
}

void GCMScheduler::demoteInvalidPlans() {
  bool changed = true;
  while (changed) {
    changed = false;
    for (Inst *inst : candidates_) {
      ScheduleInfo &info = schedule_.at(inst);
      if (info.best == info.original)
        continue;

      bool valid = true;
      for (u32 index = 0; index < inst->getOperandCount() && valid; ++index) {
        Inst *operand = inst->getArg(index);
        BasicBlock *operandBlock = isCandidate(operand)
                                       ? schedule_.at(operand).best
                                       : operand->parentBlock();
        valid = !operandBlock || dominators_.dominates(operandBlock, info.best);
      }
      for (const Use *use = inst->uses(); use && valid; use = use->next) {
        Inst *user = use->user;
        BasicBlock *block = nullptr;
        if (user->getOp() == OP_PHI)
          block = user->getIncomingBlock(use->argNo);
        else if (isCandidate(user))
          block = schedule_.at(user).best;
        else
          block = user->parentBlock();
        valid = block && dominators_.dominates(info.best, block);
      }
      if (!valid) {
        info.best = info.original;
        changed = true;
      }
    }
  }
}

std::vector<Inst *>
GCMScheduler::buildTopologicalOrder(const std::vector<Inst *> &nodes) const {
  struct Frame {
    Inst *node = nullptr; // 当前DFS节点
    u32 nextOperand = 0;  // 下一个待访问操作数
  };

  const std::unordered_set<Inst *> nodeSet(nodes.begin(), nodes.end());
  std::unordered_set<Inst *> completed;
  std::unordered_set<Inst *> active;
  std::vector<Inst *> order;
  order.reserve(nodes.size());
  for (Inst *root : nodes) {
    if (completed.count(root))
      continue;
    std::vector<Frame> stack{{root, 0}};
    active.insert(root);
    while (!stack.empty()) {
      Frame &frame = stack.back();
      if (frame.nextOperand < frame.node->getOperandCount()) {
        Inst *operand = frame.node->getArg(frame.nextOperand++);
        if (nodeSet.count(operand) && !completed.count(operand) &&
            !active.count(operand)) {
          stack.push_back({operand, 0});
          active.insert(operand);
        }
        continue;
      }
      completed.insert(frame.node);
      active.erase(frame.node);
      order.push_back(frame.node);
      stack.pop_back();
    }
  }
  return order;
}

void GCMScheduler::placeMover(Inst *inst) {
  BasicBlock *target = schedule_.at(inst).best;
  Inst *terminator = target->terminator();
  Inst *latestOperand = nullptr;
  for (Inst *cursor = terminator->previous(); cursor;
       cursor = cursor->previous()) {
    if (usesValue(inst, cursor)) {
      latestOperand = cursor;
      break;
    }
  }
  // 拓扑序保证候选操作数已先移动 无块内操作数时放在普通指令链首
  if (latestOperand)
    inst->moveAfter(latestOperand);
  else
    inst->moveBefore(target->firstInst());
}

bool GCMScheduler::placeSameBlock(Inst *inst) {
  const bool isLoad = inst->getOp() == OP_LOAD;
  const MemoryLocation location =
      isLoad ? MemoryLocation::fromMemoryInstruction(inst) : MemoryLocation{};
  Inst *anchor = nullptr;
  u32 steps = 0;
  for (Inst *cursor = inst->next(); cursor; cursor = cursor->next()) {
    if (++steps > kMaxSameBlockScan)
      return false;
    if ((isLoad && mayClobber(cursor, location)) || usesValue(cursor, inst)) {
      anchor = cursor;
      break;
    }
  }
  if (!anchor || inst->next() == anchor)
    return false;
  inst->moveBefore(anchor);
  return true;
}

bool GCMScheduler::run() {
  const std::vector<BasicBlock *> rpo = computeRPO(function_);
  if (rpo.empty())
    return false;
  for (usize index = 0; index < rpo.size(); ++index) {
    if (!rpo[index]->endsWithTerminator())
      return false;
    rpoIndices_.emplace(rpo[index], static_cast<i32>(index));
  }

  usize reachableInsts = 0;
  for (BasicBlock *block : rpo)
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      ++reachableInsts;
  const bool moveLoads = reachableInsts <= kMaxInstsForLoadMotion &&
                         rpo.size() <= kMaxBlocksForLoadMotion;

  for (BasicBlock *block : rpo) {
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if ((!moveLoads && inst->getOp() == OP_LOAD) ||
          !isMovable(inst, effects_))
        continue;
      ScheduleInfo &info = schedule_[inst];
      info.original = block;
      info.best = block;
      info.candidate = true;
      candidates_.push_back(inst);
    }
  }
  if (candidates_.empty())
    return false;

  for (Inst *inst : candidates_)
    UNUSED(scheduleEarly(inst));
  for (auto iterator = candidates_.rbegin(); iterator != candidates_.rend();
       ++iterator)
    UNUSED(scheduleLate(*iterator));
  demoteInvalidPlans();

  std::vector<Inst *> movers;
  for (Inst *inst : candidates_)
    if (schedule_.at(inst).best != schedule_.at(inst).original)
      movers.push_back(inst);
  const std::vector<Inst *> moveOrder = buildTopologicalOrder(movers);
  for (Inst *inst : moveOrder)
    placeMover(inst);

  std::vector<Inst *> sinkers;
  for (Inst *inst : candidates_) {
    if (schedule_.at(inst).best != schedule_.at(inst).original)
      continue;
    for (const Use *use = inst->uses(); use; use = use->next) {
      Inst *user = use->user;
      if (user->getOp() != OP_PHI &&
          user->parentBlock() == inst->parentBlock()) {
        sinkers.push_back(inst);
        break;
      }
    }
  }
  u32 sameBlockMoves = 0;
  const std::vector<Inst *> sinkOrder = buildTopologicalOrder(sinkers);
  for (auto iterator = sinkOrder.rbegin(); iterator != sinkOrder.rend();
       ++iterator)
    if (placeSameBlock(*iterator))
      ++sameBlockMoves;
  return !moveOrder.empty() || sameBlockMoves != 0;
}

} // namespace

std::string_view GCMPass::name() const noexcept { return "gcm"; }

PassResult GCMPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first || !function->module ||
      function->module != context.module())
    return PassResult::noChange();

  const DominatorTree &dominators = context.get<DomAnalysis>(function).tree;
  const LoopInfo &loops = context.get<LoopInfoAnalysis>(function).info;
  const AliasInfo &aliases = context.get<AliasAnalysis>(function).info;
  const GlobalSummaryResult &effects =
      context.get<GlobalSummaryAnalysis>(function->module).result;
  GCMScheduler scheduler(function, dominators, loops, aliases, &effects);
  if (!scheduler.run())
    return PassResult::noChange();

  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  preserved.preserve<SCEVAnalysis>();
  preserved.preserve<AliasAnalysis>();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
