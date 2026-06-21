#include "Analysis.h"
#include "IR.h"
#include "LIRPass.h"

#include <cassert>
#include <cstdlib>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

struct AllocaInfo {
  Inst *alloca = nullptr;              // 待提升的栈对象
  std::vector<BasicBlock *> defBlocks; // 包含Store的块
  std::vector<BasicBlock *> useBlocks; // 包含Load的块
  std::vector<Inst *> stores;          // 对该对象的Store
  std::vector<Inst *> loads;           // 对该对象的Load
};

bool isPromotableAlloca(const Inst *alloca, const BasicBlock *entry) {
  if (!alloca || alloca->getOp() != OP_ALLOCA || alloca->parentBlock() != entry)
    return false;
  const MemPayload &memory = alloca->getMem();
  if (!isScalar(memory.elementType) ||
      memory.totalSizeBytes !=
          static_cast<u32>(typeSizeBytes(memory.elementType)))
    return false;

  for (const Use *use = alloca->uses(); use; use = use->next) {
    const Inst *user = use->user;
    if (!user || user->isErased() || !user->parentBlock() || use->argNo != 0)
      return false;
    if (user->getOp() == OP_LOAD) {
      const MemPayload &loadMemory = user->getMem();
      if (user->getOperandCount() != 1 ||
          user->getType() != memory.elementType ||
          loadMemory.elementType != memory.elementType ||
          loadMemory.totalSizeBytes != memory.totalSizeBytes)
        return false;
    } else if (user->getOp() == OP_STORE) {
      const MemPayload &storeMemory = user->getMem();
      if (user->getOperandCount() != 2 ||
          storeMemory.elementType != memory.elementType ||
          storeMemory.totalSizeBytes != memory.totalSizeBytes ||
          !user->getArg(1) || user->getArg(1)->getType() != memory.elementType)
        return false;
    } else {
      return false;
    }
  }
  return true;
}

AllocaInfo collectInfo(Inst *alloca) {
  AllocaInfo info;
  info.alloca = alloca;
  std::unordered_set<BasicBlock *> defs;
  std::unordered_set<BasicBlock *> uses;
  for (const Use *use = alloca->uses(); use; use = use->next) {
    Inst *user = use->user;
    if (user->getOp() == OP_STORE) {
      info.stores.push_back(user);
      if (defs.insert(user->parentBlock()).second)
        info.defBlocks.push_back(user->parentBlock());
    } else if (user->getOp() == OP_LOAD) {
      info.loads.push_back(user);
      if (uses.insert(user->parentBlock()).second)
        info.useBlocks.push_back(user->parentBlock());
    }
  }
  return info;
}

bool hasUpwardExposedLoad(BasicBlock *block, const Inst *alloca) {
  for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
    if (inst->getOp() != OP_LOAD && inst->getOp() != OP_STORE)
      continue;
    if (inst->getArg(0) != alloca)
      continue;
    if (inst->getOp() == OP_LOAD)
      return true;
    if (inst->getOp() == OP_STORE)
      return false;
  }
  return false;
}

bool tryRewriteLocally(Function *function, const AllocaInfo &info) {
  for (BasicBlock *block : info.useBlocks)
    if (hasUpwardExposedLoad(block, info.alloca))
      return false;
  for (BasicBlock *block : info.useBlocks) {
    Inst *current = nullptr;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if (inst->getOp() == OP_STORE && inst->getArg(0) == info.alloca) {
        current = inst->getArg(1);
      } else if (inst->getOp() == OP_LOAD && inst->getArg(0) == info.alloca) {
        assert(current);
        replaceAllUsesWith(function, inst, current);
      }
    }
  }
  return true;
}

void eraseAll(const std::vector<Inst *> &instructions) {
  for (Inst *inst : instructions)
    if (!inst || inst->isErased() || !inst->eraseFromBlock())
      std::abort();
}

bool trySingleStore(Function *function, const AllocaInfo &info,
                    const DomAnalysis &dom) {
  if (info.stores.size() != 1)
    return false;
  Inst *store = info.stores.front();
  BasicBlock *storeBlock = store->parentBlock();
  bool seenStore = false;
  for (Inst *inst = storeBlock->firstInst(); inst; inst = inst->next()) {
    if (inst == store) {
      seenStore = true;
      continue;
    }
    if (!seenStore && inst->getOp() == OP_LOAD &&
        inst->getArg(0) == info.alloca)
      return false;
  }
  assert(seenStore);
  for (Inst *load : info.loads) {
    BasicBlock *loadBlock = load->parentBlock();
    if (loadBlock != storeBlock && !dom.tree.dominates(storeBlock, loadBlock))
      return false;
  }

  for (Inst *load : info.loads)
    replaceAllUsesWith(function, load, store->getArg(1));
  eraseAll(info.loads);
  eraseAll(info.stores);
  if (!info.alloca->eraseFromBlock())
    std::abort();
  return true;
}

struct PhiBinding {
  Inst *phi = nullptr; // Mem2Reg新建的Phi
  usize id = 0;        // 对应Alloca的稠密编号
};

struct Promotion {
  Inst *alloca = nullptr;       // 待由主算法提升的Alloca
  Inst *initialValue = nullptr; // 入口处的初始SSA值
};

using BlockPhiMap = std::unordered_map<BasicBlock *, std::vector<PhiBinding>>;

void placePhis(const AllocaInfo &info, usize id, const DomAnalysis &dom,
               IRBuilder &builder, Inst *undef, BlockPhiMap &blockPhis) {
  std::unordered_set<BasicBlock *> definitions(info.defBlocks.begin(),
                                               info.defBlocks.end());
  std::unordered_set<BasicBlock *> liveIn;
  std::vector<BasicBlock *> liveWorklist;
  for (BasicBlock *block : info.useBlocks) {
    if (hasUpwardExposedLoad(block, info.alloca) && liveIn.insert(block).second)
      liveWorklist.push_back(block);
  }
  while (!liveWorklist.empty()) {
    BasicBlock *block = liveWorklist.back();
    liveWorklist.pop_back();
    for (u32 slot = 0; slot < block->getPredecessorCount(); ++slot) {
      BasicBlock *predecessor = block->getPredecessor(slot);
      if (!definitions.count(predecessor) && liveIn.insert(predecessor).second)
        liveWorklist.push_back(predecessor);
    }
  }

  std::unordered_set<BasicBlock *> placed;
  std::unordered_set<BasicBlock *> queued = std::move(definitions);
  std::vector<BasicBlock *> worklist = info.defBlocks;
  while (!worklist.empty()) {
    BasicBlock *block = worklist.back();
    worklist.pop_back();
    const auto found = dom.tree.frontier().find(block);
    if (found == dom.tree.frontier().end())
      continue;
    for (BasicBlock *merge : found->second) {
      if (!liveIn.count(merge))
        continue;
      if (!placed.insert(merge).second)
        continue;
      Inst *phi =
          builder.emitPhi(info.alloca->getMem().elementType, merge, undef);
      blockPhis[merge].push_back({phi, id});
      if (queued.insert(merge).second)
        worklist.push_back(merge);
    }
  }
}

void rename(Function *function, const DomAnalysis &dom,
            const std::vector<Promotion> &promotions,
            const BlockPhiMap &blockPhis) {
  std::unordered_map<Inst *, usize> allocaIDs;
  allocaIDs.reserve(promotions.size());
  std::vector<Inst *> currentValues;
  currentValues.reserve(promotions.size());
  for (usize index = 0; index < promotions.size(); ++index) {
    allocaIDs.emplace(promotions[index].alloca, index);
    currentValues.push_back(promotions[index].initialValue);
  }

  struct VersionChange {
    usize id = 0;             // 被覆盖的Alloca编号
    Inst *previous = nullptr; // 进入子树前的SSA值
  };

  struct Frame {
    BasicBlock *block = nullptr; // 当前支配树块
    usize nextChild = 0;         // 下一个待进入的支配子块
    usize restoreSize = 0;       // 进入当前块前的版本日志长度
    bool entered = false;        // 是否已处理当前块
  };
  std::vector<Inst *> toErase;
  std::vector<VersionChange> versionLog;
  std::vector<CFGEditor::PhiEdgeValue> updates;
  const DomChildrenMap &children = dom.tree.children();
  std::vector<Frame> stack{{function->region->first, 0, 0, false}};
  while (!stack.empty()) {
    Frame &frame = stack.back();
    if (!frame.entered) {
      frame.entered = true;
      const auto phiIt = blockPhis.find(frame.block);
      if (phiIt != blockPhis.end()) {
        for (const PhiBinding &binding : phiIt->second) {
          versionLog.push_back({binding.id, currentValues[binding.id]});
          currentValues[binding.id] = binding.phi;
        }
      }
      for (Inst *inst = frame.block->firstInst(); inst; inst = inst->next()) {
        if (inst->getOp() == OP_LOAD) {
          const auto found = allocaIDs.find(inst->getArg(0));
          if (found == allocaIDs.end())
            continue;
          replaceAllUsesWith(function, inst, currentValues[found->second]);
          toErase.push_back(inst);
        } else if (inst->getOp() == OP_STORE) {
          const auto found = allocaIDs.find(inst->getArg(0));
          if (found == allocaIDs.end())
            continue;
          versionLog.push_back({found->second, currentValues[found->second]});
          currentValues[found->second] = inst->getArg(1);
          toErase.push_back(inst);
        }
      }
      forEachSuccessor(frame.block, [&](BasicBlock *successor) {
        const auto found = blockPhis.find(successor);
        if (found == blockPhis.end())
          return;
        updates.clear();
        for (const PhiBinding &binding : found->second)
          updates.push_back({binding.phi, currentValues[binding.id]});
        if (!updates.empty() && !CFGEditor::setPhiEdgeValues(
                                    function, successor, frame.block, updates))
          std::abort();
      });
    }

    const auto childIt = children.find(frame.block);
    if (childIt != children.end() && frame.nextChild < childIt->second.size()) {
      BasicBlock *child = childIt->second[frame.nextChild++];
      stack.push_back({child, 0, versionLog.size(), false});
      continue;
    }

    while (versionLog.size() > frame.restoreSize) {
      const VersionChange &change = versionLog.back();
      currentValues[change.id] = change.previous;
      versionLog.pop_back();
    }
    stack.pop_back();
  }
  eraseAll(toErase);
}

} // namespace

std::string_view Mem2RegPass::name() const noexcept { return "mem2reg"; }

PassResult Mem2RegPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();

  const bool cfgChanged = cleanupDeadBlocks(function);
  if (cfgChanged)
    context.invalidate(function, PreservedAnalyses::none());
  const DomAnalysis &dom = context.get<DomAnalysis>(function);

  BasicBlock *entry = function->region->first;
  std::vector<Inst *> candidates;
  for (Inst *inst = entry->firstInst(); inst; inst = inst->next())
    if (isPromotableAlloca(inst, entry))
      candidates.push_back(inst);

  bool changed = cfgChanged;
  IRBuilder builder(function->module, function);
  BlockPhiMap blockPhis;
  std::unordered_map<IRType, Inst *> undefCache;
  std::vector<Promotion> promotions;
  promotions.reserve(candidates.size());
  for (Inst *candidate : candidates) {
    AllocaInfo info = collectInfo(candidate);
    if (info.loads.empty()) {
      eraseAll(info.stores);
      if (!info.alloca->eraseFromBlock())
        std::abort();
      changed = true;
      continue;
    }
    if (trySingleStore(function, info, dom)) {
      changed = true;
      continue;
    }
    if (tryRewriteLocally(function, info)) {
      eraseAll(info.loads);
      eraseAll(info.stores);
      if (!info.alloca->eraseFromBlock())
        std::abort();
      changed = true;
      continue;
    }
    Inst *&undef = undefCache[info.alloca->getMem().elementType];
    if (!undef)
      undef = builder.makeUndef(info.alloca->getMem().elementType);
    const usize id = promotions.size();
    promotions.push_back({info.alloca, undef});
    placePhis(info, id, dom, builder, undef, blockPhis);
  }

  if (!promotions.empty()) {
    rename(function, dom, promotions, blockPhis);
    for (const Promotion &promotion : promotions)
      if (!promotion.alloca->eraseFromBlock())
        std::abort();
    changed = true;
  }

  if (!changed)
    return PassResult::noChange();
  PreservedAnalyses preserved;
  if (!cfgChanged)
    preserved.preserveCFGAnalyses();
  else
    preserved.preserve<DomAnalysis>();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
