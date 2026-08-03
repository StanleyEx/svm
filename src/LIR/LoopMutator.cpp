#include "LoopMutator.h"
#include "Utils.h"

#include <unordered_set>
#include <utility>

namespace svm::ir {
namespace {

Inst *resolveHeaderPhiForIteration(const HeaderPhiShape &phi, i32 cloneIndex,
                                   const IterationChain &previous) {
  if (headerPhiKeepsInitialValue(phi))
    return phi.preheaderValue;
  return cloneIndex == 0
             ? phi.latchValue
             : previous.mapAt(cloneIndex - 1)->translate(phi.latchValue);
}

LoopCloneIterationResult
cloneLoopIteration(Function *function, const CountedLoopShape &shape,
                   const std::vector<BasicBlock *> &loopBlocks,
                   BasicBlock *insertAfter, i32 cloneIndex,
                   const IterationChain &previous) {
  VERIFY(function && !loopBlocks.empty());
  auto copier = std::make_unique<DeepCopy>(function);

  forEachPhi(shape.header, [&](Inst *headerPhi) {
    const HeaderPhiShape *description = nullptr;
    for (const HeaderPhiShape &candidate : shape.headerPhis)
      if (candidate.phi == headerPhi) {
        description = &candidate;
        break;
      }
    VERIFY(description != nullptr);
    copier->mapInst(headerPhi, resolveHeaderPhiForIteration(
                                   *description, cloneIndex, previous));
  });

  BlockCloneConfig config;
  config.insertAfter = insertAfter;
  config.decideInst = [&](BasicBlock *block, Inst *inst, bool isPhi) {
    if (block == shape.header && isPhi)
      return CloneInstAction::SkipMapped;
    return copier->hasInstMapping(inst) ? CloneInstAction::SkipMapped
                                        : CloneInstAction::Clone;
  };
  std::vector<ClonedBlockPair> blocks = copier->copyBlocks(loopBlocks, config);
  VERIFY(blocks.size() == loopBlocks.size());
  // 每代立即镜像外部incoming 使后续CFG改写始终面对完整Phi元数据
  const bool addedExitPhis = copier->addTranslatedExitPhiIncomings(
      function, blocks, [&](BasicBlock *, BasicBlock *exit) {
        return !shape.loop->contains(exit);
      });
  VERIFY(addedExitPhis);
  std::unordered_set<BasicBlock *> clonedBlocks;
  for (const ClonedBlockPair &pair : blocks)
    clonedBlocks.insert(pair.clone);
  for (const ClonedBlockPair &pair : blocks)
    forEachSuccessor(pair.clone, [&](BasicBlock *successor) {
      if (!clonedBlocks.count(successor))
        VERIFY(CFGEditor::hasConsistentIncomingState(successor));
    });

  LoopCloneIterationResult result;
  result.header = copier->translateBlock(shape.header);
  result.latch = copier->translateBlock(shape.latch);
  result.layoutTail = copier->translateBlock(loopBlocks.back());
  result.copier = std::move(copier);
  return result;
}

} // namespace

DeepCopy *IterationChain::mapAt(i32 index) const noexcept {
  VERIFY(index >= 0 && static_cast<usize>(index) < iterations.size());
  return iterations[static_cast<usize>(index)].copier.get();
}

BasicBlock *IterationChain::firstHeader() const noexcept {
  VERIFY(!iterations.empty());
  return iterations.front().header;
}

BasicBlock *IterationChain::lastLatch() const noexcept {
  VERIFY(!iterations.empty());
  return iterations.back().latch;
}

DeepCopy *IterationChain::lastMap() const noexcept {
  VERIFY(!iterations.empty());
  return iterations.back().copier.get();
}

bool headerPhiKeepsInitialValue(const HeaderPhiShape &phi) noexcept {
  return phi.latchValue == phi.phi ||
         (phi.latchValue && phi.latchValue->isUndefValue());
}

IterationChain cloneLoopIterations(Function *function,
                                   const CountedLoopShape &shape,
                                   const std::vector<BasicBlock *> &loopBlocks,
                                   i32 count) {
  VERIFY(function && shape.loop && !loopBlocks.empty() && count >= 0);
  IterationChain chain;
  chain.iterations.reserve(static_cast<usize>(count));
  for (i32 index = 0; index < count; ++index) {
    BasicBlock *insertAfter =
        index == 0 ? loopBlocks.back() : chain.iterations.back().layoutTail;
    chain.iterations.push_back(cloneLoopIteration(function, shape, loopBlocks,
                                                  insertAfter, index, chain));
  }
  return chain;
}

} // namespace svm::ir
