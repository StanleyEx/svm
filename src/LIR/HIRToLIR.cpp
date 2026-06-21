#include "IR.h"
#include "LIRPass.h"

#include <cassert>
#include <limits>
#include <vector>

namespace svm::ir {
namespace {
constexpr i32 kZeroInitUnrollThreshold = 64; // 超过阈值的局部零初始化展开为循环

class HIRToLIR {
public:
  bool run(Module *module);
  bool run(Function *function);

private:
  void hoistAllocas(Function *function);
  void materializeLocalInitializers(Function *function);
  void emitZeroInitializerLoop(Function *function, Inst *anchor, Inst *base,
                               i32 begin, i32 count, IRType type);
  void lowerArrayIndices(Function *function);
  void flattenRegion(Region *region);
  void flattenBlock(BasicBlock *block);
  void expandIf(Inst *inst);
  void expandWhile(Inst *inst);
  void expandFor(Inst *inst);
  void resolveLoopTerminators(Region *region, BasicBlock *continueTarget,
                              BasicBlock *breakTarget);
  void appendJumpIfOpen(BasicBlock *block, BasicBlock *target);

  IRBuilder *builder_ = nullptr;
};

} // namespace

std::string_view HIRToLIRPass::name() const noexcept { return "hir-to-lir"; }

PassResult HIRToLIRPass::run(Module *module, PassContext &) {
  return HIRToLIR().run(module) ? PassResult::changedIR()
                                : PassResult::noChange();
}

bool HIRToLIR::run(Module *module) {
  if (!module)
    return false;
  bool changed = false;
  for (Function *function = module->functionHead; function;
       function = function->next)
    changed |= run(function);
  return changed;
}

bool HIRToLIR::run(Function *function) {
  if (!function || function->isExtern || !function->region ||
      function->phase != IRPhase::HIR)
    return false;
  IRBuilder builder(function->module, function);
  builder_ = &builder;

  hoistAllocas(function);
  materializeLocalInitializers(function);
  lowerArrayIndices(function);
  flattenRegion(function->region);
  function->phase = IRPhase::LIR;
  cleanupDeadBlocks(function);
  computePreds(function);
  computeUses(function);

  builder_ = nullptr;
  return true;
}

void HIRToLIR::hoistAllocas(Function *function) {
  BasicBlock *entry =
      function && function->region ? function->region->first : nullptr;
  if (!entry)
    return;

  std::vector<Inst *> worklist;
  forEachInstRecursive(function->region, [&](Inst *inst) {
    if (inst->getOp() == OP_ALLOCA &&
        !(inst->parentBlock() == entry && inst->atFront()))
      worklist.push_back(inst);
  });
  for (Inst *alloca : worklist) {
    builder_->setInsertAtStart(entry);
    Inst *hoisted = builder_->emitAlloca(alloca->getMem().totalSizeBytes,
                                         alloca->getMem().elementType);
    hoisted->getMem() = alloca->getMem();
    hoisted->sourceLocation = alloca->sourceLocation;
    replaceAllUsesWith(function, alloca, hoisted);
    VERIFY(alloca->eraseFromBlock());
  }
}

void HIRToLIR::materializeLocalInitializers(Function *function) {
  std::vector<Inst *> worklist;
  forEachInstRecursive(function->region, [&](Inst *inst) {
    if (inst->getOp() == OP_LOCAL_INIT_VALUE ||
        inst->getOp() == OP_LOCAL_INIT_ZERO)
      worklist.push_back(inst);
  });
  for (Inst *anchor : worklist) {
    if (!anchor->parentBlock())
      continue;
    builder_->setInsertBefore(anchor);
    builder_->setCurrentSourceLocation(anchor->sourceLocation);
    Inst *base = anchor->getArg(0);
    const i32 begin = anchor->getArg(1)->getImm();
    assert(base && base->getOp() == OP_ALLOCA && begin >= 0);
    const IRType type = base->getMem().elementType;
    const i32 elementSize = typeSizeBytes(type);
    assert(elementSize > 0);
    if (anchor->getOp() == OP_LOCAL_INIT_VALUE) {
      const i64 wideOffset = static_cast<i64>(begin) * elementSize;
      assert(wideOffset <= std::numeric_limits<i32>::max());
      Inst *address = builder_->emitGetPtr(
          base, builder_->iConst(static_cast<i32>(wideOffset)));
      builder_->emitStore(address, anchor->getArg(2), type);
    } else {
      const i32 count = anchor->getArg(2)->getImm();
      assert(count >= 0 && begin <= std::numeric_limits<i32>::max() - count);
      Inst *zero =
          type == TY_F32 ? builder_->fConst(0.0F) : builder_->iConst(0);
      if (count > kZeroInitUnrollThreshold) {
        emitZeroInitializerLoop(function, anchor, base, begin, count, type);
      } else {
        for (i32 index = 0; index < count; ++index) {
          const i64 wideOffset = static_cast<i64>(begin + index) * elementSize;
          assert(wideOffset <= std::numeric_limits<i32>::max());
          Inst *address = builder_->emitGetPtr(
              base, builder_->iConst(static_cast<i32>(wideOffset)));
          builder_->emitStore(address, zero, type);
        }
      }
    }
    base->getMem().initInfo = nullptr;
    VERIFY(anchor->eraseFromBlock());
  }
}

void HIRToLIR::emitZeroInitializerLoop(Function *function, Inst *anchor,
                                       Inst *base, i32 begin, i32 count,
                                       IRType type) {
  assert(function && anchor && base && count > kZeroInitUnrollThreshold);
  BasicBlock *entry = function->region ? function->region->first : nullptr;
  assert(entry);

  builder_->setInsertAtStart(entry);
  Inst *ivAddress = builder_->emitAlloca(typeSizeBytes(TY_I32), TY_I32);

  Region *parent = anchor->parentBlock()->parentRegion;
  Region *body = builder_->newRegion(nullptr, parent);
  BasicBlock *bodyBlock = builder_->newBlockAtEnd(body);
  builder_->setInsertAtEnd(bodyBlock);
  Inst *index = builder_->emitLoad(ivAddress, TY_I32);
  Inst *byteOffset = index;
  const i32 elementSize = typeSizeBytes(type);
  if (elementSize != 1)
    byteOffset =
        builder_->emit(OP_MUL, TY_I32, index, builder_->iConst(elementSize));
  Inst *address = builder_->emitGetPtr(base, byteOffset);
  Inst *zero = type == TY_F32 ? builder_->fConst(0.0F) : builder_->iConst(0);
  builder_->emitStore(address, zero, type);
  builder_->emitYield();

  builder_->setInsertBefore(anchor);
  builder_->emitStore(ivAddress, builder_->iConst(begin), TY_I32);
  builder_->emitFor(builder_->iConst(begin + count), builder_->iConst(1),
                    ivAddress, body);
}

void HIRToLIR::lowerArrayIndices(Function *function) {
  computeUses(function);
  std::vector<Inst *> worklist;
  forEachInstRecursive(function->region, [&](Inst *inst) {
    if (inst->getOp() == OP_ARRAYIDX)
      worklist.push_back(inst);
  });
  for (Inst *arrayIndex : worklist) {
    if (!arrayIndex->parentBlock())
      continue;
    builder_->setInsertBefore(arrayIndex);
    builder_->setCurrentSourceLocation(arrayIndex->sourceLocation);
    Inst *offset = nullptr;
    const ArrayPayload &array = arrayIndex->getArray();
    for (u32 index = 0; index < array.nDims; ++index) {
      assert(array.strides[index] <=
             static_cast<u32>(std::numeric_limits<i32>::max()));
      Inst *stride = builder_->iConst(static_cast<i32>(array.strides[index]));
      Inst *term =
          builder_->emit(OP_MUL, TY_I32, arrayIndex->getArg(index + 1), stride);
      offset = offset ? builder_->emit(OP_ADD, TY_I32, offset, term) : term;
    }
    Inst *replacement = arrayIndex->getArg(0);
    if (offset)
      replacement = builder_->emitGetPtr(replacement, offset, 1);
    replaceAllUsesWith(function, arrayIndex, replacement);
    arrayIndex->eraseFromBlock();
  }
}

void HIRToLIR::flattenRegion(Region *region) {
  for (BasicBlock *block = region ? region->first : nullptr; block;
       block = block->next())
    flattenBlock(block);
}

void HIRToLIR::flattenBlock(BasicBlock *block) {
  for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
    if (inst->getOp() == OP_IF) {
      expandIf(inst);
      return;
    }
    if (inst->getOp() == OP_WHILE) {
      expandWhile(inst);
      return;
    }
    if (inst->getOp() == OP_FOR) {
      expandFor(inst);
      return;
    }
  }
}

// current(prefix, if, suffix) -> current(br) -> then/else -> merge(suffix)
// then和else的正常Yield都改写为跳向merge的JMP 已有终结符保持不变
void HIRToLIR::expandIf(Inst *inst) {
  builder_->setCurrentSourceLocation(inst->sourceLocation);
  BasicBlock *current = inst->parentBlock();
  Region *thenRegion = inst->getScf().r[0];
  Region *elseRegion = inst->getScf().r[1];
  Inst *condition = inst->getArg(0);
  BasicBlock *thenBlock = builder_->newBlockAfter(current);
  BasicBlock *elseBlock =
      elseRegion ? builder_->newBlockAfter(thenBlock) : nullptr;
  BasicBlock *mergeBlock =
      builder_->newBlockAfter(elseBlock ? elseBlock : thenBlock);
  mergeBlock->takeInstructionSuffixAfter(inst);
  builder_->replaceWithBranch(inst, condition, thenBlock,
                              elseBlock ? elseBlock : mergeBlock);
  thenBlock->takeSingleBlockRegion(thenRegion);
  if (thenBlock->lastInst() && thenBlock->lastInst()->getOp() == OP_YIELD)
    builder_->replaceWithJumpAndEraseSuffix(thenBlock->lastInst(), mergeBlock);
  else
    appendJumpIfOpen(thenBlock, mergeBlock);
  if (elseRegion) {
    elseBlock->takeSingleBlockRegion(elseRegion);
    if (elseBlock->lastInst() && elseBlock->lastInst()->getOp() == OP_YIELD)
      builder_->replaceWithJumpAndEraseSuffix(elseBlock->lastInst(),
                                              mergeBlock);
    else
      appendJumpIfOpen(elseBlock, mergeBlock);
  }
}

// current -> condition；condition的Yield i1变为BR(body, after)
// body的正常Yield回跳condition break跳after continue跳condition
void HIRToLIR::expandWhile(Inst *inst) {
  builder_->setCurrentSourceLocation(inst->sourceLocation);
  BasicBlock *current = inst->parentBlock();
  Region *conditionRegion = inst->getScf().r[0];
  Region *bodyRegion = inst->getScf().r[1];
  BasicBlock *conditionBlock = builder_->newBlockAfter(current);
  BasicBlock *bodyBlock = builder_->newBlockAfter(conditionBlock);
  BasicBlock *afterBlock = builder_->newBlockAfter(bodyBlock);
  resolveLoopTerminators(bodyRegion, conditionBlock, afterBlock);
  afterBlock->takeInstructionSuffixAfter(inst);
  builder_->replaceWithJumpAndEraseSuffix(inst, conditionBlock);
  conditionBlock->takeSingleBlockRegion(conditionRegion);
  Inst *yield = conditionBlock->lastInst();
  assert(yield && yield->getOp() == OP_YIELD && yield->getOperandCount() == 1);
  Inst *condition = yield->getArg(0);
  builder_->replaceWithBranch(yield, condition, bodyBlock, afterBlock);
  bodyBlock->takeSingleBlockRegion(bodyRegion);
  if (bodyBlock->lastInst() && bodyBlock->lastInst()->getOp() == OP_YIELD)
    builder_->replaceWithJumpAndEraseSuffix(bodyBlock->lastInst(),
                                            conditionBlock);
  else
    appendJumpIfOpen(bodyBlock, conditionBlock);
}

// current -> preheader(load/cmp/br) -> body -> latch(load/add/store/cmp/br)。
// 首次guard保留zero-trip continue进入latch完成步进 break直接进入after
// 正步长用LT 负常量步长用GT 原OP_FOR后的suffix迁移到after
void HIRToLIR::expandFor(Inst *inst) {
  builder_->setCurrentSourceLocation(inst->sourceLocation);
  BasicBlock *current = inst->parentBlock();
  Region *bodyRegion = inst->getBody();
  Inst *stop = inst->getArg(0);
  Inst *step = inst->getArg(1);
  Inst *address = inst->getArg(2);
  BasicBlock *preheader = builder_->newBlockAfter(current);
  BasicBlock *bodyBlock = builder_->newBlockAfter(preheader);
  BasicBlock *latchBlock = builder_->newBlockAfter(bodyBlock);
  BasicBlock *afterBlock = builder_->newBlockAfter(latchBlock);
  const OpCode comparison =
      step->getOp() == OP_ICONST && step->getImm() < 0 ? OP_GT : OP_LT;
  resolveLoopTerminators(bodyRegion, latchBlock, afterBlock);
  afterBlock->takeInstructionSuffixAfter(inst);
  builder_->replaceWithJumpAndEraseSuffix(inst, preheader);
  builder_->setInsertAtEnd(preheader);
  Inst *start = builder_->emitLoad(address, TY_I32);
  Inst *guard = builder_->emit(comparison, TY_I1, start, stop);
  builder_->emitBranch(guard, bodyBlock, afterBlock);
  bodyBlock->takeSingleBlockRegion(bodyRegion);
  if (bodyBlock->lastInst() && bodyBlock->lastInst()->getOp() == OP_YIELD)
    builder_->replaceWithJumpAndEraseSuffix(bodyBlock->lastInst(), latchBlock);
  else
    appendJumpIfOpen(bodyBlock, latchBlock);
  builder_->setInsertAtEnd(latchBlock);
  Inst *value = builder_->emitLoad(address, TY_I32);
  Inst *next = builder_->emit(OP_ADD, TY_I32, value, step);
  builder_->emitStore(address, next, TY_I32);
  Inst *back = builder_->emit(comparison, TY_I1, next, stop);
  builder_->emitBranch(back, bodyBlock, afterBlock);
}

void HIRToLIR::resolveLoopTerminators(Region *region,
                                      BasicBlock *continueTarget,
                                      BasicBlock *breakTarget) {
  if (!region)
    return;
  for (BasicBlock *block = region->first; block; block = block->next()) {
    for (Inst *inst = block->firstInst(); inst;) {
      Inst *next = inst->next();
      if (inst->getOp() == OP_BREAK)
        builder_->replaceWithJumpAndEraseSuffix(inst, breakTarget);
      else if (inst->getOp() == OP_CONTINUE)
        builder_->replaceWithJumpAndEraseSuffix(inst, continueTarget);
      else if (inst->getOp() == OP_IF) {
        resolveLoopTerminators(inst->getScf().r[0], continueTarget,
                               breakTarget);
        resolveLoopTerminators(inst->getScf().r[1], continueTarget,
                               breakTarget);
      }
      if (inst->getOp() == OP_JMP)
        break;
      inst = next;
    }
  }
}

void HIRToLIR::appendJumpIfOpen(BasicBlock *block, BasicBlock *target) {
  if (block->endsWithTerminator())
    return;
  builder_->setInsertAtEnd(block);
  builder_->emitJump(target);
}
} // namespace svm::ir
