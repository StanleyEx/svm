#include "IR.h"
#include "LIRPass.h"

#include <unordered_map>
#include <vector>

namespace svm::ir {
namespace {

struct OffsetAccesses {
  i64 byteOffset = 0;           // 相对聚合根的常量字节偏移
  std::vector<Inst *> pointers; // 表示该偏移的地址指令
};

std::optional<i64> constantByteOffset(Inst *pointer) noexcept {
  if (!pointer)
    return std::nullopt;
  if (pointer->getOp() == OP_GETPTR && pointer->getOperandCount() == 2) {
    Inst *index = pointer->getArg(1);
    i64 offset = 0;
    if (index && index->getOp() == OP_ICONST && !index->isUndefValue() &&
        checkedMul(static_cast<i64>(index->getImm()),
                   static_cast<i64>(pointer->getStride()), offset))
      return offset;
    return std::nullopt;
  }
  if (pointer->getOp() != OP_ARRAYIDX)
    return std::nullopt;

  i64 offset = 0;
  const u32 indexCount = pointer->getOperandCount() - 1;
  for (u32 index = 0; index < indexCount; ++index) {
    Inst *subscript = pointer->getArg(index + 1);
    u64 rawStride = 0;
    i64 scaled = 0;
    if (!subscript || subscript->getOp() != OP_ICONST ||
        subscript->isUndefValue() ||
        !arrayIndexStrideBytes(pointer, index, rawStride) ||
        rawStride > static_cast<u64>(std::numeric_limits<i64>::max()) ||
        !checkedMul(static_cast<i64>(subscript->getImm()),
                    static_cast<i64>(rawStride), scaled) ||
        !checkedAdd(offset, scaled, offset))
      return std::nullopt;
  }
  return offset;
}

bool isCompatibleMemoryUse(const Use &use, IRType elementType,
                           u32 elementSize) noexcept {
  const Inst *user = use.user;
  if (!user || user->isErased() || use.argNo != 0)
    return false;
  if (user->getOp() != OP_LOAD && user->getOp() != OP_STORE)
    return false;
  const MemPayload &memory = user->getMem();
  return memory.elementType == elementType &&
         memory.totalSizeBytes == elementSize;
}

bool scalarizeAlloca(Function *function, Inst *alloca, IRBuilder &builder) {
  const MemPayload memory = alloca->getMem();
  const i32 signedElementSize = typeSizeBytes(memory.elementType);
  if (signedElementSize <= 0)
    return false;
  const u32 elementSize = static_cast<u32>(signedElementSize);
  if (memory.totalSizeBytes <= elementSize ||
      memory.totalSizeBytes % elementSize != 0)
    return false;

  if (!alloca->hasUses())
    return VERIFY(alloca->eraseFromBlock());

  std::unordered_map<i64, usize> offsetIDs;
  std::vector<OffsetAccesses> accesses;
  for (const Use *use = alloca->uses(); use; use = use->next) {
    Inst *pointer = use->user;
    if (!pointer || pointer->isErased() || use->argNo != 0 ||
        !isAddressingOp(pointer->getOp()))
      return false;

    const std::optional<i64> byteOffset = constantByteOffset(pointer);
    if (!byteOffset || *byteOffset < 0 ||
        static_cast<u64>(*byteOffset) + elementSize > memory.totalSizeBytes)
      return false;

    for (const Use *pointerUse = pointer->uses(); pointerUse;
         pointerUse = pointerUse->next)
      if (!isCompatibleMemoryUse(*pointerUse, memory.elementType, elementSize))
        return false;

    const auto [found, inserted] =
        offsetIDs.emplace(*byteOffset, accesses.size());
    if (inserted)
      accesses.push_back({*byteOffset, {}});
    accesses[found->second].pointers.push_back(pointer);
  }

  builder.setInsertAfter(alloca);
  std::vector<Inst *> deadPointers;
  for (const OffsetAccesses &access : accesses) {
    UNUSED(access.byteOffset);
    Inst *scalar = builder.emitAlloca(elementSize, memory.elementType);
    for (Inst *pointer : access.pointers) {
      replaceAllUsesWith(function, pointer, scalar);
      deadPointers.push_back(pointer);
    }
  }

  for (Inst *pointer : deadPointers)
    VERIFY(pointer->eraseFromBlock());
  VERIFY(alloca->eraseFromBlock());
  return true;
}

} // namespace

std::string_view SROAPass::name() const noexcept { return "sroa"; }

PassResult SROAPass::run(Function *function, PassContext &) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();

  computeUses(function);
  std::vector<Inst *> allocas;
  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      if (inst->getOp() == OP_ALLOCA)
        allocas.push_back(inst);

  IRBuilder builder(function->module, function);
  bool changed = false;
  for (Inst *alloca : allocas)
    if (!alloca->isErased() && scalarizeAlloca(function, alloca, builder))
      changed = true;

  if (!changed)
    return PassResult::noChange();
  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  preserved.preserveAllModuleAnalyses();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
