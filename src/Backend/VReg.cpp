#include "VReg.h"

#include <cassert>
#include <unordered_map>
#include <unordered_set>

namespace svm::ir {
namespace {
struct VRegFlagsTable {
  std::unordered_map<const Inst *, VRegMetadata> metadata; // 定义到元数据映射
};

bool isOrdinaryVRegDef(const Inst *inst) noexcept {
  return inst && !isVoid(inst->getType()) && inst->getOp() != MOP_NOP &&
         !inst->isPrecoloredDef();
}

bool isMetadataDef(const Inst *inst) noexcept {
  return inst && !isVoid(inst->getType()) && inst->getOp() != MOP_NOP;
}

bool isPhiGhost(const Inst *inst) noexcept {
  return inst && !inst->parentBlock() && inst->getOp() == OP_PHI &&
         !isVoid(inst->getType());
}

VRegFlagsTable *metadataTable(Function *function) noexcept {
  return static_cast<VRegFlagsTable *>(function->mirVRegFlags);
}

const VRegFlagsTable *metadataTable(const Function *function) noexcept {
  return static_cast<const VRegFlagsTable *>(function->mirVRegFlags);
}

void ensureVRegFlags(Function *function) {
  if (function && !function->mirVRegFlags)
    function->mirVRegFlags = function->arena->create<VRegFlagsTable>();
}

template <class Modify>
void mutateMetadata(Function *function, Inst *def, Modify modify) {
  if (!function || !isMetadataDef(def))
    return;
  ensureVRegFlags(function);
  modify(metadataTable(function)->metadata[def]);
}
} // namespace

void assignNewVReg(Inst *inst, Function *function) {
  if (function && isOrdinaryVRegDef(inst))
    inst->id = function->instCount++;
}

void renumberVRegs(Function *function) {
  if (!function || function->isExtern || !function->region ||
      !function->region->first)
    return;
  assert(function->phase == IRPhase::MIR && "renumberVRegs requires MIR");
  std::unordered_map<u32, u32> ids;
  std::unordered_set<Inst *> seenGhosts;
  u32 nextId = 0;
  auto renumber = [&](u32 oldId) {
    const auto [it, inserted] = ids.emplace(oldId, nextId);
    if (inserted)
      ++nextId;
    return it->second;
  };
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *inst = block->firstPhi(); inst; inst = inst->next())
      if (isOrdinaryVRegDef(inst))
        inst->id = renumber(inst->id);
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if (isOrdinaryVRegDef(inst))
        inst->id = renumber(inst->id);
      for (u32 index = 0; index < inst->getOperandCount(); ++index) {
        Inst *arg = inst->getArg(index);
        if (isPhiGhost(arg) && seenGhosts.insert(arg).second)
          arg->id = renumber(arg->id);
      }
    }
  }
  function->virtualRegisterCount = nextId;
  function->virtualRegisterClasses.assign(nextId, rv64::RC_GPR);
  auto recordClass = [&](const Inst *inst) {
    assert(inst->getType() != TY_F64 && "TY_F64 cannot enter ordinary RA");
    assert(inst->id < function->virtualRegisterCount);
    function->virtualRegisterClasses[inst->id] =
        inst->getType() == TY_F32 ? rv64::RC_FPR : rv64::RC_GPR;
  };
  std::unordered_set<const Inst *> classifiedGhosts;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *inst = block->firstPhi(); inst; inst = inst->next())
      if (isOrdinaryVRegDef(inst))
        recordClass(inst);
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if (isOrdinaryVRegDef(inst))
        recordClass(inst);
      for (u32 index = 0; index < inst->getOperandCount(); ++index) {
        Inst *arg = inst->getArg(index);
        if (isPhiGhost(arg) && classifiedGhosts.insert(arg).second)
          recordClass(arg);
      }
    }
  }
}

VRegMetadata queryVRegMetadata(const Function *function, const Inst *def) {
  if (!function || !def || !function->mirVRegFlags)
    return {};
  const auto &metadata = metadataTable(function)->metadata;
  const auto it = metadata.find(def);
  return it == metadata.end() ? VRegMetadata{} : it->second;
}

void setSpillDepth(Function *function, Inst *def, u8 depth) {
  mutateMetadata(function, def,
                 [&](VRegMetadata &metadata) { metadata.spillDepth = depth; });
}

void setStoreConst(Function *function, Inst *def, bool value) {
  mutateMetadata(function, def,
                 [&](VRegMetadata &metadata) { metadata.storeConst = value; });
}

void setForcedColor(Function *function, Inst *def, rv64::PReg color) {
  mutateMetadata(function, def,
                 [&](VRegMetadata &metadata) { metadata.forcedColor = color; });
}

void attachFactBundle(Function *function, Inst *def,
                      const ScalarFactBundle &bundle) {
  mutateMetadata(function, def, [&](VRegMetadata &metadata) {
    metadata.scalarFacts = bundle;
  });
}

ScalarFactBundle queryFactBundle(const Function *function, const Inst *def) {
  return queryVRegMetadata(function, def).scalarFacts;
}

void cloneVRegMetadata(Function *function, const Inst *oldDef, Inst *newDef,
                       u8 depthDelta) {
  if (!function || !isMetadataDef(newDef))
    return;
  const VRegMetadata source = queryVRegMetadata(function, oldDef);
  const u32 depth = static_cast<u32>(source.spillDepth) + depthDelta;
  mutateMetadata(function, newDef, [&](VRegMetadata &metadata) {
    metadata.spillDepth = static_cast<u8>(depth > 255 ? 255 : depth);
    metadata.storeConst = source.storeConst;
    metadata.forcedColor = rv64::NUM_PREGS;
    metadata.scalarFacts = source.scalarFacts;
    if (metadata.scalarFacts.valid)
      metadata.scalarFacts.source = FactSource::MetadataClone;
  });
}

} // namespace svm::ir
