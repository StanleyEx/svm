#include "Analysis.h"
#include "LIRPass.h"

#include <algorithm>
#include <limits>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

constexpr u32 kMaxLocalizedBytes = 4096; // 平铺初始化和栈占用的上界

void unlinkGlobal(Module *module, Global *global) {
  VERIFY(module != nullptr && global != nullptr);
  if (global->prev)
    global->prev->next = global->next;
  else
    module->globalHead = global->next;
  if (global->next)
    global->next->prev = global->prev;
  else
    module->globalTail = global->prev;
  global->prev = nullptr;
  global->next = nullptr;
}

Global *syntacticGlobalRoot(Inst *pointer) noexcept {
  for (u32 depth = 0; pointer && depth < 64; ++depth) {
    if (pointer->getOp() == OP_GETGLOBAL)
      return pointer->getGlobal();
    if ((pointer->getOp() != OP_GETPTR && pointer->getOp() != OP_ARRAYIDX) ||
        pointer->getOperandCount() == 0)
      return nullptr;
    pointer = pointer->getArg(0);
  }
  return nullptr;
}

bool hasExplicitStoreToGlobal(Global *global, Module *module) {
  bool found = false;
  for (Function *function = module->functionHead; function && !found;
       function = function->next) {
    if (function->isExtern || !function->region)
      continue;
    forEachInstRecursive(function->region, [&](Inst *inst) {
      if (inst->getOp() == OP_STORE && inst->getOperandCount() >= 1 &&
          syntacticGlobalRoot(inst->getArg(0)) == global)
        found = true;
    });
  }
  return found;
}

bool passedToWritingOrEscapingCall(Global *global, Module *module,
                                   const GlobalSummaryResult &summary) {
  bool unsafe = false;
  for (Function *function = module->functionHead; function && !unsafe;
       function = function->next) {
    if (function->isExtern || !function->region)
      continue;
    forEachInstRecursive(function->region, [&](Inst *inst) {
      if (unsafe || inst->getOp() != OP_CALL)
        return;
      const EffectSummary &effect = summary.calleeEffect(inst->getCallee());
      for (u32 index = 0; index < inst->getOperandCount(); ++index) {
        if (syntacticGlobalRoot(inst->getArg(index)) != global)
          continue;
        if (effect.writesParam(static_cast<i32>(index)) ||
            effect.escapesParam(static_cast<i32>(index)) ||
            effect.writesUnknownGlobal) {
          unsafe = true;
          return;
        }
      }
    });
  }
  return unsafe;
}

bool validGlobalLayout(const Global *global) noexcept {
  if (!global || (global->type != TY_I32 && global->type != TY_F32) ||
      global->numElements == 0 || global->totalSizeBytes == 0 ||
      (global->initSegmentCount != 0 && !global->initSegment))
    return false;
  const i32 elementBytes = typeSizeBytes(global->type);
  if (elementBytes <= 0 ||
      static_cast<u64>(global->numElements) * static_cast<u32>(elementBytes) !=
          global->totalSizeBytes)
    return false;
  u64 initialized = 0;
  for (u32 index = 0; index < global->initSegmentCount; ++index) {
    initialized += global->initSegment[index].count;
    if (initialized > global->numElements)
      return false;
  }
  return true;
}

Inst *initialValue(IRBuilder &builder, const Global *global, u32 index) {
  u32 remaining = index;
  for (u32 segmentIndex = 0; segmentIndex < global->initSegmentCount;
       ++segmentIndex) {
    const GlobalInitSegment &segment = global->initSegment[segmentIndex];
    if (remaining >= segment.count) {
      remaining -= segment.count;
      continue;
    }
    if (!segment.data)
      break;
    if (global->type == TY_F32)
      return builder.fConst(static_cast<const f32 *>(segment.data)[remaining]);
    return builder.iConst(static_cast<const i32 *>(segment.data)[remaining]);
  }
  return global->type == TY_F32 ? builder.fConst(0.0F) : builder.iConst(0);
}

Inst *createLocalizedStorage(Function *function, Global *global) {
  if (!function || !function->region || !function->region->first ||
      !validGlobalLayout(global))
    return nullptr;
  IRBuilder builder(function->module, function);
  builder.setInsertAtStart(function->region->first);
  Inst *storage = builder.emitAlloca(global->totalSizeBytes, global->type);
  const i32 elementBytes = typeSizeBytes(global->type);
  VERIFY(elementBytes > 0);
  for (u32 index = 0; index < global->numElements; ++index) {
    Inst *address = storage;
    if (global->numElements != 1) {
      const u64 byteOffset = static_cast<u64>(index) * elementBytes;
      VERIFY(byteOffset <= static_cast<u64>(std::numeric_limits<i32>::max()));
      address = builder.emitGetPtr(
          storage, builder.iConst(static_cast<i32>(byteOffset)));
    }
    builder.emitStore(address, initialValue(builder, global, index),
                      global->type);
  }
  return storage;
}

void replaceGlobalUses(Function *function, Global *global, Inst *storage) {
  VERIFY(function != nullptr && global != nullptr && storage != nullptr);
  forEachInstRecursive(function->region, [&](Inst *inst) {
    for (u32 index = 0; index < inst->getOperandCount(); ++index) {
      Inst *argument = inst->getArg(index);
      if (argument && argument->getOp() == OP_GETGLOBAL &&
          argument->getGlobal() == global)
        inst->setArg(index, storage);
    }
  });
  const auto found = function->constPools.globalPtrPool.find(global);
  if (found == function->constPools.globalPtrPool.end())
    return;
  Inst *globalPointer = found->second;
  if (globalPointer->hasUses())
    replaceAllUsesWith(function, globalPointer, storage);
  function->constPools.globalPtrPool.erase(found);
}

struct LocalizationCandidate {
  Global *global = nullptr;     // 待本地化全局
  Function *accessor = nullptr; // 唯一访问函数
};

} // namespace

std::string_view GlobalVariableLocalizationPass::name() const noexcept {
  return "global-variable-localization";
}

PassResult GlobalVariableLocalizationPass::run(Module *module,
                                               PassContext &context) {
  if (!module)
    return PassResult::noChange();
  const GlobalSummaryResult &summary =
      context.get<GlobalSummaryAnalysis>(module).result;
  std::vector<Global *> dead;
  std::vector<LocalizationCandidate> candidates;

  for (Global *global = module->globalHead; global; global = global->next) {
    Function *soleAccessor = nullptr;
    bool multipleAccessors = false;
    for (Function *function = module->functionHead; function;
         function = function->next) {
      if (function->isExtern || !function->region)
        continue;
      const EffectSummary &effect = summary.effectOf(function);
      if (!effect.readsUnknownGlobal && !effect.writesUnknownGlobal &&
          !effect.readsGlobal(global) && !effect.writesGlobal(global))
        continue;
      if (soleAccessor) {
        multipleAccessors = true;
        break;
      }
      soleAccessor = function;
    }
    if (!soleAccessor) {
      dead.push_back(global);
      continue;
    }
    if (multipleAccessors ||
        global->origin != Global::GlobalOrigin::SourceGlobal ||
        global->isConst || global->totalSizeBytes >= kMaxLocalizedBytes ||
        soleAccessor->phase != IRPhase::LIR || !validGlobalLayout(global))
      continue;
    if (global->numElements > 1 && hasExplicitStoreToGlobal(global, module))
      continue;
    if (passedToWritingOrEscapingCall(global, module, summary))
      continue;
    const EffectSummary &accessorEffect = summary.effectOf(soleAccessor);
    if (accessorEffect.writesGlobal(global) &&
        !summary.execOf(soleAccessor).isOnce())
      continue;
    candidates.push_back({global, soleAccessor});
  }

  std::vector<Function *> affected;
  affected.reserve(candidates.size());
  for (const LocalizationCandidate &candidate : candidates) {
    Inst *storage =
        createLocalizedStorage(candidate.accessor, candidate.global);
    if (!storage)
      continue;
    replaceGlobalUses(candidate.accessor, candidate.global, storage);
    unlinkGlobal(module, candidate.global);
    if (std::find(affected.begin(), affected.end(), candidate.accessor) ==
        affected.end())
      affected.push_back(candidate.accessor);
  }
  for (Global *global : dead)
    unlinkGlobal(module, global);
  if (affected.empty() && dead.empty())
    return PassResult::noChange();

  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  if (affected.empty())
    preserved.preserveAllFunctionAnalyses();
  PassResult result = PassResult::changedIR(std::move(preserved));
  result.affectedFunctions = std::move(affected);
  return result;
}

} // namespace svm::ir
