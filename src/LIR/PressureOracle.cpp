#include "PressureOracle.h"

#include <algorithm>
#include <limits>
#include <vector>

namespace svm::ir {
namespace {

i32 saturatingI32(i64 value) noexcept {
  return static_cast<i32>(
      std::clamp(value, static_cast<i64>(std::numeric_limits<i32>::min()),
                 static_cast<i64>(std::numeric_limits<i32>::max())));
}

} // namespace

PressureOracle::PressureOracle(Module *module, PressureOracleConfig config)
    : config_(config) {
  if (!module)
    return;
  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (function->isExtern || !function->region)
      continue;
    for (BasicBlock *block = function->region->first; block;
         block = block->next()) {
      for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
        ++moduleBaseline_;
      for (Inst *inst = block->firstInst(); inst; inst = inst->next())
        ++moduleBaseline_;
    }
  }
}

PressureSnapshot PressureOracle::buildSnapshot(Function *function) const {
  PressureSnapshot result;
  if (!function || !function->region)
    return result;

  std::unordered_map<Inst *, i32> indices;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      indices.emplace(phi, result.liveInstructions++);
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      indices.emplace(inst, result.liveInstructions++);
  }

  if (result.liveInstructions > config_.pressureScanCap) {
    result.tooLarge = true;
    return result;
  }
  if (result.liveInstructions == 0)
    return result;

  std::unordered_map<Inst *, i32> lastUses;
  const auto scanUses = [&](Inst *user) {
    const auto userPosition = indices.find(user);
    if (userPosition == indices.end())
      return;
    for (u32 index = 0; index < user->getOperandCount(); ++index) {
      Inst *operand = user->getArg(index);
      const auto definition = indices.find(operand);
      if (definition == indices.end())
        continue;
      i32 &last = lastUses[operand];
      last = std::max(last, userPosition->second);
    }
  };
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      scanUses(phi);
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      scanUses(inst);
  }

  const usize deltaSize = static_cast<usize>(result.liveInstructions) + 1;
  std::vector<i32> gprDelta(deltaSize, 0);
  std::vector<i32> fprDelta(deltaSize, 0);
  for (const auto &[value, definition] : indices) {
    if (isVoid(value->getType()))
      continue;
    const auto use = lastUses.find(value);
    if (use == lastUses.end())
      continue;
    const i32 last = std::max(definition, use->second);
    std::vector<i32> &delta = isFloat(value->getType()) ? fprDelta : gprDelta;
    ++delta[static_cast<usize>(definition)];
    --delta[static_cast<usize>(last) + 1];
  }

  i32 liveGPR = 0;
  i32 liveFPR = 0;
  for (usize index = 0; index < deltaSize; ++index) {
    liveGPR += gprDelta[index];
    liveFPR += fprDelta[index];
    result.peakGPR = std::max(result.peakGPR, liveGPR);
    result.peakFPR = std::max(result.peakFPR, liveFPR);
  }
  return result;
}

const PressureSnapshot &PressureOracle::getSnapshot(Function *function) const {
  const auto found = snapshots_.find(function);
  if (found != snapshots_.end())
    return found->second;
  return snapshots_.emplace(function, buildSnapshot(function)).first->second;
}

const PressureSnapshot &PressureOracle::snapshot(Function *function) {
  return getSnapshot(function);
}

PressureLevel PressureOracle::classify(i32 peak, i32 elevated, i32 high,
                                       bool tooLarge) const noexcept {
  if (tooLarge)
    return PressureLevel::UnknownLarge;
  if (peak >= high)
    return PressureLevel::High;
  if (peak >= elevated)
    return PressureLevel::Elevated;
  return PressureLevel::Low;
}

GrowthHint PressureOracle::hint(Function *function,
                                i32 addedInstructions) const {
  GrowthHint result;
  result.moduleBaseline = moduleBaseline_;
  result.moduleAddedObserved = moduleAdded_;
  result.addedInstructions = addedInstructions;
  const auto functionAdded = functionAdded_.find(function);
  if (functionAdded != functionAdded_.end())
    result.functionAddedObserved = functionAdded->second;
  if (function) {
    const PressureSnapshot &current = getSnapshot(function);
    result.functionLiveInstructions = current.liveInstructions;
    result.functionAfter = saturatingI32(
        static_cast<i64>(current.liveInstructions) + addedInstructions);
    result.gpr = classify(current.peakGPR, config_.gprElevated, config_.gprHigh,
                          current.tooLarge);
    result.fpr = classify(current.peakFPR, config_.fprElevated, config_.fprHigh,
                          current.tooLarge);
    result.overall = static_cast<u8>(result.gpr) >= static_cast<u8>(result.fpr)
                         ? result.gpr
                         : result.fpr;
  }
  if (moduleBaseline_ > 0) {
    result.moduleGrowthRatio =
        static_cast<f64>(static_cast<i64>(moduleAdded_) + addedInstructions) /
        static_cast<f64>(moduleBaseline_);
  }
  return result;
}

void PressureOracle::recordApplied(Function *function, i32 addedInstructions) {
  if (addedInstructions > 0) {
    moduleAdded_ =
        saturatingI32(static_cast<i64>(moduleAdded_) + addedInstructions);
    if (function) {
      i32 &functionAdded = functionAdded_[function];
      functionAdded =
          saturatingI32(static_cast<i64>(functionAdded) + addedInstructions);
    }
  }
  invalidateFunction(function);
}

void PressureOracle::invalidateFunction(Function *function) {
  if (function)
    snapshots_.erase(function);
}

void PressureOracle::invalidateAll() noexcept { snapshots_.clear(); }

} // namespace svm::ir
