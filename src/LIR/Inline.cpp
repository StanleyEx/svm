#include "Analysis.h"
#include "DeepCopy.h"
#include "IR.h"
#include "LIRPass.h"

#include <algorithm>
#include <limits>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

constexpr u32 kMaxInlineIterations = 8;
constexpr u32 kMaxCallerInstructions = 20000;
constexpr u32 kRecursiveInstructionLimit = 128;
constexpr u32 kRecursiveExpansionsPerFunction = 1;

u32 countInstructions(const Function *function) noexcept {
  if (!function || !function->region)
    return 0;
  u32 count = 0;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      ++count;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      ++count;
  }
  return count;
}

u32 countInstructionsRejectingSelfRecursion(const Function *function) noexcept {
  if (!function || !function->region || !function->region->first)
    return std::numeric_limits<u32>::max();
  u32 count = 0;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      ++count;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      ++count;
      if (inst->getOp() == OP_CALL && inst->getCallee() == function)
        return std::numeric_limits<u32>::max();
    }
  }
  return count;
}

bool hasValidReturnShape(const Function *function) noexcept {
  if (!function || !function->region)
    return false;
  u32 returns = 0;
  bool valid = true;
  forEachInstRecursive(function->region, [&](Inst *inst) {
    if (!valid || inst->getOp() != OP_RET)
      return;
    ++returns;
    const u32 expected = function->returnType == TY_VOID ? 0U : 1U;
    valid =
        inst->getOperandCount() == expected &&
        (expected == 0 || inst->getArg(0)->getType() == function->returnType);
  });
  return valid && (function->returnType == TY_VOID || returns != 0);
}

bool isInlineableCall(const Inst *call, const Function *callee) noexcept {
  if (!call || !callee || call->isErased() || call->getOp() != OP_CALL ||
      call->getCallee() != callee || callee->isExtern || !callee->region ||
      !callee->region->first || callee->phase != IRPhase::LIR ||
      (callee->functionType && callee->functionType->isVariadic) ||
      call->getOperandCount() != callee->paramCount ||
      call->getType() != callee->returnType || !hasValidReturnShape(callee))
    return false;
  for (u32 index = 0; index < callee->paramCount; ++index)
    if (call->getArg(index)->getType() != callee->paramTypes[index])
      return false;
  return true;
}

bool hasOnlyConstantArguments(const Inst *call) noexcept {
  if (!call || call->getOperandCount() == 0)
    return false;
  for (u32 index = 0; index < call->getOperandCount(); ++index) {
    const OpCode op = call->getArg(index)->getOp();
    if (op != OP_ICONST && op != OP_FCONST)
      return false;
  }
  return true;
}

bool canExpandDirectRecursion(
    Inst *call, const GlobalSummaryResult &summary, u32 instructionCount,
    const std::unordered_map<Function *, u32> &expansions) noexcept {
  if (!call || call->getOp() != OP_CALL || !call->parentBlock())
    return false;
  Function *callee = call->getCallee();
  Region *region = call->parentBlock()->parentRegion;
  Function *caller = region ? region->function : nullptr;
  const auto found = expansions.find(callee);
  const u32 expanded = found == expansions.end() ? 0 : found->second;
  return caller && callee && caller == callee && instructionCount != 0 &&
         instructionCount <= kRecursiveInstructionLimit &&
         expanded < kRecursiveExpansionsPerFunction &&
         callee->returnType != TY_VOID && call->hasUses() &&
         summary.calleeEffect(callee).isReadNoneNoSideEffect();
}

bool isDiscardablePatternInst(const Inst *inst) noexcept {
  if (!inst || inst->getOp() == OP_DIV || inst->getOp() == OP_MOD)
    return false;
  return isArithmetic(inst->getOp()) || isCompare(inst->getOp()) ||
         isConversion(inst->getOp()) || inst->getOp() == OP_LNOT ||
         inst->getOp() == OP_SELECT || inst->getOp() == OP_GETPTR;
}

bool matchCancelingFloatRecursion(Function *function,
                                  const GlobalSummaryResult &summary) noexcept {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      function->returnType != TY_F32 || function->paramCount != 2 ||
      function->paramTypes[0] != TY_F32 || function->paramTypes[1] != TY_I32 ||
      !function->region)
    return false;
  if (!summary.calleeEffect(function).isReadNoneNoSideEffect())
    return false;

  BasicBlock *entry = function->region->first;
  if (!entry || entry->firstPhi())
    return false;
  Inst *condition = entry->firstInst();
  Inst *branch = condition ? condition->next() : nullptr;
  if (!condition || !branch || branch->next() || condition->getOp() != OP_LT ||
      condition->getOperandCount() != 2 ||
      condition->getArg(0) != function->params[1] ||
      condition->getArg(1)->getOp() != OP_ICONST ||
      condition->getArg(1)->getImm() != 0 || branch->getOp() != OP_BR ||
      branch->getArg(0) != condition)
    return false;

  auto isZeroReturn = [](BasicBlock *block) {
    Inst *ret =
        block && block->endsWithTerminator() ? block->terminator() : nullptr;
    return ret && ret->getOperandCount() == 1 && ret->getOp() == OP_RET &&
           ret->getArg(0)->getOp() == OP_FCONST &&
           ret->getArg(0)->getFimm() == 0.0F;
  };
  BasicBlock *base = nullptr;
  BasicBlock *step = nullptr;
  if (isZeroReturn(branch->getBr().trueBB)) {
    base = branch->getBr().trueBB;
    step = branch->getBr().falseBB;
  } else if (isZeroReturn(branch->getBr().falseBB)) {
    base = branch->getBr().falseBB;
    step = branch->getBr().trueBB;
  } else {
    return false;
  }
  if (!base || !step || base == step)
    return false;

  std::vector<BasicBlock *> stepPath;
  std::unordered_set<BasicBlock *> pathSet;
  for (BasicBlock *block = step;;) {
    if (!block || block == entry || block == base ||
        block->parentRegion != function->region ||
        !pathSet.insert(block).second || !block->endsWithTerminator())
      return false;
    stepPath.push_back(block);
    Inst *terminator = block->terminator();
    if (terminator->getOp() == OP_RET)
      break;
    if (terminator->getOp() != OP_JMP)
      return false;
    block = terminator->getJumpTarget();
  }

  Inst *decrement = nullptr;
  Inst *firstCall = nullptr;
  Inst *sum = nullptr;
  Inst *secondCall = nullptr;
  Inst *difference = nullptr;
  Inst *matchedReturn = nullptr;
  for (BasicBlock *block : stepPath) {
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if (inst->getOp() == OP_SUB && inst->getOperandCount() == 2 &&
          inst->getArg(0) == function->params[1] &&
          inst->getArg(1)->getOp() == OP_ICONST &&
          inst->getArg(1)->getImm() == 1) {
        decrement = inst;
        continue;
      }
      if (!decrement)
        continue;
      if (inst->getOp() == OP_CALL && inst->getCallee() == function &&
          inst->getOperandCount() == 2 &&
          inst->getArg(0) == function->params[0] &&
          inst->getArg(1) == decrement) {
        firstCall = inst;
        continue;
      }
      if (firstCall && inst->getOp() == OP_FADD &&
          inst->getOperandCount() == 2 &&
          ((inst->getArg(0) == function->params[0] &&
            inst->getArg(1) == firstCall) ||
           (inst->getArg(1) == function->params[0] &&
            inst->getArg(0) == firstCall))) {
        sum = inst;
        continue;
      }
      if (sum && inst->getOp() == OP_CALL && inst->getCallee() == function &&
          inst->getOperandCount() == 2 && inst->getArg(0) == sum &&
          inst->getArg(1) == decrement) {
        secondCall = inst;
        continue;
      }
      if (secondCall && inst->getOp() == OP_FSUB &&
          inst->getOperandCount() == 2 && inst->getArg(0) == sum &&
          inst->getArg(1) == secondCall) {
        difference = inst;
        continue;
      }
      if (difference && inst->getOp() == OP_RET &&
          inst->getOperandCount() == 1 && inst->getArg(0) == difference) {
        matchedReturn = inst;
        break;
      }
    }
    if (matchedReturn)
      break;
  }
  if (!matchedReturn || matchedReturn != stepPath.back()->terminator())
    return false;

  std::unordered_set<const Inst *> required = {
      condition, branch,     base->terminator(), decrement,     firstCall,
      sum,       secondCall, difference,         matchedReturn,
  };
  for (BasicBlock *block : stepPath)
    if (block->terminator()->getOp() == OP_JMP)
      required.insert(block->terminator());
  auto validExtras = [&](BasicBlock *block) {
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      if (required.count(inst) == 0 && !isDiscardablePatternInst(inst))
        return false;
    return true;
  };
  if (!validExtras(entry) || !validExtras(base))
    return false;
  return std::all_of(stepPath.begin(), stepPath.end(), validExtras);
}

std::string uniqueFallbackName(Module *module, const Function *function) {
  const std::string base =
      std::string(function->name ? function->name : "function") +
      ".inline_fallback";
  std::string candidate = base;
  for (u32 suffix = 0;; ++suffix) {
    bool exists = false;
    for (Function *other = module->functionHead; other; other = other->next)
      if (other->name && candidate == other->name) {
        exists = true;
        break;
      }
    if (!exists)
      return candidate;
    candidate = base + "." + std::to_string(suffix + 1);
  }
}

Function *foldCancelingFloatRecursion(Function *function) {
  const std::string fallbackName =
      uniqueFallbackName(function->module, function);
  Function *fallback = DeepCopy::copyFunction(function, fallbackName.c_str());
  if (!fallback)
    return nullptr;

  IRBuilder builder(function->module, function);
  function->region = builder.newRegion(nullptr, nullptr);
  BasicBlock *entry = builder.newBlockAtEnd(function->region);
  BasicBlock *baseReturn = builder.newBlockAtEnd(function->region);
  BasicBlock *upperCheck = builder.newBlockAtEnd(function->region);
  BasicBlock *lowerCheck = builder.newBlockAtEnd(function->region);
  BasicBlock *parityCheck = builder.newBlockAtEnd(function->region);
  BasicBlock *evenReturn = builder.newBlockAtEnd(function->region);
  BasicBlock *oddReturn = builder.newBlockAtEnd(function->region);
  BasicBlock *fallbackReturn = builder.newBlockAtEnd(function->region);

  Inst *zeroI = builder.iConst(0);
  Inst *twoI = builder.iConst(2);
  Inst *zeroF = builder.fConst(0.0F);
  const f32 halfMax = std::numeric_limits<f32>::max() / 2.0F;
  Inst *upperBound = builder.fConst(halfMax);
  Inst *lowerBound = builder.fConst(-halfMax);

  builder.setInsertAtEnd(entry);
  Inst *negative = builder.emit(OP_LT, TY_I1, function->params[1], zeroI);
  builder.emitBranch(negative, baseReturn, upperCheck);

  builder.setInsertAtEnd(baseReturn);
  builder.emitReturn(zeroF);

  builder.setInsertAtEnd(upperCheck);
  Inst *belowUpper =
      builder.emit(OP_FLE, TY_I1, function->params[0], upperBound);
  builder.emitBranch(belowUpper, lowerCheck, fallbackReturn);

  builder.setInsertAtEnd(lowerCheck);
  Inst *aboveLower =
      builder.emit(OP_FGE, TY_I1, function->params[0], lowerBound);
  builder.emitBranch(aboveLower, parityCheck, fallbackReturn);

  builder.setInsertAtEnd(parityCheck);
  Inst *remainder = builder.emit(OP_MOD, TY_I32, function->params[1], twoI);
  Inst *even = builder.emit(OP_EQ, TY_I1, remainder, zeroI);
  builder.emitBranch(even, evenReturn, oddReturn);

  builder.setInsertAtEnd(evenReturn);
  Inst *normalized = builder.emit(OP_FADD, TY_F32, function->params[0], zeroF);
  builder.emitReturn(builder.emit(OP_FSUB, TY_F32, normalized, zeroF));

  builder.setInsertAtEnd(oddReturn);
  Inst *twice =
      builder.emit(OP_FADD, TY_F32, function->params[0], function->params[0]);
  builder.emitReturn(builder.emit(OP_FSUB, TY_F32, twice, twice));

  builder.setInsertAtEnd(fallbackReturn);
  Inst *args[] = {function->params[0], function->params[1]};
  Inst *fallbackCall = builder.emitCall(fallback, args, 2, TY_F32);
  builder.emitReturn(fallbackCall);

  VERIFY(computePreds(function));
  computeUses(function);
  return fallback;
}

bool inlineCall(Inst *call) {
  if (!call || call->isErased() || !call->parentBlock())
    return false;
  BasicBlock *callBlock = call->parentBlock();
  Region *callerRegion = callBlock->parentRegion;
  Function *caller = callerRegion ? callerRegion->function : nullptr;
  Function *callee = call->getCallee();
  if (!caller || !isInlineableCall(call, callee))
    return false;

  BasicBlock *continuation = CFGEditor::splitBlockAfter(caller, call);
  VERIFY(continuation != nullptr);

  DeepCopy copier(caller);
  for (u32 index = 0; index < callee->paramCount; ++index)
    copier.mapInst(callee->params[index], call->getArg(index));

  IRBuilder builder(caller->module, caller);
  RegionCloneConfig config;
  config.externalValueMode = ExternalValueMode::RequireMapped;
  config.insertInto = caller->region;
  config.insertAfter = callBlock;
  config.rewriteTerminator = [&](Inst *source, Inst *clone) {
    if (source->getOp() != OP_RET)
      return false;
    builder.replaceWithJump(clone, continuation);
    return true;
  };
  RegionCloneResult clone = copier.copyRegion(callee->region, config);
  VERIFY(clone.entry != nullptr);
  VERIFY(CFGEditor::rewriteJumpTarget(callBlock, clone.entry));
  VERIFY(computePreds(caller));

  Inst *replacement = nullptr;
  if (callee->returnType != TY_VOID) {
    VERIFY(!clone.returns.empty());
    if (clone.returns.size() == 1) {
      replacement = clone.returns.front().value;
    } else {
      builder.setInsertAtStart(continuation);
      Inst *phi = builder.emitPhi(callee->returnType, continuation,
                                  builder.makeUndef(callee->returnType));
      for (const ClonedReturnSite &site : clone.returns) {
        VERIFY(site.value != nullptr, "非void函数无返回值");
        VERIFY(CFGEditor::setPhiEdgeValues(caller, continuation, site.block,
                                           {{phi, site.value}}));
      }
      replacement = phi;
    }
  }

  if (replacement)
    replaceAllUsesWith(caller, call, replacement);
  VERIFY(call->eraseFromBlock());
  return true;
}

struct InlineCandidate {
  Inst *call = nullptr; // 调用点快照
};

std::unordered_map<Function *, u32> countCallSites(Module *module) {
  std::unordered_map<Function *, u32> counts;
  for (Function *function = module ? module->functionHead : nullptr; function;
       function = function->next) {
    if (function->isExtern || !function->region)
      continue;
    forEachInstRecursive(function->region, [&](Inst *inst) {
      if (inst->getOp() == OP_CALL && inst->getCallee())
        ++counts[inst->getCallee()];
    });
  }
  return counts;
}

bool runInlining(Module *module, PassContext &context, u32 threshold) {
  bool changedAny = false;

  std::vector<Function *> initialFunctions;
  for (Function *function = module->functionHead; function;
       function = function->next)
    initialFunctions.push_back(function);
  std::vector<Function *> foldableRecursions;
  {
    const GlobalSummaryResult &initialSummary =
        context.get<GlobalSummaryAnalysis>(module).result;
    for (Function *function : initialFunctions)
      if (matchCancelingFloatRecursion(function, initialSummary))
        foldableRecursions.push_back(function);
  }
  for (Function *function : foldableRecursions) {
    if (Function *fallback = foldCancelingFloatRecursion(function)) {
      context.notifyFunctionTopologyChanged(fallback);
      changedAny = true;
    }
  }

  const GlobalSummaryResult &summary =
      context.get<GlobalSummaryAnalysis>(module).result;
  std::unordered_map<Function *, u32> recursiveExpansions;

  for (u32 iteration = 0; iteration < kMaxInlineIterations; ++iteration) {
    bool changedIteration = false;
    const auto callSiteCounts = countCallSites(module);

    for (Function *caller = module->functionHead; caller;
         caller = caller->next) {
      if (caller->isExtern || caller->phase != IRPhase::LIR ||
          !caller->region || !caller->region->first)
        continue;
      computeUses(caller);

      std::vector<InlineCandidate> candidates;
      u64 projectedSize = countInstructions(caller);
      for (BasicBlock *block = caller->region->first; block;
           block = block->next()) {
        for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
          if (inst->getOp() != OP_CALL)
            continue;
          Function *callee = inst->getCallee();
          if (!isInlineableCall(inst, callee))
            continue;

          const ExecBound execution = summary.execOf(callee);
          const ExecSummary *facts = summary.execSummary(callee);
          const bool singleStatic = facts && facts->knownCallerCount == 1 &&
                                    facts->nonLoopCallSiteCount == 1;
          const bool constantArguments = hasOnlyConstantArguments(inst);
          const bool uniqueCall = callSiteCounts.count(callee) != 0 &&
                                  callSiteCounts.at(callee) == 1;
          u32 dynamicThreshold = threshold;
          if (execution.isOnce())
            dynamicThreshold = std::max(dynamicThreshold, u32{2000});
          else if (execution.isConstInRange(2, 4))
            dynamicThreshold = std::max(dynamicThreshold, u32{1024});
          else if (singleStatic)
            dynamicThreshold = std::max(dynamicThreshold, u32{512});
          if (constantArguments || uniqueCall)
            dynamicThreshold = std::max(dynamicThreshold, u32{2000});

          const u32 regularCount =
              countInstructionsRejectingSelfRecursion(callee);
          if (regularCount <= dynamicThreshold) {
            if (projectedSize + regularCount > kMaxCallerInstructions)
              continue;
            projectedSize += regularCount;
            candidates.push_back({inst});
            continue;
          }

          const u32 recursiveCount = countInstructions(callee);
          if (changedAny ||
              !canExpandDirectRecursion(inst, summary, recursiveCount,
                                        recursiveExpansions) ||
              projectedSize + recursiveCount > kMaxCallerInstructions)
            continue;
          projectedSize += recursiveCount;
          ++recursiveExpansions[callee];
          candidates.push_back({inst});
        }
      }

      for (const InlineCandidate &candidate : candidates) {
        if (!candidate.call || candidate.call->isErased())
          continue;
        if (!inlineCall(candidate.call))
          continue;
        changedIteration = true;
        changedAny = true;
      }
      if (!candidates.empty())
        computeUses(caller);
    }
    if (!changedIteration)
      break;
  }
  return changedAny;
}

} // namespace

InlinePass::InlinePass(i32 instructionThreshold) noexcept
    : instructionThreshold_(std::max(instructionThreshold, i32{0})) {}

std::string_view InlinePass::name() const noexcept { return "inline"; }

PassResult InlinePass::run(Module *module, PassContext &context) {
  if (!module || instructionThreshold_ <= 0)
    return PassResult::noChange();
  return runInlining(module, context, static_cast<u32>(instructionThreshold_))
             ? PassResult::changedIR()
             : PassResult::noChange();
}

} // namespace svm::ir
