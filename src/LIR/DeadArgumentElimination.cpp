#include "Analysis.h"
#include "IR.h"
#include "LIRPass.h"

#include <algorithm>
#include <cstring>
#include <limits>
#include <unordered_map>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

struct ArgumentValue {
  enum class Kind : u8 {
    None,      // 不可物化
    Int,       // i32位模式
    Float,     // f32位模式
    GlobalPtr, // 零偏移全局地址
  };

  Kind kind = Kind::None;   // 值类别
  u32 bits = 0;             // i32或f32位模式
  Global *global = nullptr; // GlobalPtr目标

  bool operator==(const ArgumentValue &other) const noexcept {
    return kind == other.kind && bits == other.bits && global == other.global;
  }
  bool operator!=(const ArgumentValue &other) const noexcept {
    return !(*this == other);
  }
};

struct CallIndex {
  std::unordered_map<Function *, std::vector<Inst *>> byCallee; // 调用快照
};

struct ParamRewrite {
  explicit ParamRewrite(u32 count = 0)
      : drop(count, 0), map(count, -1), kept(count) {} // 构造旧签名映射

  void markDrop(i32 index) noexcept { // 标记删除旧参数
    if (index >= 0 && static_cast<usize>(index) < drop.size())
      drop[static_cast<usize>(index)] = 1;
  }
  void finish() noexcept { // 生成稠密新编号
    kept = 0;
    for (usize index = 0; index < drop.size(); ++index)
      map[index] = drop[index] ? -1 : static_cast<i32>(kept++);
  }
  bool drops(i32 index) const noexcept { // 查询旧参数是否删除
    return index >= 0 && static_cast<usize>(index) < drop.size() &&
           drop[static_cast<usize>(index)] != 0;
  }
  bool empty() const noexcept { return kept == drop.size(); } // 查询无删除

  std::vector<u8> drop; // 旧参数删除标记
  std::vector<i32> map; // 旧参数到新参数编号
  u32 kept = 0;         // 新签名参数数量
};

struct UniformValueState {
  bool seen = false;   // 是否见过调用点
  bool bad = false;    // 是否存在冲突或不可物化实参
  ArgumentValue value; // 首个可物化实参
};

bool parseArgumentValue(Inst *value, ArgumentValue &result) noexcept {
  if (!value || value->isErased() || value->isUndefValue())
    return false;
  if (value->getOp() == OP_ICONST) {
    result = {ArgumentValue::Kind::Int, static_cast<u32>(value->getImm()),
              nullptr};
    return true;
  }
  if (value->getOp() == OP_FCONST) {
    const f32 immediate = value->getFimm();
    u32 bits = 0;
    std::memcpy(&bits, &immediate, sizeof(bits));
    result = {ArgumentValue::Kind::Float, bits, nullptr};
    return true;
  }
  if (value->getOp() == OP_GETGLOBAL && value->getGlobal()) {
    result = {ArgumentValue::Kind::GlobalPtr, 0, value->getGlobal()};
    return true;
  }
  return false;
}

Inst *materializeArgumentValue(Function *function, const ArgumentValue &value,
                               IRType type) {
  IRBuilder builder(function->module, function);
  if (value.kind == ArgumentValue::Kind::Int) {
    const i32 immediate = i32FromBits(value.bits);
    if (type == TY_I1)
      return builder.i1Const(immediate != 0);
    return type == TY_I32 ? builder.iConst(immediate) : nullptr;
  }
  if (value.kind == ArgumentValue::Kind::Float && type == TY_F32) {
    f32 immediate = 0.0F;
    std::memcpy(&immediate, &value.bits, sizeof(immediate));
    return builder.fConst(immediate);
  }
  if (value.kind == ArgumentValue::Kind::GlobalPtr && type == TY_PTR)
    return builder.getGlobalPtr(value.global);
  return nullptr;
}

bool isArgumentTransformable(const Function *function) noexcept {
  return function && !function->isExtern && function->region &&
         !(function->functionType && function->functionType->isVariadic);
}

CallIndex collectCalls(Module *module) {
  CallIndex result;
  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (function->isExtern || !function->region)
      continue;
    forEachInstRecursive(function->region, [&](Inst *inst) {
      if (inst->getOp() == OP_CALL && inst->getCallee())
        result.byCallee[inst->getCallee()].push_back(inst);
    });
  }
  return result;
}

std::vector<UniformValueState>
computeUniformArguments(Function *callee, const std::vector<Inst *> &calls) {
  std::vector<UniformValueState> result(callee->paramCount);
  for (Inst *call : calls) {
    if (!call || call->isErased() || call->getOp() != OP_CALL ||
        call->getCallee() != callee)
      continue;
    for (u32 index = 0; index < callee->paramCount; ++index) {
      UniformValueState &state = result[index];
      ArgumentValue value;
      if (index >= call->getOperandCount() ||
          !parseArgumentValue(call->getArg(index), value)) {
        state.bad = true;
      } else if (!state.seen) {
        state.seen = true;
        state.value = value;
      } else if (state.value != value) {
        state.bad = true;
      }
    }
  }
  return result;
}

void compressSignature(Function *function, const ParamRewrite &rewrite) {
  VERIFY(function && rewrite.drop.size() == function->paramCount &&
             rewrite.map.size() == function->paramCount,
         "DAE重写签名不匹配");
  IRType *types = rewrite.kept
                      ? function->arena->createArray<IRType>(rewrite.kept)
                      : nullptr;
  Inst **params = rewrite.kept
                      ? function->arena->createArray<Inst *>(rewrite.kept)
                      : nullptr;
  for (u32 oldIndex = 0; oldIndex < function->paramCount; ++oldIndex) {
    if (rewrite.drop[oldIndex]) {
      VERIFY(function->params[oldIndex]->hasNoUses());
      continue;
    }
    const i32 newIndex = rewrite.map[oldIndex];
    VERIFY(newIndex >= 0 && static_cast<u32>(newIndex) < rewrite.kept);
    types[newIndex] = function->paramTypes[oldIndex];
    params[newIndex] = function->params[oldIndex];
    params[newIndex]->setArgNo(newIndex);
  }
  function->paramCount = rewrite.kept;
  function->paramTypes = types;
  function->params = params;
  function->functionType = nullptr;
}

Inst *rewriteCall(Inst *call, Function *callee, const ParamRewrite &rewrite) {
  if (!call || call->isErased() || call->getOp() != OP_CALL || !callee ||
      !call->parentBlock() || call->getOperandCount() != rewrite.drop.size() ||
      (call->hasUses() && call->getType() != callee->returnType))
    return nullptr;
  Function *caller = call->parentBlock()->parentRegion
                         ? call->parentBlock()->parentRegion->function
                         : nullptr;
  if (!caller)
    return nullptr;
  std::vector<Inst *> arguments;
  arguments.reserve(rewrite.kept);
  for (u32 index = 0; index < call->getOperandCount(); ++index)
    if (!rewrite.drop[index])
      arguments.push_back(call->getArg(index));
  if (arguments.size() != rewrite.kept)
    return nullptr;

  IRBuilder builder(caller->module, caller);
  builder.setInsertBefore(call);
  builder.setCurrentSourceLocation(call->sourceLocation);
  Inst *replacement =
      builder.emitCall(callee, arguments.empty() ? nullptr : arguments.data(),
                       static_cast<u32>(arguments.size()), callee->returnType);
  if (call->hasUses())
    replaceAllUsesWith(caller, call, replacement);
  VERIFY(call->eraseFromBlock());
  return replacement;
}

void rewriteCalls(Function *callee, const std::vector<Inst *> &calls,
                  const ParamRewrite &rewrite) {
  for (Inst *call : calls)
    if (call && !call->isErased() && call->getOp() == OP_CALL &&
        call->getCallee() == callee)
      VERIFY(rewriteCall(call, callee, rewrite) != nullptr);
}

using ParamLiveness = std::unordered_map<Function *, std::vector<u8>>;
using ParamEdges =
    std::unordered_map<Function *,
                       std::vector<std::vector<std::pair<Function *, u32>>>>;
using ParamDependencies = std::unordered_map<Inst *, std::vector<u32>>;

bool isDAETransformable(const Function *function) noexcept {
  if (!isArgumentTransformable(function) || function->phase != IRPhase::LIR ||
      !function->region->first ||
      (function->paramCount != 0 &&
       (!function->params || !function->paramTypes)))
    return false;
  for (u32 index = 0; index < function->paramCount; ++index) {
    const Inst *parameter = function->params[index];
    if (!parameter || parameter->isErased() || parameter->getOp() != OP_PARAM ||
        parameter->getType() != function->paramTypes[index] ||
        parameter->getArgNo() != static_cast<i32>(index))
      return false;
  }
  return true;
}

bool isDerivedValue(const Inst *inst) noexcept {
  if (!inst || inst->getType() == TY_VOID)
    return false;
  const OpCode op = inst->getOp();
  if (op == OP_PHI)
    return true;
  if (isBinaryArithmetic(op)) {
    if (op != OP_DIV && op != OP_MOD)
      return true;
    Inst *divisor = inst->getOperandCount() == 2 ? inst->getArg(1) : nullptr;
    return divisor && divisor->getOp() == OP_ICONST && divisor->getImm() != 0;
  }
  return isUnaryArithmetic(op) || isCompare(op) || isConversion(op) ||
         isAddressingOp(op) || op == OP_SELECT;
}

bool appendUnique(std::vector<u32> &values, u32 value) {
  if (std::find(values.begin(), values.end(), value) != values.end())
    return false;
  values.push_back(value);
  return true;
}

ParamDependencies collectParamDependencies(Function *function) {
  ParamDependencies dependencies;
  for (u32 index = 0; index < function->paramCount; ++index)
    dependencies[function->params[index]].push_back(index);

  bool changed = true;
  while (changed) {
    changed = false;
    forEachInstRecursive(function->region, [&](Inst *inst) {
      if (!isDerivedValue(inst))
        return;
      std::vector<u32> &sources = dependencies[inst];
      for (u32 index = 0; index < inst->getOperandCount(); ++index) {
        const auto found = dependencies.find(inst->getArg(index));
        if (found == dependencies.end())
          continue;
        for (u32 source : found->second)
          changed |= appendUnique(sources, source);
      }
    });
  }
  return dependencies;
}

ParamLiveness computeLiveParameters(Module *module) {
  ParamLiveness live;
  ParamEdges edges;
  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (!isDAETransformable(function))
      continue;
    live.emplace(function, std::vector<u8>(function->paramCount, 0));
    edges.emplace(function,
                  std::vector<std::vector<std::pair<Function *, u32>>>(
                      function->paramCount));

    const ParamDependencies dependencies = collectParamDependencies(function);
    for (const auto &[value, sources] : dependencies) {
      for (const Use *use = value->uses(); use; use = use->next) {
        Inst *user = use->user;
        if (!user || isDerivedValue(user))
          continue;
        if (user->getOp() == OP_CALL) {
          Function *callee = user->getCallee();
          if (isDAETransformable(callee) && use->argNo < callee->paramCount) {
            for (u32 source : sources)
              edges[function][source].push_back({callee, use->argNo});
            continue;
          }
        }
        for (u32 source : sources)
          live[function][source] = 1;
      }
    }
  }

  bool changed = true;
  while (changed) {
    changed = false;
    for (const auto &[function, functionEdges] : edges) {
      for (u32 source = 0; source < functionEdges.size(); ++source) {
        if (live[function][source])
          continue;
        for (const auto &[callee, argument] : functionEdges[source]) {
          const auto destination = live.find(callee);
          const bool destinationLive = destination == live.end() ||
                                       argument >= destination->second.size() ||
                                       destination->second[argument] != 0;
          if (!destinationLive)
            continue;
          live[function][source] = 1;
          changed = true;
          break;
        }
      }
    }
  }
  return live;
}

bool hasValidCalls(Function *callee, const std::vector<Inst *> &calls) {
  for (Inst *call : calls) {
    if (!call || call->isErased() || call->getOp() != OP_CALL ||
        call->getCallee() != callee || !call->parentBlock() ||
        call->getOperandCount() != callee->paramCount ||
        call->getType() != callee->returnType)
      return false;
    Function *caller = call->parentBlock()->parentRegion
                           ? call->parentBlock()->parentRegion->function
                           : nullptr;
    if (!caller || caller->phase != IRPhase::LIR)
      return false;
    for (u32 index = 0; index < callee->paramCount; ++index)
      if (!call->getArg(index) ||
          call->getArg(index)->getType() != callee->paramTypes[index])
        return false;
  }
  return true;
}

bool constantReturnValue(Function *function, ArgumentValue &result) {
  bool seen = false;
  bool valid = true;
  forEachInstRecursive(function->region, [&](Inst *inst) {
    if (!valid || inst->getOp() != OP_RET)
      return;
    ArgumentValue value;
    if (inst->getOperandCount() != 1 || !inst->getArg(0) ||
        inst->getArg(0)->getType() != function->returnType ||
        !parseArgumentValue(inst->getArg(0), value) ||
        (value.kind != ArgumentValue::Kind::Int &&
         value.kind != ArgumentValue::Kind::Float)) {
      valid = false;
      return;
    }
    if (!seen) {
      seen = true;
      result = value;
    } else if (result != value) {
      valid = false;
    }
  });
  return valid && seen;
}

void updateParameterMetadata(Function *function, const ParamRewrite &rewrite) {
  forEachInstRecursive(function->region, [&](Inst *inst) {
    if (inst->getOp() != OP_ALLOCA || inst->getMem().paramIdx < 0)
      return;
    const i32 oldIndex = inst->getMem().paramIdx;
    if (rewrite.drops(oldIndex)) {
      inst->getMem().paramIdx = -1;
      return;
    }
    if (oldIndex < 0 || static_cast<usize>(oldIndex) >= rewrite.map.size()) {
      inst->getMem().paramIdx = -1;
      return;
    }
    const i32 newIndex = rewrite.map[oldIndex];
    VERIFY(newIndex >= 0 && newIndex <= std::numeric_limits<i16>::max());
    inst->getMem().paramIdx = static_cast<i16>(newIndex);
  });
}

bool shrinkOneRound(Module *module, const CallIndex &callIndex,
                    const GlobalSummaryResult &summary) {
  for (Function *function = module->functionHead; function;
       function = function->next)
    if (isDAETransformable(function))
      computeUses(function);
  const ParamLiveness live = computeLiveParameters(module);
  bool changed = false;
  static const std::vector<Inst *> noCalls;

  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (!isDAETransformable(function))
      continue;
    const auto indexedCalls = callIndex.byCallee.find(function);
    const std::vector<Inst *> &calls = indexedCalls == callIndex.byCallee.end()
                                           ? noCalls
                                           : indexedCalls->second;
    if (!hasValidCalls(function, calls))
      continue;

    ParamRewrite rewrite(function->paramCount);
    const std::vector<UniformValueState> uniform =
        computeUniformArguments(function, calls);
    const auto functionLive = live.find(function);
    for (u32 index = 0; index < function->paramCount; ++index) {
      if (uniform[index].seen && !uniform[index].bad) {
        const IRType type = function->paramTypes[index];
        Inst *replacement =
            materializeArgumentValue(function, uniform[index].value, type);
        if (replacement) {
          if (function->params[index]->hasUses())
            replaceAllUsesWith(function, function->params[index], replacement);
          rewrite.markDrop(static_cast<i32>(index));
          continue;
        }
      }

      const bool parameterLive = functionLive != live.end() &&
                                 index < functionLive->second.size() &&
                                 functionLive->second[index] != 0;
      if (parameterLive && function->params[index]->hasUses())
        continue;
      if (function->params[index]->hasUses()) {
        IRBuilder builder(module, function);
        Inst *undef = builder.makeUndef(function->paramTypes[index]);
        replaceAllUsesWith(function, function->params[index], undef);
      }
      rewrite.markDrop(static_cast<i32>(index));
    }
    rewrite.finish();
    if (!rewrite.empty()) {
      rewriteCalls(function, calls, rewrite);
      updateParameterMetadata(function, rewrite);
      compressSignature(function, rewrite);
      computeUses(function);
      changed = true;
      continue;
    }

    if (function->returnType == TY_VOID ||
        function == summary.getEntryPoint() || calls.empty())
      continue;

    ArgumentValue returnValue;
    if (constantReturnValue(function, returnValue)) {
      for (Inst *call : calls) {
        if (!call->hasUses())
          continue;
        Function *caller = call->parentBlock()->parentRegion->function;
        Inst *replacement =
            materializeArgumentValue(caller, returnValue, call->getType());
        if (replacement)
          replaceAllUsesWith(caller, call, replacement);
      }
    }
    if (std::any_of(calls.begin(), calls.end(),
                    [](const Inst *call) { return call->hasUses(); }))
      continue;

    IRBuilder builder(module, function);
    forEachInstRecursive(function->region, [&](Inst *inst) {
      if (inst->getOp() == OP_RET && inst->getOperandCount() != 0)
        builder.replaceInPlace(inst, OP_RET, TY_VOID);
    });
    function->returnType = TY_VOID;
    function->functionType = nullptr;
    ParamRewrite unchanged(function->paramCount);
    unchanged.finish();
    rewriteCalls(function, calls, unchanged);
    changed = true;
  }
  return changed;
}

} // namespace

std::string_view DeadArgumentEliminationPass::name() const noexcept {
  return "dead-argument-elimination";
}

PassResult DeadArgumentEliminationPass::run(Module *module,
                                            PassContext &context) {
  if (!module)
    return PassResult::noChange();
  const GlobalSummaryResult &summary =
      context.get<GlobalSummaryAnalysis>(module).result;
  bool changed = false;
  while (true) {
    const CallIndex calls = collectCalls(module);
    if (!shrinkOneRound(module, calls, summary))
      break;
    changed = true;
  }
  return changed ? PassResult::changedIR() : PassResult::noChange();
}

} // namespace svm::ir
