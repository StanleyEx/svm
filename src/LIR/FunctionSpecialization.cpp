#include "Analysis.h"
#include "DeepCopy.h"
#include "IR.h"
#include "LIRPass.h"
#include "PressureOracle.h"

#include <algorithm>
#include <cstdio>
#include <cstring>
#include <string>
#include <unordered_map>
#include <vector>

namespace svm::ir {
namespace {

struct SpecializationValue {
  enum class Kind : u8 {
    Int,       // i32原始位模式
    Float,     // IEEE754 f32原始位模式
    GlobalPtr, // 零偏移全局地址
  };

  Kind kind = Kind::Int;    // 可重新物化的值类别
  u32 bits = 0;             // i32或f32原始位
  Global *global = nullptr; // GlobalPtr目标

  bool operator==(const SpecializationValue &other) const noexcept {
    return kind == other.kind && bits == other.bits && global == other.global;
  }
};

struct SpecializationKey {
  std::vector<i32> args;                   // 固定的旧参数槽
  std::vector<SpecializationValue> values; // 与参数槽对齐的值

  bool empty() const noexcept { return args.empty(); }
  bool operator==(const SpecializationKey &other) const noexcept {
    return args == other.args && values == other.values;
  }
};

struct KeyGroup {
  SpecializationKey key; // 完整常量tuple
  u32 count = 0;         // 匹配调用点数
};

struct CallIndex {
  std::unordered_map<Function *, std::vector<Inst *>> byCallee; // 调用快照
};

struct ParamRewrite {
  explicit ParamRewrite(u32 count)
      : drop(count, 0), map(count, -1), kept(count) {}

  void markDrop(i32 index) noexcept { // 标记删除旧参数
    if (index >= 0 && static_cast<usize>(index) < drop.size())
      drop[static_cast<usize>(index)] = 1;
  }
  void finish() noexcept { // 生成新编号
    kept = 0;
    for (usize index = 0; index < drop.size(); ++index)
      map[index] = drop[index] ? -1 : static_cast<i32>(kept++);
  }

  std::vector<u8> drop; // 旧参数删除标记
  std::vector<i32> map; // 旧参数到新参数编号
  u32 kept = 0;         // 新签名参数数量
};

bool parseSpecializationValue(Inst *value,
                              SpecializationValue &result) noexcept {
  if (!value || value->isErased() || value->isUndefValue())
    return false;
  if (value->getOp() == OP_ICONST) {
    result = {SpecializationValue::Kind::Int, static_cast<u32>(value->getImm()),
              nullptr};
    return true;
  }
  if (value->getOp() == OP_FCONST) {
    const f32 immediate = value->getFimm();
    u32 bits = 0;
    std::memcpy(&bits, &immediate, sizeof(bits));
    result = {SpecializationValue::Kind::Float, bits, nullptr};
    return true;
  }
  if (value->getOp() == OP_GETGLOBAL && value->getGlobal()) {
    result = {SpecializationValue::Kind::GlobalPtr, 0, value->getGlobal()};
    return true;
  }
  return false;
}

Inst *materializeSpecializationValue(Function *function,
                                     const SpecializationValue &value,
                                     IRType type) {
  IRBuilder builder(function->module, function);
  if (value.kind == SpecializationValue::Kind::Int) {
    const i32 immediate = i32FromBits(value.bits);
    if (type == TY_I1)
      return builder.i1Const(immediate != 0);
    return type == TY_I32 ? builder.iConst(immediate) : nullptr;
  }
  if (value.kind == SpecializationValue::Kind::Float && type == TY_F32) {
    f32 immediate = 0.0F;
    std::memcpy(&immediate, &value.bits, sizeof(immediate));
    return builder.fConst(immediate);
  }
  if (value.kind == SpecializationValue::Kind::GlobalPtr && type == TY_PTR)
    return builder.getGlobalPtr(value.global);
  return nullptr;
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

bool isValidCall(Function *callee, Inst *call) noexcept {
  if (!callee || !call || call->isErased() || call->getOp() != OP_CALL ||
      call->getCallee() != callee || !call->parentBlock() ||
      call->getOperandCount() != callee->paramCount ||
      call->getType() != callee->returnType)
    return false;
  Region *region = call->parentBlock()->parentRegion;
  Function *caller = region ? region->function : nullptr;
  if (!caller || caller->phase != IRPhase::LIR)
    return false;
  for (u32 index = 0; index < callee->paramCount; ++index)
    if (!call->getArg(index) ||
        call->getArg(index)->getType() != callee->paramTypes[index])
      return false;
  return true;
}

SpecializationKey keyFromCall(Function *callee, Inst *call) {
  SpecializationKey key;
  if (!isValidCall(callee, call))
    return key;
  for (u32 index = 0; index < callee->paramCount; ++index) {
    SpecializationValue value;
    if (!parseSpecializationValue(call->getArg(index), value))
      continue;
    key.args.push_back(static_cast<i32>(index));
    key.values.push_back(value);
  }
  return key;
}

bool callMatchesKey(Inst *call, Function *callee,
                    const SpecializationKey &key) noexcept {
  if (!isValidCall(callee, call) || key.args.size() != key.values.size())
    return false;
  for (usize index = 0; index < key.args.size(); ++index) {
    const i32 argument = key.args[index];
    SpecializationValue actual;
    if (argument < 0 || static_cast<u32>(argument) >= call->getOperandCount() ||
        !parseSpecializationValue(call->getArg(argument), actual) ||
        !(actual == key.values[index]))
      return false;
  }
  return true;
}

bool callKeyEquals(Function *callee, Inst *call, const SpecializationKey &key) {
  return callMatchesKey(call, callee, key) && keyFromCall(callee, call) == key;
}

std::vector<KeyGroup> groupKeys(Function *callee,
                                const std::vector<Inst *> &calls,
                                bool &hasNonConstant) {
  std::vector<KeyGroup> groups;
  hasNonConstant = false;
  for (Inst *call : calls) {
    SpecializationKey key = keyFromCall(callee, call);
    if (key.empty()) {
      hasNonConstant = true;
      continue;
    }
    auto found =
        std::find_if(groups.begin(), groups.end(),
                     [&](const KeyGroup &group) { return group.key == key; });
    if (found == groups.end())
      groups.push_back({std::move(key), 1});
    else
      ++found->count;
  }
  return groups;
}

ParamRewrite rewriteForKey(u32 parameterCount, const SpecializationKey &key) {
  ParamRewrite rewrite(parameterCount);
  for (i32 index : key.args)
    rewrite.markDrop(index);
  rewrite.finish();
  return rewrite;
}

void compressCloneSignature(Function *function, const ParamRewrite &rewrite) {
  VERIFY(function && rewrite.drop.size() == function->paramCount &&
             rewrite.map.size() == function->paramCount,
         "特殊化克隆重写必须匹配旧签名");
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
    VERIFY(newIndex >= 0 && static_cast<u32>(newIndex) < rewrite.kept,
           "保留的特殊化后参数需要一个有效的索引");
    types[newIndex] = function->paramTypes[oldIndex];
    params[newIndex] = function->params[oldIndex];
    params[newIndex]->setArgNo(newIndex);
  }
  function->paramCount = rewrite.kept;
  function->paramTypes = types;
  function->params = params;
  function->functionType = nullptr;
}

Inst *rewriteSpecializedCall(Inst *call, Function *callee,
                             const ParamRewrite &rewrite) {
  if (!call || call->isErased() || call->getOp() != OP_CALL || !callee ||
      !call->parentBlock() || call->getOperandCount() != rewrite.drop.size() ||
      call->getType() != callee->returnType ||
      callee->paramCount != rewrite.kept)
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
  for (u32 index = 0; index < rewrite.kept; ++index)
    if (!arguments[index] ||
        arguments[index]->getType() != callee->paramTypes[index])
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

std::string cleanSymbolName(const char *name) {
  std::string result = name ? name : "anon";
  for (char &character : result) {
    const bool valid = (character >= 'a' && character <= 'z') ||
                       (character >= 'A' && character <= 'Z') ||
                       (character >= '0' && character <= '9') ||
                       character == '_' || character == '.';
    if (!valid)
      character = '_';
  }
  return result;
}

std::string valueSuffix(const SpecializationValue &value) {
  char buffer[64] = {};
  if (value.kind == SpecializationValue::Kind::Int) {
    std::snprintf(buffer, sizeof(buffer), "i%08x", value.bits);
    return buffer;
  }
  if (value.kind == SpecializationValue::Kind::Float) {
    std::snprintf(buffer, sizeof(buffer), "f%08x", value.bits);
    return buffer;
  }
  const std::string name =
      cleanSymbolName(value.global ? value.global->name : "null");
  return "g" + std::to_string(name.size()) + "_" + name;
}

std::string keySuffix(const SpecializationKey &key) {
  std::string result;
  for (usize index = 0; index < key.args.size(); ++index) {
    if (!result.empty())
      result += '_';
    result += "arg" + std::to_string(key.args[index]) + '_' +
              valueSuffix(key.values[index]);
  }
  return result;
}

bool isSpecializable(const Function *function) noexcept {
  if (!function || function->isExtern || !function->region ||
      !function->region->first ||
      (function->functionType && function->functionType->isVariadic) ||
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

std::string cloneName(Function *function, const SpecializationKey &key) {
  return cleanSymbolName(function->name ? function->name : "function") +
         ".specialized." + keySuffix(key);
}

Function *findFunction(Module *module, const std::string &name) noexcept {
  for (Function *function = module->functionHead; function;
       function = function->next)
    if (function->name && name == function->name)
      return function;
  return nullptr;
}

bool hasCloneSignature(Function *original, Function *clone,
                       const ParamRewrite &rewrite) noexcept {
  if (clone == original || !isSpecializable(clone) ||
      clone->phase != original->phase ||
      clone->returnType != original->returnType ||
      clone->paramCount != rewrite.kept)
    return false;
  for (u32 oldIndex = 0; oldIndex < original->paramCount; ++oldIndex) {
    const i32 newIndex = rewrite.map[oldIndex];
    if (newIndex >= 0 &&
        clone->paramTypes[newIndex] != original->paramTypes[oldIndex])
      return false;
  }
  return true;
}

void restoreOriginalRecursiveEdges(Function *original, Function *clone) {
  if (!clone || !clone->region)
    return;
  forEachInstRecursive(clone->region, [&](Inst *inst) {
    if (inst->getOp() == OP_CALL && inst->getCallee() == clone)
      inst->setCallee(original);
  });
}

void redirectMatchingRecursiveEdges(Function *original, Function *clone,
                                    const SpecializationKey &key,
                                    const ParamRewrite &rewrite) {
  std::vector<Inst *> calls;
  forEachInstRecursive(clone->region, [&](Inst *inst) {
    if (callMatchesKey(inst, original, key))
      calls.push_back(inst);
  });
  for (Inst *call : calls)
    if (callMatchesKey(call, original, key))
      VERIFY(rewriteSpecializedCall(call, clone, rewrite) != nullptr);
}

Function *cloneForKey(Function *original, const SpecializationKey &key,
                      const ParamRewrite &rewrite, bool allowCreate,
                      bool &created) {
  created = false;
  const std::string name = cloneName(original, key);
  if (Function *existing = findFunction(original->module, name))
    return hasCloneSignature(original, existing, rewrite) ? existing : nullptr;
  if (!allowCreate)
    return nullptr;
  Function *clone = DeepCopy::copyFunction(original, name.c_str());
  if (!clone)
    return nullptr;
  created = true;

  // DeepCopy建立普通函数clone时会闭合全部自递归边
  // 专用化只能闭合仍保持当前常量tuple的边 因此先恢复 再在参数常量化后精确筛选
  restoreOriginalRecursiveEdges(original, clone);
  VERIFY(key.args.size() == key.values.size(), "特殊化键必须有对齐的字段");
  for (usize index = 0; index < key.args.size(); ++index) {
    const i32 argument = key.args[index];
    VERIFY(argument >= 0 && static_cast<u32>(argument) < clone->paramCount);
    const IRType type = clone->paramTypes[argument];
    Inst *constant =
        materializeSpecializationValue(clone, key.values[index], type);
    VERIFY(constant != nullptr && constant->getType() == type);
    if (clone->params[argument]->hasUses())
      replaceAllUsesWith(clone, clone->params[argument], constant);
  }

  compressCloneSignature(clone, rewrite);
  redirectMatchingRecursiveEdges(original, clone, key, rewrite);
  computeUses(clone);
  return clone;
}

bool shouldSpecialize(const std::vector<KeyGroup> &groups, bool hasNonConst,
                      u32 uniformCallSiteThreshold) noexcept {
  if (groups.empty())
    return false;
  if (groups.size() >= 2 || hasNonConst)
    return true;
  return groups.front().count >= uniformCallSiteThreshold;
}

struct SpecializationRun {
  Module *module = nullptr;         // 当前模块
  PassContext *context = nullptr;   // 用于函数拓扑通知
  u32 cloneLimit = 0;               // 新clone总预算
  u32 cloneInstructionLimit = 0;    // 单函数复制体积上限
  u32 uniformCallSiteThreshold = 2; // uniform tuple收益阈值
  u32 clonesCreated = 0;            // 已创建clone数
  PressureOracle *oracle = nullptr; // 共享体积和压力信号源

  bool tryOnce(const CallIndex &calls) {
    for (Function *function = module->functionHead; function;
         function = function->next) {
      const GrowthHint growth =
          oracle ? oracle->hint(function, 0) : GrowthHint{};
      const u32 instructionCount =
          growth.functionLiveInstructions > 0
              ? static_cast<u32>(growth.functionLiveInstructions)
              : 0;
      const GlobalSummaryResult &summary =
          context->get<GlobalSummaryAnalysis>(module).result;
      if (!isSpecializable(function) || function->phase != IRPhase::LIR ||
          summary.getEntryPoint() == function ||
          instructionCount > cloneInstructionLimit ||
          growth.overall == PressureLevel::UnknownLarge)
        continue;
      const auto found = calls.byCallee.find(function);
      if (found == calls.byCallee.end() || found->second.empty())
        continue;
      if (!std::all_of(found->second.begin(), found->second.end(),
                       [&](Inst *call) { return isValidCall(function, call); }))
        continue;

      bool hasNonConst = false;
      const std::vector<KeyGroup> groups =
          groupKeys(function, found->second, hasNonConst);
      if (!shouldSpecialize(groups, hasNonConst, uniformCallSiteThreshold))
        continue;

      bool changed = false;
      i32 addedInstructions = 0;
      for (const KeyGroup &group : groups) {
        const ParamRewrite rewrite =
            rewriteForKey(function->paramCount, group.key);
        bool created = false;
        Function *clone = cloneForKey(function, group.key, rewrite,
                                      clonesCreated < cloneLimit, created);
        if (!clone)
          continue;
        if (created) {
          ++clonesCreated;
          addedInstructions += static_cast<i32>(instructionCount);
          context->notifyFunctionTopologyChanged(clone);
        }

        bool routed = false;
        for (Inst *call : found->second) {
          if (!callKeyEquals(function, call, group.key))
            continue;
          VERIFY(rewriteSpecializedCall(call, clone, rewrite) != nullptr);
          routed = true;
        }
        VERIFY(routed, "特殊化克隆必须至少拥有一个匹配的调用点");
        changed = true;
      }
      if (changed) {
        if (oracle && addedInstructions > 0)
          oracle->recordApplied(nullptr, addedInstructions);
        return true;
      }
    }
    return false;
  }
};

} // namespace

FunctionSpecializationPass::FunctionSpecializationPass(
    u32 cloneLimit, u32 cloneInstructionLimit,
    u32 uniformCallSiteThreshold) noexcept
    : cloneLimit_(cloneLimit), cloneInstructionLimit_(cloneInstructionLimit),
      uniformCallSiteThreshold_(std::max(uniformCallSiteThreshold, u32{2})) {}

std::string_view FunctionSpecializationPass::name() const noexcept {
  return "function-specialization";
}

PassResult FunctionSpecializationPass::run(Module *module,
                                           PassContext &context) {
  if (!module || cloneLimit_ == 0 || cloneInstructionLimit_ == 0)
    return PassResult::noChange();

  PressureOracle oracle(module);
  SpecializationRun run{module,
                        &context,
                        cloneLimit_,
                        cloneInstructionLimit_,
                        uniformCallSiteThreshold_,
                        0,
                        &oracle};
  bool changed = false;
  while (true) {
    const CallIndex calls = collectCalls(module);
    if (!run.tryOnce(calls))
      break;
    changed = true;
  }
  return changed ? PassResult::changedIR() : PassResult::noChange();
}

} // namespace svm::ir
