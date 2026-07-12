#include "Alias.h"
#include "GlobalSummary.h"

#include <optional>

namespace svm::ir {

namespace global_summary_detail {
namespace {

bool hasReachableCycle(Function *function) {
  const std::vector<BasicBlock *> blocks = computeRPO(function);
  std::unordered_map<BasicBlock *, u32> indegrees;
  indegrees.reserve(blocks.size());
  for (BasicBlock *block : blocks)
    indegrees.emplace(block, 0);
  for (BasicBlock *block : blocks)
    forEachSuccessor(block, [&](BasicBlock *successor) {
      const auto found = indegrees.find(successor);
      if (found != indegrees.end())
        ++found->second;
    });

  std::vector<BasicBlock *> worklist;
  worklist.reserve(blocks.size());
  for (const auto &[block, indegree] : indegrees)
    if (indegree == 0)
      worklist.push_back(block);
  usize visited = 0;
  while (!worklist.empty()) {
    BasicBlock *block = worklist.back();
    worklist.pop_back();
    ++visited;
    forEachSuccessor(block, [&](BasicBlock *successor) {
      const auto found = indegrees.find(successor);
      if (found != indegrees.end() && --found->second == 0)
        worklist.push_back(successor);
    });
  }
  return visited != blocks.size();
}

bool sameRoot(const PointerRoot &left, const PointerRoot &right) noexcept {
  if (left.kind != right.kind)
    return false;
  switch (left.kind) {
  case PointerRootKind::Alloca:
    return left.allocaDef == right.allocaDef;
  case PointerRootKind::Global:
    return left.global == right.global;
  case PointerRootKind::Param:
    return left.paramIndex == right.paramIndex;
  case PointerRootKind::Unknown:
    return true;
  }
  return false;
}

std::optional<PointerRoot>
resolvePointerRootImpl(Inst *pointer, std::unordered_set<Inst *> &active,
                       u32 depth) {
  if (!pointer || pointer->getType() != TY_PTR || depth > 256)
    return PointerRoot{};

  switch (pointer->getOp()) {
  case OP_ALLOCA:
    return PointerRoot{PointerRootKind::Alloca, pointer, nullptr, -1};
  case OP_GETGLOBAL: {
    Global *global = pointer->getGlobal();
    return global ? PointerRoot{PointerRootKind::Global, nullptr, global, -1}
                  : PointerRoot{};
  }
  case OP_PARAM:
    return PointerRoot{PointerRootKind::Param, nullptr, nullptr,
                       pointer->getArgNo()};
  case OP_GETPTR:
  case OP_ARRAYIDX:
    return resolvePointerRootImpl(pointer->getArg(0), active, depth + 1);
  default:
    break;
  }

  const bool phi = pointer->getOp() == OP_PHI;
  const bool select = pointer->getOp() == OP_SELECT;
  if (!phi && !select)
    return PointerRoot{};
  if (!active.insert(pointer).second)
    return std::nullopt;

  PointerRoot merged;
  bool haveRoot = false;
  const u32 firstOperand = select ? 1u : 0u;
  for (u32 index = firstOperand; index < pointer->getOperandCount(); ++index) {
    Inst *incoming = pointer->getArg(index);
    if (!incoming || incoming == pointer)
      continue;
    const std::optional<PointerRoot> root =
        resolvePointerRootImpl(incoming, active, depth + 1);
    if (!root)
      continue;
    if (root->kind == PointerRootKind::Unknown ||
        (haveRoot && !sameRoot(merged, *root))) {
      active.erase(pointer);
      return PointerRoot{};
    }
    if (!haveRoot) {
      merged = *root;
      haveRoot = true;
    }
  }
  active.erase(pointer);
  return haveRoot ? std::optional<PointerRoot>(merged)
                  : std::optional<PointerRoot>(PointerRoot{});
}

} // namespace

PointerRoot resolvePointerRoot(Inst *pointer) {
  std::unordered_set<Inst *> active;
  const std::optional<PointerRoot> root =
      resolvePointerRootImpl(pointer, active, 0);
  return root.value_or(PointerRoot{});
}

} // namespace global_summary_detail

namespace {

using global_summary_detail::PointerRoot;
using global_summary_detail::PointerRootKind;
using global_summary_detail::resolvePointerRoot;

void synthesizeLocalEffect(const LocalFunctionSummary &local,
                           EffectSummary &effect) {
  effect = EffectSummary{};
  effect.flags = EffectSummary::F_ALL_OPTIMISTIC;
  const LocalMemoryEffects &memory = local.localMem;

  effect.readsParamMask = memory.readsParamMask;
  effect.writesParamMask = memory.writesParamMask;
  effect.escapesParamMask = memory.escapesParamMask;
  effect.readGlobals = memory.readGlobals;
  effect.writeGlobals = memory.writeGlobals;
  effect.readsUnknownParam = memory.readsUnknownParam;
  effect.writesUnknownParam = memory.writesUnknownParam;
  effect.escapesUnknownParam = memory.escapesUnknownParam;

  if (!effect.readGlobals.empty())
    effect.flags &= static_cast<u8>(~EffectSummary::F_NO_READ_GLOBAL);
  if (!effect.writeGlobals.empty())
    effect.flags &= static_cast<u8>(~EffectSummary::F_NO_WRITE_GLOBAL);
  if (effect.readsParamMask || effect.readsUnknownParam)
    effect.flags &= static_cast<u8>(~EffectSummary::F_NO_READ_PARAM);
  if (effect.writesParamMask || effect.writesUnknownParam)
    effect.flags &= static_cast<u8>(~EffectSummary::F_NO_WRITE_PARAM);
  if (effect.escapesParamMask || effect.escapesUnknownParam)
    effect.flags &= static_cast<u8>(~EffectSummary::F_NO_ESCAPE_PARAM);

  if (memory.readsUnknownRoot) {
    effect.flags &= static_cast<u8>(
        ~(EffectSummary::F_NO_READ_GLOBAL | EffectSummary::F_NO_READ_PARAM));
    effect.readsUnknownGlobal = true;
    effect.readsUnknownParam = true;
    effect.readsParamMask = 0xFFFFu;
  }
  if (memory.writesUnknownRoot) {
    effect.flags &= static_cast<u8>(
        ~(EffectSummary::F_NO_WRITE_GLOBAL | EffectSummary::F_NO_WRITE_PARAM));
    effect.writesUnknownGlobal = true;
    effect.writesUnknownParam = true;
    effect.writesParamMask = 0xFFFFu;
  }

  for (const CallSiteLocalInfo &site : local.calls) {
    if (!site.callee || site.callee->isExtern) {
      effect.flags &= static_cast<u8>(~EffectSummary::F_NO_EXTERNAL);
      break;
    }
  }
  if (local.mayNotTerminateLocally)
    effect.flags &= static_cast<u8>(~EffectSummary::F_NO_INF_LOOP);
  effect.noTrap = !local.mayTrapLocally;
}

LocalFunctionSummary collectOne(Function *function) {
  LocalFunctionSummary local;
  local.function = function;
  local.isExternal = function->isExtern;
  local.hasBody = !function->isExtern && function->region;
  if (function->isExtern) {
    local.localEffect = externalEffectSummary(function);
    return local;
  }
  if (!local.hasBody) {
    local.localEffect = conservativeEffectSummary();
    return local;
  }

  AliasInfo aliases;
  aliases.build(function, nullptr);

  LocalMemoryEffects &memory = local.localMem;
  auto markParamEscape = [&](i32 index) {
    if (index >= 0 && index < 16)
      memory.escapesParamMask |= static_cast<u16>(u16{1} << index);
    else if (index >= 16)
      memory.escapesUnknownParam = true;
  };
  auto markUnknownEscape = [&]() {
    memory.escapesUnknownParam = true;
    memory.escapesParamMask = 0xFFFFu;
  };

  auto walkRegion = [&](Region *region, u32 loopDepth, auto &self) -> void {
    if (!region)
      return;
    for (BasicBlock *block = region->first; block; block = block->next()) {
      ++local.blockCount;
      auto inspect = [&](Inst *inst) {
        ++local.instCount;
        const OpCode op = inst->getOp();
        if (op == OP_DIV || op == OP_MOD) {
          Inst *divisor =
              inst->getOperandCount() == 2 ? inst->getArg(1) : nullptr;
          if (!divisor || divisor->getOp() != OP_ICONST ||
              divisor->getImm() == 0)
            local.mayTrapLocally = true;
        } else if (op == OP_LOAD || op == OP_STORE) {
          if (!aliases.isDereferenceable(
                  MemoryLocation::fromMemoryInstruction(inst)))
            local.mayTrapLocally = true;
        } else if (op == OP_UNREACHABLE || isMachineLoad(op) ||
                   isMachineStore(op)) {
          local.mayTrapLocally = true;
        }
        if (op == OP_LOAD) {
          const PointerRoot root = resolvePointerRoot(inst->getArg(0));
          if (root.kind == PointerRootKind::Global)
            memory.readGlobals.insert(root.global);
          else if (root.kind == PointerRootKind::Param) {
            if (root.paramIndex >= 0 && root.paramIndex < 16)
              memory.readsParamMask |=
                  static_cast<u16>(u16{1} << root.paramIndex);
            else if (root.paramIndex >= 16)
              memory.readsUnknownParam = true;
          } else if (root.kind == PointerRootKind::Unknown) {
            memory.readsUnknownRoot = true;
          }
        } else if (isMachineLoad(op)) {
          memory.readsUnknownRoot = true;
        } else if (op == OP_STORE) {
          const PointerRoot root = resolvePointerRoot(inst->getArg(0));
          if (root.kind == PointerRootKind::Global)
            memory.writeGlobals.insert(root.global);
          else if (root.kind == PointerRootKind::Param) {
            if (root.paramIndex >= 0 && root.paramIndex < 16)
              memory.writesParamMask |=
                  static_cast<u16>(u16{1} << root.paramIndex);
            else if (root.paramIndex >= 16)
              memory.writesUnknownParam = true;
          } else if (root.kind == PointerRootKind::Unknown) {
            memory.writesUnknownRoot = true;
          }

          Inst *value = inst->getArg(1);
          if (value && value->getType() == TY_PTR) {
            const PointerRoot valueRoot = resolvePointerRoot(value);
            if (valueRoot.kind == PointerRootKind::Param)
              markParamEscape(valueRoot.paramIndex);
            else if (valueRoot.kind == PointerRootKind::Unknown)
              markUnknownEscape();
          }
        } else if (isMachineStore(op)) {
          memory.writesUnknownRoot = true;
        } else if (op == OP_RET || op == MOP_RET) {
          if (inst->getOperandCount() != 0) {
            Inst *value = inst->getArg(0);
            if (value && value->getType() == TY_PTR) {
              const PointerRoot root = resolvePointerRoot(value);
              if (root.kind == PointerRootKind::Param)
                markParamEscape(root.paramIndex);
              else if (root.kind == PointerRootKind::Unknown)
                markUnknownEscape();
            }
          }
        } else if (op == OP_CALL || op == MOP_CALL) {
          ++local.callCount;
          CallSiteLocalInfo site;
          site.callee = inst->getCallee();
          site.call = inst;
          site.lexicalLoopDepth = loopDepth;
          site.args.reserve(inst->getOperandCount());
          for (u32 index = 0; index < inst->getOperandCount(); ++index)
            site.args.push_back(inst->getArg(index));
          local.calls.push_back(std::move(site));
        }

        if (isLoopOp(op))
          local.mayNotTerminateLocally = true;
        const u32 childDepth = loopDepth + (isLoopOp(op) ? 1u : 0u);
        if (op == OP_FOR)
          self(inst->getBody(), childDepth, self);
        else if (op == OP_IF || op == OP_WHILE) {
          self(inst->getScf().r[0], childDepth, self);
          self(inst->getScf().r[1], childDepth, self);
        }
      };
      forEachPhi(block, inspect);
      forEachInst(block, inspect);
    }
  };
  walkRegion(function->region, 0, walkRegion);

  if (function->phase != IRPhase::HIR &&
      global_summary_detail::hasReachableCycle(function))
    local.mayNotTerminateLocally = true;
  synthesizeLocalEffect(local, local.localEffect);
  return local;
}

} // namespace

FunctionSummaryMap collectLocalSummaries(Module *module) {
  FunctionSummaryMap summaries;
  if (!module)
    return summaries;
  for (Function *function = module->functionHead; function;
       function = function->next)
    summaries.emplace(function, collectOne(function));
  return summaries;
}

} // namespace svm::ir
