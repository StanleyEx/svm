#include "GlobalSummary.h"

#include <algorithm>
#include <string>

namespace svm::ir {

namespace {

EffectSummary builtinEffect(u8 clearFlags, u16 reads = 0, u16 writes = 0,
                            u16 escapes = 0) {
  EffectSummary effect;
  effect.flags = static_cast<u8>(EffectSummary::F_ALL_OPTIMISTIC &
                                 static_cast<u8>(~clearFlags));
  effect.readsParamMask = reads;
  effect.writesParamMask = writes;
  effect.escapesParamMask = escapes;
  return effect;
}

const std::unordered_map<std::string, EffectSummary> &builtinEffects() {
  static const std::unordered_map<std::string, EffectSummary> effects = {
      {"getint", builtinEffect(EffectSummary::F_NO_EXTERNAL)},
      {"getch", builtinEffect(EffectSummary::F_NO_EXTERNAL)},
      {"putint", builtinEffect(EffectSummary::F_NO_EXTERNAL)},
      {"putch", builtinEffect(EffectSummary::F_NO_EXTERNAL)},
      {"getfloat", builtinEffect(EffectSummary::F_NO_EXTERNAL)},
      {"putfloat", builtinEffect(EffectSummary::F_NO_EXTERNAL)},
      {"_sysy_starttime", builtinEffect(EffectSummary::F_NO_EXTERNAL)},
      {"_sysy_stoptime", builtinEffect(EffectSummary::F_NO_EXTERNAL)},
      {"getarray",
       builtinEffect(static_cast<u8>(EffectSummary::F_NO_EXTERNAL |
                                     EffectSummary::F_NO_WRITE_PARAM),
                     0, 1u << 0)},
      {"getfarray",
       builtinEffect(static_cast<u8>(EffectSummary::F_NO_EXTERNAL |
                                     EffectSummary::F_NO_WRITE_PARAM),
                     0, 1u << 0)},
      {"putarray",
       builtinEffect(static_cast<u8>(EffectSummary::F_NO_EXTERNAL |
                                     EffectSummary::F_NO_READ_PARAM),
                     1u << 1)},
      {"putfarray",
       builtinEffect(static_cast<u8>(EffectSummary::F_NO_EXTERNAL |
                                     EffectSummary::F_NO_READ_PARAM),
                     1u << 1)},
      {"memset", builtinEffect(static_cast<u8>(EffectSummary::F_NO_EXTERNAL |
                                               EffectSummary::F_NO_WRITE_PARAM),
                               0, 1u << 0)},
  };
  return effects;
}

void propagateCallee(const std::vector<Inst *> &actuals,
                     const EffectSummary &callee, EffectSummary &caller,
                     bool &changed) {
  auto clearFlag = [&](u8 flag) {
    if ((caller.flags & flag) == 0)
      return;
    caller.flags &= static_cast<u8>(~flag);
    changed = true;
  };
  auto addGlobals = [&](std::unordered_set<Global *> &destination,
                        const std::unordered_set<Global *> &source) {
    for (Global *global : source)
      if (destination.insert(global).second)
        changed = true;
  };

  // 参数与逃逸性质必须按实参根映射 其余传递性 F_NO_* 位可以直接下推
  constexpr u8 directFlags =
      EffectSummary::F_NO_READ_GLOBAL | EffectSummary::F_NO_WRITE_GLOBAL |
      EffectSummary::F_NO_RECURSE | EffectSummary::F_NO_EXTERNAL |
      EffectSummary::F_NO_INF_LOOP;
  const u8 lostFlags = static_cast<u8>((~callee.flags) & directFlags);
  const u8 mergedFlags =
      static_cast<u8>(caller.flags & static_cast<u8>(~lostFlags));
  if (mergedFlags != caller.flags) {
    caller.flags = mergedFlags;
    changed = true;
  }
  if (caller.noTrap && !callee.noTrap) {
    caller.noTrap = false;
    changed = true;
  }

  addGlobals(caller.readGlobals, callee.readGlobals);
  addGlobals(caller.writeGlobals, callee.writeGlobals);
  if (!callee.readGlobals.empty())
    clearFlag(EffectSummary::F_NO_READ_GLOBAL);
  if (!callee.writeGlobals.empty())
    clearFlag(EffectSummary::F_NO_WRITE_GLOBAL);
  if (callee.readsUnknownGlobal && !caller.readsUnknownGlobal) {
    caller.readsUnknownGlobal = true;
    changed = true;
  }
  if (callee.readsUnknownGlobal)
    clearFlag(EffectSummary::F_NO_READ_GLOBAL);
  if (callee.writesUnknownGlobal && !caller.writesUnknownGlobal) {
    caller.writesUnknownGlobal = true;
    changed = true;
  }
  if (callee.writesUnknownGlobal)
    clearFlag(EffectSummary::F_NO_WRITE_GLOBAL);

  using global_summary_detail::PointerRoot;
  using global_summary_detail::PointerRootKind;
  auto reflectMemory = [&](Inst *actual, bool reads) {
    if (!actual || actual->getType() != TY_PTR)
      return;
    const PointerRoot root = global_summary_detail::resolvePointerRoot(actual);
    if (root.kind == PointerRootKind::Alloca)
      return;
    if (root.kind == PointerRootKind::Global) {
      auto &globals = reads ? caller.readGlobals : caller.writeGlobals;
      if (globals.insert(root.global).second)
        changed = true;
      clearFlag(reads ? EffectSummary::F_NO_READ_GLOBAL
                      : EffectSummary::F_NO_WRITE_GLOBAL);
      return;
    }
    if (root.kind == PointerRootKind::Param) {
      if (root.paramIndex >= 0 && root.paramIndex < 16) {
        u16 &mask = reads ? caller.readsParamMask : caller.writesParamMask;
        const u16 oldMask = mask;
        mask |= static_cast<u16>(u16{1} << root.paramIndex);
        changed |= mask != oldMask;
      } else if (root.paramIndex >= 16) {
        bool &unknown =
            reads ? caller.readsUnknownParam : caller.writesUnknownParam;
        if (!unknown) {
          unknown = true;
          changed = true;
        }
      } else {
        bool &unknown =
            reads ? caller.readsUnknownParam : caller.writesUnknownParam;
        u16 &mask = reads ? caller.readsParamMask : caller.writesParamMask;
        if (!unknown) {
          unknown = true;
          changed = true;
        }
        if (mask != 0xFFFFu) {
          mask = 0xFFFFu;
          changed = true;
        }
      }
      clearFlag(reads ? EffectSummary::F_NO_READ_PARAM
                      : EffectSummary::F_NO_WRITE_PARAM);
      return;
    }

    clearFlag(reads ? EffectSummary::F_NO_READ_GLOBAL
                    : EffectSummary::F_NO_WRITE_GLOBAL);
    clearFlag(reads ? EffectSummary::F_NO_READ_PARAM
                    : EffectSummary::F_NO_WRITE_PARAM);
    bool &unknownGlobal =
        reads ? caller.readsUnknownGlobal : caller.writesUnknownGlobal;
    bool &unknownParam =
        reads ? caller.readsUnknownParam : caller.writesUnknownParam;
    u16 &paramMask = reads ? caller.readsParamMask : caller.writesParamMask;
    if (!unknownGlobal || !unknownParam || paramMask != 0xFFFFu) {
      unknownGlobal = true;
      unknownParam = true;
      paramMask = 0xFFFFu;
      changed = true;
    }
  };

  const usize preciseCount = std::min<usize>(actuals.size(), 16);
  for (usize index = 0; index < preciseCount; ++index) {
    if (callee.readsParamMask & static_cast<u16>(u16{1} << index))
      reflectMemory(actuals[index], true);
    if (callee.writesParamMask & static_cast<u16>(u16{1} << index))
      reflectMemory(actuals[index], false);
  }
  if (callee.readsUnknownParam)
    for (usize index = 16; index < actuals.size(); ++index)
      reflectMemory(actuals[index], true);
  if (callee.writesUnknownParam)
    for (usize index = 16; index < actuals.size(); ++index)
      reflectMemory(actuals[index], false);

  auto reflectEscape = [&](Inst *actual) {
    if (!actual || actual->getType() != TY_PTR)
      return;
    const PointerRoot root = global_summary_detail::resolvePointerRoot(actual);
    if (root.kind == PointerRootKind::Param && root.paramIndex >= 0 &&
        root.paramIndex < 16) {
      const u16 oldMask = caller.escapesParamMask;
      caller.escapesParamMask |= static_cast<u16>(u16{1} << root.paramIndex);
      changed |= oldMask != caller.escapesParamMask;
      clearFlag(EffectSummary::F_NO_ESCAPE_PARAM);
    } else if (root.kind == PointerRootKind::Param && root.paramIndex >= 16) {
      if (!caller.escapesUnknownParam) {
        caller.escapesUnknownParam = true;
        changed = true;
      }
      clearFlag(EffectSummary::F_NO_ESCAPE_PARAM);
    } else if (root.kind == PointerRootKind::Unknown ||
               (root.kind == PointerRootKind::Param && root.paramIndex < 0)) {
      const u16 oldMask = caller.escapesParamMask;
      caller.escapesParamMask = 0xFFFFu;
      if (oldMask != caller.escapesParamMask || !caller.escapesUnknownParam)
        changed = true;
      caller.escapesUnknownParam = true;
      clearFlag(EffectSummary::F_NO_ESCAPE_PARAM);
    }
  };
  for (usize index = 0; index < preciseCount; ++index)
    if (callee.escapesParamMask & static_cast<u16>(u16{1} << index))
      reflectEscape(actuals[index]);
  if (callee.escapesUnknownParam)
    for (usize index = 16; index < actuals.size(); ++index)
      reflectEscape(actuals[index]);
}

void solveComponent(
    const std::vector<CGNode *> &component, const FunctionSummaryMap &locals,
    std::unordered_map<const Function *, EffectSummary> &effects) {
  bool recursive = false;
  for (CGNode *node : component) {
    recursive |= node->inRecursion;
    const auto local = locals.find(node->function);
    effects[node->function] = local == locals.end()
                                  ? conservativeEffectSummary()
                                  : local->second.localEffect;
  }

  bool changed = false;
  do {
    changed = false;
    for (CGNode *node : component) {
      Function *function = node->function;
      if (function->isExtern)
        continue;
      EffectSummary &caller = effects.at(function);
      const auto local = locals.find(function);
      if (local == locals.end())
        continue;
      for (const CallSiteLocalInfo &site : local->second.calls) {
        if (!site.call)
          continue;
        const EffectSummary *callee = nullptr;
        if (!site.callee || site.callee->isExtern) {
          callee = &effectSummaryForCallee(site.callee, &effects);
        } else {
          const auto found = effects.find(site.callee);
          callee = found == effects.end() ? &conservativeEffectSummary()
                                          : &found->second;
        }
        propagateCallee(site.args, *callee, caller, changed);
      }
      if (node->inRecursion) {
        constexpr u8 recursionFlags =
            EffectSummary::F_NO_RECURSE | EffectSummary::F_NO_INF_LOOP;
        if (caller.flags & recursionFlags) {
          caller.flags &= static_cast<u8>(~recursionFlags);
          changed = true;
        }
      }
    }
  } while (recursive && changed);
}

} // namespace

const EffectSummary &conservativeEffectSummary() {
  static const EffectSummary effect = [] {
    EffectSummary value;
    value.flags = 0;
    value.readsParamMask = 0xFFFFu;
    value.writesParamMask = 0xFFFFu;
    value.escapesParamMask = 0xFFFFu;
    value.readsUnknownGlobal = true;
    value.writesUnknownGlobal = true;
    value.readsUnknownParam = true;
    value.writesUnknownParam = true;
    value.escapesUnknownParam = true;
    return value;
  }();
  return effect;
}

const EffectSummary &externalEffectSummary(const Function *callee) {
  if (!callee || !callee->isExtern || !callee->name)
    return conservativeEffectSummary();
  const auto &builtins = builtinEffects();
  const auto found = builtins.find(callee->name);
  return found == builtins.end() ? conservativeEffectSummary() : found->second;
}

const EffectSummary &effectSummaryForCallee(
    const Function *callee,
    const std::unordered_map<const Function *, EffectSummary> *effects) {
  if (!callee)
    return conservativeEffectSummary();
  if (callee->isExtern)
    return externalEffectSummary(callee);
  if (effects) {
    const auto found = effects->find(callee);
    if (found != effects->end())
      return found->second;
  }
  return conservativeEffectSummary();
}

std::unordered_map<const Function *, EffectSummary>
solveModuleEffects(Module *module, const FunctionSummaryMap &locals,
                   const CallGraph &graph) {
  std::unordered_map<const Function *, EffectSummary> effects;
  if (!module)
    return effects;
  for (const std::vector<CGNode *> &component : graph.sccGroups())
    solveComponent(component, locals, effects);

  for (auto &[function, effect] : effects) {
    if (!function || function->paramCount >= 16)
      continue;
    const u16 validMask =
        function->paramCount == 0
            ? 0
            : static_cast<u16>((u32{1} << function->paramCount) - 1u);
    effect.readsParamMask &= validMask;
    effect.writesParamMask &= validMask;
    effect.escapesParamMask &= validMask;
  }
  return effects;
}

} // namespace svm::ir
