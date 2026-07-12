#include "GlobalSummary.h"

namespace svm::ir {

const EffectSummary &
GlobalSummaryResult::effectOf(const Function *function) const {
  if (!function)
    return conservativeEffectSummary();
  if (function->isExtern)
    return externalEffectSummary(function);
  const auto found = effects.find(function);
  return found == effects.end() ? conservativeEffectSummary() : found->second;
}

const EffectSummary &
GlobalSummaryResult::calleeEffect(const Function *callee) const {
  return effectSummaryForCallee(callee, &effects);
}

ExecBound GlobalSummaryResult::execOf(const Function *function) const noexcept {
  const auto found = fnExec.find(const_cast<Function *>(function));
  return found == fnExec.end() ? ExecBound::unknownMany()
                               : found->second.maxExec;
}

const ExecSummary *
GlobalSummaryResult::execSummary(const Function *function) const noexcept {
  const auto found = fnExec.find(const_cast<Function *>(function));
  return found == fnExec.end() ? nullptr : &found->second;
}

const CallSiteSummary *
GlobalSummaryResult::callSiteSummary(const Inst *call) const noexcept {
  const auto found = callSites.find(const_cast<Inst *>(call));
  return found == callSites.end() ? nullptr : &found->second;
}

void buildCallGraphFromLocals(Module *module, const FunctionSummaryMap &locals,
                              CallGraph &graph) {
  graph.clear();
  for (Function *function = module->functionHead; function;
       function = function->next)
    graph.getOrCreate(function);

  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (function->isExtern)
      continue;
    const auto local = locals.find(function);
    if (local == locals.end())
      continue;
    for (const CallSiteLocalInfo &site : local->second.calls)
      if (site.call && site.callee)
        graph.addEdge(function, site.callee, site.call);
  }
  graph.computeSCCs();
}

} // namespace svm::ir
