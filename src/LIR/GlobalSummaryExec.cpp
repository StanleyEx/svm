#include "Analysis.h"
#include "GlobalSummary.h"

#include <algorithm>
#include <cstring>

namespace svm::ir {

namespace {

ExecBound saturatingAdd(ExecBound accumulated, ExecBound contribution,
                        u32 cap) noexcept {
  if (accumulated.isUnknownMany() || contribution.isUnknownMany())
    return ExecBound::unknownMany();
  if (accumulated.isOverCap() || contribution.isOverCap())
    return ExecBound::overCap();
  if (accumulated.isNever())
    return contribution;
  if (contribution.isNever())
    return accumulated;
  const u64 sum = static_cast<u64>(accumulated.n) + contribution.n;
  return sum > cap ? ExecBound::overCap()
                   : ExecBound::constN(static_cast<u32>(sum));
}

} // namespace

void populateExecutionSummaries(Module *module,
                                const FunctionSummaryMap &locals,
                                const CallGraph &graph,
                                ModuleAnalysisManager &manager,
                                GlobalSummaryResult &result) {
  result.fnExec.clear();
  result.callSites.clear();
  if (!module)
    return;

  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (function->isExtern)
      continue;
    ExecSummary summary;
    if (CGNode *node = graph.findNode(function))
      summary.recursiveSCC = node->inRecursion;
    result.fnExec.emplace(function, summary);
    if (function->name && std::strcmp(function->name, "main") == 0)
      result.entryPoint = function;
  }

  bool reachableUnknownCall = false;
  if (result.entryPoint) {
    result.fnExec.at(result.entryPoint).reachableFromEntry = true;
    result.fnExec.at(result.entryPoint).maxExec = ExecBound::constN(1);
    std::vector<Function *> worklist{result.entryPoint};
    while (!worklist.empty()) {
      Function *caller = worklist.back();
      worklist.pop_back();
      const auto local = locals.find(caller);
      if (local != locals.end())
        for (const CallSiteLocalInfo &site : local->second.calls)
          reachableUnknownCall |= site.call && !site.callee;

      CGNode *node = graph.findNode(caller);
      if (!node)
        continue;
      for (const CGNode::Edge &edge : node->callees) {
        Function *callee = edge.callee ? edge.callee->function : nullptr;
        if (!callee || callee->isExtern)
          continue;
        auto found = result.fnExec.find(callee);
        if (found != result.fnExec.end() && !found->second.reachableFromEntry) {
          found->second.reachableFromEntry = true;
          worklist.push_back(callee);
        }
      }
    }
  }

  // 未知直接目标可能命中任意内部函数 也可能形成递归
  if (reachableUnknownCall)
    for (auto &[function, summary] : result.fnExec) {
      UNUSED(function);
      summary.reachableFromEntry = true;
      summary.maxExec = ExecBound::unknownMany();
    }

  std::unordered_map<Function *, std::unordered_set<Function *>> callerSets;
  FunctionAnalysisManager *functionAnalyses = manager.functionLink();
  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (function->isExtern)
      continue;
    const auto local = locals.find(function);
    if (local == locals.end())
      continue;
    const auto execution = result.fnExec.find(function);
    const bool callerReachable = execution != result.fnExec.end() &&
                                 execution->second.reachableFromEntry;

    const LoopInfo *loopInfo = nullptr;
    if (callerReachable && functionAnalyses && function->phase != IRPhase::HIR)
      loopInfo = &functionAnalyses->getResult<LoopInfoAnalysis>(function).info;

    for (const CallSiteLocalInfo &localSite : local->second.calls) {
      if (!localSite.call)
        continue;
      CallSiteSummary site;
      site.caller = function;
      site.callee = localSite.callee;
      site.call = localSite.call;
      site.reachable = callerReachable;
      site.loopDepth = localSite.lexicalLoopDepth;
      if (loopInfo) {
        const i32 depth = loopInfo->getLoopDepth(localSite.call->parentBlock());
        if (depth > 0)
          site.loopDepth = std::max(site.loopDepth, static_cast<u32>(depth));
      } else if (callerReachable && function->phase != IRPhase::HIR) {
        site.loopDepth = std::max(site.loopDepth, u32{1});
      }
      result.callSites.emplace(localSite.call, site);

      Function *callee = localSite.callee;
      auto calleeExecution = result.fnExec.find(callee);
      if (!callee || callee->isExtern || calleeExecution == result.fnExec.end())
        continue;
      ++calleeExecution->second.directCallSiteCount;
      if (site.loopDepth == 0)
        ++calleeExecution->second.nonLoopCallSiteCount;
      callerSets[callee].insert(function);
    }
  }
  for (const auto &[function, callers] : callerSets) {
    const auto found = result.fnExec.find(function);
    if (found != result.fnExec.end())
      found->second.knownCallerCount = static_cast<u32>(callers.size());
  }

  const auto &components = graph.sccGroups();
  for (usize reverseIndex = components.size(); reverseIndex > 0;
       --reverseIndex) {
    const std::vector<CGNode *> &component = components[reverseIndex - 1];
    bool recursive = false;
    for (CGNode *node : component)
      recursive |= node->inRecursion;
    if (recursive)
      for (CGNode *node : component) {
        const auto found = result.fnExec.find(node->function);
        if (found != result.fnExec.end() && found->second.reachableFromEntry)
          found->second.maxExec = ExecBound::unknownMany();
      }

    for (CGNode *node : component) {
      const auto caller = result.fnExec.find(node->function);
      if (caller == result.fnExec.end())
        continue;
      for (const CGNode::Edge &edge : node->callees) {
        Function *calleeFunction =
            edge.callee ? edge.callee->function : nullptr;
        const auto callee = result.fnExec.find(calleeFunction);
        if (!calleeFunction || calleeFunction->isExtern ||
            callee == result.fnExec.end())
          continue;
        const auto callSite = result.callSites.find(edge.callSite);
        if (callSite == result.callSites.end() || !callSite->second.reachable)
          continue;
        const bool precise = callSite->second.loopDepth == 0 &&
                             !caller->second.recursiveSCC &&
                             !callee->second.recursiveSCC;
        callee->second.maxExec =
            precise
                ? saturatingAdd(callee->second.maxExec, caller->second.maxExec,
                                GlobalSummaryResult::kExecCap)
                : ExecBound::unknownMany();
      }
    }
  }
}

} // namespace svm::ir
