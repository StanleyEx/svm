#include "Analysis.h"
#include "LIRPass.h"

#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

void unlinkFunction(Module *module, Function *target) {
  VERIFY(module != nullptr && target != nullptr);
  Function *previous = nullptr;
  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (function != target) {
      previous = function;
      continue;
    }
    if (previous)
      previous->next = target->next;
    else
      module->functionHead = target->next;
    if (module->functionTail == target)
      module->functionTail = previous;
    target->next = nullptr;
    return;
  }
  VERIFY(false, "目标函数不在模块中");
}

} // namespace

std::string_view DeadFunctionEliminationPass::name() const noexcept {
  return "dead-function-elimination";
}

PassResult DeadFunctionEliminationPass::run(Module *module,
                                            PassContext &context) {
  if (!module)
    return PassResult::noChange();
  const GlobalSummaryResult &summary =
      context.get<GlobalSummaryAnalysis>(module).result;
  const CallGraph &graph = summary.graph();
  std::unordered_set<const CGNode *> reachable;
  std::vector<const CGNode *> worklist;
  for (CGNode *node : graph.nodes()) {
    Function *function = node ? node->function : nullptr;
    if (!function ||
        (!function->isExtern && function != summary.getEntryPoint()))
      continue;
    if (reachable.insert(node).second)
      worklist.push_back(node);
  }
  while (!worklist.empty()) {
    const CGNode *node = worklist.back();
    worklist.pop_back();
    for (const CGNode::Edge &edge : node->callees)
      if (edge.callee && reachable.insert(edge.callee).second)
        worklist.push_back(edge.callee);
  }

  std::vector<Function *> dead;
  for (CGNode *node : graph.nodes()) {
    Function *function = node ? node->function : nullptr;
    if (function && !function->isExtern &&
        summary.getEntryPoint() != function && reachable.count(node) == 0)
      dead.push_back(function);
  }
  if (dead.empty())
    return PassResult::noChange();

  for (Function *function : dead) {
    context.notifyFunctionTopologyChanged(function);
    unlinkFunction(module, function);
  }
  PreservedAnalyses preserved;
  preserved.preserveAllFunctionAnalyses();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
