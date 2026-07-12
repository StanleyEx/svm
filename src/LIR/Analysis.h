#ifndef LIR_ANALYSIS_H
#define LIR_ANALYSIS_H

#include "Alias.h"
#include "DomAnalysis.h"
#include "GlobalSummary.h"
#include "LoopInfo.h"
#include "PassManager.h"
#include "SCEV.h"

#include <cstdlib>

namespace svm::ir {

struct DomAnalysis {
  DominatorTree tree;
  static const AnalysisKey *ID() noexcept {
    static AnalysisKey key;
    return &key;
  }
  void run(Function *function, FunctionAnalysisManager &) {
    if (!tree.build(function))
      std::abort();
  }
  bool invalidate(Function *, const PreservedAnalyses &preserved) const {
    return !(preserved.preservesCFGAnalyses() || preserved.preserves(ID()));
  }
};

struct PostDomAnalysis {
  PostDominatorTree tree;
  static const AnalysisKey *ID() noexcept {
    static AnalysisKey key;
    return &key;
  }
  void run(Function *function, FunctionAnalysisManager &) {
    if (!tree.build(function))
      std::abort();
  }
  bool invalidate(Function *, const PreservedAnalyses &preserved) const {
    return !(preserved.preservesCFGAnalyses() || preserved.preserves(ID()));
  }
};

struct LoopInfoAnalysis {
  LoopInfo info;
  static const AnalysisKey *ID() noexcept {
    static AnalysisKey key;
    return &key;
  }
  void run(Function *function, FunctionAnalysisManager &manager) {
    info.build(function, manager.getResult<DomAnalysis>(function).tree);
  }
  bool invalidate(Function *, const PreservedAnalyses &preserved) const {
    return !(preserved.preservesCFGAnalyses() || preserved.preserves(ID()));
  }
};

struct SCEVAnalysis {
  SCEV info;
  static const AnalysisKey *ID() noexcept {
    static AnalysisKey key;
    return &key;
  }
  void run(Function *function, FunctionAnalysisManager &manager) {
    info.build(function, manager);
  }
  bool invalidate(Function *, const PreservedAnalyses &preserved) const {
    const bool dependenciesPreserved =
        preserved.preservesCFGAnalyses() ||
        (preserved.preserves<DomAnalysis>() &&
         preserved.preserves<LoopInfoAnalysis>());
    return !preserved.preserves(ID()) || !dependenciesPreserved;
  }
};

struct AliasAnalysis {
  AliasInfo info;
  static const AnalysisKey *ID() noexcept {
    static AnalysisKey key;
    return &key;
  }
  void run(Function *function, FunctionAnalysisManager &manager) {
    const SCEV *scev = nullptr;
    if (function && function->phase == IRPhase::LIR && !function->isExtern &&
        function->region && function->region->first)
      scev = &manager.getResult<SCEVAnalysis>(function).info;
    info.build(function, scev, manager.moduleLink());
  }
  bool invalidate(Function *function,
                  const PreservedAnalyses &preserved) const {
    UNUSED(function);
    if (!preserved.preserves(ID()))
      return true;
    if (!info.scev_)
      return false;
    const bool scalarDependenciesPreserved =
        preserved.preservesCFGAnalyses() ||
        (preserved.preserves<DomAnalysis>() &&
         preserved.preserves<LoopInfoAnalysis>());
    return !preserved.preserves<SCEVAnalysis>() || !scalarDependenciesPreserved;
  }
};

struct GlobalSummaryAnalysis {
  GlobalSummaryResult result;
  static const AnalysisKey *ID() noexcept {
    static AnalysisKey key;
    return &key;
  }
  void run(Module *module, ModuleAnalysisManager &manager) {
    VERIFY(module != nullptr);
    result = GlobalSummaryResult{};
    result.module = module;
    result.locals = collectLocalSummaries(module);
    buildCallGraphFromLocals(module, result.locals, result.callGraph);
    result.effects =
        solveModuleEffects(module, result.locals, result.callGraph);
    populateExecutionSummaries(module, result.locals, result.callGraph, manager,
                               result);
  }
  bool invalidate(Module *, const PreservedAnalyses &preserved) const {
    return !(preserved.preservesAllModuleAnalyses() ||
             preserved.preserves(ID()));
  }
};

} // namespace svm::ir

#endif // LIR_ANALYSIS_H
