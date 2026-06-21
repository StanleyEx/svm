#ifndef LIR_ANALYSIS_H
#define LIR_ANALYSIS_H

#include "DomAnalysis.h"
#include "LoopInfo.h"
#include "PassManager.h"

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

} // namespace svm::ir

#endif // LIR_ANALYSIS_H
