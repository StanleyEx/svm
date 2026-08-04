#ifndef LIR_PASS_H
#define LIR_PASS_H

#include "PassManager.h"

#include <cstdio>

namespace svm::ir {

DECLARE_MODULE_PASS(HIRToLIRPass);
DECLARE_MODULE_PASS(AggressiveConstFoldPass);
DECLARE_MODULE_PASS(GlobalMergePass);
DECLARE_MODULE_PASS(DeadArgumentEliminationPass);
DECLARE_MODULE_PASS(DeadFunctionEliminationPass);
DECLARE_MODULE_PASS(GlobalVariableLocalizationPass);
DECLARE_MODULE_PASS(DSEPass);
DECLARE_FUNCTION_PASS(Mem2RegPass);
DECLARE_FUNCTION_PASS(ShortCircuitCanonicalizePass);
DECLARE_FUNCTION_PASS(SwitchCanonicalizePass);
DECLARE_FUNCTION_PASS(SCCPPass);
DECLARE_FUNCTION_PASS(SimplifyCFGPass);
DECLARE_FUNCTION_PASS(DCEPass);
DECLARE_FUNCTION_PASS(ADCEPass);
DECLARE_FUNCTION_PASS(GVNPass);
DECLARE_FUNCTION_PASS(GCMPass);
DECLARE_FUNCTION_PASS(LICMPass);
DECLARE_FUNCTION_PASS(JumpThreadingPass);
DECLARE_FUNCTION_PASS(IfConversionPass);
DECLARE_FUNCTION_PASS(SROAPass);
DECLARE_FUNCTION_PASS(LoopSimplifyPass);
DECLARE_FUNCTION_PASS(IndVarSimpPass);
DECLARE_FUNCTION_PASS(SimpleLoopUnswitchPass);
DECLARE_FUNCTION_PASS(InvariantRepeatReductionPass);
DECLARE_FUNCTION_PASS(LowerArrayIndexPass);
DECLARE_FUNCTION_PASS(LSRPass);

DECLARE_FUNCTION_PASS(LCSSAPass);
DECLARE_FUNCTION_PASS(LCSSATeardownPass);

struct LoopInterchangeConfig {
  u32 maxTransformsPerFunction = 4;  // 每函数最多成功交换次数
  u32 maxCandidatesPerFunction = 64; // 每函数最多检查的相邻循环对
  i64 minScoreDelta = 2;             // 交换前后局部性分数的最小增益
};

class LoopInterchangePass final : public FunctionPass {
public:
  explicit LoopInterchangePass(LoopInterchangeConfig config = {}) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;

private:
  LoopInterchangeConfig config_;
};

struct UnrollAndJamConfig {
  u32 maxTransformsPerFunction = 4;    // 单函数最多接受的候选数
  u32 maxCandidatesPerFunction = 32;   // 单函数最多检查的外层循环数
  u32 maxJamDepth = 6;                 // single-child chain最大融合深度
  i32 maxFunctionInstructions = 20000; // 变换后函数指令硬上限
  i32 minimumReuseScore = 1;           // 最少外层不变Load收益分
  bool emitRemarks = false;            // 输出候选决策诊断
};

class UnrollAndJamPass final : public FunctionPass {
public:
  explicit UnrollAndJamPass(UnrollAndJamConfig config = {}) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;

private:
  UnrollAndJamConfig config_;
};

// 对函数内所有自然循环构造Loop-Closed SSA 返回是否修改IR
bool formLCSSA(Function *function, FunctionAnalysisManager &analyses);
bool teardownLCSSA(Function *function);
// 验证循环内定义仅通过退出Phi流向循环外
bool verifyLCSSA(Function *function, FunctionAnalysisManager &analyses);
// 验证所有自然循环具有唯一preheader,唯一latch和dedicated exit
bool verifyLoopSimplify(Function *function, FunctionAnalysisManager &analyses);
// CFG循环变换后恢复LoopSimplify与LCSSA
bool repairLoopForm(Function *function, PassContext &context);

class LoopUnrollPass final : public FunctionPass {
public:
  explicit LoopUnrollPass(i32 maxFullTripCount = 64,
                          i32 maxFullInstructions = 1024, i32 partialFactor = 2,
                          i32 maxPartialBodyInstructions = 100,
                          i32 maxFunctionInstructions = 20000) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;

private:
  i32 maxFullTripCount_ = 64;            // 完全展开的最大迭代次数
  i32 maxFullInstructions_ = 1024;       // 完全展开的最大新增指令数
  i32 partialFactor_ = 2;                // 部分展开因子
  i32 maxPartialBodyInstructions_ = 100; // 可部分展开的最大循环体积
  i32 maxFunctionInstructions_ = 20000;  // 展开后的函数体积上限
};

class InlinePass final : public ModulePass {
public:
  explicit InlinePass(i32 instructionThreshold = 256) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Module *module, PassContext &context) override;

private:
  i32 instructionThreshold_ = 256; // 内联的指令数阈值
};

class FunctionSpecializationPass final : public ModulePass {
public:
  explicit FunctionSpecializationPass(
      u32 cloneLimit = 8, u32 cloneInstructionLimit = 2000,
      u32 uniformCallSiteThreshold = 2) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Module *module, PassContext &context) override;

private:
  u32 cloneLimit_ = 8;               // 单次运行最多创建的clone数
  u32 cloneInstructionLimit_ = 2000; // 可复制函数的最大指令数
  u32 uniformCallSiteThreshold_ = 2; // uniform tuple的最少调用点数
};

class InstCombinePass final : public FunctionPass {
public:
  explicit InstCombinePass(bool fastMath = false) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;

private:
  bool fastMath_ = false;
};

class ReassociatePass final : public FunctionPass {
public:
  explicit ReassociatePass(bool fastMath = false) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Function *function, PassContext &context) override;

private:
  bool fastMath_ = false;
};

class PrintLLVMIR final : public ModulePass {
public:
  explicit PrintLLVMIR(FILE *output, bool printSource = true) noexcept;
  std::string_view name() const noexcept override;
  PassResult run(Module *module, PassContext &context) override;

private:
  FILE *output_ = stdout;
  bool printSource_ = true;
};

} // namespace svm::ir

#endif // LIR_PASS_H
