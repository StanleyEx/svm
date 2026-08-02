#include "ASTPrinter.h"
#include "ASTToHIR.h"
#include "Arena.h"
#include "DiagnosticEngine.h"
#include "Frontend/Lexer.h"
#include "Frontend/Parser.h"
#include "HIRPass.h"
#include "LIRPass.h"
#include "MIRPass.h"
#include "PassManager.h"
#include "Sema.h"
#include "Utils.h"

#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <optional>
#include <string>
#include <string_view>

namespace svm {

enum class Stage {
  TokenDump,
  AstDump,
  HirDump,
  LirDumpPre,
  LirDump,
  Assembly,
};
struct CompilerOptions {
  Stage stage = Stage::Assembly;
  const char *inputPath = nullptr;
  const char *outputPath = nullptr;
  bool enableOptimizations = true;
  bool timePasses = false;

  static int parse(int argc, char *argv[], CompilerOptions &options) {
    auto usage = [](bool isHelp = false) {
      std::fputs("Usage: svm [options] <input-file.sy>\n"
                 "Options:\n"
                 "  -emit-tokens       Dump tokens\n"
                 "  -emit-ast          Dump AST\n"
                 "  -emit-hir          Dump HIR\n"
                 "  -emit-lir-pre      Dump LLVM IR\n"
                 "  -emit-lir          Dump optimized LLVM IR\n"
                 "  -emit-asm, -S      Emit RV64GC assembly (default)\n"
                 "  -o <output-file>   Specify output file path\n"
                 "  -O0                Disable optimizations\n"
                 "  -O1                Enable optimizations (default)\n"
                 "  -time              Print pass timing statistics\n"
                 "  -help, -h          Display this information\n",
                 isHelp ? stdout : stderr);
      return isHelp ? -1 : 1;
    };
    for (int i = 1; i < argc; ++i) {
      const std::string_view arg = argv[i];
      if (arg == "-emit-tokens")
        options.stage = Stage::TokenDump;
      else if (arg == "-emit-ast")
        options.stage = Stage::AstDump;
      else if (arg == "-emit-hir")
        options.stage = Stage::HirDump;
      else if (arg == "-emit-lir-pre")
        options.stage = Stage::LirDumpPre;
      else if (arg == "-emit-lir")
        options.stage = Stage::LirDump;
      else if (arg == "-emit-asm" || arg == "-S")
        options.stage = Stage::Assembly;
      else if (arg == "-time")
        options.timePasses = true;
      else if (arg == "-h" || arg == "-help")
        return usage(true);
      else if (arg == "-o") {
        if (++i >= argc) {
          std::fprintf(stderr, "Error: Missing output file path after -o\n");
          return usage();
        }
        options.outputPath = argv[i];
      } else if (arg.size() >= 2 && arg.substr(0, 2) == "-O") {
        options.enableOptimizations = (arg != "-O0");
      } else if (arg[0] == '-') {
        std::fprintf(stderr, "Unknown option: %s\n", arg.data());
        return usage();
      } else if (!options.inputPath) {
        options.inputPath = arg.data();
      } else {
        std::fprintf(stderr, "Error: Multiple input files specified\n");
        return usage();
      }
    }
    if (!options.inputPath) {
      std::fprintf(stderr, "Error: No input file specified\n");
      return usage();
    }
    return 0;
  }
};

int run(const CompilerOptions &options, std::string_view sourceView,
        FILE *output) {
  Arena arena;
  DiagnosticEngine diagnostics(arena, sourceView);
  auto finish = [&]() {
    diagnostics.printAll();
    return diagnostics.getErrorCount() > 0;
  };

  // 词法分析
  Lexer lexer(arena, diagnostics, options.inputPath, sourceView);
  if (options.stage == Stage::TokenDump) {
    while (true) {
      const auto token = lexer.next();
      dumpToken(token, output);
      if (token.kind == TokenKind::EoF)
        break;
    }
    return finish();
  }

  // 语法分析
  Parser parser(arena, diagnostics, lexer);
  CompUnit *compUnit = parser.parse();
  if (diagnostics.getErrorCount() != 0)
    return finish();

  if (options.stage == Stage::AstDump) {
    dumpAST(compUnit, output);
    return finish();
  }

  // 语义分析
  TypeContext typeContext(arena);
  Sema sema(arena, diagnostics, typeContext);
  sema.run(compUnit);
  if (diagnostics.getErrorCount() != 0)
    return finish();

  // 前端完成 降级到HIR进入中端
  using namespace svm::ir;
  ASTToHIR lowering(arena, diagnostics);
  Module *module = lowering.run(compUnit);
  if (diagnostics.getErrorCount() != 0 || !module)
    return finish();

  PassManager passManager(&diagnostics);
  passManager.options().setTimePasses(options.timePasses);

  auto unoptimizedPipeline = [&]() {
    if (options.stage == Stage::HirDump) {
      passManager.addPass<PrintHIR>(output);
      return;
    }
    passManager.addPass<HIRToLIRPass>();
    if (options.stage == Stage::LirDumpPre || options.stage == Stage::LirDump) {
      passManager.addPass<PrintLLVMIR>(output);
      return;
    }
    passManager.addPass<LowerToRV64Pass>();
    passManager.addPass<EliminatePhisPass>();
    passManager.addPass<IRCAllocPass>();
    passManager.addPass<ComputeFrameLayoutPass>();
    passManager.addPass<FixupStackOffsetsPass>();
    passManager.addPass<LowerCallShufflesPass>();
    passManager.addPass<EmitAssembly>(output);
  };

  auto optimizedPipeline = [&]() {
    passManager.addPass<HIRInstCombinePass>();
    passManager.addPass<RaiseToForPass>();
    passManager.addPass<TCOPass>();
    passManager.addPass<ModuloUnrollPass>();
    passManager.addPass<HIRInstCombinePass>();

    if (options.stage == Stage::HirDump) {
      passManager.addPass<PrintHIR>(output);
      return;
    }

    passManager.addPass<HIRToLIRPass>();
    if (options.stage == Stage::LirDumpPre) {
      passManager.addPass<PrintLLVMIR>(output);
      return;
    }

    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<Mem2RegPass>();

    // 先缩小函数体 进行一轮函数级优化
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<InstCombinePass>();
    passManager.addPass<SCCPPass>();
    passManager.addPass<GVNPass>();
    passManager.addPass<DCEPass>();
    passManager.addPass<FunctionSpecializationPass>();
    passManager.addPass<DeadFunctionEliminationPass>();
    passManager.addPass<InlinePass>();
    passManager.addPass<DeadFunctionEliminationPass>();
    passManager.addPass<GlobalVariableLocalizationPass>();
    passManager.addPass<DeadArgumentEliminationPass>();
    passManager.addPass<DeadFunctionEliminationPass>();

    // GVL 暴露局部小数组的在进入主优化循环前立即拆分并提升
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<SROAPass>();
    passManager.addPass<Mem2RegPass>();
    passManager.addPass<SimplifyCFGPass>();

    for (u32 iteration = 0; iteration < 3; ++iteration) {
      passManager.addPass<InstCombinePass>();
      passManager.addPass<SCCPPass>();
      passManager.addPass<DCEPass>();
      passManager.addPass<SimplifyCFGPass>();
      passManager.addPass<JumpThreadingPass>();
      passManager.addPass<SimplifyCFGPass>();
      passManager.addPass<ADCEPass>();
      passManager.addPass<SimplifyCFGPass>();
      passManager.addPass<DCEPass>();
      passManager.addPass<LICMPass>();
      passManager.addPass<GCMPass>();
      passManager.addPass<ReassociatePass>();
      passManager.addPass<GVNPass>();
      passManager.addPass<DCEPass>();
      passManager.addPass<SimplifyCFGPass>();
      passManager.addPass<ADCEPass>();
      passManager.addPass<SimplifyCFGPass>();
      passManager.addPass<DCEPass>();
    }

    // DSE只证明内存写不可观察 随后交给标量与控制流清理收割地址生产链
    passManager.addPass<DSEPass>();
    passManager.addPass<DCEPass>();
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<ADCEPass>();
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<DCEPass>();
    passManager.addPass<ADCEPass>();
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<DCEPass>();

#ifndef NDEBUG
    const auto hookLCSSAVerifier = [&passManager](std::string_view passName) {
      passManager.options().hook(
          passName,
          [&passManager, passName](Module *currentModule, const PassResult &) {
            for (Function *function = currentModule->functionHead; function;
                 function = function->next) {
              if (function->isExtern || function->phase != IRPhase::LIR)
                continue;
              const bool valid =
                  verifyLCSSA(function, passManager.functionAnalyses());
              if (!valid)
                std::fprintf(stderr, "LCSSA broken after %.*s in %s\n",
                             static_cast<i32>(passName.size()), passName.data(),
                             function->name);
              VERIFY(valid, "LCSSA invariant broken");
            }
          });
    };
    hookLCSSAVerifier("lcssa");
    hookLCSSAVerifier("indvars");
    hookLCSSAVerifier("loop-unroll");
    hookLCSSAVerifier("lsr");
#endif
    passManager.addPass<LoopSimplifyPass>();
    passManager.addPass<LCSSAPass>();
    passManager.addPass<IndVarSimpPass>();
    passManager.addPass<LoopUnrollPass>();
    passManager.addPass<InstCombinePass>();
    passManager.addPass<SCCPPass>();
    passManager.addPass<ReassociatePass>();
    passManager.addPass<AggressiveConstFoldPass>();
    passManager.addPass<DCEPass>();

    // 标量清理可能改变入口或折掉封口Phi LSR前重新规范化
    passManager.addPass<LoopSimplifyPass>();
    passManager.addPass<LCSSAPass>();
    passManager.addPass<LSRPass>();
    passManager.addPass<LCSSATeardownPass>();
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<DCEPass>();
    passManager.addPass<SROAPass>();
    passManager.addPass<Mem2RegPass>();

    for (u32 i = 0; i < 3; ++i) {
      passManager.addPass<InstCombinePass>();
      passManager.addPass<SCCPPass>();
      passManager.addPass<DCEPass>();
      passManager.addPass<SimplifyCFGPass>();
      passManager.addPass<JumpThreadingPass>();
      passManager.addPass<SimplifyCFGPass>();
      passManager.addPass<ADCEPass>();
      passManager.addPass<SimplifyCFGPass>();
      passManager.addPass<DCEPass>();
      passManager.addPass<LICMPass>();
      passManager.addPass<GCMPass>();
      passManager.addPass<ReassociatePass>();
      passManager.addPass<GVNPass>();
      passManager.addPass<DCEPass>();
      passManager.addPass<SimplifyCFGPass>();
      passManager.addPass<ADCEPass>();
      passManager.addPass<SimplifyCFGPass>();
      passManager.addPass<DCEPass>();
    }

    passManager.addPass<DSEPass>();
    passManager.addPass<DCEPass>();
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<ADCEPass>();
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<DCEPass>();

    passManager.addPass<ShortCircuitCanonicalizePass>();
    passManager.addPass<InstCombinePass>();
    passManager.addPass<SCCPPass>();
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<DCEPass>();
    passManager.addPass<SwitchCanonicalizePass>();

    passManager.addPass<DSEPass>();
    passManager.addPass<DCEPass>();
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<ADCEPass>();
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<DCEPass>();

    passManager.addPass<IfConversionPass>();
    passManager.addPass<InstCombinePass>();
    passManager.addPass<SimplifyCFGPass>();
    passManager.addPass<DCEPass>();

    // Lowering 之前合并全局变量
    passManager.addPass<GlobalMergePass>();

    if (options.stage == Stage::LirDump) {
      passManager.addPass<PrintLLVMIR>(output);
      return;
    }

    passManager.addPass<LowerToRV64Pass>();
    passManager.addPass<MachineInstCombinePass>();
    passManager.addPass<DivByConstPass>();
    passManager.addPass<ConstantHoistPass>();
    passManager.addPass<PeepholePass>();
    passManager.addPass<MachineCSEPass>();
    passManager.addPass<EliminatePhisPass>();
    passManager.addPass<IRCAllocPass>();
    passManager.addPass<ComputeFrameLayoutPass>();
    passManager.addPass<FixupStackOffsetsPass>();
    passManager.addPass<LowerCallShufflesPass>();
    passManager.addPass<PeepholePostRAPass>();

    passManager.addPass<EmitAssembly>(output);
  };

  if (options.enableOptimizations)
    optimizedPipeline();
  else
    unoptimizedPipeline();

  passManager.run(module);

  return finish();
}

} // namespace svm

int main(int argc, char *argv[]) {
  svm::CompilerOptions options;
  if (int status = svm::CompilerOptions::parse(argc, argv, options);
      status != 0)
    return status > 0 ? status : 0;

  struct FileCloser {
    void operator()(FILE *file) const {
      if (file && file != stdout && file != stderr)
        std::fclose(file);
    }
  };
  using ScopedFile = std::unique_ptr<FILE, FileCloser>;

  auto sourceOpt = [](const char *path) -> std::optional<std::string> {
    if (!path || *path == '\0')
      return std::nullopt;
    auto fail = [path]() {
      std::fprintf(stderr, "Error: Could not read input file: %s\n", path);
      return std::nullopt;
    };
    ScopedFile file(std::fopen(path, "rb"));
    if (!file)
      return fail();
    if (std::fseek(file.get(), 0, SEEK_END) != 0)
      return fail();
    long size = std::ftell(file.get());
    if (size < 0)
      return fail();
    if (std::fseek(file.get(), 0, SEEK_SET) != 0)
      return fail();
    std::string buffer(static_cast<size_t>(size), '\0');
    if (std::fread(buffer.data(), 1, buffer.size(), file.get()) !=
        buffer.size())
      return fail();
    return buffer;
  }(options.inputPath);
  if (!sourceOpt) {
    return 1;
  }

  ScopedFile output(stdout);
  if (options.outputPath) {
    auto outputFile = std::fopen(options.outputPath, "w");
    if (!outputFile) {
      std::fprintf(stderr, "Error: Could not open output file: %s\n",
                   options.outputPath);
      return 1;
    }
    output.reset(outputFile);
  }

  int status = svm::run(options, *sourceOpt, output.get());

  if (output.get() != stdout &&
      (std::fflush(output.get()) != 0 || std::ferror(output.get()))) {
    std::fprintf(stderr, "Error: Could not write output file: %s\n",
                 options.outputPath);
    return 1;
  }
  return status;
}
