

#include "Utils/Arena.h"
#include "Utils/Types.h"
#include <cstdio>
#include <cstring>
#include <fstream>

enum class Stage {
  TokenDump,
  AstDump,

};

int main(int argc, char *argv[]) {
  // 解析命令行参数
  Stage stage = Stage::AstDump;
  const char *inputPath = nullptr;
  const char *outputPath = nullptr;
  auto usage = []() {
    std::fputs("Usage: svm [options] <input-file.sy>\n"
               "Options:\n"
               "  -emit-tokens       Dump tokens\n"
               "  -emit-ast          Dump AST (default)\n"
               "  -o <output-file>   Specify output file path\n",
               stderr);
    return 1;
  };
  for (i8 i = 1; i < argc; ++i) {
    auto *arg = argv[i];
    if (std::strcmp(arg, "-emit-tokens") == 0) {
      stage = Stage::TokenDump;
    } else if (std::strcmp(arg, "-emit-ast") == 0) {
      stage = Stage::AstDump;
    } else if (std::strcmp(arg, "-o") == 0) {
      if (i + 1 >= argc) {
        std::fprintf(stderr, "Error: Missing output file path after -o\n");
        return usage();
      }
      outputPath = argv[++i];
    } else if (arg[0] == '-') {
      std::fprintf(stderr, "Unknown option: %s\n", arg);
      return usage();
    } else if (!inputPath) {
      inputPath = arg;
    } else {
      return usage();
    }
  }
  if (!inputPath) {
    std::fprintf(stderr, "Error: No input file specified\n");
    return usage();
  }

  // I/O
  std::string source;
  {
    std::ifstream inFile(inputPath);
    if (!inFile) {
      std::fprintf(stderr, "Error: Could not open input file: %s\n", inputPath);
      return 1;
    }
    source.assign((std::istreambuf_iterator<char>(inFile)),
                  std::istreambuf_iterator<char>());
  }

  FILE *output = stdout;
  if (outputPath) {
    output = std::fopen(outputPath, "w");
    if (!output) {
      std::fprintf(stderr, "Error: Could not open output file: %s\n",
                   outputPath);
      return 1;
    }
  }

  // 前端
  Arena arena;

  return 0;
}