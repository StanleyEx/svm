#ifndef DIAGNOSTIC_ENGINE_H
#define DIAGNOSTIC_ENGINE_H

#include "Arena.h"
#include "SourceLocation.h"
#include "Utils.h"

#include <cassert>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <vector>

namespace svm {
enum class DiagnosticLevel : u8 { Note, Warn, Error, Fatal };
struct Diagnostic {
  DiagnosticLevel level;
  SourceLocation location;
  const char *message = nullptr;
};

class DiagnosticEngine {
public:
  explicit DiagnosticEngine(Arena &arena) : arena_(arena) {}

  void diagEmit(DiagnosticLevel level, SourceLocation location,
                [[maybe_unused]] const char *file,
                [[maybe_unused]] const char *func, [[maybe_unused]] usize line,
                const char *fmt, ...) {
    va_list args, argsCopy;
    va_start(args, fmt);

    va_copy(argsCopy, args);
    int size = std::vsnprintf(nullptr, 0, fmt, argsCopy);
    va_end(argsCopy);
    if (size < 0) {
      diagnostics_.push_back({DiagnosticLevel::Error, location,
                              "Failed to format diagnostic message."});
      ++errorCount_;
      va_end(args);
      return;
    }

    char *buffer = nullptr;
#ifdef NDEBUG
    buffer = static_cast<char *>(arena_.allocate(size + 1, alignof(char)));
    std::vsnprintf(buffer, size + 1, fmt, args);
#else
    const char *suffixFmt = " (in %s at %s:%zu)";
    int suffixSize = std::snprintf(nullptr, 0, suffixFmt, func, file, line);
    assert(suffixSize >= 0);
    buffer = static_cast<char *>(
        arena_.allocate(size + suffixSize + 1, alignof(char)));
    std::vsnprintf(buffer, size + 1, fmt, args);
    std::snprintf(buffer + size, suffixSize + 1, suffixFmt, func, file, line);
#endif
    va_end(args);

    diagnostics_.push_back({level, location, buffer});
    switch (level) {
    case DiagnosticLevel::Warn:
      ++warningCount_;
      break;
    case DiagnosticLevel::Error:
      ++errorCount_;
      break;
    case DiagnosticLevel::Fatal:
      ++errorCount_;
      printAll(stderr);
      std::exit(EXIT_FAILURE);
      break;
    default:
      break;
    }
  }

  usize getWarningCount() const { return warningCount_; }

  usize getErrorCount() const { return errorCount_; }

  void printAll(FILE *out = stderr) const {
    for (const auto &diag : diagnostics_) {
      const char *levelStr = nullptr;
      bool enableColor = (out == stderr);
      switch (diag.level) {
      case DiagnosticLevel::Note:
        levelStr = enableColor ? "\033[32m[Note]\033[0m" : "[Note]";
        break;
      case DiagnosticLevel::Warn:
        levelStr = enableColor ? "\033[33m[Warning]\033[0m" : "[Warning]";
        break;
      case DiagnosticLevel::Error:
        levelStr = enableColor ? "\033[31m[Error]\033[0m" : "[Error]";
        break;
      case DiagnosticLevel::Fatal:
        levelStr = enableColor ? "\033[1;31m[Fatal]\033[0m" : "[Fatal]";
        break;
      }
      if (diag.location.isValid()) {
        std::fprintf(out, "%s %u:%u: %s\n", levelStr, diag.location.line,
                     diag.location.column, diag.message);
      } else {
        std::fprintf(out, "%s %s\n", levelStr, diag.message);
      }
    }
  }

private:
  Arena &arena_;
  std::vector<Diagnostic> diagnostics_;
  usize warningCount_ = 0;
  usize errorCount_ = 0;
};

} // namespace svm

#define SVM_NOTE(ENGINE, SRCLOC, FMT, ...)                                     \
  do {                                                                         \
    (ENGINE).diagEmit(::svm::DiagnosticLevel::Note, (SRCLOC), __FILE__,        \
                      __func__, __LINE__, (FMT), ##__VA_ARGS__);               \
  } while (0)

#define SVM_WARN(ENGINE, SRCLOC, FMT, ...)                                     \
  do {                                                                         \
    (ENGINE).diagEmit(::svm::DiagnosticLevel::Warn, (SRCLOC), __FILE__,        \
                      __func__, __LINE__, (FMT), ##__VA_ARGS__);               \
  } while (0)

#define SVM_ERROR(ENGINE, SRCLOC, FMT, ...)                                    \
  do {                                                                         \
    (ENGINE).diagEmit(::svm::DiagnosticLevel::Error, (SRCLOC), __FILE__,       \
                      __func__, __LINE__, (FMT), ##__VA_ARGS__);               \
  } while (0)

#define SVM_FATAL(ENGINE, SRCLOC, FMT, ...)                                    \
  do {                                                                         \
    (ENGINE).diagEmit(::svm::DiagnosticLevel::Fatal, (SRCLOC), __FILE__,       \
                      __func__, __LINE__, (FMT), ##__VA_ARGS__);               \
  } while (0)

#define SVM_ASSERT(COND, ENGINE, SRCLOC, FMT, ...)                             \
  do {                                                                         \
    if (!(COND)) {                                                             \
      (ENGINE).diagEmit(::svm::DiagnosticLevel::Fatal, (SRCLOC), __FILE__,     \
                        __func__, __LINE__, (FMT), ##__VA_ARGS__);             \
    }                                                                          \
  } while (0)

#endif // DIAGNOSTIC_ENGINE_H