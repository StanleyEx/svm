#ifndef LEXER_H
#define LEXER_H

#include "Arena.h"
#include "DiagnosticEngine.h"
#include "Token.h"
#include "Utils.h"

#include <string_view>
namespace svm {

class Lexer {
public:
  Lexer(Arena &arena, DiagnosticEngine &diagEngine, std::string_view source)
      : arena_(arena), diagEngine_(diagEngine), source_(source),
        sourceLength_(source.size()) {}

  Token next();

private:
  Arena &arena_;
  DiagnosticEngine &diagEngine_;

  std::string_view source_;
  usize sourceLength_ = 0;

  usize offset_ = 0;
  u32 line_ = 1;
  u32 column_ = 1;

  bool isAtEnd() const noexcept { return offset_ >= sourceLength_; }

  char peek(usize n = 0) const noexcept {
    usize p = offset_ + n;
    return p < sourceLength_ ? source_[p] : '\0';
  }

  char advance() noexcept {
    if (isAtEnd())
      return '\0';
    char c = source_[offset_];
    ++offset_;
    if (c == '\n') {
      ++line_, column_ = 1;
    } else {
      ++column_;
    }
    return c;
  }

  bool match(char expected) noexcept {
    if (isAtEnd() || peek() != expected) {
      return false;
    }
    advance();
    return true;
  }
};

} // namespace svm

#endif // LEXER_H