#include "Lexer.h"
#include "DiagnosticEngine.h"
#include "Token.h"
#include "Types.h"

#include <cstdlib>
#include <string>
#include <string_view>

namespace svm {
static auto isIdentStart = [](char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
};

static auto isDigit = [](char c) { return c >= '0' && c <= '9'; };

static auto isHexDigit = [](char c) {
  return isDigit(c) || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
};

static auto isIdentContinue = [](char c) {
  return isIdentStart(c) || isDigit(c);
};

static auto matchKeyword = [](std::string_view text) -> TokenType {
  if (text == "const")
    return TokenType::KW_Const;
  if (text == "int")
    return TokenType::KW_Int;
  if (text == "float")
    return TokenType::KW_Float;
  if (text == "void")
    return TokenType::KW_Void;
  if (text == "if")
    return TokenType::KW_If;
  if (text == "else")
    return TokenType::KW_Else;
  if (text == "while")
    return TokenType::KW_While;
  if (text == "break")
    return TokenType::KW_Break;
  if (text == "continue")
    return TokenType::KW_Continue;
  if (text == "return")
    return TokenType::KW_Return;
  return TokenType::Identifier;
};

Token Lexer::nextToken() {
  // 跳过空白字符和注释
  while (!isAtEnd()) {
    char ch = peek();
    if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n') {
      advance();
    } else if (ch == '/' && peek(1) == '/') {
      advance();
      advance();
      while (!isAtEnd() && peek() != '\n')
        advance();
    } else if (ch == '/' && peek(1) == '*') {
      advance();
      advance();
      while (!isAtEnd() && !(peek() == '*' && peek(1) == '/'))
        advance();
      if (isAtEnd()) {
        SVM_ERROR(diagEngine_, SourceLocation(offset_, line_, column_, 0),
                  "Unterminated block comment.");
        return Token(TokenType::Error,
                     SourceLocation(offset_, line_, column_, 0), {});
      } else {
        advance();
        advance();
      }
    } else {
      break;
    }
  }

  usize startOffset = offset_;
  u32 startLine = line_;
  u32 startColumn = column_;

#define SRC_LOC                                                                \
  SourceLocation(startOffset, startLine, startColumn, offset_ - startOffset)

  if (isAtEnd()) {
    return Token(TokenType::EoF, SRC_LOC, {});
  }
  char ch = peek();

  // 标识符或关键字
  if (isIdentStart(ch)) {
    advance();
    while (!isAtEnd() && isIdentContinue(peek()))
      advance();

    std::string_view text = source_.substr(startOffset, offset_ - startOffset);

    Token token(matchKeyword(text), SRC_LOC, text);
    return token;
  }

  auto MK_ERROR = [this, startOffset, startLine,
                   startColumn](const char *MSG) -> Token {
    SVM_ERROR(diagEngine_, SRC_LOC, MSG);
    return Token(TokenType::Error, SRC_LOC, {});
  };

  // 数字字面量
  if (isDigit(ch) || (ch == '.' && isDigit(peek(1)))) {
    bool isFloat = false;
    bool isHex = false;

    if (ch == '0' && (peek(1) == 'x' || peek(1) == 'X')) {
      // 16 进制字面量
      isHex = true;
      advance();
      advance();
      while (isHexDigit(peek())) {
        advance();
      }
      if (peek() == '.') {
        isFloat = true;
        advance();
        while (isHexDigit(peek())) {
          advance();
        }
      }
      if (peek() == 'p' || peek() == 'P') {
        isFloat = true;
        advance();
        if (peek() == '+' || peek() == '-') {
          advance();
        }
        if (!isDigit(peek())) {
          return MK_ERROR(
              "Invalid hexadecimal literal: missing exponent digits.");
        }
        while (isDigit(peek())) {
          advance();
        }
      }
    } else if (peek() == '.') {
      // '.'开头的浮点数
      isFloat = true;
      advance();
      if (!isDigit(peek())) {
        return MK_ERROR("Invalid float literal: '.' not followed by digit.");
      }
      while (isDigit(peek())) {
        advance();
      }
      if (peek() == 'e' || peek() == 'E') {
        advance();
        if (peek() == '+' || peek() == '-') {
          advance();
        }
        if (!isDigit(peek())) {
          return MK_ERROR("Invalid float literal: missing exponent digits.");
        }
        while (isDigit(peek())) {
          advance();
        }
      }
    } else {
      // 十进制、八进制整数和浮点数
      while (isDigit(peek())) {
        advance();
      }
      if (peek() == '.') {
        isFloat = true;
        advance();
        while (isDigit(peek())) {
          advance();
        }
      }
      if (peek() == 'e' || peek() == 'E') {
        isFloat = true;
        advance();
        if (peek() == '+' || peek() == '-') {
          advance();
        }
        if (!isDigit(peek())) {
          return MK_ERROR("Invalid float literal: missing exponent digits.");
        }
        while (isDigit(peek())) {
          advance();
        }
      }
    }

    auto text = source_.substr(startOffset, offset_ - startOffset);
    Token token(isFloat ? TokenType::FloatLiteral : TokenType::IntegerLiteral,
                SRC_LOC, text);

    std::string digit(text);
    char *end = nullptr;
    if (isFloat) {
      token.floatValue = std::strtof(digit.c_str(), &end);
      if (end != digit.c_str() + digit.size()) {
        return MK_ERROR("Invalid float literal.");
      }
    } else {
      i32 base = 10;
      if (isHex) {
        base = 16;
        digit = std::string(text.substr(2)); // 跳过0x
        if (digit.empty()) {
          return MK_ERROR("Invalid hexadecimal literal: missing digits.");
        }
      } else if (text.length() > 1 && text[0] == '0') {
        base = 8;
        digit = std::string(text.substr(1)); // 跳过0
      }
      u64 value = std::strtoull(digit.c_str(), &end, base);
      if (*end != '\0' && base == 8) {
        return MK_ERROR("Invalid octal digit in integer literal.");
      }
      if (value > 0x7FFFFFFFull) {
        SVM_WARN(diagEngine_, SRC_LOC, "Integer literal '%s' exceeds 32 bits.",
                 std::string(token.text).c_str());
      }
      token.intValue = static_cast<i32>(static_cast<u32>(value));
    }
    return token;
  }

  // 字符串字面量
  if (ch == '"') {
    advance();
    std::string buffer;
    buffer.reserve(32);
    bool terminated = false;
    while (!isAtEnd()) {
      char c = peek();
      if (c == '"') {
        advance();
        terminated = true;
        break;
      }
      if (c == '\n') {
        return MK_ERROR("Newline in string literal.");
      }
      if (c == '\\') {
        advance();
        if (isAtEnd()) {
          break;
        }
        char escape = advance();
        switch (escape) {
        case 'n':
          buffer.push_back('\n');
          break;
        case 't':
          buffer.push_back('\t');
          break;
        case 'r':
          buffer.push_back('\r');
          break;
        case '0':
          buffer.push_back('\0');
          break;
        case '\\':
          buffer.push_back('\\');
          break;
        case '\'':
          buffer.push_back('\'');
          break;
        case '"':
          buffer.push_back('"');
          break;
        default:
          SVM_WARN(diagEngine_, SRC_LOC,
                   "Invalid escape sequence '\\%c' in string literal.", escape);
          break;
        }
      } else {
        buffer.push_back(c);
        advance();
      }
    }
    if (!terminated) {
      return MK_ERROR("Unterminated string literal.");
    }
    return Token(
        TokenType::StringLiteral, SRC_LOC,
        std::string_view(arena_.duplicateString(buffer.data(), buffer.length()),
                         buffer.length()));
  }

  // 运算符和标点符号
  advance();
  switch (ch) {
  case '(':
    return Token(TokenType::LParen, SRC_LOC, "(");
  case ')':
    return Token(TokenType::RParen, SRC_LOC, ")");
  case '[':
    return Token(TokenType::LBracket, SRC_LOC, "[");
  case ']':
    return Token(TokenType::RBracket, SRC_LOC, "]");
  case '{':
    return Token(TokenType::LBrace, SRC_LOC, "{");
  case '}':
    return Token(TokenType::RBrace, SRC_LOC, "}");
  case ';':
    return Token(TokenType::Semicolon, SRC_LOC, ";");
  case ',':
    return Token(TokenType::Comma, SRC_LOC, ",");
  case '+':
    return Token(TokenType::Plus, SRC_LOC, "+");
  case '-':
    return Token(TokenType::Minus, SRC_LOC, "-");
  case '*':
    return Token(TokenType::Star, SRC_LOC, "*");
  case '/':
    return Token(TokenType::Slash, SRC_LOC, "/");
  case '%':
    return Token(TokenType::Percent, SRC_LOC, "%");
  case '=':
    if (match('=')) {
      return Token(TokenType::Eq, SRC_LOC, "==");
    } else {
      return Token(TokenType::Assign, SRC_LOC, "=");
    }
  case '!':
    if (match('=')) {
      return Token(TokenType::NotEq, SRC_LOC, "!=");
    } else {
      return Token(TokenType::Not, SRC_LOC, "!");
    }
  case '<':
    if (match('=')) {
      return Token(TokenType::LessEq, SRC_LOC, "<=");
    } else {
      return Token(TokenType::Less, SRC_LOC, "<");
    }
  case '>':
    if (match('=')) {
      return Token(TokenType::GreaterEq, SRC_LOC, ">=");
    } else {
      return Token(TokenType::Greater, SRC_LOC, ">");
    }
  case '&':
    if (match('&')) {
      return Token(TokenType::AndAnd, SRC_LOC, "&&");
    } else {
      return MK_ERROR("Expected &&, bitwise & not supported.");
    }
  case '|':
    if (match('|')) {
      return Token(TokenType::OrOr, SRC_LOC, "||");
    } else {
      return MK_ERROR("Expected ||, bitwise | not supported.");
    }
  }
  return MK_ERROR("Unexpected character.");
#undef SRC_LOC
}
} // namespace svm