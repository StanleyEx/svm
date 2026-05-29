#ifndef TOKEN_H
#define TOKEN_H

#include "SourceLocation.h"
#include "Utils.h"

#include <string_view>

namespace svm {

enum class TokenKind : u16 {
  EoF,
  Error,

  IntegerLiteral,
  FloatLiteral,
  StringLiteral,
  Identifier,

  KW_Const,
  KW_Int,
  KW_Float,
  KW_Void,
  KW_If,
  KW_Else,
  KW_While,
  KW_Break,
  KW_Continue,
  KW_Return,

  LParen,    // (
  RParen,    // )
  LBracket,  // [
  RBracket,  // ]
  LBrace,    // {
  RBrace,    // }
  Comma,     // ,
  Semicolon, // ;

  Assign,    // =
  Plus,      // +
  Minus,     // -
  Star,      // *
  Slash,     // /
  Percent,   // %
  Eq,        // ==
  NotEq,     // !=
  Less,      // <
  LessEq,    // <=
  Greater,   // >
  GreaterEq, // >=
  AndAnd,    // &&
  OrOr,      // ||
  Not,       // !

  NUMBER_OF_TOKEN_TYPES,
};

struct Token {
  Token() = default;
  Token(TokenKind kind, SourceLocation location, std::string_view text)
      : kind(kind), location(location), text(text), intValue(0) {}

  TokenKind kind = TokenKind::EoF;
  SourceLocation location;
  std::string_view text;

  union {
    i32 intValue = 0;
    f32 floatValue;
  };

  [[maybe_unused]] const char *toString() const {
    switch (kind) {
    case TokenKind::EoF:
      return "<EOF>";
    case TokenKind::Error:
      return "<Error>";
    case TokenKind::IntegerLiteral:
      return "<IntegerLiteral>";
    case TokenKind::FloatLiteral:
      return "<FloatLiteral>";
    case TokenKind::StringLiteral:
      return "<StringLiteral>";
    case TokenKind::Identifier:
      return "<Identifier>";
    case TokenKind::KW_Const:
      return "const";
    case TokenKind::KW_Int:
      return "int";
    case TokenKind::KW_Float:
      return "float";
    case TokenKind::KW_Void:
      return "void";
    case TokenKind::KW_If:
      return "if";
    case TokenKind::KW_Else:
      return "else";
    case TokenKind::KW_While:
      return "while";
    case TokenKind::KW_Break:
      return "break";
    case TokenKind::KW_Continue:
      return "continue";
    case TokenKind::KW_Return:
      return "return";
    case TokenKind::LParen:
      return "(";
    case TokenKind::RParen:
      return ")";
    case TokenKind::LBracket:
      return "[";
    case TokenKind::RBracket:
      return "]";
    case TokenKind::LBrace:
      return "{";
    case TokenKind::RBrace:
      return "}";
    case TokenKind::Comma:
      return ",";
    case TokenKind::Semicolon:
      return ";";
    case TokenKind::Assign:
      return "=";
    case TokenKind::Plus:
      return "+";
    case TokenKind::Minus:
      return "-";
    case TokenKind::Star:
      return "*";
    case TokenKind::Slash:
      return "/";
    case TokenKind::Percent:
      return "%";
    case TokenKind::Eq:
      return "==";
    case TokenKind::NotEq:
      return "!=";
    case TokenKind::Less:
      return "<";
    case TokenKind::LessEq:
      return "<=";
    case TokenKind::Greater:
      return ">";
    case TokenKind::GreaterEq:
      return ">=";
    case TokenKind::AndAnd:
      return "&&";
    case TokenKind::OrOr:
      return "||";
    case TokenKind::Not:
      return "!";
    default:
      return "<InvalidToken>";
    }
  }
};

} // namespace svm

#endif // TOKEN_H