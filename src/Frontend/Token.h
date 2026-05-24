#ifndef TOKEN_H
#define TOKEN_H

#include "Utils/SourceLocation.h"
#include "Utils/Types.h"

#include <string_view>

namespace svm {

enum class TokenType : u16 {
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
  TokenType type = TokenType::EoF;
  SourceLocation location;
  std::string_view text;

  Token(TokenType type, SourceLocation location, std::string_view text)
      : type(type), location(location), text(text) {}

  union {
    i32 intValue = 0;
    f32 floatValue;
  };

  const char *toString() const {
    switch (type) {
    case TokenType::EoF:
      return "<EOF>";
    case TokenType::Error:
      return "<Error>";
    case TokenType::IntegerLiteral:
      return "<IntegerLiteral>";
    case TokenType::FloatLiteral:
      return "<FloatLiteral>";
    case TokenType::StringLiteral:
      return "<StringLiteral>";
    case TokenType::Identifier:
      return "<Identifier>";
    case TokenType::KW_Const:
      return "const";
    case TokenType::KW_Int:
      return "int";
    case TokenType::KW_Float:
      return "float";
    case TokenType::KW_Void:
      return "void";
    case TokenType::KW_If:
      return "if";
    case TokenType::KW_Else:
      return "else";
    case TokenType::KW_While:
      return "while";
    case TokenType::KW_Break:
      return "break";
    case TokenType::KW_Continue:
      return "continue";
    case TokenType::KW_Return:
      return "return";
    case TokenType::LParen:
      return "(";
    case TokenType::RParen:
      return ")";
    case TokenType::LBracket:
      return "[";
    case TokenType::RBracket:
      return "]";
    case TokenType::LBrace:
      return "{";
    case TokenType::RBrace:
      return "}";
    case TokenType::Comma:
      return ",";
    case TokenType::Semicolon:
      return ";";
    case TokenType::Assign:
      return "=";
    case TokenType::Plus:
      return "+";
    case TokenType::Minus:
      return "-";
    case TokenType::Star:
      return "*";
    case TokenType::Slash:
      return "/";
    case TokenType::Percent:
      return "%";
    case TokenType::Eq:
      return "==";
    case TokenType::NotEq:
      return "!=";
    case TokenType::Less:
      return "<";
    case TokenType::LessEq:
      return "<=";
    case TokenType::Greater:
      return ">";
    case TokenType::GreaterEq:
      return ">=";
    case TokenType::AndAnd:
      return "&&";
    case TokenType::OrOr:
      return "||";
    case TokenType::Not:
      return "!";
    default:
      return "<InvalidToken>";
    }
  }
};

} // namespace svm

#endif // TOKEN_H