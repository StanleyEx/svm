#ifndef PARSER_H
#define PARSER_H

#include "AST.h"
#include "DiagnosticEngine.h"
#include "Lexer.h"
#include "Type.h"
#include "Utils.h"

namespace svm {
class Parser {
public:
  Parser(Arena &arena, DiagnosticEngine &diagEngine, Lexer &lexer) noexcept
      : arena_(arena), diagEngine_(diagEngine), lexer_(lexer) {}

  Parser(const Parser &) = delete;
  Parser &operator=(const Parser &) = delete;

  CompUnit *parse() noexcept;

private:
  Arena &arena_;
  DiagnosticEngine &diagEngine_;
  Lexer &lexer_;

  // Token流操作 ================================
  constexpr static u32 kMaxTokenCount = 8;
  Token tokens_[kMaxTokenCount]; // LL(8), 用于peek
  u32 tokenCount_ = 0;           // 有效的Token数量

  const Token &peek(u32 n = 0) {
    assert(n < kMaxTokenCount);
    while (tokenCount_ <= n)
      tokens_[tokenCount_++] = lexer_.next();
    return tokens_[n];
  }

  Token advance() {
    UNUSED(peek()); // 填充tokens_[0]
    Token token = tokens_[0];
    for (u32 i = 1; i < tokenCount_; ++i)
      tokens_[i - 1] = tokens_[i];
    --tokenCount_;
    return token;
  }

  bool match(TokenKind kind) {
    if (peek().kind == kind) {
      advance();
      return true;
    } else
      return false;
  }

  Token expect(TokenKind kind, const char *ctx) {
    auto &cur = peek();
    if (cur.kind == kind)
      return advance();

    SVM_ERROR(diagEngine_, cur.location, "Expected %s, but got %s.", ctx,
              cur.toString());
    return cur; // 不消耗
  }

  // 错误恢复 一直跳过直到EoF, RBrace, Semicolon
  void syncronize() {
    while (true) {
      auto &cur = peek();
      if (cur.kind == TokenKind::EoF)
        return;
      if (cur.kind == TokenKind::RBrace)
        return;
      if (cur.kind == TokenKind::Semicolon) {
        advance();
        return;
      }
      advance();
    }
  };

  // Parse ================================
  TypeKind getBaseTypeFromToken(const Token &token) {
    switch (token.kind) {
    case TokenKind::KW_Int:
      return TypeKind::Int;
    case TokenKind::KW_Float:
      return TypeKind::Float;
    default:
      SVM_ERROR(diagEngine_, token.location, "Expected base type, but got %s.",
                token.toString());
      syncronize();
      return TypeKind::Void;
    }
  }

  void parseTopLevelItem(std::vector<DeclNode *> &declsOut);
  void parseVarDecl(std::vector<DeclNode *> &declsOut,
                    SourceLocation *rangeOut = nullptr);
  void parseConstDecl(std::vector<DeclNode *> &declsOut,
                      SourceLocation *rangeOut = nullptr);
  void parseDeclarator(std::vector<ExprNode *> &dimsOut, const char *&nameOut,
                       SourceLocation &nameLocOut, SourceLocation &rangeOut);
  InitNode *parseInitNode();
  FuncDecl *parseFuncDecl();
  FuncParam *parseFuncParam();

  BlockStmt *parseBlock();
  void parseLocalDecl(std::vector<StmtNode *> &declsOut);
  StmtNode *parseStmt();
  StmtNode *parseExprOrAssignStmt();

  ExprNode *parseExpr();
  ExprNode *parseLogicOr();  // ||
  ExprNode *parseLogicAnd(); // &&
  ExprNode *parseEq();       // == !=
  ExprNode *parseRel();      // < > <= >=
  ExprNode *parseAdd();      // + -
  ExprNode *parseMul();      // * / %
  ExprNode *parseUnary();    // + -  !
  ExprNode *parsePrimary();  // Literal | LVal | Call | '(' Expr ')'
  ExprNode *parseCallOrLVal(const char *name, SourceLocation nameLoc);

  void parseFuncRParams(std::vector<ExprNode *> &paramsOut);
};
} // namespace svm

#endif // PARSER_H
