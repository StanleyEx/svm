#include "Parser.h"
#include "AST.h"
#include "DiagnosticEngine.h"
#include "Lexer.h"
#include "SourceLocation.h"
#include "Token.h"
#include "Utils.h"

#include <string_view>
#include <vector>

namespace svm {
CompUnit *Parser::parse() noexcept {
  SourceLocation start = peek().location;

  std::vector<DeclNode *> decls;
  while (peek().kind != TokenKind::EoF) {
    parseTopLevelItem(decls);
  }

  u64 count = 0;
  auto buffer = arena_.storeVectorToArena(decls, count);
  return arena_.create<CompUnit>(start, lexer_.filename(), buffer, count);
}

void Parser::parseTopLevelItem(std::vector<DeclNode *> &declsOut) {
  const Token &cur = peek();
  switch (cur.kind) {
  case TokenKind::KW_Const:
    parseConstDecl(declsOut);
    return;

  case TokenKind::KW_Void: {
    auto funcDecl = parseFuncDecl();
    if (funcDecl)
      declsOut.push_back(funcDecl);
    return;
  }

  case TokenKind::KW_Int:
  case TokenKind::KW_Float: {
    // Type IDENT( 函数声明
    if (peek(1).kind == TokenKind::Identifier &&
        peek(2).kind == TokenKind::LParen) {
      auto funcDecl = parseFuncDecl();
      if (funcDecl)
        declsOut.push_back(funcDecl);
      return;
    } else
      parseVarDecl(declsOut);
    return;
  }

  default:
    SVM_ERROR(diagEngine_, cur.location,
              "Expected declaration of function definition, but got %s.",
              cur.toString());
    return;
  }
}

// VarDecl -> BType VarDef {',' VarDef ';'}
// VarDef -> Ident {'['] ConstExpr [']'} ['=' InitVal]
void Parser::parseVarDecl(std::vector<DeclNode *> &declsOut) {
  auto basicType = getBasicTypeFromToken(peek());
  advance();

  do {
    std::vector<ExprNode *> dims;
    const char *name = nullptr; // Ident
    SourceLocation nameLoc;
    parseDeclarator(dims, name, nameLoc);

    InitNode *init = nullptr;
    match(TokenKind::Assign);
    if (peek().kind != TokenKind::Semicolon)
      init = parseInitNode();

    u64 dimCount = 0;
    auto buffer = arena_.storeVectorToArena(dims, dimCount);
    declsOut.push_back(arena_.create<VarDecl>(nameLoc, name, basicType, buffer,
                                              dimCount, init));
  } while (match(TokenKind::Comma));

  expect(TokenKind::Semicolon, "';' after variable declaration");
}

// ConstDecl -> 'const' BType ConstDef {',' ConstDef } ';'
// ConstDef -> Ident {'['] ConstExpr [']'} '=' ConstInitVal
void Parser::parseConstDecl(std::vector<DeclNode *> &declsOut) {
  auto constLoc = peek().location;
  advance(); // const
  auto basicType = getBasicTypeFromToken(peek());
  advance();

  do {
    std::vector<ExprNode *> dims;
    const char *name = nullptr;
    SourceLocation nameLoc;
    parseDeclarator(dims, name, nameLoc);

    if (!match(TokenKind::Assign))
      SVM_ERROR(diagEngine_, constLoc + peek().location,
                "Const declaration '%s' requires an initializer.", name);
    InitNode *init = parseInitNode();

    u64 dimCount = 0;
    auto buffer = arena_.storeVectorToArena(dims, dimCount);
    declsOut.push_back(arena_.create<ConstDecl>(nameLoc, name, basicType,
                                                buffer, dimCount, init));
  } while (match(TokenKind::Comma));
  expect(TokenKind::Semicolon, "';' after constant declaration");
}

void Parser::parseDeclarator(std::vector<ExprNode *> &dimsOut,
                             const char *&nameOut, SourceLocation &nameLocOut) {
  auto &ident = peek();
  if (ident.kind != TokenKind::Identifier) {
    SVM_ERROR(diagEngine_, ident.location,
              "Expected function name, but got %s.", ident.toString());
    nameOut = "<Error>";
    nameLocOut = ident.location;
    return;
  }

  nameOut = arena_.duplicateString(ident.text.data(), ident.text.size());
  nameLocOut = ident.location;
  advance();

  while (match(TokenKind::LBracket)) {
    auto *expr = parseExpr();
    expect(TokenKind::RBracket, "']' after array dimension");
    if (expr)
      dimsOut.push_back(expr);
  }
}

// InitVal -> Exp | '{' [ InitVal { ',' InitVal } ] '}'
// 不区分ConstInitVal
InitNode *Parser::parseInitNode() {
  auto &cur = peek();
  if (cur.kind == TokenKind::LBrace) {
    auto LBraceLoc = cur.location;
    advance();

    std::vector<InitNode *> inits;
    if (peek().kind != TokenKind::RBrace) {
      inits.push_back(parseInitNode());
      while (match(TokenKind::Comma)) {
        inits.push_back(parseInitNode());
      }
    }
    auto RBraceLoc =
        expect(TokenKind::RBrace, "'}' after initializer list").location;

    u64 initCount = 0;
    auto buffer = arena_.storeVectorToArena(inits, initCount);
    return arena_.create<InitList>(LBraceLoc + RBraceLoc, buffer, initCount);
  }

  auto expr = parseExpr();
  return arena_.create<InitExpr>(cur.location, expr);
}

// FuncDef     -> FuncType Ident '(' [FuncFParams] ')' Block
// FuncType    -> 'void' | 'int' | 'float'
// FuncFParams -> FuncFParam { ',' FuncFParam }
// FuncFParam  -> BType Ident ['[' ']' { '[' Exp ']' }]
FuncDecl *Parser::parseFuncDecl() {
  auto returnTypeToken = peek();
  TypeKind returnType;
  switch (returnTypeToken.kind) {
  case TokenKind::KW_Void:
    returnType = TypeKind::Void;
    break;
  case TokenKind::KW_Int:
    returnType = TypeKind::Int;
    break;
  case TokenKind::KW_Float:
    returnType = TypeKind::Float;
    break;
  default:
    SVM_ERROR(diagEngine_, returnTypeToken.location,
              "Expected function return type, got %s",
              returnTypeToken.toString());
    syncronize();
    return nullptr;
  }

  auto returnTypeLoc = returnTypeToken.location;
  advance();

  auto &ident = peek();
  if (ident.kind != TokenKind::Identifier) {
    SVM_ERROR(diagEngine_, ident.location,
              "Expected function name, but got %s.", ident.toString());
    syncronize();
    return nullptr;
  }
  auto name = arena_.duplicateString(ident.text.data(), ident.text.size());
  advance();

  expect(TokenKind::LParen, "'(' after function name");

  std::vector<FuncParam *> params;
  if (peek().kind != TokenKind::RParen) {
    auto param = parseFuncParam();
    if (param)
      params.push_back(param);
    while (match(TokenKind::Comma)) {
      param = parseFuncParam();
      if (param)
        params.push_back(param);
    }
  }
  auto RParenLoc =
      expect(TokenKind::RParen, "')' after function parameters").location;

  BlockStmt *body = nullptr;
  // 支持函数定义 如果后面跟的是分号 那么这个语句就是函数定义 body为空
  if (!match(TokenKind::Semicolon))
    body = parseBlock();

  u64 paramCount = 0;
  auto buffer = arena_.storeVectorToArena(params, paramCount);
  return arena_.create<FuncDecl>(returnTypeLoc + RParenLoc, name, returnType,
                                 buffer, paramCount, body);
}

FuncParam *Parser::parseFuncParam() {
  auto basicType = getBasicTypeFromToken(peek());
  if (basicType == TypeKind::Void)
    return nullptr;
  auto basicTypeLoc = peek().location;
  advance();

  auto &ident = peek();
  if (ident.kind != TokenKind::Identifier) {
    SVM_ERROR(diagEngine_, ident.location,
              "Expected parameter name, but got %s.", ident.toString());
    return nullptr;
  }
  auto name = arena_.duplicateString(ident.text.data(), ident.text.size());
  advance();

  bool isArray = false;
  std::vector<ExprNode *> dims;
  if (match(TokenKind::LBracket)) {
    isArray = true;
    expect(TokenKind::RBracket, "']' for omitted first parameter dimension");
    while (match(TokenKind::LBracket)) {
      auto expr = parseExpr();
      expect(TokenKind::RBracket, "']' after array dimension");
      if (expr)
        dims.push_back(expr);
    }
  }

  u64 dimCount = 0;
  auto buffer = arena_.storeVectorToArena(dims, dimCount);
  return arena_.create<FuncParam>(basicTypeLoc, name, basicType, isArray,
                                  buffer, dimCount);
}

BlockStmt *Parser::parseBlock() {
  auto LBraceLoc = peek().location;
  if (!match(TokenKind::LBrace)) {
    SVM_ERROR(diagEngine_, LBraceLoc,
              "Expected '{' to begin block, but got %s.", peek().toString());
    // 不能直接返回 nullptr, 因为BlockStmt能出现在任何块级作用域
    // 直接返回会导致nullptr出现在任何地方
    return arena_.create<BlockStmt>(LBraceLoc, nullptr, 0);
  }

  std::vector<StmtNode *> stmts;
  while (peek().kind != TokenKind::RBrace && peek().kind != TokenKind::EoF) {
    // BlockItem = Decl | Stmt
    auto tokenKind = peek().kind;
    if (tokenKind == TokenKind::KW_Const || tokenKind == TokenKind::KW_Int ||
        tokenKind == TokenKind::KW_Float)
      parseLocalDecl(stmts);
    else {
      auto stmt = parseStmt();
      if (stmt)
        stmts.push_back(stmt);
    }
  }
  expect(TokenKind::RBrace, "'}' to close block");

  u64 stmtCount = 0;
  auto buffer = arena_.storeVectorToArena(stmts, stmtCount);
  return arena_.create<BlockStmt>(LBraceLoc, buffer, stmtCount);
}

void Parser::parseLocalDecl(std::vector<StmtNode *> &declsOut) {
  std::vector<DeclNode *> decls;
  if (peek().kind == TokenKind::KW_Const)
    parseConstDecl(decls);
  else
    parseVarDecl(decls);

  for (auto decl : decls)
    declsOut.push_back(arena_.create<DeclStmt>(decl->getLocation(), decl));
}

StmtNode *Parser::parseStmt() {
  auto &cur = peek();
  switch (cur.kind) {
  case TokenKind::LBrace:
    return parseBlock();
  case TokenKind::Semicolon: {
    auto loc = cur.location;
    advance();
    return arena_.create<EmptyStmt>(loc);
  }
  case TokenKind::KW_If: {
    auto loc = cur.location;
    advance();
    expect(TokenKind::LParen, "'(' after 'if'");
    auto cond = parseExpr();
    auto RParenLoc =
        expect(TokenKind::RParen, "')' to close 'if' condition").location;
    StmtNode *thenStmt = parseStmt(), *elseStmt = nullptr;
    if (match(TokenKind::KW_Else))
      elseStmt = parseStmt();

    return arena_.create<IfStmt>(loc + RParenLoc, cond, thenStmt, elseStmt);
  }
  case TokenKind::KW_While: {
    auto loc = cur.location;
    advance();
    expect(TokenKind::LParen, "'(' after 'while'");
    auto cond = parseExpr();
    auto RParenLoc =
        expect(TokenKind::RParen, "')' to close 'while' condition").location;
    auto body = parseStmt();
    return arena_.create<WhileStmt>(loc + RParenLoc, cond, body);
  }
  case TokenKind::KW_Break: {
    auto loc = cur.location;
    advance();
    auto semicolonToken = expect(TokenKind::Semicolon, "';' after 'break'");
    if (semicolonToken.kind != TokenKind::Semicolon)
      syncronize();
    return arena_.create<BreakStmt>(loc);
  }
  case TokenKind::KW_Continue: {
    auto loc = cur.location;
    advance();
    auto semicolonToken = expect(TokenKind::Semicolon, "';' after 'continue'");
    if (semicolonToken.kind != TokenKind::Semicolon)
      syncronize();
    return arena_.create<ContinueStmt>(loc);
  }
  case TokenKind::KW_Return: {
    auto loc = cur.location;
    advance();
    ExprNode *expr = nullptr;
    if (peek().kind != TokenKind::Semicolon)
      expr = parseExpr();
    auto semicolonToken = expect(TokenKind::Semicolon, "';' after 'return'");
    if (semicolonToken.kind != TokenKind::Semicolon)
      syncronize();
    return arena_.create<ReturnStmt>(loc, expr);
  }
  default:
    return parseExprOrAssignStmt();
  }
}

// Expr ';' 或者 LVal '=' Expr ';'
StmtNode *Parser::parseExprOrAssignStmt() {
  auto loc = peek().location;
  auto lhs = parseExpr();
  if (match(TokenKind::Assign)) {
    if (lhs && !isa<LValueExpr>(lhs)) {
      SVM_ERROR(diagEngine_, loc,
                "Left-hand side of assignment must be an lvalue, but got %.*s.",
                SVM_SV(diagEngine_.getSource(lhs->getLocation())));
    }
    auto rhs = parseExpr();
    auto semicolonToken = expect(TokenKind::Semicolon, "';' after assignment");
    if (semicolonToken.kind != TokenKind::Semicolon)
      syncronize();
    return arena_.create<AssignStmt>(loc, lhs, rhs);
  }

  auto semicolonToken =
      expect(TokenKind::Semicolon, "';' after expression statement");
  if (semicolonToken.kind != TokenKind::Semicolon)
    syncronize();

  if (!lhs) // 按道理不会出现
    return arena_.create<EmptyStmt>(loc);
  return arena_.create<ExprStmt>(loc, lhs);
}

ExprNode *Parser::parseExpr() {
  // 按照文法这里应该要区分Expr和Cond 但是为了兼容C语言(反正是超集)
  // 这里直接下降到LogicOr
  return parseLogicOr();
}

// LOrExp -> LAndExp { '||' LAndExp }
ExprNode *Parser::parseLogicOr() {
  auto lhs = parseLogicAnd();
  while (peek().kind == TokenKind::OrOr) {
    auto loc = peek().location;
    advance();
    auto rhs = parseLogicAnd();
    lhs =
        arena_.create<BinaryExpr>(loc, BinaryExpr::BinaryOp::LogicOr, lhs, rhs);
  }
  return lhs;
}

// LAndExp -> EqExp { '&&' EqExp }
ExprNode *Parser::parseLogicAnd() {
  auto lhs = parseEq();
  while (peek().kind == TokenKind::AndAnd) {
    auto loc = peek().location;
    advance();
    auto rhs = parseEq();
    lhs = arena_.create<BinaryExpr>(loc, BinaryExpr::BinaryOp::LogicAnd, lhs,
                                    rhs);
  }
  return lhs;
}

// EqExp -> RelExp { ('==' | '!=') RelExp }
ExprNode *Parser::parseEq() {
  auto lhs = parseRel();
  while (peek().kind == TokenKind::Eq || peek().kind == TokenKind::NotEq) {
    auto loc = peek().location;
    auto op = (peek().kind == TokenKind::Eq) ? BinaryExpr::BinaryOp::Eq
                                             : BinaryExpr::BinaryOp::NotEq;
    advance();
    auto rhs = parseRel();
    lhs = arena_.create<BinaryExpr>(loc, op, lhs, rhs);
  }
  return lhs;
}

// RelExp -> AddExp { ('<' | '>' | '<=' | '>=') AddExp }
ExprNode *Parser::parseRel() {
  auto *lhs = parseAdd();
  while (true) {
    auto tokenKind = peek().kind;
    BinaryExpr::BinaryOp op;
    switch (tokenKind) {
    case TokenKind::Less:
      op = BinaryExpr::BinaryOp::Less;
      break;
    case TokenKind::Greater:
      op = BinaryExpr::BinaryOp::Greater;
      break;
    case TokenKind::LessEq:
      op = BinaryExpr::BinaryOp::LessEq;
      break;
    case TokenKind::GreaterEq:
      op = BinaryExpr::BinaryOp::GreaterEq;
      break;
    default:
      return lhs;
    }
    auto loc = peek().location;
    advance();
    auto rhs = parseAdd();
    lhs = arena_.create<BinaryExpr>(loc, op, lhs, rhs);
  }
  return lhs;
}

// AddExp -> MulExp { ('+' | '-') MulExp }
ExprNode *Parser::parseAdd() {
  auto lhs = parseMul();
  while (peek().kind == TokenKind::Plus || peek().kind == TokenKind::Minus) {
    auto loc = peek().location;
    auto op = (peek().kind == TokenKind::Plus) ? BinaryExpr::BinaryOp::Add
                                               : BinaryExpr::BinaryOp::Sub;
    advance();
    auto rhs = parseMul();
    lhs = arena_.create<BinaryExpr>(loc, op, lhs, rhs);
  }
  return lhs;
}

// MulExp -> UnaryExp { ('*' | '/' | '%') UnaryExp }
ExprNode *Parser::parseMul() {
  auto lhs = parseUnary();
  while (true) {
    auto tokenKind = peek().kind;
    BinaryExpr::BinaryOp op;
    switch (tokenKind) {
    case TokenKind::Star:
      op = BinaryExpr::BinaryOp::Mul;
      break;
    case TokenKind::Slash:
      op = BinaryExpr::BinaryOp::Div;
      break;
    case TokenKind::Percent:
      op = BinaryExpr::BinaryOp::Mod;
      break;
    default:
      return lhs;
    }
    auto loc = peek().location;
    advance();
    auto rhs = parseUnary();
    lhs = arena_.create<BinaryExpr>(loc, op, lhs, rhs);
  }
  return lhs;
}

// UnaryExp -> PrimaryExp | Ident '(' [FuncRParams] ')' | UnaryOp
// UnaryOp  -> '+' | '-' | '!' (因为统一了Expr和Cond 逻辑非可以出现在任何表达式)
ExprNode *Parser::parseUnary() {
  auto tokenKind = peek().kind;
  if (tokenKind == TokenKind::Plus || tokenKind == TokenKind::Minus ||
      tokenKind == TokenKind::Not) {
    auto loc = peek().location;
    UnaryExpr::UnaryOp op;
    switch (tokenKind) {
    case TokenKind::Plus:
      op = UnaryExpr::UnaryOp::Plus;
      break;
    case TokenKind::Minus:
      op = UnaryExpr::UnaryOp::Minus;
      break;
    case TokenKind::Not:
      op = UnaryExpr::UnaryOp::LogicNot;
      break;
    default:
      break;
    }
    advance();
    auto operand = parseUnary();
    return arena_.create<UnaryExpr>(loc, op, operand);
  }
  return parsePrimary();
}

// PrimaryExp -> '(' Exp ')' | LVal | Number
ExprNode *Parser::parsePrimary() {
  auto &cur = peek();
  switch (cur.kind) {
  case TokenKind::IntegerLiteral: {
    advance();
    return arena_.create<IntLiteralExpr>(cur.location, cur.intValue);
  }
  case TokenKind::FloatLiteral: {
    advance();
    return arena_.create<FloatLiteralExpr>(cur.location, cur.floatValue);
  }
  case TokenKind::LParen: {
    advance();
    auto expr = parseExpr();
    expect(TokenKind::RParen, "')' to close paren expression");
    return expr;
  }
  case TokenKind::Identifier: {
    auto name = arena_.duplicateString(cur.text.data(), cur.text.length());
    advance();
    return parseCallOrLVal(name, cur.location);
  }
  default:
    SVM_ERROR(diagEngine_, cur.location, "Expected expression, but got %s.",
              cur.toString());
    // dummy
    return arena_.create<IntLiteralExpr>(cur.location, 0);
  }
}

ExprNode *Parser::parseCallOrLVal(const char *name, SourceLocation nameLoc) {
  if (match(TokenKind::LParen)) {
    std::vector<ExprNode *> args;
    if (peek().kind != TokenKind::RParen)
      parseFuncRParams(args);
    expect(TokenKind::RParen, "')' to close function call");

    u64 argCount = 0;
    auto buffer = arena_.storeVectorToArena(args, argCount);
    return arena_.create<CallExpr>(nameLoc, name, buffer, argCount);
  }

  std::vector<ExprNode *> subscripts;
  while (match(TokenKind::LBracket)) {
    auto expr = parseExpr();
    expect(TokenKind::RBracket, "']' after array subscript");
    if (expr)
      subscripts.push_back(expr);
  }

  u64 subscriptCount = 0;
  auto buffer = arena_.storeVectorToArena(subscripts, subscriptCount);
  return arena_.create<LValueExpr>(nameLoc, name, buffer, subscriptCount);
}

// FuncRParams -> Exp { ',' Exp }
// 针对putf特判第一个参数可以是字符串字面量
void Parser::parseFuncRParams(std::vector<ExprNode *> &paramsOut) {
  auto parseOneArg = [this]() -> ExprNode * {
    if (peek().kind == TokenKind::StringLiteral) {
      auto token = peek();
      advance();
      return arena_.create<StringLiteralExpr>(token.location, token.text);
    }
    return parseExpr();
  };
  paramsOut.push_back(parseOneArg());
  while (match(TokenKind::Comma)) {
    paramsOut.push_back(parseOneArg());
  };
}
} // namespace svm
