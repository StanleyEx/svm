#include "ASTPrinter.h"

#include "Type.h"

#include <cctype>

namespace svm {
static void putIndent(FILE *out, i32 indent) {
  for (i32 i = 0; i < indent; ++i)
    std::fputs("  ", out);
}

static void putQuoted(FILE *out, std::string_view value) {
  std::fputc('"', out);
  for (char ch : value) {
    unsigned char c = static_cast<unsigned char>(ch);
    switch (c) {
    case '\n':
      std::fputs("\\n", out);
      break;
    case '\t':
      std::fputs("\\t", out);
      break;
    case '\r':
      std::fputs("\\r", out);
      break;
    case '\\':
      std::fputs("\\\\", out);
      break;
    case '"':
      std::fputs("\\\"", out);
      break;
    case '\0':
      std::fputs("\\0", out);
      break;
    default:
      if (std::isprint(c))
        std::fputc(c, out);
      else
        std::fprintf(out, "\\x%02x", c);
      break;
    }
  }
  std::fputc('"', out);
}

void dumpToken(const Token &token, FILE *out) {
  switch (token.kind) {
  case TokenKind::Identifier:
    std::fprintf(out, "%u:%u\t%s\t[%.*s]\n", token.location.line,
                 token.location.column, token.toString(),
                 static_cast<int>(token.text.size()), token.text.data());
    break;
  case TokenKind::IntegerLiteral:
    std::fprintf(out, "%u:%u\t%s\t[%d]\n", token.location.line,
                 token.location.column, token.toString(), token.intValue);
    break;
  case TokenKind::FloatLiteral:
    std::fprintf(out, "%u:%u\t%s\t[%g]\n", token.location.line,
                 token.location.column, token.toString(),
                 static_cast<double>(token.floatValue));
    break;
  case TokenKind::StringLiteral:
    std::fprintf(out, "%u:%u\t%s\t", token.location.line, token.location.column,
                 token.toString());
    putQuoted(out, token.text);
    std::fputc('\n', out);
    break;
  default:
    std::fprintf(out, "%u:%u\t%s\n", token.location.line, token.location.column,
                 token.toString());
    break;
  }
}

void dumpAST(const ASTNode *node, FILE *out, i32 indent) {
  putIndent(out, indent);
  if (!node) {
    std::fputs("<null>\n", out);
    return;
  }

  switch (node->getKind()) {
  case ASTKind::CompUnit: {
    auto *n = cast<CompUnit>(node);
    std::fprintf(out, "CompUnit \"%s\"\n", n->filename ? n->filename : "");
    for (u32 i = 0; i < n->declCount; ++i)
      dumpAST(n->decls[i], out, indent + 1);
    return;
  }
  case ASTKind::VarDecl: {
    auto *n = cast<VarDecl>(node);
    std::fprintf(out, "VarDecl %s %s", getString(n->baseType),
                 n->name ? n->name : "");
    if (n->dimensionCount)
      std::fprintf(out, " [%u dims]", n->dimensionCount);
    std::fputc('\n', out);
    for (u32 i = 0; i < n->dimensionCount; ++i) {
      putIndent(out, indent + 1);
      std::fprintf(out, "Dim[%u]:\n", i);
      dumpAST(n->dimensions[i], out, indent + 2);
    }
    if (n->init) {
      putIndent(out, indent + 1);
      std::fputs("Init:\n", out);
      dumpAST(n->init, out, indent + 2);
    }
    return;
  }
  case ASTKind::ConstDecl: {
    auto *n = cast<ConstDecl>(node);
    std::fprintf(out, "ConstDecl %s %s", getString(n->baseType),
                 n->name ? n->name : "");
    if (n->dimensionCount)
      std::fprintf(out, " [%u dims]", n->dimensionCount);
    std::fputc('\n', out);
    for (u32 i = 0; i < n->dimensionCount; ++i) {
      putIndent(out, indent + 1);
      std::fprintf(out, "Dim[%u]:\n", i);
      dumpAST(n->dimensions[i], out, indent + 2);
    }
    if (n->init) {
      putIndent(out, indent + 1);
      std::fputs("Init:\n", out);
      dumpAST(n->init, out, indent + 2);
    }
    return;
  }
  case ASTKind::FuncDecl: {
    auto *n = cast<FuncDecl>(node);
    std::fprintf(out, "FuncDecl %s %s(%u params)\n", getString(n->returnType),
                 n->name ? n->name : "", n->paramCount);
    for (u32 i = 0; i < n->paramCount; ++i)
      dumpAST(n->params[i], out, indent + 1);
    if (n->body) {
      putIndent(out, indent + 1);
      std::fputs("Body:\n", out);
      dumpAST(n->body, out, indent + 2);
    }
    return;
  }
  case ASTKind::FuncParam: {
    auto *n = cast<FuncParam>(node);
    std::fprintf(out, "FuncParam %s %s", getString(n->baseType),
                 n->name ? n->name : "");
    if (n->isArray)
      std::fputs(" []", out);
    std::fputc('\n', out);
    for (u32 i = 0; i < n->dimensionCount; ++i) {
      putIndent(out, indent + 1);
      std::fprintf(out, "Dim[%u]:\n", i);
      dumpAST(n->dimensions[i], out, indent + 2);
    }
    return;
  }
  case ASTKind::IntegerLiteralExpr:
    std::fprintf(out, "IntegerLiteralExpr %d\n",
                 cast<IntLiteralExpr>(node)->value);
    return;
  case ASTKind::FloatLiteralExpr:
    std::fprintf(out, "FloatLiteralExpr %g\n",
                 static_cast<double>(cast<FloatLiteralExpr>(node)->value));
    return;
  case ASTKind::StringLiteralExpr:
    std::fputs("StringLiteralExpr ", out);
    putQuoted(out, cast<StringLiteralExpr>(node)->value);
    std::fputc('\n', out);
    return;
  case ASTKind::LValueExpr: {
    auto *n = cast<LValueExpr>(node);
    std::fprintf(out, "LValueExpr %s", n->name ? n->name : "");
    if (n->subscriptCount)
      std::fprintf(out, " [%u subs]", n->subscriptCount);
    std::fputc('\n', out);
    for (u32 i = 0; i < n->subscriptCount; ++i) {
      putIndent(out, indent + 1);
      std::fprintf(out, "Sub[%u]:\n", i);
      dumpAST(n->subscripts[i], out, indent + 2);
    }
    return;
  }
  case ASTKind::CallExpr: {
    auto *n = cast<CallExpr>(node);
    std::fprintf(out, "CallExpr %s(%u args)\n", n->callee ? n->callee : "",
                 n->argCount);
    for (u32 i = 0; i < n->argCount; ++i) {
      putIndent(out, indent + 1);
      std::fprintf(out, "Arg[%u]:\n", i);
      dumpAST(n->args[i], out, indent + 2);
    }
    return;
  }
  case ASTKind::UnaryExpr: {
    auto *n = cast<UnaryExpr>(node);
    std::fprintf(out, "UnaryExpr %s\n", n->toString());
    dumpAST(n->operand, out, indent + 1);
    return;
  }
  case ASTKind::BinaryExpr: {
    auto *n = cast<BinaryExpr>(node);
    std::fprintf(out, "BinaryExpr %s\n", n->toString());
    dumpAST(n->lhs, out, indent + 1);
    dumpAST(n->rhs, out, indent + 1);
    return;
  }
  case ASTKind::ImplicitCastExpr: {
    auto *n = cast<ImplicitCastExpr>(node);
    std::fprintf(out, "ImplicitCastExpr %s\n", n->toString());
    dumpAST(n->operand, out, indent + 1);
    return;
  }
  case ASTKind::InitExpr:
    std::fputs("InitExpr\n", out);
    dumpAST(cast<InitExpr>(node)->expr, out, indent + 1);
    return;
  case ASTKind::InitList: {
    auto *n = cast<InitList>(node);
    std::fprintf(out, "InitList (%u items)\n", n->initCount);
    for (u32 i = 0; i < n->initCount; ++i)
      dumpAST(n->inits[i], out, indent + 1);
    return;
  }
  case ASTKind::BlockStmt: {
    auto *n = cast<BlockStmt>(node);
    std::fprintf(out, "BlockStmt (%u items)\n", n->stmtCount);
    for (u32 i = 0; i < n->stmtCount; ++i)
      dumpAST(n->stmts[i], out, indent + 1);
    return;
  }
  case ASTKind::ExprStmt:
    std::fputs("ExprStmt\n", out);
    dumpAST(cast<ExprStmt>(node)->expr, out, indent + 1);
    return;
  case ASTKind::AssignStmt: {
    auto *n = cast<AssignStmt>(node);
    std::fputs("AssignStmt\n", out);
    putIndent(out, indent + 1);
    std::fputs("Lhs:\n", out);
    dumpAST(n->lhs, out, indent + 2);
    putIndent(out, indent + 1);
    std::fputs("Rhs:\n", out);
    dumpAST(n->rhs, out, indent + 2);
    return;
  }
  case ASTKind::IfStmt: {
    auto *n = cast<IfStmt>(node);
    std::fputs("IfStmt\n", out);
    putIndent(out, indent + 1);
    std::fputs("Cond:\n", out);
    dumpAST(n->cond, out, indent + 2);
    putIndent(out, indent + 1);
    std::fputs("Then:\n", out);
    dumpAST(n->thenStmt, out, indent + 2);
    if (n->elseStmt) {
      putIndent(out, indent + 1);
      std::fputs("Else:\n", out);
      dumpAST(n->elseStmt, out, indent + 2);
    }
    return;
  }
  case ASTKind::WhileStmt: {
    auto *n = cast<WhileStmt>(node);
    std::fputs("WhileStmt\n", out);
    putIndent(out, indent + 1);
    std::fputs("Cond:\n", out);
    dumpAST(n->cond, out, indent + 2);
    putIndent(out, indent + 1);
    std::fputs("Body:\n", out);
    dumpAST(n->body, out, indent + 2);
    return;
  }
  case ASTKind::BreakStmt:
    std::fputs("BreakStmt\n", out);
    return;
  case ASTKind::ContinueStmt:
    std::fputs("ContinueStmt\n", out);
    return;
  case ASTKind::ReturnStmt:
    std::fputs("ReturnStmt\n", out);
    if (cast<ReturnStmt>(node)->expr)
      dumpAST(cast<ReturnStmt>(node)->expr, out, indent + 1);
    return;
  case ASTKind::DeclStmt:
    std::fputs("DeclStmt\n", out);
    dumpAST(cast<DeclStmt>(node)->decl, out, indent + 1);
    return;
  case ASTKind::EmptyStmt:
    std::fputs("EmptyStmt\n", out);
    return;
  default:
    std::fprintf(out, "<Unhandled %s>\n", getString(node->getKind()));
    return;
  }
}
} // namespace svm
