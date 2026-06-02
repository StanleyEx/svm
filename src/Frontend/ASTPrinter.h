#ifndef AST_PRINTER_H
#define AST_PRINTER_H

#include "AST.h"
#include "Token.h"

#include <cstdio>

namespace svm {
void dumpToken(const Token &token, FILE *out = stdout);
void dumpAST(const ASTNode *node, FILE *out = stdout, i32 indent = 0);
} // namespace svm

#endif // AST_PRINTER_H
