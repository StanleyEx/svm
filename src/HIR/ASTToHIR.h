#ifndef AST_TO_HIR_H
#define AST_TO_HIR_H

#include "AST.h"
#include "DiagnosticEngine.h"
#include "IR.h"

#include <string>
#include <unordered_map>

namespace svm::ir {
class ASTToHIR {
public:
  ASTToHIR(Arena &arena, DiagnosticEngine &diagnostics) noexcept;
  Module *run(CompUnit *unit);

private:
  void registerGlobals(CompUnit *unit);
  void registerFunctions(CompUnit *unit);
  void registerRuntimeCallees(CompUnit *unit);
  Function *registerFunction(FuncDecl *declaration);
  void lowerFunctionBodies(CompUnit *unit);
  void lowerFunction(FuncDecl *declaration, Function *function);
  void visitRuntimeExpr(ExprNode *expr);
  void visitRuntimeInit(InitNode *init);
  void visitRuntimeStmt(StmtNode *stmt);
  void lowerStmt(StmtNode *stmt);
  void lowerLocal(DeclNode *declaration);
  Inst *lowerLocalStorage(const ASTNode *declaration, Type *type,
                          TypeKind baseType, InitSegment *segments,
                          u32 segmentCount);
  Inst *lowerExpr(ExprNode *expr);
  Inst *lowerLogical(BinaryExpr *expr);
  Inst *lowerCall(CallExpr *expr);
  Inst *lowerAddress(LValueExpr *expr);                 // 左值地址
  Inst *materializeAddress(const ASTNode *declaration); // 解析存储地址
  Inst *lowerCondition(ExprNode *expr);
  Inst *materializeString(StringLiteralExpr *literal);
  // 打包全局初始化
  bool packGlobalInit(InitSegment *segments, u32 segmentCount,
                      const ArrayType *array, Global *global,
                      SourceLocation location);
  // 读取常量字面量
  bool extractConstantLiteral(ExprNode *expr, IRType target, i32 &integer,
                              f32 &floating) const;
  // 校验函数签名
  bool hasValidSignature(FuncDecl *declaration);
  // 比较函数签名
  bool signaturesMatch(FuncDecl *left, FuncDecl *right) const;
  Type *declarationType(const ASTNode *declaration) const noexcept;
  Type *scalarElementType(Type *type) const noexcept;
  IRType scalarType(Type *type) const noexcept;
  IRType baseType(TypeKind type) const noexcept;
  void setSourceLocation(const ASTNode *node);
  void diagnose(SourceLocation location, const char *message);

  Arena &arena_;
  DiagnosticEngine &diagnostics_;
  Module *module_ = nullptr;
  IRBuilder *builder_ = nullptr;
  std::unordered_map<const ASTNode *, Inst *> locals_;
  std::unordered_map<const ASTNode *, const SourceLocation *> locations_;
  std::unordered_map<std::string, FuncDecl *> canonicalFunctions_;
  u32 nextStringId_ = 0;
};
} // namespace svm::ir

#endif // AST_TO_HIR_H
