#ifndef AST_H
#define AST_H

#include "TypeSystem.h"
#include "Utils/SourceLocation.h"
#include "Utils/Types.h"

#include <string_view>

namespace svm {
enum class ASTKind : u16 {
  CompUnit,

  AST_DECL_START,
  VarDecl = AST_DECL_START,
  ConstDecl,
  FuncDecl,
  AST_DECL_END = FuncDecl,

  AST_EXPR_START,
  IntegerLiteralExpr = AST_EXPR_START,
  FloatLiteralExpr,
  StringLiteralExpr,
  LValueExpr,
  CallExpr,
  UnaryExpr,
  BinaryExpr,
  ImplicitCastExpr,
  AST_EXPR_END = ImplicitCastExpr,

  AST_STMT_START,
  BlockStmt = AST_STMT_START,
  ExprStmt,
  AssignStmt,
  IfStmt,
  WhileStmt,
  BreakStmt,
  ContinueStmt,
  ReturnStmt,
  DeclStmt,
  EmptyStmt,
  AST_STMT_END = EmptyStmt,

  AST_INIT_START,
  InitExpr = AST_INIT_START,
  InitList,
  AST_INIT_END = InitList,

  FuncParam,
};

[[maybe_unused]] static const char *getString(ASTKind type) {
  switch (type) {
  case ASTKind::CompUnit:
    return "CompUnit";
  case ASTKind::VarDecl:
    return "VarDecl";
  case ASTKind::ConstDecl:
    return "ConstDecl";
  case ASTKind::FuncDecl:
    return "FuncDecl";
  case ASTKind::IntegerLiteralExpr:
    return "IntegerLiteralExpr";
  case ASTKind::FloatLiteralExpr:
    return "FloatLiteralExpr";
  case ASTKind::StringLiteralExpr:
    return "StringLiteralExpr";
  case ASTKind::LValueExpr:
    return "LValueExpr";
  case ASTKind::CallExpr:
    return "CallExpr";
  case ASTKind::UnaryExpr:
    return "UnaryExpr";
  case ASTKind::BinaryExpr:
    return "BinaryExpr";
  case ASTKind::ImplicitCastExpr:
    return "ImplicitCastExpr";
  case ASTKind::BlockStmt:
    return "BlockStmt";
  case ASTKind::ExprStmt:
    return "ExprStmt";
  case ASTKind::AssignStmt:
    return "AssignStmt";
  case ASTKind::IfStmt:
    return "IfStmt";
  case ASTKind::WhileStmt:
    return "WhileStmt";
  case ASTKind::BreakStmt:
    return "BreakStmt";
  case ASTKind::ContinueStmt:
    return "ContinueStmt";
  case ASTKind::ReturnStmt:
    return "ReturnStmt";
  case ASTKind::DeclStmt:
    return "DeclStmt";
  case ASTKind::EmptyStmt:
    return "EmptyStmt";
  case ASTKind::InitExpr:
    return "InitExpr";
  case ASTKind::InitList:
    return "InitList";
  case ASTKind::FuncParam:
    return "FuncParam";
  default:
    return "<InvalidASTKind>";
  }
}

// -Node 抽象基类
class ASTNode {
public:
  ASTKind getKind() const noexcept { return type_; }
  SourceLocation getLocation() const noexcept { return location_; }

protected:
  ASTNode(ASTKind type, SourceLocation location)
      : type_(type), location_(location) {}

  ASTKind type_;
  SourceLocation location_;
};

class DeclNode : public ASTNode {
public:
  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() >= ASTKind::AST_DECL_START &&
           node->getKind() <= ASTKind::AST_DECL_END;
  }

protected:
  DeclNode(ASTKind type, SourceLocation location) noexcept
      : ASTNode(type, location) {}
};

class ExprNode : public ASTNode {
public:
  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() >= ASTKind::AST_EXPR_START &&
           node->getKind() <= ASTKind::AST_EXPR_END;
  }

  Type *getType() const noexcept { return type_; }
  void setType(Type *type) noexcept { type_ = type; }

protected:
  ExprNode(ASTKind type, SourceLocation location) noexcept
      : ASTNode(type, location) {}

  Type *type_ = nullptr;
};

class StmtNode : public ASTNode {
public:
  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() >= ASTKind::AST_STMT_START &&
           node->getKind() <= ASTKind::AST_STMT_END;
  }

protected:
  StmtNode(ASTKind type, SourceLocation location) noexcept
      : ASTNode(type, location) {}
};

class InitNode : public ASTNode {
public:
  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() >= ASTKind::AST_INIT_START &&
           node->getKind() <= ASTKind::AST_INIT_END;
  }

protected:
  InitNode(ASTKind type, SourceLocation location) noexcept
      : ASTNode(type, location) {}
};

// -Expr
class IntLiteralExpr final : public ExprNode {
public:
  i32 value;

  IntLiteralExpr(SourceLocation location, i32 value) noexcept
      : ExprNode(ASTKind::IntegerLiteralExpr, location), value(value) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::IntegerLiteralExpr;
  }
};

class FloatLiteralExpr final : public ExprNode {
public:
  f32 value;

  FloatLiteralExpr(SourceLocation location, f32 value) noexcept
      : ExprNode(ASTKind::FloatLiteralExpr, location), value(value) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::FloatLiteralExpr;
  }
};

class StringLiteralExpr final : public ExprNode {
public:
  std::string_view value;

  StringLiteralExpr(SourceLocation location, std::string_view value) noexcept
      : ExprNode(ASTKind::StringLiteralExpr, location), value(value) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::StringLiteralExpr;
  }
};

class LValueExpr final : public ExprNode {
public:
  const char *name;
  ExprNode **subscripts;
  u32 subscriptCount;

  ASTNode *resolved = nullptr; // 由Sema填充 VarDecl / ConstDecl / FuncParam

  LValueExpr(SourceLocation location, const char *name, ExprNode **subscripts,
             u32 subscriptCount) noexcept
      : ExprNode(ASTKind::LValueExpr, location), name(name),
        subscripts(subscripts), subscriptCount(subscriptCount) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::LValueExpr;
  }
};

class FuncDecl;
class CallExpr final : public ExprNode {
public:
  const char *callee;
  ExprNode **args;
  u32 argCount;

  FuncDecl *resolvedFunc = nullptr; // 由Sema解析

  CallExpr(SourceLocation location, const char *callee, ExprNode **args,
           u32 argCount) noexcept
      : ExprNode(ASTKind::CallExpr, location), callee(callee), args(args),
        argCount(argCount) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::CallExpr;
  }
};

class UnaryExpr final : public ExprNode {
public:
  enum class UnaryOp : u8 {
    Plus,
    Minus,
    LogicNot,
  };
  UnaryOp op;
  ExprNode *operand;

  UnaryExpr(SourceLocation location, UnaryOp op, ExprNode *operand) noexcept
      : ExprNode(ASTKind::UnaryExpr, location), op(op), operand(operand) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::UnaryExpr;
  }

  [[maybe_unused]] const char *getString(UnaryOp op) {
    switch (op) {
    case UnaryOp::Plus:
      return "+";
    case UnaryOp::Minus:
      return "-";
    case UnaryOp::LogicNot:
      return "!";
    default:
      return "<InvalidUnaryOp>";
    }
  }
};

class BinaryExpr final : public ExprNode {
public:
  enum class BinaryOp : u8 {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    NotEq,
    Less,
    LessEq,
    Greater,
    GreaterEq,
    LogicAnd,
    LogicOr,
  };
  BinaryOp op;
  ExprNode *lhs;
  ExprNode *rhs;

  BinaryExpr(SourceLocation location, BinaryOp op, ExprNode *lhs,
             ExprNode *rhs) noexcept
      : ExprNode(ASTKind::BinaryExpr, location), op(op), lhs(lhs), rhs(rhs) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::BinaryExpr;
  }

  [[maybe_unused]] const char *toString() {
    switch (op) {
    case BinaryOp::Add:
      return "+";
    case BinaryOp::Sub:
      return "-";
    case BinaryOp::Mul:
      return "*";
    case BinaryOp::Div:
      return "/";
    case BinaryOp::Mod:
      return "%";
    case BinaryOp::Eq:
      return "==";
    case BinaryOp::NotEq:
      return "!=";
    case BinaryOp::Less:
      return "<";
    case BinaryOp::LessEq:
      return "<=";
    case BinaryOp::Greater:
      return ">";
    case BinaryOp::GreaterEq:
      return ">=";
    case BinaryOp::LogicAnd:
      return "&&";
    case BinaryOp::LogicOr:
      return "||";
    default:
      return "<InvalidBinaryOp>";
    }
  }
};

class ImplicitCastExpr final : public ExprNode {
public:
  enum class CastKind : u8 {
    IntToFloat,
    FloatToInt,
  };
  CastKind kind;
  ExprNode *operand;

  ImplicitCastExpr(SourceLocation location, CastKind kind,
                   ExprNode *operand) noexcept
      : ExprNode(ASTKind::ImplicitCastExpr, location), kind(kind),
        operand(operand) {}
  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::ImplicitCastExpr;
  }

  [[maybe_unused]] const char *toString() const {
    switch (kind) {
    case CastKind::IntToFloat:
      return "int->float";
    case CastKind::FloatToInt:
      return "float->int";
    default:
      return "<InvalidCastKind>";
    }
  }
};

class InitExpr final : public InitNode {
public:
  ExprNode *expr;

  InitExpr(SourceLocation location, ExprNode *expr) noexcept
      : InitNode(ASTKind::InitExpr, location), expr(expr) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::InitExpr;
  }
};

// { expr, expr, ... }
class InitList final : public InitNode {
public:
  InitNode **inits;
  u32 initCount;

  InitList(SourceLocation location, InitNode **inits, u32 initCount) noexcept
      : InitNode(ASTKind::InitList, location), inits(inits),
        initCount(initCount) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::InitList;
  }
};

// Sema分析InitList时将其转换这个结构体
struct InitSegment {
  u32 initCount;
  InitExpr *initExprs; // 如果为nullptr则说明全部为0初始化
};

// -Decl
class VarDecl final : public DeclNode {
public:
  const char *name;
  TypeKind basicType;    // Parse时填充
  ExprNode **dimensions; // 如果是标量则为nullptr
  u32 dimensionCount;    // 如果是标量则为0
  InitNode *init;        // 如果没有初始化则为nullptr

  // 以下均由Sema填充 有默认值
  Type *type = nullptr; // 完整类型
  InitSegment *initSegments = nullptr;
  u32 initSegmentCount = 0;
  bool isGlobal = false;

  VarDecl(SourceLocation location, const char *name, TypeKind basicType,
          ExprNode **dimensions, u32 dimensionCount, InitExpr *init) noexcept
      : DeclNode(ASTKind::VarDecl, location), name(name), basicType(basicType),
        dimensions(dimensions), dimensionCount(dimensionCount), init(init) {}

  bool isArray() const noexcept { return dimensionCount > 0; }

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::VarDecl;
  }
};

class ConstDecl final : public DeclNode {
public:
  const char *name;
  TypeKind basicType;    // Parse时填充
  ExprNode **dimensions; // 如果是标量则为nullptr
  u32 dimensionCount;    // 如果是标量则为0
  InitNode *init;        // 规定必须有初始化

  // 以下均由Sema填充 有默认值
  Type *type = nullptr; // 完整类型
  InitSegment *initSegments = nullptr;
  u32 initSegmentCount = 0;
  bool isGlobal = false;

  ConstDecl(SourceLocation location, const char *name, TypeKind basicType,
            ExprNode **dimensions, u32 dimensionCount, InitExpr *init) noexcept
      : DeclNode(ASTKind::ConstDecl, location), name(name),
        basicType(basicType), dimensions(dimensions),
        dimensionCount(dimensionCount), init(init) {}

  bool isArray() const noexcept { return dimensionCount > 0; }

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::ConstDecl;
  }
};

// 注意这里继承自ASTNode而不是DeclNode 因为Decl只能附在Program或者BlockStmt中
// 而且FuncParam的降级方法和VarDecl/ConstDecl不同
class FuncParam final : public ASTNode {
public:
  const char *name;
  TypeKind basicType;
  bool isArray;
  ExprNode **dimensions;
  u32 dimensionCount;

  Type *type = nullptr; // 完整类型 由Sema填充

  FuncParam(SourceLocation location, const char *name, TypeKind basicType,
            bool isArray, ExprNode **dimensions, u32 dimensionCount) noexcept
      : ASTNode(ASTKind::FuncParam, location), name(name), basicType(basicType),
        isArray(isArray), dimensions(dimensions),
        dimensionCount(dimensionCount) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::FuncParam;
  }
};

class FuncDecl final : public DeclNode {
public:
  const char *name;
  TypeKind returnType;
  FuncParam **params;
  u32 paramCount;
  StmtNode *body;

  // 以下均由Sema填充 有默认值
  FunctionType *type = nullptr;
  bool isRuntime = false; // SysY运行时库函数

  FuncDecl(SourceLocation location, const char *name, TypeKind returnType,
           FuncParam **params, u32 paramCount, StmtNode *body) noexcept
      : DeclNode(ASTKind::FuncDecl, location), name(name),
        returnType(returnType), params(params), paramCount(paramCount),
        body(body) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::FuncDecl;
  }
};

// -Stmt
class BlockStmt final : public StmtNode {
public:
  StmtNode **stmts;
  u32 stmtCount;

  BlockStmt(SourceLocation location, StmtNode **stmts, u32 stmtCount) noexcept
      : StmtNode(ASTKind::BlockStmt, location), stmts(stmts),
        stmtCount(stmtCount) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::BlockStmt;
  }
};

class ExprStmt final : public StmtNode {
public:
  ExprNode *expr; // 永不为空 空语句是EmptyStmt

  ExprStmt(SourceLocation location, ExprNode *expr) noexcept
      : StmtNode(ASTKind::ExprStmt, location), expr(expr) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::ExprStmt;
  }
};

class EmptyStmt final : public StmtNode {
public:
  explicit EmptyStmt(SourceLocation location) noexcept
      : StmtNode(ASTKind::EmptyStmt, location) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::EmptyStmt;
  }
};

class AssignStmt final : public StmtNode {
public:
  ExprNode *lhs, *rhs;

  AssignStmt(SourceLocation location, ExprNode *lhs, ExprNode *rhs) noexcept
      : StmtNode(ASTKind::AssignStmt, location), lhs(lhs), rhs(rhs) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::AssignStmt;
  }
};

class IfStmt final : public StmtNode {
public:
  ExprNode *cond;
  StmtNode *thenStmt;
  StmtNode *elseStmt; // 如果没有则为nullptr

  IfStmt(SourceLocation location, ExprNode *cond, StmtNode *thenStmt,
         StmtNode *elseStmt) noexcept
      : StmtNode(ASTKind::IfStmt, location), cond(cond), thenStmt(thenStmt),
        elseStmt(elseStmt) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::IfStmt;
  }
};

class WhileStmt final : public StmtNode {
public:
  ExprNode *cond;
  StmtNode *body;

  WhileStmt(SourceLocation location, ExprNode *cond, StmtNode *body) noexcept
      : StmtNode(ASTKind::WhileStmt, location), cond(cond), body(body) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::WhileStmt;
  }
};

class BreakStmt final : public StmtNode {
public:
  explicit BreakStmt(SourceLocation location) noexcept
      : StmtNode(ASTKind::BreakStmt, location) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::BreakStmt;
  }
};

class ContinueStmt final : public StmtNode {
public:
  explicit ContinueStmt(SourceLocation location) noexcept
      : StmtNode(ASTKind::ContinueStmt, location) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::ContinueStmt;
  }
};

class ReturnStmt final : public StmtNode {
public:
  ExprNode *expr; // 如果没有则为nullptr

  ReturnStmt(SourceLocation location, ExprNode *expr) noexcept
      : StmtNode(ASTKind::ReturnStmt, location), expr(expr) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::ReturnStmt;
  }
};

class DeclStmt final : public StmtNode {
public:
  DeclNode *decl;

  DeclStmt(SourceLocation location, DeclNode *decl) noexcept
      : StmtNode(ASTKind::DeclStmt, location), decl(decl) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::DeclStmt;
  }
};

class CompUnit final : public ASTNode {
public:
  const char *filename;
  DeclNode **decls; // VarDecl/ConstDecl/FuncDecl
  u32 declCount;

  CompUnit(SourceLocation location, const char *filename, DeclNode **decls,
           u32 declCount) noexcept
      : ASTNode(ASTKind::CompUnit, location), filename(filename), decls(decls),
        declCount(declCount) {}

  static bool classof(const ASTNode *node) noexcept {
    return node->getKind() == ASTKind::CompUnit;
  }
};

// LLVM-style RTTI
template <typename To, typename From> inline bool isa(const From *p) noexcept {
  return p != nullptr && To::classof(p);
}

template <typename To, typename From> inline To *dyn_cast(From *p) noexcept {
  return (p && To::classof(p)) ? static_cast<To *>(p) : nullptr;
}

template <typename To, typename From>
inline const To *dyn_cast(const From *p) noexcept {
  return (p && To::classof(p)) ? static_cast<const To *>(p) : nullptr;
}

template <typename To, typename From> inline To *cast(From *p) noexcept {
  assert(p && To::classof(p) && "cast<> Failed: type mismatch");
  return static_cast<To *>(p);
}

template <typename To, typename From>
inline const To *cast(const From *p) noexcept {
  assert(p && To::classof(p) && "cast<> Failed: type mismatch");
  return static_cast<const To *>(p);
}

} // namespace svm

#endif // AST_H
