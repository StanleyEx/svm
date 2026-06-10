#ifndef SEMA_H
#define SEMA_H

#include "AST.h"
#include "DiagnosticEngine.h"
#include "Type.h"
#include <algorithm>
#include <string>
#include <unordered_map>
#include <vector>

namespace svm {

class Sema;

// 连续零的数量超过这个值时 生成一个InitSegment
static constexpr u32 ZERO_RUN_LIMIT = 4;

class InitSegmentBuilder {
public:
  explicit InitSegmentBuilder(Arena &arena) noexcept : arena_(arena) {}

  void add(ExprNode *expr) {
    if (!expr || ((isa<IntLiteralExpr>(expr) &&
                   cast<IntLiteralExpr>(expr)->value == 0) ||
                  (isa<FloatLiteralExpr>(expr) &&
                   cast<FloatLiteralExpr>(expr)->value == 0.0f)))
      ++zeroRun_;
    else {
      flushZeros();
      pending_.push_back(expr);
    }
    totalEmitted_++;
  }

  void fillZero(u64 count) {
    zeroRun_ += count;
    totalEmitted_ += count;
  }

  u64 size() const { return totalEmitted_; }

  void resize(u64 newSize) {
    if (newSize >= totalEmitted_) {
      fillZero(newSize - totalEmitted_);
      return;
    }
    u64 toRemove = totalEmitted_ - newSize;
    while (toRemove > 0) {
      if (zeroRun_ > 0) {
        auto drop = std::min<u64>(zeroRun_, toRemove);
        zeroRun_ -= drop;
        toRemove -= drop;
      } else if (!pending_.empty()) {
        auto drop = std::min<u64>(pending_.size(), toRemove);
        pending_.resize(pending_.size() - drop);
        toRemove -= drop;
      } else if (!segments_.empty()) {
        auto &lastSeg = segments_.back();
        if (lastSeg.initCount <= toRemove) {
          toRemove -= lastSeg.initCount;
          segments_.pop_back();
        } else {
          lastSeg.initCount -= toRemove;
          toRemove = 0;
        }
      } else {
        break;
      }
    }
    totalEmitted_ = newSize;
  }

  InitSegment *finalize(u64 &segmentCount) {
    flushZeros();
    flushPending();
    segmentCount = segments_.size();
    if (segmentCount == 0)
      return nullptr;
    auto *result = arena_.createArray<InitSegment>(segmentCount);
    std::memcpy(result, segments_.data(), sizeof(InitSegment) * segmentCount);
    return result;
  }

private:
  Arena &arena_;
  std::vector<InitSegment> segments_;
  std::vector<ExprNode *> pending_;
  u64 zeroRun_ = 0;
  u64 totalEmitted_ = 0;

  void flushZeros() {
    if (zeroRun_ == 0)
      return;
    if (zeroRun_ < ZERO_RUN_LIMIT) {
      for (u64 i = 0; i < zeroRun_; ++i)
        pending_.push_back(nullptr);
    } else {
      flushPending();
      segments_.push_back(InitSegment{zeroRun_, nullptr});
    }
    zeroRun_ = 0;
  }

  void flushPending() {
    if (pending_.empty())
      return;
    u64 n = pending_.size();
    auto buffer = arena_.createArray<ExprNode *>(n);
    for (u64 i = 0; i < n; ++i) {
      buffer[i] = pending_[i];
    }
    segments_.push_back(InitSegment{n, buffer});
    pending_.clear();
  }
};

// 求值结果
struct ConstValue {
  enum class Kind : u8 {
    Int,
    Float,
  };
  Kind kind = Kind::Int;
  union {
    i32 intValue;
    f32 floatValue;
  };

  ConstValue() noexcept : kind(Kind::Int), intValue(0) {}
  ConstValue(i32 value) noexcept : kind(Kind::Int), intValue(value) {}
  ConstValue(f32 value) noexcept : kind(Kind::Float), floatValue(value) {}

  bool isInt() const noexcept { return kind == Kind::Int; }
  bool isFloat() const noexcept { return kind == Kind::Float; }
  i32 asInt() const noexcept {
    return isInt() ? intValue : static_cast<i32>(floatValue);
  }
  f32 asFloat() const noexcept {
    return isFloat() ? floatValue : static_cast<f32>(intValue);
  }
};

class Sema {
public:
  Sema(Arena &arena, DiagnosticEngine &diagEngine,
       TypeContext &typeCtx) noexcept
      : arena_(arena), diagEngine_(diagEngine), typeCtx_(typeCtx) {}
  Sema(const Sema &) = delete;
  Sema &operator=(const Sema &) = delete;

  void run(CompUnit *compUnit);

private:
  Arena &arena_;
  DiagnosticEngine &diagEngine_;
  TypeContext &typeCtx_;

  std::unordered_map<std::string, ASTNode *> globals_;
  std::unordered_map<std::string, FuncDecl *> functions_;
  using SymTable = std::unordered_map<std::string, ASTNode *>;
  std::vector<SymTable> scopes_;

  FuncDecl *currentFunction_ = nullptr;
  i32 loopDepth_ = 0;
  SourceLocation nowhereLoc{};

  // 驱动函数
  void collectGlobals(CompUnit *compUnit);
  void processTopLevelDecls(CompUnit *compUnit);
  void verifyMain();

  // 分析声明
  void checkDecl(DeclNode *decl, bool isGlobal);
  ExprNode *checkInitExpr(InitExpr *initExpr, Type *baseType, bool needEval);
  void processScalarInit(InitNode *init, Type *baseType, bool needEval,
                         InitSegmentBuilder &initSegBuilder);
  void processInitList(InitList *initList, Type *baseType, const i32 *dims,
                       u32 dimCount, bool needEval,
                       InitSegmentBuilder &initSegBuilder);
  void checkFunc(FuncDecl *funcDecl);
  Type *computeParamType(FuncParam *param);

  i32 evalDimExpr(ExprNode *expr);
  Type *getScalarType(TypeKind baseTypeKind) noexcept; // int/float
  Type *getReturnType(TypeKind returnType) noexcept;   // int/float/void

  // 分析语句/表达式
  void checkStmt(StmtNode *stmt);
  ExprNode *checkExpr(ExprNode *expr);
  ExprNode *checkCond(ExprNode *condExpr);
  ExprNode *checkLValue(LValueExpr *lvalExpr);
  ExprNode *checkCall(CallExpr *callExpr);
  void checkBinary(BinaryExpr *binExpr);
  void checkBinaryArith(BinaryExpr *binExpr);
  void checkBinaryRelation(BinaryExpr *binExpr);
  void checkBinaryEq(BinaryExpr *binExpr);
  void checkBinaryLogic(BinaryExpr *binExpr);

  // 强制转换
  Type *ArithConvert(ExprNode *&lhs, ExprNode *&rhs);
  ExprNode *coerceTo(ExprNode *expr, Type *target);
  ExprNode *toIntCond(ExprNode *expr);
  ExprNode *makeCast(ExprNode *src, ImplicitCastExpr::CastKind castKind);

  // 求值
  bool eval(ExprNode *expr, ConstValue &out);
  ExprNode *makeLiteralFromConst(SourceLocation loc, Type *scalarType,
                                 const ConstValue &value);

  // 作用域管理
  void pushScope() { scopes_.emplace_back(); }
  void popScope() { scopes_.pop_back(); }
  bool declareGlobal(const char *name, ASTNode *node);
  bool declare(const char *name, ASTNode *node);
  ASTNode *lookupValue(const char *name);
  FuncDecl *lookupFunc(const char *name);
};
} // namespace svm

#endif // SEMA_H
