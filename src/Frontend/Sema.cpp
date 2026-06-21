#include "Sema.h"
#include "AST.h"
#include "DiagnosticEngine.h"
#include "SourceLocation.h"
#include "Type.h"
#include "Utils.h"
#include <cstring>
#include <limits>

namespace svm {
void Sema::run(CompUnit *compUnit) {
  if (!compUnit)
    return;

  // 注入运行时库函数
  constexpr struct RuntimeProto {
    const char *name;
    TypeKind returnType;
    const char
        *paramTypes; // "" 无参数, "i" int, "f" float, "I" int[], "F" float[]
    bool isVariadic;
  } runtimeProtos[] = {
      {"getint", TypeKind::Int, "", false},
      {"getch", TypeKind::Int, "", false},
      {"getfloat", TypeKind::Float, "", false},
      {"getarray", TypeKind::Int, "I", false},
      {"getfarray", TypeKind::Int, "F", false},
      {"putint", TypeKind::Void, "i", false},
      {"putch", TypeKind::Void, "i", false},
      {"putfloat", TypeKind::Void, "f", false},
      {"putarray", TypeKind::Void, "iI", false},
      {"putfarray", TypeKind::Void, "iF", false},
      {"putf", TypeKind::Void, "", true},
      {"_sysy_starttime", TypeKind::Void, "i", false},
      {"_sysy_stoptime", TypeKind::Void, "i", false},
  };
  for (const auto &proto : runtimeProtos) {
    usize paramCount = std::strlen(proto.paramTypes);
    FuncParam **params = arena_.createArray<FuncParam *>(paramCount);
    Type **paramTypes = arena_.createArray<Type *>(paramCount);

    for (usize i = 0; i < paramCount; i++) {
      TypeKind typeKind = TypeKind::Int;
      bool isArray = false;
      switch (proto.paramTypes[i]) {
      case 'i':
        typeKind = TypeKind::Int;
        isArray = false;
        break;
      case 'f':
        typeKind = TypeKind::Float;
        isArray = false;
        break;
      case 'I':
        typeKind = TypeKind::Int;
        isArray = true;
        break;
      case 'F':
        typeKind = TypeKind::Float;
        isArray = true;
        break;
      default:
        assert(false && "Invalid runtime proto");
      }
      char nameBuf[32];
      std::snprintf(nameBuf, sizeof(nameBuf), "_arg%u", static_cast<u32>(i));
      auto pname = arena_.duplicateString(nameBuf);
      params[i] = arena_.create<FuncParam>(nowhereLoc, pname, typeKind, isArray,
                                           nullptr, 0);
      paramTypes[i] = params[i]->type = computeParamType(params[i]);
    }

    FuncDecl *funcDecl = arena_.create<FuncDecl>(
        nowhereLoc, proto.name, proto.returnType, params, paramCount, nullptr);
    funcDecl->isRuntime = true;
    funcDecl->type =
        typeCtx_.getFunctionType(getReturnType(proto.returnType), paramTypes,
                                 paramCount, proto.isVariadic);
    functions_[proto.name] = funcDecl;
    globals_[proto.name] = funcDecl;
  }

  collectGlobals(compUnit);
  processTopLevelDecls(compUnit);
  verifyMain();
}

void Sema::collectGlobals(CompUnit *compUnit) {
  for (u32 i = 0; i < compUnit->declCount; i++) {
    auto *decl = compUnit->decls[i];
    if (!decl)
      continue;

    switch (decl->getKind()) {
    case ASTKind::VarDecl: {
      auto *varDecl = cast<VarDecl>(decl);
      varDecl->isGlobal = true;
      declareGlobal(varDecl->name, varDecl);
      break;
    }
    case ASTKind::ConstDecl: {
      auto *constDecl = cast<ConstDecl>(decl);
      constDecl->isGlobal = true;
      checkDecl(constDecl, true); // 必须先求值 供确定函数签名的数组维度表达式
      declareGlobal(constDecl->name, constDecl);
      break;
    }
    default:
      break;
    }
  }

  auto registerFuncBody = [&](FuncDecl *funcDecl) {
    Type **pTypes = nullptr;
    if (funcDecl->paramCount > 0) {
      pTypes = arena_.createArray<Type *>(funcDecl->paramCount);
      for (u32 i = 0; i < funcDecl->paramCount; i++)
        funcDecl->params[i]->type = pTypes[i] =
            computeParamType(funcDecl->params[i]);
    }
    Type *retType = getReturnType(funcDecl->returnType);
    funcDecl->type =
        typeCtx_.getFunctionType(retType, pTypes, funcDecl->paramCount, false);
    globals_[funcDecl->name] = funcDecl;
    functions_[funcDecl->name] = funcDecl;
  };

  auto sameSignature = [](FuncDecl *lhs, FuncDecl *rhs) {
    if (!lhs || !rhs || lhs->returnType != rhs->returnType ||
        lhs->paramCount != rhs->paramCount)
      return false;
    for (u32 i = 0; i < lhs->paramCount; ++i) {
      if (lhs->params[i]->baseType != rhs->params[i]->baseType ||
          lhs->params[i]->isArray != rhs->params[i]->isArray ||
          lhs->params[i]->dimensionCount != rhs->params[i]->dimensionCount)
        return false;
    }
    return true;
  };

  for (u32 i = 0; i < compUnit->declCount; i++) {
    auto *funcDecl = dyn_cast<FuncDecl>(compUnit->decls[i]);
    if (!funcDecl)
      continue;

    auto it = globals_.find(funcDecl->name);
    if (it != globals_.end()) { // 检查全局符号表是否有同名
      auto *oldDecl = it->second;
      if (auto *oldFuncDecl = dyn_cast<FuncDecl>(oldDecl)) { // 同名函数定义
        if (oldFuncDecl->isRuntime && funcDecl->body) {      // 重定义运行时函数
          SVM_ERROR(diagEngine_, funcDecl->getLocation(),
                    "Redefinition of runtime function '%s'.", funcDecl->name);
          continue;
        }

        if (!sameSignature(oldFuncDecl, funcDecl)) {
          SVM_ERROR(diagEngine_, funcDecl->getLocation(),
                    "Conflicting declaration of function '%s'.",
                    funcDecl->name);
        } else {
          funcDecl->type = oldFuncDecl->type;
          for (u32 index = 0; index < funcDecl->paramCount; ++index)
            funcDecl->params[index]->type =
                oldFuncDecl->type->paramTypes[index];
        }
        if (sameSignature(oldFuncDecl, funcDecl) && !oldFuncDecl->body &&
            funcDecl->body) {
          registerFuncBody(funcDecl);
        } else if (sameSignature(oldFuncDecl, funcDecl) && oldFuncDecl->body &&
                   funcDecl->body) {
          SVM_ERROR(diagEngine_, funcDecl->getLocation(),
                    "Redefinition of function '%s'.", funcDecl->name);
        }
      } else // 同名与变量冲突
        SVM_ERROR(diagEngine_, funcDecl->getLocation(),
                  "Redefinition of '%s', previous declared as a variable.",
                  funcDecl->name);
      continue;
    }

    registerFuncBody(funcDecl);
  }
}

void Sema::processTopLevelDecls(CompUnit *compUnit) {
  for (u32 i = 0; i < compUnit->declCount; i++) {
    auto decl = compUnit->decls[i];
    if (!decl)
      continue;

    switch (decl->getKind()) {
    case ASTKind::VarDecl: {
      auto varDecl = cast<VarDecl>(decl);
      varDecl->isGlobal = true;
      checkDecl(varDecl, true);
      declareGlobal(varDecl->name, varDecl);
      break;
    }
    case ASTKind::ConstDecl: {
      // 在collectGlobals()中处理
      break;
    }
    case ASTKind::FuncDecl: {
      checkFunc(cast<FuncDecl>(decl));
      break;
    }
    default:
      break;
    }
  }
}

void Sema::verifyMain() {
  auto it = functions_.find("main");
  if (it == functions_.end()) {
    SVM_ERROR(diagEngine_, nowhereLoc, "No main function found.");
    return;
  }
  auto mainFunc = it->second;
  if (mainFunc->paramCount != 0)
    SVM_ERROR(diagEngine_, mainFunc->getLocation(),
              "'main' function should have no parameters.");
  if (mainFunc->returnType != TypeKind::Int)
    SVM_ERROR(diagEngine_, mainFunc->getLocation(),
              "'main' function should return int.");
}

// 分析声明
void Sema::checkDecl(DeclNode *decl, bool isGlobal) {
  TypeKind baseTypeKind;
  ExprNode **dims = nullptr;
  u32 dimCount = 0;
  InitNode *init = nullptr;
  bool isConst = false;
  const char *name;
  SourceLocation location;

  if (auto varDecl = dyn_cast<VarDecl>(decl)) {
    baseTypeKind = varDecl->baseType;
    dims = varDecl->dimensions;
    dimCount = varDecl->dimensionCount;
    init = varDecl->init;
    isConst = false;
    name = varDecl->name;
    location = varDecl->getLocation();
  } else if (auto constDecl = dyn_cast<ConstDecl>(decl)) {
    baseTypeKind = constDecl->baseType;
    dims = constDecl->dimensions;
    dimCount = constDecl->dimensionCount;
    init = constDecl->init;
    isConst = true;
    name = constDecl->name;
    location = constDecl->getLocation();
  } else
    return;

  i32 *evaledDims = nullptr;
  if (dimCount > 0) {
    evaledDims = arena_.createArray<i32>(dimCount);
    for (u32 i = 0; i < dimCount; i++)
      evaledDims[i] = evalDimExpr(dims[i]);
  }
  auto baseType = getScalarType(baseTypeKind);

  u32 totalElems = 1;
  for (u32 i = 0; i < dimCount; i++) {
    const u64 product =
        static_cast<u64>(totalElems) * static_cast<u64>(evaledDims[i]);
    if (product > std::numeric_limits<u32>::max()) {
      SVM_ERROR(diagEngine_, location, "Array '%s' has too many elements.",
                name);
      evaledDims[i] = 1;
      continue;
    }
    totalElems = static_cast<u32>(product);
  }
  auto declType = dimCount == 0
                      ? baseType
                      : typeCtx_.getArrayType(baseType, evaledDims, dimCount);

  InitSegmentBuilder initSegBuilder(arena_);
  bool needEval = isConst || isGlobal;

  if (init) {
    if (auto initExpr = dyn_cast<InitExpr>(init)) { // = expr
      if (dimCount > 0) {
        SVM_ERROR(diagEngine_, initExpr->getLocation(),
                  "Array initializer must be an initializer list.");
        initSegBuilder.fillZero(totalElems);
      } else {
        initSegBuilder.add(checkInitExpr(initExpr, baseType, needEval));
      }
    } else if (auto initList = dyn_cast<InitList>(init)) { // = { ... }
      if (dimCount == 0)
        processScalarInit(initList, baseType, needEval, initSegBuilder);
      else {
        processInitList(initList, baseType, evaledDims, dimCount, needEval,
                        initSegBuilder);
        initSegBuilder.resize(totalElems);
      }
    }
  } else {         // 无初始化器
    if (isConst) { // const必须要有初始值
      SVM_ERROR(diagEngine_, location,
                "Constant declaration '%s' must have an initializer.", name);
      initSegBuilder.fillZero(totalElems);
    } else if (isGlobal) // 全局变量默认初始化为0
      initSegBuilder.fillZero(totalElems);
  }

  u64 segmentCount = 0;
  auto initSegments = initSegBuilder.finalize(segmentCount);
  if (auto varDecl = dyn_cast<VarDecl>(decl)) {
    varDecl->type = declType;
    varDecl->initSegments = initSegments;
    varDecl->initSegmentCount = segmentCount;
    varDecl->isGlobal = isGlobal;
  } else if (auto constDecl = dyn_cast<ConstDecl>(decl)) {
    constDecl->type = declType;
    constDecl->initSegments = initSegments;
    constDecl->initSegmentCount = segmentCount;
    constDecl->isGlobal = isGlobal;
  }
}

ExprNode *Sema::checkInitExpr(InitExpr *initExpr, Type *baseType,
                              bool needEval) {
  if (!initExpr || !initExpr->expr)
    return nullptr;
  ExprNode *value = checkExpr(initExpr->expr);
  initExpr->expr = coerceTo(value, baseType);
  value = initExpr->expr;
  if (!needEval || !value)
    return value;

  ConstValue constValue;
  if (eval(value, constValue))
    return makeLiteralFromConst(value->getLocation(), baseType, constValue);
  SVM_ERROR(diagEngine_, value->getLocation(),
            "Initializer must be a constant expression.");
  return nullptr;
}

void Sema::processScalarInit(InitNode *init, Type *baseType, bool needEval,
                             InitSegmentBuilder &initSegBuilder) {
  if (auto *initExpr = dyn_cast<InitExpr>(init)) {
    initSegBuilder.add(checkInitExpr(initExpr, baseType, needEval));
    return;
  }

  auto *initList = dyn_cast<InitList>(init);
  if (!initList) {
    initSegBuilder.fillZero(1);
    return;
  }

  const u64 start = initSegBuilder.size();
  for (u32 index = 0; index < initList->initCount; ++index) {
    if (initList->inits[index])
      processScalarInit(initList->inits[index], baseType, needEval,
                        initSegBuilder);
  }
  const u64 initialized = initSegBuilder.size() - start;
  if (initialized == 0)
    initSegBuilder.fillZero(1);
  else if (initialized > 1) {
    SVM_ERROR(diagEngine_, initList->getLocation(),
              "Scalar initializer has too many elements.");
    initSegBuilder.resize(start + 1);
  }
}

void Sema::processInitList(InitList *initList, Type *baseType, const i32 *dims,
                           u32 dimCount, bool needEval,
                           InitSegmentBuilder &initSegBuilder) {
  assert(initList && baseType && dims && dimCount > 0);

  u64 subobjectSize = 1;
  for (u32 i = 1; i < dimCount; i++)
    subobjectSize *= static_cast<u64>(dims[i]);
  const u64 expectedElems = static_cast<u64>(dims[0]) * subobjectSize;

  const u64 start = initSegBuilder.size();

  for (u32 i = 0; i < initList->initCount; i++) {
    InitNode *item = initList->inits[i];
    if (!item)
      continue;

    if (auto initExpr = dyn_cast<InitExpr>(item)) {
      initSegBuilder.add(checkInitExpr(initExpr, baseType, needEval));
    } else if (auto initListInner = dyn_cast<InitList>(item)) {
      const u64 initialized = initSegBuilder.size() - start;
      if (dimCount > 1) {
        const u64 offset = initialized % subobjectSize;
        if (offset != 0)
          initSegBuilder.fillZero(subobjectSize - offset);
        processInitList(initListInner, baseType, dims + 1, dimCount - 1,
                        needEval, initSegBuilder);
        continue;
      }

      processScalarInit(initListInner, baseType, needEval, initSegBuilder);
    }
  }
  const u64 actualSegments = initSegBuilder.size() - start;
  if (actualSegments > expectedElems) {
    SVM_WARN(diagEngine_, initList->getLocation(),
             "Too many elements in initializer list. (%llu, got %llu)",
             static_cast<unsigned long long>(expectedElems),
             static_cast<unsigned long long>(actualSegments));
    initSegBuilder.resize(start + expectedElems);
  } else if (actualSegments < expectedElems)
    initSegBuilder.fillZero(expectedElems - actualSegments);
}

void Sema::checkFunc(FuncDecl *funcDecl) {
  if (!funcDecl || !funcDecl->body)
    return;

  currentFunction_ = funcDecl;
  loopDepth_ = 0;

  pushScope();

  for (u32 i = 0; i < funcDecl->paramCount; i++) {
    auto param = funcDecl->params[i];
    if (!param)
      continue;
    if (param->type == nullptr)
      param->type = computeParamType(param);
    declare(param->name, param);
  }

  if (funcDecl->body)
    checkStmt(funcDecl->body);
  else if (!funcDecl->isRuntime)
    SVM_ERROR(diagEngine_, funcDecl->getLocation(),
              "Function '%s' has no body.", funcDecl->name);

  popScope();
}

Type *Sema::computeParamType(FuncParam *param) {
  if (!param)
    return nullptr;

  auto type = getScalarType(param->baseType);

  if (!param->isArray)
    return type;

  if (param->dimensionCount == 0)
    return typeCtx_.getPointerType(typeCtx_.getAnyDimArrayType(type));

  i32 *evaledDims = arena_.createArray<i32>(param->dimensionCount);
  for (u32 i = 0; i < param->dimensionCount; i++)
    evaledDims[i] = evalDimExpr(param->dimensions[i]);
  return typeCtx_.getPointerType(
      typeCtx_.getArrayType(type, evaledDims, param->dimensionCount));
}

i32 Sema::evalDimExpr(ExprNode *expr) {
  auto checkedExpr = checkExpr(expr);
  ConstValue constValue;
  if (!eval(checkedExpr, constValue)) {
    SVM_ERROR(diagEngine_, expr->getLocation(),
              "Array dimension must be a constant expression.");
    return 1;
  }
  i32 value = constValue.asInt();
  if (value <= 0) {
    SVM_ERROR(diagEngine_, expr->getLocation(),
              "Array dimension must be positive.");
    return 1;
  }
  return value;
}

Type *Sema::getScalarType(TypeKind baseTypeKind) noexcept {
  switch (baseTypeKind) {
  case TypeKind::Int:
    return typeCtx_.getIntType();
  case TypeKind::Float:
    return typeCtx_.getFloatType();
  default:
    return typeCtx_.getIntType();
  }
}

Type *Sema::getReturnType(TypeKind returnType) noexcept {
  if (returnType == TypeKind::Void)
    return typeCtx_.getVoidType();
  return getScalarType(returnType);
}

// 分析语句/表达式
void Sema::checkStmt(StmtNode *stmt) {
  if (!stmt)
    return;

  switch (stmt->getKind()) {
  case ASTKind::BlockStmt: {
    auto *blockStmt = cast<BlockStmt>(stmt);
    pushScope();
    for (u32 i = 0; i < blockStmt->stmtCount; i++)
      checkStmt(blockStmt->stmts[i]);
    popScope();
    return;
  }
  case ASTKind::DeclStmt: {
    auto *declStmt = cast<DeclStmt>(stmt);
    auto *decl = declStmt->decl;
    if (!decl)
      return;
    checkDecl(decl, false);
    const char *name = nullptr;
    if (auto *varDecl = dyn_cast<VarDecl>(decl))
      name = varDecl->name;
    else if (auto *constDecl = dyn_cast<ConstDecl>(decl))
      name = constDecl->name;
    if (name)
      declare(name, decl);
    return;
  }
  case ASTKind::AssignStmt: {
    auto *assignStmt = cast<AssignStmt>(stmt);
    assignStmt->lhs = checkExpr(assignStmt->lhs);
    assignStmt->rhs = checkExpr(assignStmt->rhs);

    auto lval = dyn_cast<LValueExpr>(assignStmt->lhs);
    if (!lval)
      return;

    if (lval->resolved) {
      if (isa<ConstDecl>(lval->resolved)) {
        SVM_ERROR(diagEngine_, lval->getLocation(), "Cannot assign to '%s'.",
                  lval->name);
        return;
      }
      if (auto *varDecl = dyn_cast<VarDecl>(lval->resolved))
        varDecl->isMutated = true;
    }

    auto lhsType = lval->getType();
    if (!isScalarType(lhsType)) {
      SVM_ERROR(diagEngine_, lval->getLocation(),
                "Cannot assign to non-scalar value '%s'.", lval->name);
      return;
    }
    assignStmt->rhs = coerceTo(assignStmt->rhs, lhsType);
    return;
  }
  case ASTKind::ExprStmt: {
    auto *exprStmt = cast<ExprStmt>(stmt);
    exprStmt->expr = checkExpr(exprStmt->expr);
    return;
  }
  case ASTKind::IfStmt: {
    auto *ifStmt = cast<IfStmt>(stmt);
    ifStmt->cond = checkCond(ifStmt->cond);
    checkStmt(ifStmt->thenStmt);
    if (ifStmt->elseStmt)
      checkStmt(ifStmt->elseStmt);
    return;
  }
  case ASTKind::WhileStmt: {
    auto *whileStmt = cast<WhileStmt>(stmt);
    whileStmt->cond = checkCond(whileStmt->cond);
    ++loopDepth_;
    checkStmt(whileStmt->body);
    --loopDepth_;
    return;
  }
  case ASTKind::BreakStmt:
    if (loopDepth_ <= 0)
      SVM_ERROR(diagEngine_, stmt->getLocation(),
                "Break statement outside of a loop.");
    return;
  case ASTKind::ContinueStmt:
    if (loopDepth_ <= 0)
      SVM_ERROR(diagEngine_, stmt->getLocation(),
                "Continue statement outside of a loop.");
    return;
  case ASTKind::ReturnStmt: {
    auto *returnStmt = cast<ReturnStmt>(stmt);
    if (!returnStmt)
      return;
    auto returnType = currentFunction_->returnType;
    if (returnStmt->expr) {
      if (returnType == TypeKind::Void) {
        SVM_ERROR(diagEngine_, returnStmt->getLocation(),
                  "Return statement in void function.");
        returnStmt->expr = checkExpr(returnStmt->expr);
      } else {
        returnStmt->expr = checkExpr(returnStmt->expr);
        returnStmt->expr =
            coerceTo(returnStmt->expr, getReturnType(returnType));
      }
    } else if (returnType != TypeKind::Void) {
      SVM_ERROR(diagEngine_, returnStmt->getLocation(),
                "non-void function '%s' must return a value.",
                currentFunction_->name);
    }
    return;
  }
  case ASTKind::EmptyStmt:
  default:
    return;
  }
}

ExprNode *Sema::checkExpr(ExprNode *expr) {
  if (!expr)
    return nullptr;

  switch (expr->getKind()) {
  case ASTKind::IntegerLiteralExpr:
    expr->setType(typeCtx_.getIntType());
    return expr;
  case ASTKind::FloatLiteralExpr:
    expr->setType(typeCtx_.getFloatType());
    return expr;
  case ASTKind::StringLiteralExpr:
    SVM_ERROR(diagEngine_, expr->getLocation(),
              "String literals is only allowed in putf");
    expr->setType(typeCtx_.getIntType());
    return expr;
  case ASTKind::LValueExpr:
    return checkLValue(cast<LValueExpr>(expr));
  case ASTKind::CallExpr:
    return checkCall(cast<CallExpr>(expr));
  case ASTKind::UnaryExpr: {
    auto *unaryExpr = cast<UnaryExpr>(expr);
    unaryExpr->operand = checkExpr(unaryExpr->operand);
    Type *operandType =
        unaryExpr->operand ? unaryExpr->operand->getType() : nullptr;
    if (!isScalarType(operandType)) {
      SVM_ERROR(diagEngine_, unaryExpr->getLocation(),
                "Unary expression must require a scalar.");
      unaryExpr->setType(typeCtx_.getIntType());
      return unaryExpr;
    }
    switch (unaryExpr->op) {
    case UnaryExpr::UnaryOp::Plus:
    case UnaryExpr::UnaryOp::Minus:
      unaryExpr->setType(operandType);
      break;
    case UnaryExpr::UnaryOp::LogicNot:
      unaryExpr->setType(typeCtx_.getIntType());
      break;
    }
    return unaryExpr;
  }
  case ASTKind::BinaryExpr: {
    auto *binExpr = cast<BinaryExpr>(expr);
    checkBinary(binExpr);
    return binExpr;
  }
  case ASTKind::ImplicitCastExpr:
  default:
    expr->setType(typeCtx_.getIntType());
    return expr;
  }
}

ExprNode *Sema::checkCond(ExprNode *condExpr) {
  return toIntCond(checkExpr(condExpr));
}

ExprNode *Sema::checkLValue(LValueExpr *lvalExpr) {
  auto *decl = lookupValue(lvalExpr->name);
  if (!decl) {
    SVM_ERROR(diagEngine_, lvalExpr->getLocation(),
              "use of undeclared variable '%s'.", lvalExpr->name);
    lvalExpr->setType(typeCtx_.getIntType());
    return lvalExpr;
  }
  lvalExpr->resolved = decl;

  Type *declType = nullptr;
  if (auto *varDecl = dyn_cast<VarDecl>(decl))
    declType = varDecl->type;
  else if (auto *constDecl = dyn_cast<ConstDecl>(decl))
    declType = constDecl->type;
  else if (auto *paramDecl = dyn_cast<FuncParam>(decl))
    declType = paramDecl->type;

  if (!declType) {
    lvalExpr->setType(typeCtx_.getIntType());
    return lvalExpr;
  }

  for (u32 i = 0; i < lvalExpr->subscriptCount; i++) {
    lvalExpr->subscripts[i] = checkExpr(lvalExpr->subscripts[i]);
    auto *subscript = lvalExpr->subscripts[i];
    if (subscript && isa<FloatType>(subscript->getType()))
      lvalExpr->subscripts[i] = coerceTo(subscript, typeCtx_.getIntType());
    else if (subscript && !isa<IntType>(subscript->getType()))
      SVM_ERROR(diagEngine_, subscript->getLocation(),
                "Array subscript must be an integer.");
  }

  Type *result = [&](Type *type, u32 count) -> Type * {
    if (count == 0)
      return type;
    if (isScalarType(type))
      return nullptr;

    Type *baseElemType = nullptr;
    const i32 *dims = nullptr;
    u32 dimCount = 0;
    if (auto *pointerType = dyn_cast<PointerType>(type)) {
      if (isScalarType(pointerType->pointee)) {
        if (count != 1)
          return nullptr;
        return pointerType->pointee;
      } else if (auto *anyDimArrayType =
                     dyn_cast<AnyDimArrayType>(pointerType->pointee)) {
        if (count != 1)
          return nullptr;
        return anyDimArrayType->elementType;
      } else if (auto *arrayType = dyn_cast<ArrayType>(pointerType->pointee)) {
        if (count - 1 > arrayType->dimCount)
          return nullptr;
        if (count - 1 == arrayType->dimCount)
          return arrayType->elementType;
        baseElemType = arrayType->elementType;
        dims = arrayType->dims;
        dimCount = arrayType->dimCount;
        count--;
      }
    } else if (auto *arrayType = dyn_cast<ArrayType>(type)) {
      if (count > arrayType->dimCount)
        return nullptr;
      if (count == arrayType->dimCount)
        return arrayType->elementType;
      baseElemType = arrayType->elementType;
      dims = arrayType->dims;
      dimCount = arrayType->dimCount;
    }
    u32 left = dimCount - count;
    if (left == 1)
      return typeCtx_.getPointerType(baseElemType);
    return typeCtx_.getArrayType(baseElemType, dims + count + 1, left - 1);
  }(declType, lvalExpr->subscriptCount);
  if (!result) {
    SVM_ERROR(diagEngine_, lvalExpr->getLocation(),
              "invalid subscript for '%s'", lvalExpr->name);
    lvalExpr->setType(typeCtx_.getIntType());
  }
  lvalExpr->setType(result);
  return lvalExpr;
}

ExprNode *Sema::checkCall(CallExpr *callExpr) {
  // starttime() -> _sysy_starttime(__LINE__)
  // stoptime()  -> _sysy_stoptime(__LINE__)
  if (std::strcmp(callExpr->callee, "starttime") == 0 ||
      std::strcmp(callExpr->callee, "stoptime") == 0) {
    const char *sysyName = (std::strcmp(callExpr->callee, "starttime") == 0)
                               ? "_sysy_starttime"
                               : "_sysy_stoptime";
    callExpr->callee = arena_.duplicateString(sysyName);
    auto newArgs = arena_.createArray<ExprNode *>(1);
    newArgs[0] = arena_.create<IntLiteralExpr>(
        callExpr->getLocation(),
        static_cast<i32>(callExpr->getLocation().line));
    callExpr->args = newArgs;
    callExpr->argCount = 1;
  }

  FuncDecl *func = lookupFunc(callExpr->callee);
  if (!func) {
    SVM_ERROR(diagEngine_, callExpr->getLocation(),
              "call to undeclared function '%s'", callExpr->callee);
    callExpr->setType(typeCtx_.getIntType());
    return callExpr;
  }
  callExpr->resolvedFunc = func;

  Type *returnType = getReturnType(func->returnType);

  // putf不定长参数调用
  if (func->isRuntime && std::strcmp(func->name, "putf") == 0) {
    if (callExpr->argCount < 1) {
      SVM_ERROR(diagEngine_, callExpr->getLocation(),
                "putf requires at least a format string argument");
      callExpr->setType(returnType);
      return callExpr;
    }
    auto first = callExpr->args[0];
    if (!first || !isa<StringLiteralExpr>(first))
      SVM_ERROR(diagEngine_, callExpr->getLocation(),
                "first argument of putf() must be a string literal");
    else // 打上int类型占位符以保持下游遍历正常工作
      first->setType(typeCtx_.getIntType());

    for (u32 i = 1; i < callExpr->argCount; ++i) {
      callExpr->args[i] = checkExpr(callExpr->args[i]);
      auto arg = callExpr->args[i];
      if (arg && !isScalarType(arg->getType()))
        SVM_ERROR(diagEngine_, arg->getLocation(),
                  "putf argument %u must be a scalar", i);
    }
    callExpr->setType(returnType);
    return callExpr;
  }

  // 普通固定参数个数调用
  if (callExpr->argCount != func->paramCount) {
    SVM_ERROR(diagEngine_, callExpr->getLocation(),
              "call to function '%s' requires %u arguments, but got %u",
              func->name, func->paramCount, callExpr->argCount);
    for (u32 i = 0; i < callExpr->argCount; ++i)
      callExpr->args[i] = checkExpr(callExpr->args[i]);
    callExpr->setType(returnType);
    return callExpr;
  }

  for (u32 i = 0; i < callExpr->argCount; ++i) {
    callExpr->args[i] = checkExpr(callExpr->args[i]);
    auto *arg = callExpr->args[i];
    auto *formal = func->params[i]->type;
    if (!arg || !formal)
      continue;

    if (isScalarType(formal)) {
      if (!isScalarType(arg->getType())) {
        SVM_ERROR(diagEngine_, arg->getLocation(),
                  "Argument %u of '%s' must be a scalar.", i + 1, func->name);
      } else {
        callExpr->args[i] = coerceTo(arg, formal);
      }
      continue;
    }

    if (!isa<PointerType>(formal)) {
      SVM_ERROR(diagEngine_, arg->getLocation(),
                "Unsupported parameter type in call to '%s'.", func->name);
      continue;
    }

    auto *actualType = arg->getType();
    if (!isa<PointerType>(actualType) && !isa<ArrayType>(actualType)) {
      SVM_ERROR(diagEngine_, arg->getLocation(),
                "Argument %u of '%s' must be an array.", i + 1, func->name);
      continue;
    }

    bool mayMutate =
        !(func->isRuntime && (std::strcmp(func->name, "putarray") == 0 ||
                              std::strcmp(func->name, "putfarray") == 0));
    if (mayMutate) {
      auto *cur = arg;
      while (auto *castExpr = dyn_cast<ImplicitCastExpr>(cur))
        cur = castExpr->operand;
      if (auto *lval = dyn_cast<LValueExpr>(cur)) {
        if (auto *varDecl = dyn_cast<VarDecl>(lval->resolved))
          varDecl->isMutated = true;
      }
    }
  }
  callExpr->setType(returnType);
  return callExpr;
}

void Sema::checkBinary(BinaryExpr *binExpr) {
  binExpr->lhs = checkExpr(binExpr->lhs);
  binExpr->rhs = checkExpr(binExpr->rhs);

  switch (binExpr->op) {
  case BinaryExpr::BinaryOp::Add:
  case BinaryExpr::BinaryOp::Sub:
  case BinaryExpr::BinaryOp::Mul:
  case BinaryExpr::BinaryOp::Div:
  case BinaryExpr::BinaryOp::Mod:
    checkBinaryArith(binExpr);
    return;
  case BinaryExpr::BinaryOp::Less:
  case BinaryExpr::BinaryOp::LessEq:
  case BinaryExpr::BinaryOp::Greater:
  case BinaryExpr::BinaryOp::GreaterEq:
    checkBinaryRelation(binExpr);
    return;
  case BinaryExpr::BinaryOp::Eq:
  case BinaryExpr::BinaryOp::NotEq:
    checkBinaryEq(binExpr);
    return;
  case BinaryExpr::BinaryOp::LogicAnd:
  case BinaryExpr::BinaryOp::LogicOr:
    checkBinaryLogic(binExpr);
    return;
  }
}

void Sema::checkBinaryArith(BinaryExpr *binExpr) {
  Type *lhsType = binExpr->lhs ? binExpr->lhs->getType() : nullptr;
  Type *rhsType = binExpr->rhs ? binExpr->rhs->getType() : nullptr;
  if (!isScalarType(lhsType) || !isScalarType(rhsType)) {
    SVM_ERROR(diagEngine_, binExpr->getLocation(),
              "Arithmetic operator '%s' requires scalar operands.",
              binExpr->toString());
    binExpr->setType(typeCtx_.getIntType());
    return;
  }

  if (binExpr->op == BinaryExpr::BinaryOp::Mod) {
    if (!isa<IntType>(lhsType) || !isa<IntType>(rhsType))
      SVM_ERROR(diagEngine_, binExpr->getLocation(),
                "Operator '%%' requires integer operands.");
    binExpr->setType(typeCtx_.getIntType());
    return;
  }

  binExpr->setType(ArithConvert(binExpr->lhs, binExpr->rhs));
}

void Sema::checkBinaryRelation(BinaryExpr *binExpr) {
  Type *lhsType = binExpr->lhs ? binExpr->lhs->getType() : nullptr;
  Type *rhsType = binExpr->rhs ? binExpr->rhs->getType() : nullptr;
  if (!isScalarType(lhsType) || !isScalarType(rhsType)) {
    SVM_ERROR(diagEngine_, binExpr->getLocation(),
              "Relation operator '%s' requires scalar operands.",
              binExpr->toString());
    binExpr->setType(typeCtx_.getIntType());
    return;
  }
  ArithConvert(binExpr->lhs, binExpr->rhs);
  binExpr->setType(typeCtx_.getIntType());
}

void Sema::checkBinaryEq(BinaryExpr *binExpr) {
  Type *lhsType = binExpr->lhs ? binExpr->lhs->getType() : nullptr;
  Type *rhsType = binExpr->rhs ? binExpr->rhs->getType() : nullptr;
  if (!isScalarType(lhsType) || !isScalarType(rhsType)) {
    SVM_ERROR(diagEngine_, binExpr->getLocation(),
              "Equality operator '%s' requires scalar operands.",
              binExpr->toString());
    binExpr->setType(typeCtx_.getIntType());
    return;
  }
  ArithConvert(binExpr->lhs, binExpr->rhs);
  binExpr->setType(typeCtx_.getIntType());
}

void Sema::checkBinaryLogic(BinaryExpr *binExpr) {
  binExpr->lhs = toIntCond(binExpr->lhs);
  binExpr->rhs = toIntCond(binExpr->rhs);
  binExpr->setType(typeCtx_.getIntType());
}

// 强制转换
Type *Sema::ArithConvert(ExprNode *&lhs, ExprNode *&rhs) {
  Type *lhsType = lhs ? lhs->getType() : nullptr;
  Type *rhsType = rhs ? rhs->getType() : nullptr;
  if (isa<FloatType>(lhsType) || isa<FloatType>(rhsType)) {
    lhs = coerceTo(lhs, typeCtx_.getFloatType());
    rhs = coerceTo(rhs, typeCtx_.getFloatType());
    return typeCtx_.getFloatType();
  }
  return typeCtx_.getIntType();
}

ExprNode *Sema::coerceTo(ExprNode *expr, Type *target) {
  if (!expr || !target)
    return expr;
  Type *src = expr->getType();
  if (src == target)
    return expr;
  if (isa<IntType>(src) && isa<FloatType>(target))
    return makeCast(expr, ImplicitCastExpr::CastKind::IntToFloat);
  if (isa<FloatType>(src) && isa<IntType>(target))
    return makeCast(expr, ImplicitCastExpr::CastKind::FloatToInt);
  if (!isScalarType(src) || !isScalarType(target))
    SVM_ERROR(diagEngine_, expr->getLocation(), "Cannot convert %s to %s.",
              src ? getString(src->getKind()) : "<unknown>",
              getString(target->getKind()));
  return expr;
}

ExprNode *Sema::toIntCond(ExprNode *expr) {
  if (!expr)
    return nullptr;
  Type *type = expr->getType();
  if (isa<IntType>(type))
    return expr;
  if (isa<FloatType>(type)) {
    auto *zero = arena_.create<FloatLiteralExpr>(expr->getLocation(), 0.0f);
    zero->setType(typeCtx_.getFloatType());
    auto *cmp = arena_.create<BinaryExpr>(
        expr->getLocation(), BinaryExpr::BinaryOp::NotEq, expr, zero);
    cmp->setType(typeCtx_.getIntType());
    return cmp;
  }
  SVM_ERROR(diagEngine_, expr->getLocation(), "Condition must be a scalar.");
  expr->setType(typeCtx_.getIntType());
  return expr;
}

ExprNode *Sema::makeCast(ExprNode *src, ImplicitCastExpr::CastKind castKind) {
  if (!src)
    return nullptr;
  auto *castExpr =
      arena_.create<ImplicitCastExpr>(src->getLocation(), castKind, src);
  castExpr->setType(castKind == ImplicitCastExpr::CastKind::IntToFloat
                        ? static_cast<Type *>(typeCtx_.getFloatType())
                        : static_cast<Type *>(typeCtx_.getIntType()));
  return castExpr;
}

// 求值
bool Sema::eval(ExprNode *expr, ConstValue &out) {
  if (!expr)
    return false;

  switch (expr->getKind()) {
  case ASTKind::IntegerLiteralExpr:
    out = ConstValue(cast<IntLiteralExpr>(expr)->value);
    return true;
  case ASTKind::FloatLiteralExpr:
    out = ConstValue(cast<FloatLiteralExpr>(expr)->value);
    return true;
  case ASTKind::ImplicitCastExpr: {
    auto *castExpr = cast<ImplicitCastExpr>(expr);
    ConstValue src;
    if (!eval(castExpr->operand, src))
      return false;
    out = castExpr->kind == ImplicitCastExpr::CastKind::IntToFloat
              ? ConstValue(src.asFloat())
              : ConstValue(src.asInt());
    return true;
  }
  case ASTKind::UnaryExpr: {
    auto *unaryExpr = cast<UnaryExpr>(expr);
    ConstValue operand;
    if (!eval(unaryExpr->operand, operand))
      return false;
    switch (unaryExpr->op) {
    case UnaryExpr::UnaryOp::Plus:
      out = operand;
      return true;
    case UnaryExpr::UnaryOp::Minus:
      out = operand.isInt() ? ConstValue(-operand.intValue)
                            : ConstValue(-operand.floatValue);
      return true;
    case UnaryExpr::UnaryOp::LogicNot: {
      bool zero =
          operand.isInt() ? operand.intValue == 0 : operand.floatValue == 0.0f;
      out = ConstValue(static_cast<i32>(zero));
      return true;
    }
    }
    return false;
  }
  case ASTKind::BinaryExpr: {
    auto *binExpr = cast<BinaryExpr>(expr);
    if (binExpr->op == BinaryExpr::BinaryOp::LogicAnd ||
        binExpr->op == BinaryExpr::BinaryOp::LogicOr) {
      ConstValue lhs;
      if (!eval(binExpr->lhs, lhs))
        return false;
      bool lhsZero = lhs.isInt() ? lhs.intValue == 0 : lhs.floatValue == 0.0f;
      if (binExpr->op == BinaryExpr::BinaryOp::LogicAnd && lhsZero) {
        out = ConstValue(0);
        return true;
      }
      if (binExpr->op == BinaryExpr::BinaryOp::LogicOr && !lhsZero) {
        out = ConstValue(1);
        return true;
      }
      ConstValue rhs;
      if (!eval(binExpr->rhs, rhs))
        return false;
      bool rhsZero = rhs.isInt() ? rhs.intValue == 0 : rhs.floatValue == 0.0f;
      out = ConstValue(static_cast<i32>(
          binExpr->op == BinaryExpr::BinaryOp::LogicAnd ? !rhsZero : !rhsZero));
      return true;
    }

    ConstValue lhs, rhs;
    if (!eval(binExpr->lhs, lhs) || !eval(binExpr->rhs, rhs))
      return false;

    bool isFloat = lhs.isFloat() || rhs.isFloat();
    f32 lf = lhs.asFloat(), rf = rhs.asFloat();
    i32 li = lhs.asInt(), ri = rhs.asInt();
    switch (binExpr->op) {
    case BinaryExpr::BinaryOp::Add:
      out = isFloat ? ConstValue(lf + rf) : ConstValue(li + ri);
      return true;
    case BinaryExpr::BinaryOp::Sub:
      out = isFloat ? ConstValue(lf - rf) : ConstValue(li - ri);
      return true;
    case BinaryExpr::BinaryOp::Mul:
      out = isFloat ? ConstValue(lf * rf) : ConstValue(li * ri);
      return true;
    case BinaryExpr::BinaryOp::Div:
      if (!isFloat && ri == 0) {
        SVM_ERROR(diagEngine_, binExpr->getLocation(),
                  "Division by zero in constant expression.");
        return false;
      }
      out = isFloat ? ConstValue(lf / rf) : ConstValue(li / ri);
      return true;
    case BinaryExpr::BinaryOp::Mod:
      if (ri == 0) {
        SVM_ERROR(diagEngine_, binExpr->getLocation(),
                  "Modulo by zero in constant expression.");
        return false;
      }
      out = ConstValue(li % ri);
      return true;
    case BinaryExpr::BinaryOp::Less:
      out = ConstValue(static_cast<i32>(isFloat ? lf < rf : li < ri));
      return true;
    case BinaryExpr::BinaryOp::LessEq:
      out = ConstValue(static_cast<i32>(isFloat ? lf <= rf : li <= ri));
      return true;
    case BinaryExpr::BinaryOp::Greater:
      out = ConstValue(static_cast<i32>(isFloat ? lf > rf : li > ri));
      return true;
    case BinaryExpr::BinaryOp::GreaterEq:
      out = ConstValue(static_cast<i32>(isFloat ? lf >= rf : li >= ri));
      return true;
    case BinaryExpr::BinaryOp::Eq:
      out = ConstValue(static_cast<i32>(isFloat ? lf == rf : li == ri));
      return true;
    case BinaryExpr::BinaryOp::NotEq:
      out = ConstValue(static_cast<i32>(isFloat ? lf != rf : li != ri));
      return true;
    case BinaryExpr::BinaryOp::LogicAnd:
    case BinaryExpr::BinaryOp::LogicOr:
      return false;
    }
    return false;
  }
  case ASTKind::LValueExpr: {
    auto *lval = cast<LValueExpr>(expr);
    auto *constDecl = dyn_cast<ConstDecl>(lval->resolved);
    if (!constDecl || constDecl->initSegmentCount == 0)
      return false;

    if (lval->subscriptCount == 0) {
      if (constDecl->dimensionCount > 0)
        return false;
      auto &seg = constDecl->initSegments[0];
      if (!seg.initExprs) {
        out = ConstValue(0);
        return true;
      }
      return eval(seg.initExprs[0], out);
    }

    if (!constDecl->isArray() ||
        lval->subscriptCount != constDecl->dimensionCount)
      return false;
    auto *arrayType = dyn_cast<ArrayType>(constDecl->type);
    if (!arrayType)
      return false;

    i32 offset = 0;
    for (u32 i = 0; i < lval->subscriptCount; ++i) {
      ConstValue idxValue;
      if (!eval(lval->subscripts[i], idxValue))
        return false;
      i32 idx = idxValue.asInt();
      if (idx < 0 || idx >= arrayType->dims[i]) {
        SVM_ERROR(diagEngine_, lval->subscripts[i]->getLocation(),
                  "Array index %d out of bounds.", idx);
        return false;
      }
      offset = offset * arrayType->dims[i] + idx;
    }

    u32 pos = 0;
    for (u32 i = 0; i < constDecl->initSegmentCount; ++i) {
      auto &seg = constDecl->initSegments[i];
      if (static_cast<u32>(offset) < pos + seg.initCount) {
        if (!seg.initExprs) {
          out = ConstValue(0);
          return true;
        }
        return eval(seg.initExprs[offset - pos], out);
      }
      pos += seg.initCount;
    }
    return false;
  }
  case ASTKind::CallExpr:
  default:
    return false;
  }
}

ExprNode *Sema::makeLiteralFromConst(SourceLocation loc, Type *scalarType,
                                     const ConstValue &value) {
  if (isa<FloatType>(scalarType)) {
    auto *literal = arena_.create<FloatLiteralExpr>(loc, value.asFloat());
    literal->setType(typeCtx_.getFloatType());
    return literal;
  }
  auto *literal = arena_.create<IntLiteralExpr>(loc, value.asInt());
  literal->setType(typeCtx_.getIntType());
  return literal;
}

// 作用域管理
bool Sema::declareGlobal(const char *name, ASTNode *node) {
  std::string key(name ? name : "");
  auto it = globals_.find(key);
  if (it != globals_.end()) {
    if (it->second == node)
      return true;
    SVM_ERROR(diagEngine_, node ? node->getLocation() : nowhereLoc,
              "Redefinition of '%s' at file scope.", key.c_str());
    return false;
  }
  globals_.emplace(std::move(key), node);
  return true;
}

bool Sema::declare(const char *name, ASTNode *node) {
  if (scopes_.empty())
    return declareGlobal(name, node);
  std::string key(name ? name : "");
  auto &scope = scopes_.back();
  auto it = scope.find(key);
  if (it != scope.end()) {
    SVM_ERROR(diagEngine_, node ? node->getLocation() : nowhereLoc,
              "Redefinition of '%s' in this scope.", key.c_str());
    return false;
  }
  scope.emplace(std::move(key), node);
  return true;
}

ASTNode *Sema::lookupValue(const char *name) {
  std::string key(name ? name : "");
  for (auto it = scopes_.rbegin(); it != scopes_.rend(); ++it) {
    auto sym = it->find(key);
    if (sym != it->end())
      return sym->second;
  }
  auto global = globals_.find(key);
  if (global == globals_.end() || isa<FuncDecl>(global->second))
    return nullptr;
  return global->second;
}

FuncDecl *Sema::lookupFunc(const char *name) {
  auto it = functions_.find(name ? name : "");
  return it == functions_.end() ? nullptr : it->second;
}
} // namespace svm
