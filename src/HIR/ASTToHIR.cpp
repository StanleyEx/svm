#include "ASTToHIR.h"

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <limits>
#include <vector>

namespace svm::ir {
namespace {

void appendInitSegment(std::vector<InitSegment> &segments, u64 count,
                       ExprNode **expressions) {
  if (count == 0)
    return;
  if (!expressions && !segments.empty() && !segments.back().initExprs) {
    segments.back().initCount += count;
    return;
  }
  segments.push_back(InitSegment{count, expressions});
}

// 保持源码初始化顺序 仅在逻辑下标映射不连续处插入压缩零段
bool remapArrayInitializer(const ArrayType *array, InitSegment *sourceSegments,
                           u32 sourceSegmentCount,
                           std::vector<InitSegment> &result) {
  const u64 logicalSize = array->logicalSize();
  const u64 physicalSize = array->totalSize();
  if (physicalSize < logicalSize)
    return false;

  u64 logicalOffset = 0;
  u64 physicalOffset = 0;
  for (u32 segmentIndex = 0; segmentIndex < sourceSegmentCount;
       ++segmentIndex) {
    InitSegment &source = sourceSegments[segmentIndex];
    if (source.initCount > logicalSize - logicalOffset)
      return false;

    if (!source.initExprs) {
      logicalOffset += source.initCount;
      const u64 nextPhysical = logicalOffset == logicalSize
                                   ? physicalSize
                                   : array->physicalOffset(logicalOffset);
      if (nextPhysical < physicalOffset)
        return false;
      appendInitSegment(result, nextPhysical - physicalOffset, nullptr);
      physicalOffset = nextPhysical;
      continue;
    }

    u64 consumed = 0;
    while (consumed < source.initCount) {
      const u64 target = array->physicalOffset(logicalOffset);
      if (target < physicalOffset)
        return false;
      appendInitSegment(result, target - physicalOffset, nullptr);

      u64 run = 1;
      while (consumed + run < source.initCount &&
             array->physicalOffset(logicalOffset + run) == target + run)
        ++run;
      appendInitSegment(result, run, source.initExprs + consumed);
      consumed += run;
      logicalOffset += run;
      physicalOffset = target + run;
    }
  }

  if (physicalOffset > physicalSize)
    return false;
  appendInitSegment(result, physicalSize - physicalOffset, nullptr);
  return result.size() <= std::numeric_limits<u32>::max();
}

// ARRAYIDX降级使用i32字节步长 仅零下标可安全跳过超大步长
bool arrayIndexStridesFitI32(Inst *const *indices, u32 indexCount,
                             IRType elementType, const u32 *dimensions,
                             u32 rank) noexcept {
  for (u32 index = 0; index < indexCount; ++index) {
    u64 stride = static_cast<u64>(typeSizeBytes(elementType));
    const u32 firstDimension = index == 0 ? 0 : index;
    for (u32 dimension = firstDimension; dimension < rank; ++dimension) {
      u64 product = 0;
      if (!checkedMul(stride, static_cast<u64>(dimensions[dimension]), product))
        return false;
      stride = product;
    }
    Inst *subscript = indices[index];
    const bool constantZero = subscript->getOp() == OP_ICONST &&
                              !subscript->isUndefValue() &&
                              subscript->getImm() == 0;
    if (!constantZero &&
        stride > static_cast<u64>(std::numeric_limits<i32>::max()))
      return false;
  }
  return true;
}

} // namespace

ASTToHIR::ASTToHIR(Arena &arena, DiagnosticEngine &diagnostics) noexcept
    : arena_(arena), diagnostics_(diagnostics) {}

Module *ASTToHIR::run(CompUnit *unit) {
  if (!unit) {
    diagnose({}, "cannot lower a null compilation unit");
    return nullptr;
  }
  module_ = Module::create(arena_);
  module_->diagnostics = &diagnostics_;
  const std::string_view source = diagnostics_.getSource();
  module_->sourceText =
      source.empty() ? arena_.duplicateString("", 0)
                     : arena_.duplicateString(source.data(), source.size());
  module_->sourceLength = source.size();
  locations_.clear();
  canonicalFunctions_.clear();
  nextStringId_ = 0;
  // 先建立全局对象和函数符号 再补齐运行时依赖 最后降低函数体
  // 这样调用和全局地址在生成指令前均已有稳定的Module映射
  registerGlobals(unit);
  registerFunctions(unit);
  registerRuntimeCallees(unit);
  lowerFunctionBodies(unit);
  return module_;
}

void ASTToHIR::registerGlobals(CompUnit *unit) {
  for (u32 index = 0; index < unit->declCount; ++index) {
    DeclNode *declaration = unit->decls[index];
    Type *type = declarationType(declaration);
    if (!type)
      continue;

    const char *name = nullptr;
    bool isConst = false;
    bool isMutated = true;
    InitSegment *segments = nullptr;
    u32 segmentCount = 0;
    if (auto *variable = dyn_cast<VarDecl>(declaration)) {
      if (!variable->isGlobal)
        continue;
      name = variable->name;
      isMutated = variable->isMutated;
      segments = variable->initSegments;
      segmentCount = variable->initSegmentCount;
    } else if (auto *constant = dyn_cast<ConstDecl>(declaration)) {
      if (!constant->isGlobal)
        continue;
      name = constant->name;
      isConst = true;
      segments = constant->initSegments;
      segmentCount = constant->initSegmentCount;
    } else {
      continue;
    }
    if (!name || !*name) {
      diagnose(declaration->getLocation(), "global has no name");
      continue;
    }

    auto *array = dyn_cast<ArrayType>(type);
    Type *element = array ? array->elementType : type;
    const IRType elementType = scalarType(element);
    if (elementType != TY_I32 && elementType != TY_F32) {
      diagnose(declaration->getLocation(), "global has an unsupported type");
      continue;
    }
    const u64 wideCount = array ? array->totalSize() : 1;
    const u64 wideBytes =
        wideCount * static_cast<u64>(typeSizeBytes(elementType));
    if (wideCount > std::numeric_limits<u32>::max() ||
        wideBytes > std::numeric_limits<u32>::max()) {
      diagnose(declaration->getLocation(), "global object is too large");
      continue;
    }
    Global packed;
    packed.type = elementType;
    packed.numElements = static_cast<u32>(wideCount);
    if (!packGlobalInit(segments, segmentCount, array, &packed,
                        declaration->getLocation()))
      continue;
    Global *global = module_->newGlobal(
        arena_.duplicateString(name), elementType, static_cast<u32>(wideBytes),
        static_cast<u32>(wideCount), isConst || !isMutated, array != nullptr);
    global->initSegment = packed.initSegment;
    global->initSegmentCount = packed.initSegmentCount;
    module_->declToGlobal.emplace(declaration, global);
  }
}

void ASTToHIR::registerFunctions(CompUnit *unit) {
  for (u32 index = 0; index < unit->declCount; ++index) {
    auto *function = dyn_cast<FuncDecl>(unit->decls[index]);
    if (function && function->body)
      registerFunction(function);
  }
  for (u32 index = 0; index < unit->declCount; ++index) {
    auto *function = dyn_cast<FuncDecl>(unit->decls[index]);
    if (function && !function->body)
      registerFunction(function);
  }
}

Function *ASTToHIR::registerFunction(FuncDecl *declaration) {
  if (!declaration)
    return nullptr;
  auto registered = module_->declToFunction.find(declaration);
  if (registered != module_->declToFunction.end())
    return registered->second;
  if (!hasValidSignature(declaration))
    return nullptr;
  const std::string name = declaration->name ? declaration->name : "";
  if (name.empty()) {
    diagnose(declaration->getLocation(), "function has no name");
    return nullptr;
  }
  auto canonical = canonicalFunctions_.find(name);
  if (canonical != canonicalFunctions_.end()) {
    if (canonical->second->body && declaration->body) {
      diagnose(declaration->getLocation(), "function has multiple definitions");
      return nullptr;
    }
    if (!signaturesMatch(canonical->second, declaration)) {
      diagnose(declaration->getLocation(),
               "function redeclaration has an incompatible signature");
      return nullptr;
    }
    Function *function = module_->declToFunction.at(canonical->second);
    module_->declToFunction.emplace(declaration, function);
    return function;
  }
  std::vector<IRType> parameters(declaration->paramCount);
  for (u32 index = 0; index < declaration->paramCount; ++index) {
    FuncParam *parameter = declaration->params[index];
    parameters[index] =
        parameter && parameter->isArray
            ? TY_PTR
            : baseType(parameter ? parameter->baseType : TypeKind::Int);
  }
  Function *function = module_->newFunction(
      arena_.duplicateString(declaration->name),
      baseType(declaration->returnType), parameters.data(),
      declaration->paramCount, declaration->type,
      declaration->isRuntime || declaration->body == nullptr);
  module_->declToFunction.emplace(declaration, function);
  canonicalFunctions_.emplace(name, declaration);
  return function;
}

void ASTToHIR::registerRuntimeCallees(CompUnit *unit) {
  for (u32 index = 0; index < unit->declCount; ++index) {
    if (auto *function = dyn_cast<FuncDecl>(unit->decls[index]))
      visitRuntimeStmt(function->body);
  }
}

void ASTToHIR::visitRuntimeExpr(ExprNode *expr) {
  if (!expr)
    return;
  if (auto *call = dyn_cast<CallExpr>(expr)) {
    if (call->resolvedFunc && call->resolvedFunc->isRuntime &&
        !module_->declToFunction.count(call->resolvedFunc))
      registerFunction(call->resolvedFunc);
    for (u32 index = 0; index < call->argCount; ++index)
      visitRuntimeExpr(call->args[index]);
  } else if (auto *unary = dyn_cast<UnaryExpr>(expr)) {
    visitRuntimeExpr(unary->operand);
  } else if (auto *binary = dyn_cast<BinaryExpr>(expr)) {
    visitRuntimeExpr(binary->lhs);
    visitRuntimeExpr(binary->rhs);
  } else if (auto *conversion = dyn_cast<ImplicitCastExpr>(expr)) {
    visitRuntimeExpr(conversion->operand);
  } else if (auto *lvalue = dyn_cast<LValueExpr>(expr)) {
    for (u32 index = 0; index < lvalue->subscriptCount; ++index)
      visitRuntimeExpr(lvalue->subscripts[index]);
  }
}

void ASTToHIR::visitRuntimeInit(InitNode *init) {
  if (auto *expression = dyn_cast<InitExpr>(init)) {
    visitRuntimeExpr(expression->expr);
  } else if (auto *list = dyn_cast<InitList>(init)) {
    for (u32 index = 0; index < list->initCount; ++index)
      visitRuntimeInit(list->inits[index]);
  }
}

void ASTToHIR::visitRuntimeStmt(StmtNode *stmt) {
  if (!stmt)
    return;
  if (auto *block = dyn_cast<BlockStmt>(stmt)) {
    for (u32 index = 0; index < block->stmtCount; ++index)
      visitRuntimeStmt(block->stmts[index]);
  } else if (auto *expression = dyn_cast<ExprStmt>(stmt)) {
    visitRuntimeExpr(expression->expr);
  } else if (auto *assignment = dyn_cast<AssignStmt>(stmt)) {
    visitRuntimeExpr(assignment->lhs);
    visitRuntimeExpr(assignment->rhs);
  } else if (auto *conditional = dyn_cast<IfStmt>(stmt)) {
    visitRuntimeExpr(conditional->cond);
    visitRuntimeStmt(conditional->thenStmt);
    visitRuntimeStmt(conditional->elseStmt);
  } else if (auto *loop = dyn_cast<WhileStmt>(stmt)) {
    visitRuntimeExpr(loop->cond);
    visitRuntimeStmt(loop->body);
  } else if (auto *result = dyn_cast<ReturnStmt>(stmt)) {
    visitRuntimeExpr(result->expr);
  } else if (auto *declaration = dyn_cast<DeclStmt>(stmt)) {
    if (auto *variable = dyn_cast<VarDecl>(declaration->decl))
      visitRuntimeInit(variable->init);
    else if (auto *constant = dyn_cast<ConstDecl>(declaration->decl))
      visitRuntimeInit(constant->init);
  }
}

void ASTToHIR::lowerFunctionBodies(CompUnit *unit) {
  for (u32 index = 0; index < unit->declCount; ++index) {
    auto *declaration = dyn_cast<FuncDecl>(unit->decls[index]);
    if (!declaration || !declaration->body || declaration->isRuntime)
      continue;
    auto found = module_->declToFunction.find(declaration);
    if (found == module_->declToFunction.end()) {
      diagnose(declaration->getLocation(),
               "function symbol was not registered");
      continue;
    }
    lowerFunction(declaration, found->second);
  }
}

void ASTToHIR::lowerFunction(FuncDecl *declaration, Function *function) {
  locals_.clear();
  IRBuilder builder(module_, function);
  builder_ = &builder;
  BasicBlock *entry = builder.newBlockAtEnd(function->region);
  builder.setInsertAtEnd(entry);

  for (u32 index = 0; index < declaration->paramCount; ++index) {
    FuncParam *parameter = declaration->params[index];
    if (!parameter)
      continue;
    setSourceLocation(parameter);
    if (parameter->isArray) {
      locals_.emplace(parameter, function->params[index]);
    } else {
      // 标量参数需要映射到函数内存槽, 使后续读写与普通局部变量共享严格的
      // 地址降低路径. 参数值只在入口处写入一次, locals_ 始终保存其地址.
      const IRType type = baseType(parameter->baseType);
      Inst *storage = builder.emitAllocaParam(typeSizeBytes(type), type,
                                              static_cast<i16>(index));
      builder.emitStore(storage, function->params[index], type);
      locals_.emplace(parameter, storage);
    }
  }
  lowerStmt(declaration->body);
  BasicBlock *tail = function->region->last;
  if (tail && !tail->endsWithTerminator()) {
    builder.setInsertAtEnd(tail);
    setSourceLocation(declaration);
    builder.emitReturn(function->returnType == TY_VOID
                           ? nullptr
                           : builder.makeUndef(function->returnType));
  }
  builder_ = nullptr;
  locals_.clear();
}

void ASTToHIR::lowerStmt(StmtNode *stmt) {
  if (!stmt || !builder_->insertBlock() ||
      builder_->insertBlock()->endsWithTerminator())
    return;
  if (auto *block = dyn_cast<BlockStmt>(stmt)) {
    for (u32 index = 0; index < block->stmtCount; ++index) {
      lowerStmt(block->stmts[index]);
      if (builder_->insertBlock()->endsWithTerminator())
        break;
    }
  } else if (auto *declaration = dyn_cast<DeclStmt>(stmt)) {
    lowerLocal(declaration->decl);
  } else if (auto *assignment = dyn_cast<AssignStmt>(stmt)) {
    auto *left = dyn_cast<LValueExpr>(assignment->lhs);
    if (!left) {
      diagnose(assignment->getLocation(), "assignment target is not an lvalue");
      return;
    }
    Inst *address = lowerAddress(left);
    Inst *value = lowerExpr(assignment->rhs);
    if (!address || !value)
      return;
    const IRType type = scalarType(left->getType());
    if (type != TY_I32 && type != TY_F32) {
      diagnose(left->getLocation(), "assignment target has no scalar type");
      return;
    }
    value = builder_->castTo(value, type);
    setSourceLocation(assignment);
    builder_->emitStore(address, value, type);
  } else if (auto *expression = dyn_cast<ExprStmt>(stmt)) {
    UNUSED(lowerExpr(expression->expr));
  } else if (auto *result = dyn_cast<ReturnStmt>(stmt)) {
    Inst *value = result->expr ? lowerExpr(result->expr) : nullptr;
    const IRType returnType = builder_->function()->returnType;
    if (returnType == TY_VOID && result->expr) {
      diagnose(result->getLocation(), "void function cannot return a value");
      value = nullptr;
    } else if (returnType != TY_VOID && !result->expr) {
      diagnose(result->getLocation(), "non-void function must return a value");
      value = builder_->makeUndef(returnType);
    } else if (value) {
      value = builder_->castTo(value, returnType);
    } else if (returnType != TY_VOID) {
      value = builder_->makeUndef(returnType);
    }
    setSourceLocation(result);
    builder_->emitReturn(value);
  } else if (isa<BreakStmt>(stmt)) {
    setSourceLocation(stmt);
    builder_->emitBreak();
  } else if (isa<ContinueStmt>(stmt)) {
    setSourceLocation(stmt);
    builder_->emitContinue();
  } else if (auto *conditional = dyn_cast<IfStmt>(stmt)) {
    Inst *condition = lowerCondition(conditional->cond);
    if (!condition)
      return;
    BasicBlock *outer = builder_->insertBlock();
    Region *parent = outer->parentRegion;
    setSourceLocation(conditional);
    Inst *ifInst = builder_->emitIf(condition, nullptr, nullptr);
    Region *thenRegion = builder_->newRegion(ifInst, parent);
    Region *elseRegion =
        conditional->elseStmt ? builder_->newRegion(ifInst, parent) : nullptr;
    ifInst->getScf().r[0] = thenRegion;
    ifInst->getScf().r[1] = elseRegion;

    BasicBlock *thenBlock = builder_->newBlockAtEnd(thenRegion);
    builder_->setInsertAtEnd(thenBlock);
    lowerStmt(conditional->thenStmt);
    if (!builder_->insertBlock()->endsWithTerminator())
      builder_->emitYield();
    if (elseRegion) {
      BasicBlock *elseBlock = builder_->newBlockAtEnd(elseRegion);
      builder_->setInsertAtEnd(elseBlock);
      lowerStmt(conditional->elseStmt);
      if (!builder_->insertBlock()->endsWithTerminator())
        builder_->emitYield();
    }
    builder_->setInsertAfter(ifInst);
  } else if (auto *loop = dyn_cast<WhileStmt>(stmt)) {
    BasicBlock *outer = builder_->insertBlock();
    Region *parent = outer->parentRegion;
    setSourceLocation(loop);
    Inst *whileInst = builder_->emitWhile(nullptr, nullptr);
    Region *conditionRegion = builder_->newRegion(whileInst, parent);
    Region *bodyRegion = builder_->newRegion(whileInst, parent);
    whileInst->getScf().r[0] = conditionRegion;
    whileInst->getScf().r[1] = bodyRegion;

    BasicBlock *conditionBlock = builder_->newBlockAtEnd(conditionRegion);
    builder_->setInsertAtEnd(conditionBlock);
    Inst *condition = lowerCondition(loop->cond);
    builder_->emitYield(condition ? condition : builder_->i1Const(false));
    BasicBlock *bodyBlock = builder_->newBlockAtEnd(bodyRegion);
    builder_->setInsertAtEnd(bodyBlock);
    lowerStmt(loop->body);
    if (!builder_->insertBlock()->endsWithTerminator())
      builder_->emitYield();
    builder_->setInsertAfter(whileInst);
  } else if (!isa<EmptyStmt>(stmt)) {
    diagnose(stmt->getLocation(), "unsupported statement during HIR lowering");
  }
}

void ASTToHIR::lowerLocal(DeclNode *declaration) {
  if (auto *variable = dyn_cast<VarDecl>(declaration)) {
    Inst *storage =
        lowerLocalStorage(variable, variable->type, variable->baseType,
                          variable->initSegments, variable->initSegmentCount);
    if (storage)
      locals_.emplace(variable, storage);
  } else if (auto *constant = dyn_cast<ConstDecl>(declaration)) {
    Inst *storage =
        lowerLocalStorage(constant, constant->type, constant->baseType,
                          constant->initSegments, constant->initSegmentCount);
    if (storage)
      locals_.emplace(constant, storage);
  } else if (declaration) {
    diagnose(declaration->getLocation(), "unsupported local declaration");
  }
}

Inst *ASTToHIR::lowerLocalStorage(const ASTNode *declaration, Type *type,
                                  TypeKind sourceBaseType,
                                  InitSegment *segments, u32 segmentCount) {
  if (!type) {
    diagnose(declaration->getLocation(), "local declaration has no type");
    return nullptr;
  }
  const IRType elementType = baseType(sourceBaseType);
  if (elementType != TY_I32 && elementType != TY_F32) {
    diagnose(declaration->getLocation(),
             "local has an unsupported element type");
    return nullptr;
  }
  auto *array = dyn_cast<ArrayType>(type);
  const u64 wideCount = array ? array->totalSize() : 1;
  const u64 wideBytes =
      wideCount * static_cast<u64>(typeSizeBytes(elementType));
  if (wideCount == 0 ||
      wideCount > static_cast<u64>(std::numeric_limits<i32>::max()) ||
      wideBytes > static_cast<u64>(std::numeric_limits<i32>::max())) {
    diagnose(declaration->getLocation(), "local object has an invalid size");
    return nullptr;
  }
  setSourceLocation(declaration);
  Inst *storage =
      builder_->emitAlloca(static_cast<u32>(wideBytes), elementType);
  if (segmentCount == 0)
    return storage;

  if (!segments) {
    diagnose(declaration->getLocation(), "initializer segments are missing");
    return storage;
  }

  if (!array) {
    if (segmentCount != 1 || segments[0].initCount != 1) {
      diagnose(declaration->getLocation(),
               "malformed scalar initializer layout");
      return storage;
    }
    Inst *value = nullptr;
    if (segments[0].initExprs && segments[0].initExprs[0])
      value = lowerExpr(segments[0].initExprs[0]);
    else
      value =
          elementType == TY_F32 ? builder_->fConst(0.0F) : builder_->iConst(0);
    if (value) {
      value = builder_->castTo(value, elementType);
      setSourceLocation(declaration);
      builder_->emitStore(storage, value, elementType);
    }
    return storage;
  }

  std::vector<InitSegment> physicalSegments;
  if (!remapArrayInitializer(array, segments, segmentCount, physicalSegments)) {
    diagnose(declaration->getLocation(), "malformed array initializer layout");
    return storage;
  }
  segments = physicalSegments.data();
  segmentCount = static_cast<u32>(physicalSegments.size());

  u64 validatedCount = 0;
  for (u32 segment = 0; segment < segmentCount; ++segment) {
    if (segments[segment].initCount >
            static_cast<u64>(std::numeric_limits<i32>::max()) ||
        validatedCount + segments[segment].initCount > wideCount) {
      diagnose(declaration->getLocation(),
               "local initializer exceeds object bounds");
      return storage;
    }
    validatedCount += segments[segment].initCount;
  }

  const bool needsTailZero = validatedCount < wideCount;
  const u32 resultSegmentCount = segmentCount + (needsTailZero ? 1U : 0U);
  LocalInitInfo *info = arena_.create<LocalInitInfo>();
  info->elementType = elementType;
  info->segments.reserve(resultSegmentCount);
  u64 baseOffset = 0;
  // 初始化锚点只描述物理区间和值 暂不展开为逐元素Store
  // 后续Pass可以优化为批量清零或常量物化等
  for (u32 segment = 0; segment < segmentCount; ++segment) {
    InitSegment &source = segments[segment];
    info->segments.emplace_back();
    LocalInitSegment &destination = info->segments.back();
    destination.count = static_cast<u32>(source.initCount);
    if (!source.initExprs) {
      Inst *args[] = {storage, builder_->iConst(static_cast<i32>(baseOffset)),
                      builder_->iConst(static_cast<i32>(source.initCount))};
      setSourceLocation(declaration);
      // 锚点表示从baseOffset开始的连续零区间
      destination.zeroAnchor =
          builder_->emitN(OP_LOCAL_INIT_ZERO, TY_VOID, args, 3);
    } else {
      destination.values.reserve(destination.count);
      for (u32 index = 0; index < destination.count; ++index) {
        ExprNode *expression = source.initExprs[index];
        Inst *value = expression ? lowerExpr(expression) : nullptr;
        if (!value)
          value = elementType == TY_F32 ? builder_->fConst(0.0F)
                                        : builder_->iConst(0);
        value = builder_->castTo(value, elementType);
        Inst *args[] = {storage,
                        builder_->iConst(static_cast<i32>(baseOffset + index)),
                        value};
        setSourceLocation(expression ? static_cast<ASTNode *>(expression)
                                     : declaration);
        // 锚点同时固定数组偏移和动态表达式的源码顺序
        destination.values.push_back(
            builder_->emitN(OP_LOCAL_INIT_VALUE, TY_VOID, args, 3));
      }
    }
    baseOffset += source.initCount;
  }
  if (needsTailZero) {
    info->segments.emplace_back();
    LocalInitSegment &tail = info->segments.back();
    tail.count = static_cast<u32>(wideCount - validatedCount);
    Inst *args[] = {storage, builder_->iConst(static_cast<i32>(baseOffset)),
                    builder_->iConst(static_cast<i32>(tail.count))};
    setSourceLocation(declaration);
    // 尾部仍用单个锚点表示 避免膨胀IR
    tail.zeroAnchor = builder_->emitN(OP_LOCAL_INIT_ZERO, TY_VOID, args, 3);
  }
  storage->getMem().initInfo = info;
  return storage;
}

Inst *ASTToHIR::lowerExpr(ExprNode *expr) {
  if (!expr) {
    diagnose({}, "cannot lower a null expression");
    return nullptr;
  }
  if (auto *integer = dyn_cast<IntLiteralExpr>(expr)) {
    setSourceLocation(expr);
    return builder_->iConst(integer->value);
  }
  if (auto *floating = dyn_cast<FloatLiteralExpr>(expr)) {
    setSourceLocation(expr);
    return builder_->fConst(floating->value);
  }
  if (isa<StringLiteralExpr>(expr)) {
    diagnose(expr->getLocation(),
             "string literal is only valid as putf format");
    return nullptr;
  }
  if (auto *lvalue = dyn_cast<LValueExpr>(expr)) {
    Inst *address = lowerAddress(lvalue);
    if (!address)
      return nullptr;
    Type *type = lvalue->getType();
    if (!type) {
      diagnose(lvalue->getLocation(), "lvalue has no semantic type");
      return nullptr;
    }
    if (isa<ArrayType>(type) || isa<PointerType>(type) ||
        isa<AnyDimArrayType>(type))
      return address;
    const IRType elementType = scalarType(type);
    setSourceLocation(lvalue);
    return builder_->emitLoad(address, elementType);
  }
  if (auto *call = dyn_cast<CallExpr>(expr))
    return lowerCall(call);
  if (auto *unary = dyn_cast<UnaryExpr>(expr)) {
    Inst *operand = lowerExpr(unary->operand);
    if (!operand)
      return nullptr;
    if (unary->op == UnaryExpr::UnaryOp::Plus)
      return operand;
    setSourceLocation(unary);
    if (unary->op == UnaryExpr::UnaryOp::LogicNot)
      return builder_->emit(OP_LNOT, TY_I1, builder_->toI1(operand));
    if (operand->getType() == TY_I1)
      operand = builder_->emit(OP_ZEXT, TY_I32, operand);
    return builder_->emit(operand->getType() == TY_F32 ? OP_FNEG : OP_NEG,
                          operand->getType(), operand);
  }
  if (auto *conversion = dyn_cast<ImplicitCastExpr>(expr)) {
    Inst *operand = lowerExpr(conversion->operand);
    if (!operand)
      return nullptr;
    setSourceLocation(conversion);
    const IRType target = scalarType(conversion->getType());
    if (target != TY_I32 && target != TY_F32 && target != TY_I1) {
      diagnose(conversion->getLocation(),
               "implicit conversion has no scalar target type");
      return nullptr;
    }
    return builder_->castTo(operand, target);
  }
  auto *binary = dyn_cast<BinaryExpr>(expr);
  if (!binary) {
    diagnose(expr->getLocation(), "unsupported expression during HIR lowering");
    return nullptr;
  }
  if (binary->op == BinaryExpr::BinaryOp::LogicAnd ||
      binary->op == BinaryExpr::BinaryOp::LogicOr)
    return lowerLogical(binary);
  Inst *left = lowerExpr(binary->lhs);
  Inst *right = lowerExpr(binary->rhs);
  if (!left || !right)
    return nullptr;
  IRBuilder::Coerced pair = builder_->coercePair(left, right);
  const bool floating = pair.type == TY_F32;
  OpCode op = OP_ADD;
  switch (binary->op) {
  case BinaryExpr::BinaryOp::Add:
    op = floating ? OP_FADD : OP_ADD;
    break;
  case BinaryExpr::BinaryOp::Sub:
    op = floating ? OP_FSUB : OP_SUB;
    break;
  case BinaryExpr::BinaryOp::Mul:
    op = floating ? OP_FMUL : OP_MUL;
    break;
  case BinaryExpr::BinaryOp::Div:
    op = floating ? OP_FDIV : OP_DIV;
    break;
  case BinaryExpr::BinaryOp::Mod:
    op = OP_MOD;
    break;
  case BinaryExpr::BinaryOp::Eq:
    op = floating ? OP_FEQ : OP_EQ;
    break;
  case BinaryExpr::BinaryOp::NotEq:
    op = floating ? OP_FNE : OP_NE;
    break;
  case BinaryExpr::BinaryOp::Less:
    op = floating ? OP_FLT : OP_LT;
    break;
  case BinaryExpr::BinaryOp::LessEq:
    op = floating ? OP_FLE : OP_LE;
    break;
  case BinaryExpr::BinaryOp::Greater:
    op = floating ? OP_FGT : OP_GT;
    break;
  case BinaryExpr::BinaryOp::GreaterEq:
    op = floating ? OP_FGE : OP_GE;
    break;
  default:
    diagnose(binary->getLocation(), "invalid non-logical binary operator");
    return nullptr;
  }
  if (op == OP_MOD && pair.type != TY_I32) {
    diagnose(binary->getLocation(), "floating-point remainder is unsupported");
    return nullptr;
  }
  setSourceLocation(binary);
  return builder_->emit(op, isCompare(op) ? TY_I1 : pair.type, pair.left,
                        pair.right);
}

Inst *ASTToHIR::lowerLogical(BinaryExpr *expr) {
  const bool isAnd = expr->op == BinaryExpr::BinaryOp::LogicAnd;
  setSourceLocation(expr);
  Inst *storage = builder_->emitAlloca(1, TY_I1);
  Inst *left = lowerCondition(expr->lhs);
  if (!left)
    return nullptr;
  BasicBlock *outer = builder_->insertBlock();
  Region *parent = outer->parentRegion;
  setSourceLocation(expr);
  Inst *ifInst = builder_->emitIf(left, nullptr, nullptr);
  Region *thenRegion = builder_->newRegion(ifInst, parent);
  Region *elseRegion = builder_->newRegion(ifInst, parent);
  ifInst->getScf().r[0] = thenRegion;
  ifInst->getScf().r[1] = elseRegion;

  BasicBlock *thenBlock = builder_->newBlockAtEnd(thenRegion);
  builder_->setInsertAtEnd(thenBlock);
  Inst *thenValue = isAnd ? lowerCondition(expr->rhs) : builder_->i1Const(true);
  builder_->emitStore(storage, thenValue ? thenValue : builder_->i1Const(false),
                      TY_I1);
  builder_->emitYield();

  BasicBlock *elseBlock = builder_->newBlockAtEnd(elseRegion);
  builder_->setInsertAtEnd(elseBlock);
  Inst *elseValue =
      isAnd ? builder_->i1Const(false) : lowerCondition(expr->rhs);
  builder_->emitStore(storage, elseValue ? elseValue : builder_->i1Const(false),
                      TY_I1);
  builder_->emitYield();

  builder_->setInsertAfter(ifInst);
  setSourceLocation(expr);
  return builder_->emitLoad(storage, TY_I1);
}

Inst *ASTToHIR::lowerCall(CallExpr *expr) {
  if (!expr->resolvedFunc) {
    diagnose(expr->getLocation(), "call has no resolved function");
    return nullptr;
  }
  auto found = module_->declToFunction.find(expr->resolvedFunc);
  if (found == module_->declToFunction.end()) {
    diagnose(expr->getLocation(), "callee was not registered before lowering");
    return nullptr;
  }
  Function *callee = found->second;
  FunctionType *functionType = callee->functionType;
  if (!functionType) {
    diagnose(expr->getLocation(), "callee has no function type");
    return nullptr;
  }
  if ((!functionType->isVariadic &&
       expr->argCount != functionType->paramCount) ||
      (functionType->isVariadic && expr->argCount < functionType->paramCount)) {
    diagnose(expr->getLocation(), "call argument count does not match callee");
    return nullptr;
  }
  if (functionType->isVariadic && expr->argCount == 0) {
    diagnose(expr->getLocation(),
             "variadic runtime call requires a format string");
    return nullptr;
  }
  std::vector<Inst *> arguments;
  arguments.reserve(expr->argCount);
  for (u32 index = 0; index < expr->argCount; ++index) {
    ExprNode *argument = expr->args[index];
    if (functionType->isVariadic && index == 0) {
      if (auto *literal = dyn_cast<StringLiteralExpr>(argument)) {
        Inst *address = materializeString(literal);
        if (!address)
          return nullptr;
        arguments.push_back(address);
        continue;
      }
      diagnose(argument ? argument->getLocation() : expr->getLocation(),
               "variadic runtime format must be a string literal");
      return nullptr;
    }
    Type *parameterType = index < functionType->paramCount
                              ? functionType->paramTypes[index]
                              : nullptr;
    if (parameterType && isa<PointerType>(parameterType)) {
      auto *lvalue = dyn_cast<LValueExpr>(argument);
      if (!lvalue) {
        diagnose(argument ? argument->getLocation() : expr->getLocation(),
                 "array argument is not an addressable lvalue");
        return nullptr;
      }
      Inst *address = lowerAddress(lvalue);
      if (!address)
        return nullptr;
      arguments.push_back(address);
    } else {
      Inst *value = lowerExpr(argument);
      if (!value)
        return nullptr;
      if (parameterType)
        value = builder_->castTo(value, scalarType(parameterType));
      else if (value->getType() == TY_I1)
        value = builder_->castTo(value, TY_I32);
      arguments.push_back(value);
    }
  }
  setSourceLocation(expr);
  return builder_->emitCall(callee, arguments.data(),
                            static_cast<u32>(arguments.size()),
                            callee->returnType);
}

Inst *ASTToHIR::materializeString(StringLiteralExpr *literal) {
  const usize length = literal->value.size();
  if (length >= std::numeric_limits<u32>::max()) {
    diagnose(literal->getLocation(), "string literal is too large");
    return nullptr;
  }
  char name[48];
  std::snprintf(name, sizeof(name), ".str.%u", nextStringId_++);
  const u32 count = static_cast<u32>(length + 1);
  Global *global = module_->newGlobal(arena_.duplicateString(name), TY_I32,
                                      count, count, true, true);
  global->origin = Global::GlobalOrigin::StringLiteral;
  global->initSegmentCount = 1;
  global->initSegment = arena_.createArray<GlobalInitSegment>(1);
  global->initSegment[0].count = count;
  i32 *data = arena_.createArray<i32>(count);
  for (u32 index = 0; index < count - 1; ++index)
    data[index] = static_cast<unsigned char>(literal->value[index]);
  data[count - 1] = 0;
  global->initSegment[0].data = data;
  setSourceLocation(literal);
  return builder_->getGlobalPtr(global);
}

Inst *ASTToHIR::lowerAddress(LValueExpr *expr) {
  if (!expr->resolved) {
    diagnose(expr->getLocation(), "lvalue has no resolved declaration");
    return nullptr;
  }
  Inst *base = materializeAddress(expr->resolved);
  if (!base || expr->subscriptCount == 0)
    return base;

  Type *declaredType = declarationType(expr->resolved);
  Type *element = scalarElementType(declaredType);
  const IRType elementType = scalarType(element);
  if (!declaredType || (elementType != TY_I32 && elementType != TY_F32)) {
    diagnose(expr->getLocation(),
             "subscripted object has no scalar element type");
    return nullptr;
  }
  const u32 count = expr->subscriptCount;
  auto lowerSubscript = [&](u32 index) -> Inst * {
    Inst *value = lowerExpr(expr->subscripts[index]);
    return value ? builder_->castTo(value, TY_I32) : nullptr;
  };

  auto *directArray = dyn_cast<ArrayType>(declaredType);
  auto *pointer = dyn_cast<PointerType>(declaredType);
  auto *pointerArray =
      pointer ? dyn_cast<ArrayType>(pointer->pointee) : nullptr;
  ArrayType *sourceShape = directArray ? directArray : pointerArray;
  if (sourceShape) {
    if (directArray) {
      if (count > sourceShape->dimCount) {
        diagnose(expr->getLocation(), "too many subscripts for array shape");
        return nullptr;
      }
      std::vector<Inst *> indices(count + 1);
      indices[0] = builder_->iConst(0);
      for (u32 index = 0; index < count; ++index) {
        indices[index + 1] = lowerSubscript(index);
        if (!indices[index + 1])
          return nullptr;
      }
      std::vector<u32> physicalDims(sourceShape->dimCount);
      for (u32 index = 0; index < sourceShape->dimCount; ++index)
        physicalDims[index] =
            static_cast<u32>(paddedArrayDim(sourceShape->dims[index]));
      if (!arrayIndexStridesFitI32(
              indices.data(), static_cast<u32>(indices.size()), elementType,
              physicalDims.data(), sourceShape->dimCount)) {
        diagnose(expr->getLocation(), "array index stride is too large");
        return nullptr;
      }
      setSourceLocation(expr);
      return builder_->emitArrayIndex(
          base, indices.data(), static_cast<u32>(indices.size()), elementType,
          physicalDims.data(), sourceShape->dimCount);
    }

    // SysY数组形参省略首维 先用尾部物理聚合大小完成首层指针步进
    if (count > sourceShape->dimCount + 1U) {
      diagnose(expr->getLocation(), "too many subscripts for array shape");
      return nullptr;
    }
    Inst *leadingIndex = lowerSubscript(0);
    if (!leadingIndex)
      return nullptr;
    setSourceLocation(expr);
    const bool zeroLeadingIndex = leadingIndex->getOp() == OP_ICONST &&
                                  !leadingIndex->isUndefValue() &&
                                  leadingIndex->getImm() == 0;
    Inst *tailBase = base;
    if (!zeroLeadingIndex) {
      u64 tailElements = 1;
      for (u32 dimension = 0; dimension < sourceShape->dimCount; ++dimension) {
        u64 product = 0;
        if (!checkedMul(
                tailElements,
                static_cast<u64>(paddedArrayDim(sourceShape->dims[dimension])),
                product)) {
          diagnose(expr->getLocation(), "array parameter shape is too large");
          return nullptr;
        }
        tailElements = product;
      }
      u64 strideBytes = 0;
      if (!checkedMul(tailElements,
                      static_cast<u64>(typeSizeBytes(elementType)),
                      strideBytes) ||
          strideBytes == 0 ||
          strideBytes > static_cast<u64>(std::numeric_limits<i32>::max())) {
        diagnose(expr->getLocation(), "array parameter stride is too large");
        return nullptr;
      }
      tailBase = builder_->emitGetPtr(base, leadingIndex,
                                      static_cast<i32>(strideBytes));
    }
    if (count == 1)
      return tailBase;

    std::vector<Inst *> indices(count);
    indices[0] = builder_->iConst(0);
    for (u32 index = 1; index < count; ++index) {
      indices[index] = lowerSubscript(index);
      if (!indices[index])
        return nullptr;
    }
    std::vector<u32> physicalDims(sourceShape->dimCount);
    for (u32 index = 0; index < sourceShape->dimCount; ++index)
      physicalDims[index] =
          static_cast<u32>(paddedArrayDim(sourceShape->dims[index]));
    if (!arrayIndexStridesFitI32(indices.data(),
                                 static_cast<u32>(indices.size()), elementType,
                                 physicalDims.data(), sourceShape->dimCount)) {
      diagnose(expr->getLocation(), "array index stride is too large");
      return nullptr;
    }
    return builder_->emitArrayIndex(tailBase, indices.data(), count,
                                    elementType, physicalDims.data(),
                                    sourceShape->dimCount);
  }

  if (!pointer || count != 1) {
    diagnose(expr->getLocation(), "subscripted pointer has no array shape");
    return nullptr;
  }
  Inst *index = lowerSubscript(0);
  if (!index)
    return nullptr;
  setSourceLocation(expr);
  return builder_->emitGetPtr(base, index, typeSizeBytes(elementType));
}

Inst *ASTToHIR::materializeAddress(const ASTNode *declaration) {
  auto local = locals_.find(declaration);
  if (local != locals_.end())
    return local->second;
  auto global = module_->declToGlobal.find(declaration);
  if (global != module_->declToGlobal.end())
    return builder_->getGlobalPtr(global->second);
  diagnose(declaration ? declaration->getLocation() : SourceLocation{},
           "declaration has no materialized storage");
  return nullptr;
}

Inst *ASTToHIR::lowerCondition(ExprNode *expr) {
  Inst *value = lowerExpr(expr);
  if (!value)
    return nullptr;
  setSourceLocation(expr);
  return builder_->toI1(value);
}

bool ASTToHIR::packGlobalInit(InitSegment *segments, u32 segmentCount,
                              const ArrayType *array, Global *global,
                              SourceLocation location) {
  if (!segmentCount) {
    global->initSegment = nullptr;
    global->initSegmentCount = 0;
    return true;
  }
  if (!segments) {
    diagnose(location, "global initializer segments are missing");
    return false;
  }

  std::vector<InitSegment> physicalSegments;
  if (array) {
    if (!remapArrayInitializer(array, segments, segmentCount,
                               physicalSegments)) {
      diagnose(location, "malformed array initializer layout");
      return false;
    }
    segments = physicalSegments.data();
    segmentCount = static_cast<u32>(physicalSegments.size());
  }

  struct PackedSegment {
    u32 count = 0;             // 段元素数
    std::vector<i32> integers; // 整数初始化值
    std::vector<f32> floating; // 浮点初始化值
    bool zero = false;         // 是否为全零段
  };
  std::vector<PackedSegment> packed(segmentCount);
  u64 total = 0;
  for (u32 segment = 0; segment < segmentCount; ++segment) {
    InitSegment &source = segments[segment];
    if (source.initCount > std::numeric_limits<u32>::max() ||
        total + source.initCount > global->numElements) {
      diagnose(location, "global initializer exceeds object bounds");
      return false;
    }
    PackedSegment &destination = packed[segment];
    destination.count = static_cast<u32>(source.initCount);
    total += source.initCount;
    if (!source.initExprs) {
      destination.zero = true;
      continue;
    }
    if (global->type == TY_F32) {
      destination.floating.resize(destination.count);
      for (u32 index = 0; index < destination.count; ++index) {
        i32 integer = 0;
        f32 floating = 0.0F;
        if (!extractConstantLiteral(source.initExprs[index], TY_F32, integer,
                                    floating)) {
          diagnose(source.initExprs[index]
                       ? source.initExprs[index]->getLocation()
                       : location,
                   "global initializer is not a representable constant");
          return false;
        }
        destination.floating[index] = floating;
      }
    } else {
      destination.integers.resize(destination.count);
      for (u32 index = 0; index < destination.count; ++index) {
        i32 integer = 0;
        f32 floating = 0.0F;
        if (!extractConstantLiteral(source.initExprs[index], TY_I32, integer,
                                    floating)) {
          diagnose(source.initExprs[index]
                       ? source.initExprs[index]->getLocation()
                       : location,
                   "global initializer is not a representable constant");
          return false;
        }
        destination.integers[index] = integer;
      }
    }
  }

  const bool needsTailZero = total < global->numElements;
  const u32 resultCount = segmentCount + (needsTailZero ? 1U : 0U);
  GlobalInitSegment *result =
      arena_.createArray<GlobalInitSegment>(resultCount);
  for (u32 segment = 0; segment < segmentCount; ++segment) {
    result[segment].count = packed[segment].count;
    if (packed[segment].zero)
      continue;
    if (global->type == TY_F32) {
      f32 *data = arena_.createArray<f32>(packed[segment].count);
      std::copy(packed[segment].floating.begin(),
                packed[segment].floating.end(), data);
      result[segment].data = data;
    } else {
      i32 *data = arena_.createArray<i32>(packed[segment].count);
      std::copy(packed[segment].integers.begin(),
                packed[segment].integers.end(), data);
      result[segment].data = data;
    }
  }
  if (needsTailZero)
    result[segmentCount].count = global->numElements - static_cast<u32>(total);
  global->initSegment = result;
  global->initSegmentCount = resultCount;
  return true;
}

bool ASTToHIR::extractConstantLiteral(ExprNode *expr, IRType target,
                                      i32 &integer, f32 &floating) const {
  if (!expr)
    return true;
  while (auto *conversion = dyn_cast<ImplicitCastExpr>(expr))
    expr = conversion->operand;
  if (auto *value = dyn_cast<IntLiteralExpr>(expr)) {
    integer = value->value;
    floating = static_cast<f32>(value->value);
    return true;
  }
  if (auto *value = dyn_cast<FloatLiteralExpr>(expr)) {
    floating = value->value;
    if (target == TY_I32)
      return false;
    return true;
  }
  return false;
}

bool ASTToHIR::hasValidSignature(FuncDecl *declaration) {
  if (!declaration->type) {
    diagnose(declaration->getLocation(),
             "function is missing its semantic type");
    return false;
  }
  if (declaration->type->paramCount != declaration->paramCount) {
    diagnose(declaration->getLocation(),
             "function parameter list disagrees with its semantic type");
    return false;
  }
  if (declaration->paramCount &&
      (!declaration->params || !declaration->type->paramTypes)) {
    diagnose(declaration->getLocation(),
             "function parameter metadata is missing");
    return false;
  }
  if (scalarType(declaration->type->returnType) !=
      baseType(declaration->returnType)) {
    diagnose(declaration->getLocation(),
             "function return type disagrees with its semantic type");
    return false;
  }
  for (u32 index = 0; index < declaration->paramCount; ++index) {
    FuncParam *parameter =
        declaration->params ? declaration->params[index] : nullptr;
    Type *semantic = declaration->type->paramTypes[index];
    if (!parameter || !parameter->type || parameter->type != semantic ||
        (parameter->isArray
             ? scalarType(semantic) != TY_PTR
             : scalarType(semantic) != baseType(parameter->baseType))) {
      diagnose(declaration->getLocation(),
               "function parameter disagrees with its semantic type");
      return false;
    }
  }
  return true;
}

bool ASTToHIR::signaturesMatch(FuncDecl *left, FuncDecl *right) const {
  if (left->type->isVariadic != right->type->isVariadic ||
      left->type->paramCount != right->type->paramCount ||
      scalarType(left->type->returnType) != scalarType(right->type->returnType))
    return false;
  for (u32 index = 0; index < left->type->paramCount; ++index)
    if (left->type->paramTypes[index] != right->type->paramTypes[index])
      return false;
  return true;
}

Type *ASTToHIR::declarationType(const ASTNode *declaration) const noexcept {
  if (auto *variable = dyn_cast<VarDecl>(declaration))
    return variable->type;
  if (auto *constant = dyn_cast<ConstDecl>(declaration))
    return constant->type;
  if (auto *parameter = dyn_cast<FuncParam>(declaration))
    return parameter->type;
  return nullptr;
}

Type *ASTToHIR::scalarElementType(Type *type) const noexcept {
  if (auto *array = dyn_cast<ArrayType>(type))
    return array->elementType;
  if (auto *pointer = dyn_cast<PointerType>(type)) {
    if (auto *array = dyn_cast<ArrayType>(pointer->pointee))
      return array->elementType;
    if (auto *array = dyn_cast<AnyDimArrayType>(pointer->pointee))
      return array->elementType;
    return pointer->pointee;
  }
  if (auto *array = dyn_cast<AnyDimArrayType>(type))
    return array->elementType;
  return type;
}

IRType ASTToHIR::scalarType(Type *type) const noexcept {
  if (!type)
    return TY_VOID;
  switch (type->getKind()) {
  case TypeKind::Int:
    return TY_I32;
  case TypeKind::Float:
    return TY_F32;
  case TypeKind::Void:
    return TY_VOID;
  case TypeKind::Pointer:
  case TypeKind::Array:
  case TypeKind::AnyDimArray:
    return TY_PTR;
  case TypeKind::Function:
    return TY_VOID;
  }
  return TY_VOID;
}

IRType ASTToHIR::baseType(TypeKind type) const noexcept {
  switch (type) {
  case TypeKind::Float:
    return TY_F32;
  case TypeKind::Void:
    return TY_VOID;
  default:
    return TY_I32;
  }
}

void ASTToHIR::setSourceLocation(const ASTNode *node) {
  if (!builder_)
    return;
  if (!node) {
    builder_->setCurrentSourceLocation(nullptr);
    return;
  }
  auto found = locations_.find(node);
  if (found == locations_.end()) {
    const SourceLocation *location =
        arena_.create<SourceLocation>(node->getLocation());
    found = locations_.emplace(node, location).first;
  }
  builder_->setCurrentSourceLocation(found->second);
}

void ASTToHIR::diagnose(SourceLocation location, const char *message) {
  SVM_ERROR(diagnostics_, location, "%s", message);
}

} // namespace svm::ir
