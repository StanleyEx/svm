#include "PassManager.h"

#include <vector>

namespace svm::ir {
namespace {
struct TailReturn {
  Inst *ret = nullptr;     // 被改写的返回指令 OP_RET
  Inst *call = nullptr;    // 当前函数的尾调用 OP_CALL
  Inst *wrapper = nullptr; // 可选的整数加法或乘法包装 OP_ADD/OP_MUL
  Inst *term = nullptr;    // 本轮累加/累乘的项或因子
};

class TCO final : public FunctionPass {
public:
  std::string_view name() const noexcept override { return "tco"; }
  PassResult run(Function *function, PassContext &) override;
};

bool collectScalarParamSlots(Function *function, std::vector<Inst *> &slots,
                             Inst *&firstBodyInst) {
  slots.assign(function->paramCount, nullptr);
  BasicBlock *entry = function->region ? function->region->first : nullptr;
  std::vector<bool> initialized(function->paramCount, false);
  firstBodyInst = entry ? entry->firstInst() : nullptr;
  for (; firstBodyInst; firstBodyInst = firstBodyInst->next()) {
    // 局部变量/形参的栈分配
    if (firstBodyInst->getOp() == OP_ALLOCA) {
      const i16 index = firstBodyInst->getMem().paramIdx;
      if (index < 0)
        continue; // 跳过非形参的局部变量Alloca
      const u32 paramIndex = static_cast<u32>(index);
      if (paramIndex >= function->paramCount)
        return false; // 形参索引越界
      const u32 expectedSize =
          static_cast<u32>(typeSizeBytes(function->paramTypes[paramIndex]));
      // 数组形参也转成可变入口槽，循环体只读取本轮参数值
      if (slots[paramIndex] || function->paramTypes[paramIndex] == TY_PTR ||
          firstBodyInst->getType() != TY_PTR ||
          firstBodyInst->getMem().elementType !=
              function->paramTypes[paramIndex] ||
          firstBodyInst->getMem().totalSizeBytes < expectedSize)
        return false;
      slots[paramIndex] = firstBodyInst; // 建立形参索引到Alloca的映射
      continue;
    }
    // 形参的初始化赋值指令
    if (firstBodyInst->getOp() != OP_STORE ||
        firstBodyInst->getOperandCount() != 2)
      break; // 既不是Alloca也不是Store 初始化段结束
    bool parameterInitialization = false;
    for (u32 index = 0; index < function->paramCount; ++index) {
      if (!slots[index] || firstBodyInst->getArg(0) != slots[index] ||
          firstBodyInst->getArg(1) != function->params[index])
        continue;
      if (initialized[index] ||
          firstBodyInst->getMem().elementType != function->paramTypes[index])
        return false; // 重复初始化或类型不匹配
      initialized[index] = true;
      parameterInitialization = true; // 成功匹配到形参初始化
      break;
    }
    if (!parameterInitialization)
      break; // Store指令不是形参初始化 初始化段结束
  }
  // 检查所有非指针类型形参是否都有对应的Alloca和初始化赋值
  for (u32 index = 0; index < function->paramCount; ++index)
    if (function->paramTypes[index] != TY_PTR &&
        (!slots[index] || !initialized[index]))
      return false;
  return true;
}

bool validateTailCall(Function *function, Inst *call) noexcept {
  if (!call || call->getOp() != OP_CALL || call->getCallee() != function ||
      call->getOperandCount() != function->paramCount)
    return false;
  for (u32 index = 0; index < function->paramCount; ++index) {
    if (call->getArg(index)->getType() != function->paramTypes[index])
      return false;
    // 如果形参是指针类型 追踪内存基址
    if (function->paramTypes[index] == TY_PTR) {
      const Inst *base = getMemoryBase(call->getArg(index));
      // 内存基址来源于本函数的栈帧 说明局部变量的引用传给了下一轮调用
      // 由于TCO复用栈帧 会导致下一轮调用覆盖本轮局部变量的值 拒绝
      if (!base || base->getOp() == OP_ALLOCA)
        return false;
    }
  }
  return true;
}

bool transform(Function *function) {
  auto isOnlyUseBy = [](const Inst *value, const Inst *user) {
    return value && value->hasOneUse() && value->uses()->user == user;
  };
  auto isInsideRegion = [](const Inst *inst, const Region *outer) {
    for (const Region *region = inst && inst->parentBlock()
                                    ? inst->parentBlock()->parentRegion
                                    : nullptr;
         region; region = region->parent)
      if (region == outer)
        return true;
    return false;
  };
  if (!function || function->isExtern || function->phase != IRPhase::HIR ||
      !function->region || !function->region->first)
    return false;

  std::vector<Inst *> returns;
  forEachInstRecursive(function->region, [&](Inst *inst) {
    if (inst->getOp() == OP_RET)
      returns.push_back(inst);
  });

  std::vector<TailReturn> tails;   // 存放筛选出的所有合法尾调用候选集
  std::vector<Inst *> baseReturns; // 存放普通终止返回点
  OpCode moduloOp = OP_ADD;        // 记录Modulo TCO的统一算符 默认占位为ADD
  bool hasModulo = false;          // 是否激活Modulo TCO模式

  // 严苛审查并分类每一个返回指令
  for (Inst *ret : returns) {
    if (ret->getOperandCount() == 0) {
      baseReturns.push_back(ret); // 无返回值的Return BaseReturn
      continue;
    }
    if (ret->getOperandCount() != 1)
      return false;
    Inst *value = ret->getArg(0);
    // 标准尾调用模式 return self(args);
    if (value->getOp() == OP_CALL && value->getCallee() == function) {
      if (getEnclosingLoop(ret) || !isOnlyUseBy(value, ret) ||
          !validateTailCall(function, value))
        return false;
      tails.push_back({ret, value, nullptr, nullptr});
      continue;
    }
    // Modulo TCO模式 return self(args) + C 或 return C * self(args)
    if (value->getOp() != OP_ADD && value->getOp() != OP_MUL) {
      baseReturns.push_back(ret); // 既不是CALL也不是加法或乘法 BaseReturn
      continue;
    }

    // 拆解加法或乘法的左右操作数
    Inst *left = value->getArg(0);
    Inst *right = value->getArg(1);
    const bool leftSelf =
        left->getOp() == OP_CALL && left->getCallee() == function;
    const bool rightSelf =
        right->getOp() == OP_CALL && right->getCallee() == function;
    if (leftSelf && rightSelf)
      return false; // 左右同时是自递归调用 不支持
    Inst *call = leftSelf ? left : (rightSelf ? right : nullptr);
    if (!call) {
      baseReturns.push_back(ret); // 左右无自递归 BaseReturn
      continue;
    }
    Inst *term = call == left ? right : left;
    // Modulo TCO: 禁止在循环中 限定TY_I32整数运算 唯一消费者
    if (getEnclosingLoop(ret) || function->returnType != TY_I32 ||
        value->getType() != TY_I32 || call->getType() != TY_I32 ||
        term->getType() != TY_I32 || !isOnlyUseBy(call, value) ||
        !isOnlyUseBy(value, ret) || !validateTailCall(function, call))
      return false;
    // 如果有多个Modulo TCO尾调用 要求使用相同的算符
    if (hasModulo && moduloOp != value->getOp())
      return false;
    hasModulo = true;
    moduloOp = value->getOp();
    tails.push_back({ret, call, value, term});
  }
  if (tails.empty())
    return false;
  if (hasModulo) // Modulo TCO模式 检查所有BaseReturn的返回值类型必须是TY_I32
    for (Inst *ret : baseReturns)
      if (ret->getOperandCount() != 1 || ret->getArg(0)->getType() != TY_I32)
        return false;

  std::vector<Inst *> paramSlots;
  Inst *firstBodyInst = nullptr;
  if (!collectScalarParamSlots(function, paramSlots, firstBodyInst))
    return false;

  IRBuilder builder(function->module, function);
  BasicBlock *entry = function->region->first;

  // 指针形参也转成可变入口槽 循环体只读取本轮参数值
  std::vector<Inst *> pointerLoads(function->paramCount, nullptr);
  for (u32 index = 0; index < function->paramCount; ++index) {
    if (function->paramTypes[index] != TY_PTR)
      continue;
    // 在函数入口分配一个Alloca槽 用于存放每轮调用的参数值 并把原始形参写入槽中
    builder.setInsertAtStart(entry);
    Inst *slot = builder.emitAlloca(typeSizeBytes(TY_PTR), TY_PTR);
    builder.setInsertAfter(slot);
    builder.emitStore(slot, function->params[index], TY_PTR);
    paramSlots[index] = slot;
  }

  // 如果是Modulo TCO模式 在函数入口分配一个累加器/累乘器
  Inst *accumulator = nullptr;
  if (hasModulo) {
    builder.setInsertAtStart(entry);
    accumulator = builder.emitAlloca(typeSizeBytes(TY_I32), TY_I32);
    builder.setInsertAfter(accumulator);
    builder.emitStore(
        accumulator, moduloOp == OP_ADD ? builder.iConst(0) : builder.iConst(1),
        TY_I32);
  }

  // 条件Region 固定为true
  Region *condition = builder.newRegion(nullptr, function->region);
  BasicBlock *conditionBlock = builder.newBlockAtEnd(condition);
  builder.setInsertAtEnd(conditionBlock);
  builder.emitYield(builder.i1Const(true));
  Region *body = builder.newRegion(nullptr, function->region);
  if (firstBodyInst) {
    BasicBlock *split = builder.newBlockAtEnd(body);
    split->takeInstructionSuffixFrom(firstBodyInst);
  }
  // 将原函数的所有指令移动到新建的循环体Region中
  for (BasicBlock *block = entry->next(); block;) {
    BasicBlock *next = block->next();
    block->moveToEnd(body);
    block = next;
  }
  // 如果循环体Region为空 则补一个Yield
  if (!body->first) {
    BasicBlock *emptyBody = builder.newBlockAtEnd(body);
    builder.setInsertAtEnd(emptyBody);
    builder.emitYield();
  }

  BasicBlock *bodyEntry = body->first;
  for (u32 index = 0; index < function->paramCount; ++index) {
    if (function->paramTypes[index] != TY_PTR)
      continue;
    builder.setInsertAtStart(bodyEntry);
    pointerLoads[index] = builder.emitLoad(paramSlots[index], TY_PTR);
  }
  // 重写Use-Def: 将循环体内所有对原始形参的使用改为头部发射的局部Load
  // 保证每次读到的都是本轮调用被更新后的参数值 (依旧想象数组传参)
  for (u32 index = 0; index < function->paramCount; ++index) {
    Inst *replacement = pointerLoads[index];
    if (!replacement)
      continue;
    std::vector<Use *> uses;
    for (const Use *use = function->params[index]->uses(); use; use = use->next)
      if (use->user && isInsideRegion(use->user, body))
        uses.push_back(const_cast<Use *>(use));
    for (Use *use : uses)
      use->user->setArg(use->argNo, replacement);
  }

  // Entry块尾部发射While
  builder.setInsertAtEnd(entry);
  Inst *loop = builder.emitWhile(condition, body);

  // 把所有尾调用替换为Continue
  for (const TailReturn &tail : tails) {
    builder.setInsertBefore(tail.ret);
    // 如果是Modulo TCO模式 在尾调用前更新累加器/累乘器
    if (accumulator && tail.term) {
      Inst *current = builder.emitLoad(accumulator, TY_I32);
      Inst *next = builder.emit(moduloOp, TY_I32, current, tail.term);
      builder.emitStore(accumulator, next, TY_I32);
    }

    // 在擦除Call指令前将本轮新实参原子写回对应的Alloca槽以复用栈帧
    for (u32 index = 0; index < function->paramCount; ++index)
      builder.emitStore(paramSlots[index], tail.call->getArg(index),
                        function->paramTypes[index]);
    // Return -> Continue
    builder.replaceInPlace(tail.ret, OP_CONTINUE, TY_VOID);
    // 失去了Return的Use-Def边后 删除尾调用和包装指令
    if (tail.wrapper) {
      const bool erased = tail.wrapper->eraseFromBlock();
      assert(erased);
      UNUSED(erased);
    }
    const bool erased = tail.call->eraseFromBlock();
    assert(erased);
    UNUSED(erased);
  }

  // Modulo TCO模式 在循环体尾部把累加器/累乘器的值写回所有BaseReturn的返回值
  if (accumulator) {
    for (Inst *ret : baseReturns) {
      builder.setInsertBefore(ret);
      Inst *current = builder.emitLoad(accumulator, TY_I32);
      Inst *result = builder.emit(moduloOp, TY_I32, current, ret->getArg(0));
      ret->setArg(0, result);
    }
  }
  // 在While结构尾部(实际上不可达的After块)发射Return指令 维护CFG终结符完整性
  builder.setInsertAfter(loop);
  builder.emitReturn(function->returnType == TY_VOID
                         ? nullptr
                         : builder.makeUndef(function->returnType));
  return true;
}

PassResult TCO::run(Function *function, PassContext &) {
  return transform(function) ? PassResult::changedIR() : PassResult::noChange();
}

} // namespace
} // namespace svm::ir

SVM_REGISTER_FUNCTION_PASS("tco", svm::ir::TCO)
