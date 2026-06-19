#include "IR.h"

#include <cmath>
#include <cstring>
#include <limits>
#include <vector>

namespace svm {
namespace ir {

void IRBuilder::allocatePayload(Inst *inst) {
  assert(inst && function_ && function_->arena);
  switch (inst->op_) {
  case OP_ALLOCA:
  case OP_LOAD:
  case OP_STORE:
    inst->mem_ = function_->arena->create<MemPayload>();
    break;
  case OP_ARRAYIDX:
    inst->array_ = function_->arena->create<ArrayPayload>();
    break;
  case OP_CALL:
  case MOP_CALL:
    inst->callInfo_ = function_->arena->create<CallInfoPayload>();
    break;
  case OP_BR:
  case MOP_BEQ:
  case MOP_BNE:
  case MOP_BLT:
  case MOP_BGE:
  case MOP_BLTU:
  case MOP_BGTU:
    inst->branch_ = function_->arena->create<BrPayload>();
    break;
  case OP_IF:
  case OP_WHILE:
    inst->scf_ = function_->arena->create<ScfPayload>();
    break;
  case OP_SWITCH:
    inst->switch_ = function_->arena->create<SwitchPayload>();
    break;
  default:
    break;
  }
}

IRBuilder::IRBuilder(Module *module, Function *function) noexcept
    : module_(module), function_(function) {
  assert(module_ && function_ && function_->arena);
  assert(function_->module == module_);
}

void IRBuilder::setInsertAtEnd(BasicBlock *block) noexcept {
  insertBlock_ = block;
  insertAfter_ = block ? block->instLast_ : nullptr;
}

void IRBuilder::setInsertAtStart(BasicBlock *block) noexcept {
  insertBlock_ = block;
  insertAfter_ = nullptr;
}

void IRBuilder::setInsertAfter(Inst *inst) noexcept {
  assert(inst && inst->block_);
  insertBlock_ = inst->block_;
  insertAfter_ = inst;
}

void IRBuilder::setInsertBefore(Inst *inst) noexcept {
  assert(inst && inst->block_);
  insertBlock_ = inst->block_;
  insertAfter_ = inst->prev_;
}

Inst *IRBuilder::newInst(OpCode op, IRType type, u32 operandCount) {
  assert(function_ && function_->arena);
  assert(operandCount <= std::numeric_limits<u16>::max());

  Inst *inst = function_->arena->create<Inst>();
  inst->op_ = op;
  inst->type_ = type;
  inst->operandCount_ = static_cast<u16>(operandCount);
  inst->erased_ = false;
  inst->undefValue_ = false;
  inst->inlineArgs_[0] = {};
  inst->inlineArgs_[1] = {};
  inst->args_ = operandCount > 2
                    ? function_->arena->createArray<InstRef>(operandCount)
                    : inst->inlineArgs_;
  inst->uses_ = nullptr;
  std::memset(inst->payload_, 0, sizeof(inst->payload_));
  allocatePayload(inst);

  inst->arena = function_->arena;
  inst->prev_ = nullptr;
  inst->next_ = nullptr;
  inst->block_ = nullptr;
  inst->id = function_->instCount++;
  inst->sourceLocation = currentSourceLocation_;
  return inst;
}

void IRBuilder::attach(Inst *inst) {
  assert(inst && insertBlock_ && !inst->block_);

  if (inst->getOp() == OP_PHI) {
    if (insertBlock_->phiLast_)
      inst->linkAfter(insertBlock_->phiLast_);
    else {
      inst->block_ = insertBlock_;
      insertBlock_->phiFirst_ = insertBlock_->phiLast_ = inst;
    }
    insertAfter_ = inst;
    return;
  }

  Inst *after = insertAfter_;
  if (after) {
    assert(after->block_ == insertBlock_);
    if (after->getOp() == OP_PHI)
      after = nullptr;
  }

  if (!after) {
    if (insertBlock_->instFirst_)
      inst->linkBefore(insertBlock_->instFirst_);
    else {
      inst->block_ = insertBlock_;
      insertBlock_->instFirst_ = insertBlock_->instLast_ = inst;
    }
  } else
    inst->linkAfter(after);
  insertAfter_ = inst;
}

Inst *IRBuilder::replaceHeader(Inst *victim, OpCode op, IRType type) {
  assert(victim && !victim->isErased());
  assert((victim->getOp() == OP_PHI) == (op == OP_PHI));

  victim->dropAllOperands();
  victim->op_ = op;
  victim->type_ = type;
  victim->operandCount_ = 0;
  victim->erased_ = false;
  victim->undefValue_ = false;
  victim->inlineArgs_[0] = {};
  victim->inlineArgs_[1] = {};
  victim->args_ = victim->inlineArgs_;
  std::memset(victim->payload_, 0, sizeof(victim->payload_));
  allocatePayload(victim);
  return victim;
}

Inst *IRBuilder::replaceInPlace(Inst *victim, OpCode op, IRType type) {
  return replaceHeader(victim, op, type);
}

Inst *IRBuilder::replaceInPlace(Inst *victim, OpCode op, IRType type,
                                Inst *arg0) {
  replaceHeader(victim, op, type);
  victim->operandCount_ = 1;
  victim->setArg(0, arg0);
  return victim;
}

Inst *IRBuilder::replaceInPlace(Inst *victim, OpCode op, IRType type,
                                Inst *arg0, Inst *arg1) {
  replaceHeader(victim, op, type);
  victim->operandCount_ = 2;
  victim->setArg(0, arg0);
  victim->setArg(1, arg1);
  return victim;
}

Inst *IRBuilder::replaceWithJump(Inst *victim, BasicBlock *target) {
  assert(victim && target);
  const OpCode op = function_->phase == IRPhase::MIR ? MOP_J : OP_JMP;
  Inst *jump = replaceInPlace(victim, op, TY_VOID);
  jump->setJumpTarget(target);
  return jump;
}

Inst *IRBuilder::replaceWithBranch(Inst *victim, Inst *condition,
                                   BasicBlock *trueBlock,
                                   BasicBlock *falseBlock) {
  assert(victim && condition && trueBlock && falseBlock);
  assert(function_->phase != IRPhase::MIR);
  Inst *branch = replaceInPlace(victim, OP_BR, TY_VOID, condition);
  branch->mutableBranch() = {trueBlock, falseBlock};
  return branch;
}

Inst *IRBuilder::replaceWithJumpAndEraseSuffix(Inst *victim,
                                               BasicBlock *target) {
  Inst *jump = replaceWithJump(victim, target);
  eraseAfter(jump);
  return jump;
}

void IRBuilder::eraseAfter(Inst *anchor) {
  assert(anchor && anchor->block_);
  std::vector<Inst *> dead;
  for (Inst *inst = anchor->next_; inst; inst = inst->next_)
    dead.push_back(inst);
  for (Inst *inst : dead)
    inst->dropAllOperands();
  for (Inst *inst : dead) {
    const bool erased = inst->eraseFromBlock();
    assert(erased);
    UNUSED(erased);
  }
}

bool IRBuilder::eraseRegionContents(Region *region) {
  if (!region || region == function_->region || region->function != function_ ||
      (region->owner && !region->owner->isErased()))
    return false;

  std::vector<Inst *> instructions;
  forEachInstRecursive(region,
                       [&](Inst *inst) { instructions.push_back(inst); });

  // 先切断整个死图的Use-Def边 再执行物理脱链 不依赖指令拓扑顺序
  for (Inst *inst : instructions)
    inst->dropAllOperands();
  for (auto it = instructions.rbegin(); it != instructions.rend(); ++it) {
    if (!(*it)->parentBlock())
      continue;
    const bool erased = (*it)->eraseFromBlock();
    assert(erased);
    UNUSED(erased);
  }
  region->owner = nullptr;
  region->parent = nullptr;
  return true;
}

Inst *IRBuilder::iConstImpl(i32 value, IRType type) {
  assert(type == TY_I1 || type == TY_I32);
  const IConstKey key{type, value};
  auto &pool = function_->constPools.iConstPool;
  const auto found = pool.find(key);
  if (found != pool.end())
    return found->second;

  Inst *inst = newInst(OP_ICONST, type, 0);
  inst->setImm(value);
  inst->sourceLocation = nullptr;
  pool.emplace(key, inst);
  return inst;
}

Inst *IRBuilder::iConst(i32 value) { return iConstImpl(value, TY_I32); }

Inst *IRBuilder::i1Const(bool value) {
  return iConstImpl(value ? 1 : 0, TY_I1);
}

Inst *IRBuilder::fConst(f32 value) {
  u32 bits = 0;
  static_assert(sizeof(bits) == sizeof(value));
  std::memcpy(&bits, &value, sizeof(bits));

  auto &pool = function_->constPools.fConstPool;
  const auto found = pool.find(bits);
  if (found != pool.end())
    return found->second;

  Inst *inst = newInst(OP_FCONST, TY_F32, 0);
  inst->setFimm(value);
  inst->sourceLocation = nullptr;
  pool.emplace(bits, inst);
  return inst;
}

Inst *IRBuilder::getGlobalPtr(Global *global) {
  assert(global);
  auto &pool = function_->constPools.globalPtrPool;
  const auto found = pool.find(global);
  if (found != pool.end())
    return found->second;

  Inst *inst = newInst(OP_GETGLOBAL, TY_PTR, 0);
  inst->setGlobal(global);
  inst->sourceLocation = nullptr;
  pool.emplace(global, inst);
  return inst;
}

Inst *IRBuilder::makeUndef(IRType type) {
  Inst *inst = newInst(OP_ICONST, type, 0);
  inst->undefValue_ = true;
  inst->sourceLocation = nullptr;
  return inst;
}

Inst *IRBuilder::tryFoldConstant(OpCode op, IRType type, Inst *left,
                                 Inst *right) {
  if (!left || left->isUndefValue())
    return nullptr;

  if ((op == OP_NEG || op == OP_LNOT) && left->getOp() == OP_ICONST) {
    const i32 value = left->getImm();
    if (op == OP_NEG)
      return iConstImpl(i32NegWrap(value), type);
    return i1Const(value == 0);
  }

  if ((isBinaryArithmetic(op) || isIntCompare(op)) && right &&
      !right->isUndefValue() && left->getOp() == OP_ICONST &&
      right->getOp() == OP_ICONST) {
    const i32 lhs = left->getImm();
    const i32 rhs = right->getImm();
    switch (op) {
    case OP_ADD:
      return iConstImpl(i32AddWrap(lhs, rhs), type);
    case OP_SUB:
      return iConstImpl(i32SubWrap(lhs, rhs), type);
    case OP_MUL:
      return iConstImpl(i32MulWrap(lhs, rhs), type);
    case OP_DIV:
      if (rhs == 0 || (lhs == std::numeric_limits<i32>::min() && rhs == -1))
        return nullptr;
      return iConstImpl(lhs / rhs, type);
    case OP_MOD:
      if (rhs == 0 || (lhs == std::numeric_limits<i32>::min() && rhs == -1))
        return nullptr;
      return iConstImpl(lhs % rhs, type);
    case OP_EQ:
      return i1Const(lhs == rhs);
    case OP_NE:
      return i1Const(lhs != rhs);
    case OP_LT:
      return i1Const(lhs < rhs);
    case OP_LE:
      return i1Const(lhs <= rhs);
    case OP_GT:
      return i1Const(lhs > rhs);
    case OP_GE:
      return i1Const(lhs >= rhs);
    default:
      break;
    }
  }

  if (op == OP_FNEG && left->getOp() == OP_FCONST)
    return fConst(-left->getFimm());

  if ((op >= OP_FADD && op <= OP_FGE) && right && !right->isUndefValue() &&
      left->getOp() == OP_FCONST && right->getOp() == OP_FCONST) {
    const f32 lhs = left->getFimm();
    const f32 rhs = right->getFimm();
    switch (op) {
    case OP_FADD:
      return fConst(lhs + rhs);
    case OP_FSUB:
      return fConst(lhs - rhs);
    case OP_FMUL:
      return fConst(lhs * rhs);
    case OP_FDIV:
      if (rhs == 0.0F)
        return nullptr;
      return fConst(lhs / rhs);
    case OP_FEQ:
      return i1Const(lhs == rhs);
    case OP_FNE:
      return i1Const(lhs != rhs);
    case OP_FLT:
      return i1Const(lhs < rhs);
    case OP_FLE:
      return i1Const(lhs <= rhs);
    case OP_FGT:
      return i1Const(lhs > rhs);
    case OP_FGE:
      return i1Const(lhs >= rhs);
    default:
      break;
    }
  }

  if (op == OP_I2F && left->getOp() == OP_ICONST)
    return fConst(static_cast<f32>(left->getImm()));
  if (op == OP_F2I && left->getOp() == OP_FCONST &&
      canConvertToI32(left->getFimm())) {
    return iConst(
        static_cast<i32>(std::trunc(static_cast<f64>(left->getFimm()))));
  }
  if (op == OP_ZEXT && left->getOp() == OP_ICONST)
    return iConst(left->getImm() != 0 ? 1 : 0);
  return nullptr;
}

Inst *IRBuilder::emit(OpCode op, IRType type) {
  Inst *inst = newInst(op, type, 0);
  attach(inst);
  return inst;
}

Inst *IRBuilder::emit(OpCode op, IRType type, Inst *arg0) {
  if (Inst *folded = tryFoldConstant(op, type, arg0))
    return folded;
  Inst *inst = newInst(op, type, 1);
  inst->setArg(0, arg0);
  attach(inst);
  return inst;
}

Inst *IRBuilder::emit(OpCode op, IRType type, Inst *arg0, Inst *arg1) {
  if (Inst *folded = tryFoldConstant(op, type, arg0, arg1))
    return folded;
  Inst *inst = newInst(op, type, 2);
  inst->setArg(0, arg0);
  inst->setArg(1, arg1);
  attach(inst);
  return inst;
}

Inst *IRBuilder::emitN(OpCode op, IRType type, Inst *const *args, u32 count) {
  assert(count == 0 || args);
  Inst *inst = newInst(op, type, count);
  for (u32 index = 0; index < count; ++index)
    inst->setArg(index, args[index]);
  attach(inst);
  return inst;
}

Inst *IRBuilder::emitPhi(IRType type, BasicBlock *block, Inst *initialValue) {
  assert(block && initialValue);
  BasicBlock *savedBlock = insertBlock_;
  Inst *savedAfter = insertAfter_;
  insertBlock_ = block;
  insertAfter_ = block->phiLast_;

  const u32 count = block->getPredecessorCount();
  Inst *phi = newInst(OP_PHI, type, count);
  phi->setIncomingArray(function_->arena->createArray<BasicBlock *>(count));
  for (u32 index = 0; index < count; ++index) {
    phi->setIncomingBlock(index, block->getPredecessor(index));
    phi->setArg(index, initialValue);
  }
  attach(phi);

  insertBlock_ = savedBlock;
  insertAfter_ = savedAfter;
  return phi;
}

Inst *IRBuilder::emitLoad(Inst *address, IRType elementType) {
  Inst *load = emit(OP_LOAD, elementType, address);
  const i32 size = typeSizeBytes(elementType);
  assert(size > 0);
  load->getMem() = {static_cast<u32>(size), elementType, -1, nullptr};
  return load;
}

Inst *IRBuilder::emitStore(Inst *address, Inst *value, IRType elementType) {
  Inst *store = emit(OP_STORE, TY_VOID, address, value);
  const i32 size = typeSizeBytes(elementType);
  assert(size > 0);
  store->getMem() = {static_cast<u32>(size), elementType, -1, nullptr};
  return store;
}

Inst *IRBuilder::emitAlloca(u32 totalSizeBytes, IRType elementType) {
  assert(totalSizeBytes > 0);
  Inst *alloca = emit(OP_ALLOCA, TY_PTR);
  alloca->getMem() = {totalSizeBytes, elementType, -1, nullptr};
  return alloca;
}

Inst *IRBuilder::emitAllocaParam(u32 totalSizeBytes, IRType elementType,
                                 i16 paramIndex) {
  assert(paramIndex >= 0);
  Inst *alloca = emitAlloca(totalSizeBytes, elementType);
  alloca->getMem().paramIdx = paramIndex;
  return alloca;
}

Inst *IRBuilder::emitGetPtr(Inst *base, Inst *index, i32 stride) {
  assert(stride > 0);
  Inst *getPtr = emit(OP_GETPTR, TY_PTR, base, index);
  getPtr->setStride(stride);
  return getPtr;
}

Inst *IRBuilder::emitArrayIndex(Inst *base, Inst *const *indices, u32 count,
                                IRType elementType, const u32 *strides,
                                const u32 *dims) {
  assert(base && (count == 0 || (indices && strides && dims)));
  assert(count < std::numeric_limits<u16>::max());
  Inst *arrayIndex = newInst(OP_ARRAYIDX, TY_PTR, count + 1);
  arrayIndex->setArg(0, base);
  for (u32 index = 0; index < count; ++index)
    arrayIndex->setArg(index + 1, indices[index]);

  ArrayPayload &payload = arrayIndex->getArray();
  payload.elementType = elementType;
  payload.nDims = static_cast<u16>(count);
  payload.strides = function_->arena->createArray<u32>(count);
  payload.dims = function_->arena->createArray<u32>(count);
  if (count) {
    std::memcpy(payload.strides, strides, sizeof(u32) * count);
    std::memcpy(payload.dims, dims, sizeof(u32) * count);
  }
  attach(arrayIndex);
  return arrayIndex;
}

Inst *IRBuilder::emitFor(Inst *stop, Inst *step, Inst *ivAddress,
                         Region *body) {
  Inst *forInst = newInst(OP_FOR, TY_VOID, 3);
  forInst->setArg(0, stop);
  forInst->setArg(1, step);
  forInst->setArg(2, ivAddress);
  forInst->setBody(body);
  if (body)
    body->owner = forInst;
  attach(forInst);
  return forInst;
}

Inst *IRBuilder::emitCall(Function *callee, Inst *const *args, u32 count,
                          IRType returnType) {
  assert(callee);
  Inst *call = emitN(OP_CALL, returnType, args, count);
  call->setCallee(callee);
  return call;
}

Inst *IRBuilder::castTo(Inst *value, IRType target) {
  assert(value);
  const IRType source = value->getType();
  if (source == target)
    return value;
  if (source == TY_I32 && target == TY_F32)
    return emit(OP_I2F, TY_F32, value);
  if (source == TY_F32 && target == TY_I32)
    return emit(OP_F2I, TY_I32, value);
  if (source == TY_I1 && target == TY_I32)
    return emit(OP_ZEXT, TY_I32, value);
  if (source == TY_I1 && target == TY_F32)
    return emit(OP_I2F, TY_F32, emit(OP_ZEXT, TY_I32, value));
  return value;
}

Inst *IRBuilder::toI1(Inst *value) {
  assert(value);
  if (value->getType() == TY_I1)
    return value;
  if (value->getType() == TY_I32)
    return emit(OP_NE, TY_I1, value, iConst(0));
  if (value->getType() == TY_F32)
    return emit(OP_FNE, TY_I1, value, fConst(0.0F));
  return value;
}

IRBuilder::Coerced IRBuilder::coercePair(Inst *left, Inst *right) {
  assert(left);
  if (!right)
    return {left, nullptr, left->getType()};

  if (left->getType() == TY_I1)
    left = castTo(left, TY_I32);
  if (right->getType() == TY_I1)
    right = castTo(right, TY_I32);
  if (left->getType() == right->getType())
    return {left, right, left->getType()};
  if (left->getType() == TY_I32 && right->getType() == TY_F32)
    return {castTo(left, TY_F32), right, TY_F32};
  if (left->getType() == TY_F32 && right->getType() == TY_I32)
    return {left, castTo(right, TY_F32), TY_F32};
  return {left, right, left->getType()};
}

Inst *IRBuilder::emitJump(BasicBlock *target) {
  assert(target);
  Inst *jump = emit(OP_JMP, TY_VOID);
  jump->setJumpTarget(target);
  return jump;
}

Inst *IRBuilder::emitBranch(Inst *condition, BasicBlock *trueBlock,
                            BasicBlock *falseBlock) {
  assert(condition && trueBlock && falseBlock);
  Inst *branch = emit(OP_BR, TY_VOID, condition);
  branch->mutableBranch() = {trueBlock, falseBlock};
  return branch;
}

Inst *IRBuilder::emitReturn(Inst *value) {
  return value ? emit(OP_RET, TY_VOID, value) : emit(OP_RET, TY_VOID);
}

Inst *IRBuilder::emitYield(Inst *condition) {
  return condition ? emit(OP_YIELD, TY_VOID, condition)
                   : emit(OP_YIELD, TY_VOID);
}

Inst *IRBuilder::emitBreak() { return emit(OP_BREAK, TY_VOID); }

Inst *IRBuilder::emitContinue() { return emit(OP_CONTINUE, TY_VOID); }

Inst *IRBuilder::emitIf(Inst *condition, Region *thenRegion,
                        Region *elseRegion) {
  assert(condition);
  Inst *ifInst = emit(OP_IF, TY_VOID, condition);
  ifInst->getScf().r[0] = thenRegion;
  ifInst->getScf().r[1] = elseRegion;
  if (thenRegion)
    thenRegion->owner = ifInst;
  if (elseRegion)
    elseRegion->owner = ifInst;
  return ifInst;
}

Inst *IRBuilder::emitWhile(Region *conditionRegion, Region *bodyRegion) {
  Inst *whileInst = emit(OP_WHILE, TY_VOID);
  whileInst->getScf().r[0] = conditionRegion;
  whileInst->getScf().r[1] = bodyRegion;
  if (conditionRegion)
    conditionRegion->owner = whileInst;
  if (bodyRegion)
    bodyRegion->owner = whileInst;
  return whileInst;
}

Inst *IRBuilder::emitSwitch(Inst *selector, const SwitchCase *cases,
                            u32 caseCount, BasicBlock *defaultTarget) {
  assert(selector && defaultTarget && (caseCount == 0 || cases));
  for (u32 index = 1; index < caseCount; ++index)
    assert(cases[index - 1].getValue() < cases[index].getValue());

  Inst *switchInst = emit(OP_SWITCH, TY_VOID, selector);
  SwitchPayload &payload = switchInst->mutableSwitch();
  payload.caseCount_ = caseCount;
  payload.defaultTarget_ = defaultTarget;
  payload.cases_ = function_->arena->createArray<SwitchCase>(caseCount);
  if (caseCount)
    std::memcpy(payload.cases_, cases, sizeof(SwitchCase) * caseCount);
  return switchInst;
}

void IRBuilder::bindJumpTable(Inst *inst, JumpTable *table) const noexcept {
  assert(inst && table);
  inst->setJumpTable(table);
}

Inst *IRBuilder::cloneInst(const Inst *source) {
  assert(source && !source->isErased());
  Inst *clone =
      newInst(source->getOp(), source->getType(), source->getOperandCount());
  clone->undefValue_ = source->undefValue_;
  clone->sourceLocation = source->sourceLocation;

  switch (source->getOp()) {
  case OP_ALLOCA:
  case OP_LOAD:
  case OP_STORE:
    *clone->mem_ = *source->mem_;
    break;
  case OP_ARRAYIDX: {
    *clone->array_ = *source->array_;
    const u32 count = source->array_->nDims;
    clone->array_->strides = function_->arena->createArray<u32>(count);
    clone->array_->dims = function_->arena->createArray<u32>(count);
    if (count) {
      std::memcpy(clone->array_->strides, source->array_->strides,
                  sizeof(u32) * count);
      std::memcpy(clone->array_->dims, source->array_->dims,
                  sizeof(u32) * count);
    }
    break;
  }
  case OP_CALL:
  case MOP_CALL:
    *clone->callInfo_ = *source->callInfo_;
    break;
  case OP_BR:
  case MOP_BEQ:
  case MOP_BNE:
  case MOP_BLT:
  case MOP_BGE:
  case MOP_BLTU:
  case MOP_BGTU:
    *clone->branch_ = *source->branch_;
    break;
  case OP_IF:
  case OP_WHILE:
    *clone->scf_ = *source->scf_;
    break;
  case OP_PHI: {
    const u32 count = source->getOperandCount();
    clone->incoming_ = function_->arena->createArray<BasicBlock *>(count);
    if (count)
      std::memcpy(clone->incoming_, source->incoming_,
                  sizeof(BasicBlock *) * count);
    break;
  }
  case OP_SWITCH: {
    clone->switch_->caseCount_ = source->switch_->caseCount_;
    clone->switch_->defaultTarget_ = source->switch_->defaultTarget_;
    const u32 count = source->switch_->caseCount_;
    clone->switch_->cases_ = function_->arena->createArray<SwitchCase>(count);
    if (count)
      std::memcpy(clone->switch_->cases_, source->switch_->cases_,
                  sizeof(SwitchCase) * count);
    break;
  }
  default:
    std::memcpy(clone->payload_, source->payload_, sizeof(clone->payload_));
    break;
  }
  return clone;
}

Region *IRBuilder::newRegion(Inst *owner, Region *parent) {
  Region *region = function_->arena->create<Region>();
  region->owner = owner;
  region->parent = parent;
  region->function = function_;
  return region;
}

BasicBlock *IRBuilder::newBlockAtEnd(Region *region) {
  assert(region && region->function == function_);
  BasicBlock *block = function_->arena->create<BasicBlock>();
  block->id = function_->blockCount++;
  region->adoptBlock(block);
  return block;
}

BasicBlock *IRBuilder::newBlockAfter(BasicBlock *anchor) {
  assert(anchor && anchor->parentRegion &&
         anchor->parentRegion->function == function_);
  BasicBlock *block = function_->arena->create<BasicBlock>();
  block->id = function_->blockCount++;
  block->moveAfter(anchor);
  return block;
}

} // namespace ir
} // namespace svm
