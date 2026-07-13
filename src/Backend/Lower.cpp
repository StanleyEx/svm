#include "Analysis.h"
#include "MIRPass.h"
#include "MoveInfo.h"
#include "RV64.h"
#include "VReg.h"

#include <algorithm>
#include <cassert>
#include <cstring>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

using rv64::A0;
using rv64::FA0;
using rv64::FPR_ARG;
using rv64::FPR_ARG_N;
using rv64::GPR_ARG;
using rv64::GPR_ARG_N;
using rv64::SP;

// 常量按使用点物化 确保每个机器操作数都是IRC可见的块内定义
class Lowering {
public:
  explicit Lowering(Function *function, const SCEV *scev)
      : function_(function), builder_(function->module, function), scev_(scev) {
  }

  bool run() {
    if (!function_ || !function_->region || !function_->region->first)
      return false;
    computeUses(function_);
    lowerParameters();
    for (BasicBlock *block = function_->region->first; block;
         block = block->next())
      lowerBlock(block);
    computeUses(function_);
    return !failed_;
  }

private:
  // 只拍摄无控制流上下文的LIR事实 避免把边上成立的结论固化到MIR定义
  ScalarFactBundle computeStableScalarFacts(Inst *value) const {
    if (!value || (value->getType() != TY_I1 && value->getType() != TY_I32))
      return {};
    if (value->getOp() == OP_ICONST) {
      ScalarFactBundle facts =
          ScalarFactBundle::fromConstant(value->getImm(), FactSource::LIR_SCEV);
      canonicalizeBundle(facts);
      return facts;
    }
    if (!scev_)
      return {};
    ScalarFactBundle facts = ScalarFactBundle::fromRange(
        scev_->getI32Range(value), FactSource::LIR_SCEV);
    canonicalizeBundle(facts);
    return facts;
  }

  // 仅允许语义保值或布尔化的i32结果继承LIR事实
  static bool canBridgeScalarFacts(OpCode lirOp, OpCode mirOp) noexcept {
    if (lirOp == OP_ICONST)
      return mirOp == MOP_LI;
    if ((lirOp >= OP_EQ && lirOp <= OP_GE) ||
        (lirOp >= OP_FEQ && lirOp <= OP_FGE) || lirOp == OP_LNOT)
      return mirOp == MOP_SLT || mirOp == MOP_SEQZ || mirOp == MOP_SNEZ ||
             mirOp == MOP_FEQ_S || mirOp == MOP_FLT_S || mirOp == MOP_FLE_S;
    return lirOp == OP_ZEXT && mirOp == MOP_ANDI;
  }

  // 将规范化后的稳定事实附到对应MIR虚拟寄存器定义
  void annotateScalarFacts(Inst *definition, ScalarFactBundle facts) const {
    if (!definition || definition->getType() != TY_I32 || !facts.valid)
      return;
    canonicalizeBundle(facts);
    attachFactBundle(function_, definition, facts);
  }

  // 所有LIR事实下传统一经过操作码语义门限
  void annotateLoweredScalarFacts(Inst *definition, ScalarFactBundle facts,
                                  OpCode lirOp, OpCode mirOp) const {
    if (canBridgeScalarFacts(lirOp, mirOp))
      annotateScalarFacts(definition, facts);
  }

  // Lowering自行物化的i32立即数具有确定的机器语义
  void attachI32ConstantFact(Inst *definition, i32 value) const {
    if (!definition || definition->getType() != TY_I32)
      return;
    ScalarFactBundle facts =
        ScalarFactBundle::fromConstant(value, FactSource::LoweringSemantic);
    canonicalizeBundle(facts);
    attachFactBundle(function_, definition, facts);
  }

  // 在使用点之前物化浮点或整数值
  Inst *materialize(Inst *value, Inst *before) {
    if (!value)
      return nullptr;
    if (value->parentBlock() || value->isPrecoloredDef())
      return value;
    builder_.setInsertBefore(before);
    if (value->isUndefValue()) {
      if (value->getType() == TY_F32) {
        Inst *bits = builder_.emit(MOP_LI, TY_I32);
        bits->setImm(0);
        attachI32ConstantFact(bits, 0);
        return builder_.emit(MOP_FMV_W_X, TY_F32, bits);
      }
      Inst *zero = builder_.emit(MOP_LI, value->getType());
      zero->setImm(0);
      attachI32ConstantFact(zero, 0);
      return zero;
    }
    switch (value->getOp()) {
    case OP_ICONST: {
      Inst *li = builder_.emit(MOP_LI, value->getType());
      li->setImm(value->getImm());
      attachI32ConstantFact(li, value->getImm());
      return li;
    }
    case OP_FCONST: {
      u32 bits = 0;
      f32 number = value->getFimm();
      std::memcpy(&bits, &number, sizeof(bits));
      Inst *li = builder_.emit(MOP_LI, TY_I32);
      li->setImm(i32FromBits(bits));
      return builder_.emit(MOP_FMV_W_X, TY_F32, li);
    }
    case OP_GETGLOBAL: {
      return materializeGlobalAddress(value->getGlobal());
    }
    default:
      return value;
    }
  }

  Inst *arg(Inst *instruction, u32 index) {
    return materialize(instruction->getArg(index), instruction);
  }

  Inst *materializeGlobalAddress(Global *global) {
    assert(global);
    BasicBlock *savedBlock = builder_.insertBlock();
    Inst *savedAfter = builder_.insertAfter();
    BasicBlock *entry = function_->region->first;
    if (entryCursor_)
      builder_.setInsertAfter(entryCursor_);
    else
      builder_.setInsertAtStart(entry);

    Inst *base = builder_.emit(MOP_LA, TY_PTR);
    if (global->globalMergeMember) {
      base->setSymbolRef(SymbolRef::mergedBaseRef(global->globalMergeGroup));
      entryCursor_ = base;
      if (global->globalMergeOffset != 0) {
        assert(rv64::fitsImm12(global->globalMergeOffset));
        Inst *address = builder_.emit(MOP_ADDI, TY_PTR, base);
        address->setImm(global->globalMergeOffset);
        entryCursor_ = address;
        base = address;
      }
    } else {
      base->setGlobal(global);
      entryCursor_ = base;
    }
    if (savedAfter)
      builder_.setInsertAfter(savedAfter);
    else
      builder_.setInsertAtStart(savedBlock);
    return base;
  }

  // 将形参绑定到ABI位置 OP_PARAM是浮空SSA锚点 替换其使用即可完成消除
  void lowerParameters() {
    BasicBlock *entry = function_->region->first;
    builder_.setInsertAtStart(entry);
    u32 gpr = 0, fpr = 0;
    for (u32 index = 0; index < function_->paramCount; ++index) {
      Inst *parameter = function_->params[index];
      const IRType type = function_->paramTypes[index];
      Inst *bound = nullptr;
      if (type == TY_F32 && fpr < FPR_ARG_N) {
        const rv64::PReg source = FPR_ARG[fpr++];
        bound = builder_.emit(MOP_FCOPY, TY_F32,
                              function_->module->physicalRegister(source));
        markMove(function_, bound, MoveKind::ArgCopy, source);
      } else if (gpr < GPR_ARG_N) {
        const rv64::PReg source = GPR_ARG[gpr++];
        const IRType copyType = type == TY_PTR ? TY_PTR : TY_I32;
        Inst *gprCopy = builder_.emit(
            MOP_COPY, copyType, function_->module->physicalRegister(source));
        markMove(function_, gprCopy, MoveKind::ArgCopy, source);
        bound = type == TY_F32 ? builder_.emit(MOP_FMV_W_X, TY_F32, gprCopy)
                               : gprCopy;
      } else {
        const OpCode load = type == TY_F32   ? MOP_FLW_FRAME
                            : type == TY_PTR ? MOP_LD_FRAME
                                             : MOP_LW_FRAME;
        const i32 slot =
            function_->newFrameSlot(8, 8, Function::FrameSlot::Kind::ArgPass);
        bound =
            builder_.emit(load, type, function_->module->physicalRegister(SP));
        bound->setFrameIndex(slot);
      }
      entryCursor_ = bound;
      replaceAllUsesWith(function_, parameter, bound);
    }
  }

  void lowerBlock(BasicBlock *block) {
    for (Inst *instruction = block->firstInst(); instruction;) {
      Inst *next = instruction->next();
      lowerInstruction(instruction);
      instruction = next;
    }
  }

  // 替换LIR分支并保留两个CFG后继
  void lowerBranch(Inst *instruction) {
    const BrPayload old = instruction->getBr();
    Inst *original = instruction->getArg(0);
    OpCode branch = MOP_BNE;
    Inst *left = nullptr;
    Inst *right = function_->module->physicalRegister(rv64::ZERO);
    if (original->getOp() == MOP_SLT && original->hasOneUse()) {
      branch = MOP_BLT;
      left = materialize(original->getArg(0), instruction);
      right = materialize(original->getArg(1), instruction);
    } else if (original->getOp() == MOP_SEQZ && original->hasOneUse()) {
      Inst *source = original->getArg(0);
      if (source->getOp() == MOP_SLT && source->hasOneUse()) {
        branch = MOP_BGE;
        left = materialize(source->getArg(0), instruction);
        right = materialize(source->getArg(1), instruction);
      } else {
        branch = MOP_BEQ;
        left = materialize(source, instruction);
      }
    } else if (original->getOp() == MOP_SNEZ && original->hasOneUse()) {
      Inst *source = original->getArg(0);
      if (source->getOp() == MOP_SLT && source->hasOneUse()) {
        branch = MOP_BLT;
        left = materialize(source->getArg(0), instruction);
        right = materialize(source->getArg(1), instruction);
      } else {
        left = materialize(source, instruction);
      }
    } else {
      left = arg(instruction, 0);
    }
    builder_.replaceInPlace(instruction, branch, TY_VOID, left, right);
    CFGEditor::rewriteBranchSlot(instruction->parentBlock(), true, old.trueBB);
    CFGEditor::rewriteBranchSlot(instruction->parentBlock(), false,
                                 old.falseBB);
  }

  void lowerCall(Inst *instruction, const ScalarFactBundle &facts) {
    Function *callee = instruction->getCallee();
    const u32 count = instruction->getOperandCount();
    std::vector<Inst *> arguments;
    arguments.reserve(count);
    for (u32 index = 0; index < count; ++index)
      arguments.push_back(arg(instruction, index));

    builder_.setInsertBefore(instruction);
    u32 gpr = 0, fpr = 0, stackWords = 0;
    std::vector<Inst *> callArguments;
    callArguments.reserve(count);
    const u32 fixed = callee && callee->functionType
                          ? callee->functionType->paramCount
                          : (callee ? callee->paramCount : 0);
    const bool variadic =
        callee && callee->functionType && callee->functionType->isVariadic;
    for (u32 index = 0; index < count; ++index) {
      Inst *value = arguments[index];
      const bool vararg = variadic && index >= fixed;
      if (vararg && value->getType() == TY_F32) {
        // RA后的调用归位会把该伪指令原子展开为fcvt.d.s和fmv.x.d
        // 保持单值形态也能让溢出路径使用8字节类型
        value = builder_.emit(MOP_F32_TO_GPR64, TY_I64, value);
      }

      bool inRegister = false;
      if (value->getType() == TY_F32 && !vararg) {
        if (fpr < FPR_ARG_N) {
          callArguments.push_back(value);
          ++fpr;
          inRegister = true;
        } else if (gpr < GPR_ARG_N) {
          callArguments.push_back(builder_.emit(MOP_FMV_X_W, TY_I32, value));
          ++gpr;
          inRegister = true;
        }
      } else if (gpr < GPR_ARG_N) {
        callArguments.push_back(value);
        ++gpr;
        inRegister = true;
      }

      if (!inRegister) {
        const OpCode store = value->getType() == TY_F32 ? MOP_FSW : MOP_SD;
        const i32 offset = static_cast<i32>(stackWords * 8);
        Inst *stackPointer = function_->module->physicalRegister(SP);
        if (rv64::fitsImm12(offset)) {
          Inst *storeInst = builder_.emit(store, TY_VOID, stackPointer, value);
          storeInst->setImm(offset);
        } else {
          // 出参区可能超过2 KiB 它不是FrameSlot 必须在Lowering时直接展开地址
          // 不能等待frame伪指令修正
          Inst *wideOffset = builder_.emit(MOP_LI, TY_I64);
          wideOffset->setImm64(offset);
          Inst *address =
              builder_.emit(MOP_ADD, TY_PTR, stackPointer, wideOffset);
          Inst *storeInst = builder_.emit(store, TY_VOID, address, value);
          storeInst->setImm(0);
        }
        ++stackWords;
      }
    }
    function_->maxCallArgStack =
        std::max(function_->maxCallArgStack, static_cast<i32>(stackWords * 8));
    Inst *call =
        builder_.emitN(MOP_CALL, TY_VOID,
                       callArguments.empty() ? nullptr : callArguments.data(),
                       static_cast<u32>(callArguments.size()));
    call->setCallee(callee);
    function_->isLeaf = false;
    if (instruction->getType() != TY_VOID) {
      Inst *result =
          instruction->getType() == TY_F32
              ? builder_.emit(MOP_FCOPY, TY_F32,
                              function_->module->physicalRegister(FA0))
              : builder_.emit(MOP_COPY,
                              instruction->getType() == TY_PTR ? TY_PTR
                                                               : TY_I32,
                              function_->module->physicalRegister(A0));
      annotateLoweredScalarFacts(result, facts, OP_CALL, result->getOp());
      replaceAllUsesWith(function_, instruction, result);
    }
    instruction->eraseFromBlock();
  }

  struct MemoryAddress {
    Inst *base = nullptr;
    i32 offset = 0;
  };

  MemoryAddress selectMemoryAddress(Inst *address, Inst *before) {
    MemoryAddress selected{materialize(address, before), 0};
    while (selected.base && selected.base->getOp() == MOP_ADDI &&
           selected.base->getType() == TY_PTR) {
      const i64 combined = static_cast<i64>(selected.offset) +
                           static_cast<i64>(selected.base->getImm());
      if (!rv64::fitsImm12(combined))
        break;
      selected.offset = static_cast<i32>(combined);
      selected.base = selected.base->getArg(0);
    }
    return selected;
  }

  static bool isIntegerConstant(Inst *value, i32 &constant) {
    if (!value || (value->getOp() != OP_ICONST && value->getOp() != MOP_LI))
      return false;
    constant = value->getImm();
    return true;
  }

  void lowerInstruction(Inst *instruction) {
    if (!instruction || instruction->isMachine() ||
        instruction->getOp() == OP_PHI)
      return;
    // 原地替换会保留旧指针 重新发射的指令则必须显式继承当前LIR源码位置
    builder_.setCurrentSourceLocation(instruction->sourceLocation);
    const OpCode op = instruction->getOp();
    const ScalarFactBundle oldFacts = computeStableScalarFacts(instruction);
    switch (op) {
    case OP_FADD:
      builder_.replaceInPlace(instruction, MOP_FADD_S, TY_F32,
                              arg(instruction, 0), arg(instruction, 1));
      return;
    case OP_FSUB:
      builder_.replaceInPlace(instruction, MOP_FSUB_S, TY_F32,
                              arg(instruction, 0), arg(instruction, 1));
      return;
    case OP_FMUL:
      builder_.replaceInPlace(instruction, MOP_FMUL_S, TY_F32,
                              arg(instruction, 0), arg(instruction, 1));
      return;
    case OP_FDIV:
      builder_.replaceInPlace(instruction, MOP_FDIV_S, TY_F32,
                              arg(instruction, 0), arg(instruction, 1));
      return;
    case OP_FNEG:
      builder_.replaceInPlace(instruction, MOP_FNEG_S, TY_F32,
                              arg(instruction, 0));
      return;
    case OP_I2F:
      builder_.replaceInPlace(instruction, MOP_FCVT_S_W, TY_F32,
                              arg(instruction, 0));
      return;
    case OP_F2I:
      builder_.replaceInPlace(instruction, MOP_FCVT_W_S, TY_I32,
                              arg(instruction, 0));
      return;
    case OP_NEG:
      builder_.replaceInPlace(instruction, MOP_NEGW, TY_I32,
                              arg(instruction, 0));
      return;
    case OP_ADD:
    case OP_SUB: {
      Inst *left = arg(instruction, 0);
      Inst *rightOriginal = instruction->getArg(1);
      if (rightOriginal && (rightOriginal->getOp() == OP_ICONST ||
                            rightOriginal->getOp() == MOP_LI)) {
        const i32 value = rightOriginal->getImm();
        const i64 immediate = op == OP_ADD ? value : -static_cast<i64>(value);
        if (immediate >= -2048 && immediate <= 2047) {
          builder_.setInsertBefore(instruction);
          Inst *result = builder_.emit(MOP_ADDIW, TY_I32, left);
          result->setImm(static_cast<i32>(immediate));
          annotateLoweredScalarFacts(result, oldFacts, op, result->getOp());
          replaceAllUsesWith(function_, instruction, result);
          instruction->eraseFromBlock();
          return;
        }
      }
      builder_.replaceInPlace(instruction, op == OP_ADD ? MOP_ADDW : MOP_SUBW,
                              TY_I32, left, arg(instruction, 1));
      return;
    }
    case OP_MUL:
      builder_.replaceInPlace(instruction, MOP_MULW, TY_I32,
                              arg(instruction, 0), arg(instruction, 1));
      return;
    case OP_DIV:
      builder_.replaceInPlace(instruction, MOP_DIVW, TY_I32,
                              arg(instruction, 0), arg(instruction, 1));
      return;
    case OP_MOD:
      builder_.replaceInPlace(instruction, MOP_REMW, TY_I32,
                              arg(instruction, 0), arg(instruction, 1));
      return;
    case OP_EQ:
    case OP_NE:
    case OP_LT:
    case OP_LE:
    case OP_GT:
    case OP_GE: {
      Inst *leftOriginal = instruction->getArg(0);
      Inst *rightOriginal = instruction->getArg(1);
      i32 leftConstant = 0;
      i32 rightConstant = 0;
      const bool leftIsConstant = isIntegerConstant(leftOriginal, leftConstant);
      const bool rightIsConstant =
          isIntegerConstant(rightOriginal, rightConstant);
      if ((op == OP_EQ || op == OP_NE) && leftIsConstant && !rightIsConstant) {
        std::swap(leftOriginal, rightOriginal);
      }
      Inst *left = materialize(leftOriginal, instruction);
      Inst *right = nullptr;
      builder_.setInsertBefore(instruction);
      Inst *result = nullptr;
      i32 immediate = 0;
      const bool rightIsImmediate = isIntegerConstant(rightOriginal, immediate);
      if ((op == OP_EQ || op == OP_NE) && rightIsImmediate) {
        Inst *lhs = left;
        if (immediate == 0) {
          result =
              builder_.emit(op == OP_EQ ? MOP_SEQZ : MOP_SNEZ, TY_I32, lhs);
        } else if (rv64::fitsImm12(immediate)) {
          Inst *difference = builder_.emit(MOP_XORI, TY_I32, lhs);
          difference->setImm(immediate);
          result = builder_.emit(op == OP_EQ ? MOP_SEQZ : MOP_SNEZ, TY_I32,
                                 difference);
        }
      }
      if (!result && op == OP_LT) {
        right = arg(instruction, 1);
        result = builder_.emit(MOP_SLT, TY_I32, left, right);
      } else if (!result && op == OP_GT) {
        right = arg(instruction, 1);
        result = builder_.emit(MOP_SLT, TY_I32, right, left);
      } else if (!result && (op == OP_EQ || op == OP_NE)) {
        right = arg(instruction, 1);
        Inst *difference = builder_.emit(MOP_SUBW, TY_I32, left, right);
        result = builder_.emit(op == OP_EQ ? MOP_SEQZ : MOP_SNEZ, TY_I32,
                               difference);
      } else if (!result) {
        right = arg(instruction, 1);
        Inst *less = builder_.emit(MOP_SLT, TY_I32, op == OP_LE ? right : left,
                                   op == OP_LE ? left : right);
        result = builder_.emit(MOP_SEQZ, TY_I32, less);
      }
      annotateLoweredScalarFacts(result, oldFacts, op, result->getOp());
      replaceAllUsesWith(function_, instruction, result);
      instruction->eraseFromBlock();
      return;
    }
    case OP_FEQ:
      builder_.replaceInPlace(instruction, MOP_FEQ_S, TY_I32,
                              arg(instruction, 0), arg(instruction, 1));
      annotateLoweredScalarFacts(instruction, oldFacts, op,
                                 instruction->getOp());
      return;
    case OP_FNE: {
      builder_.setInsertBefore(instruction);
      Inst *equal = builder_.emit(MOP_FEQ_S, TY_I32, arg(instruction, 0),
                                  arg(instruction, 1));
      Inst *result = builder_.emit(MOP_SEQZ, TY_I32, equal);
      annotateLoweredScalarFacts(result, oldFacts, op, result->getOp());
      replaceAllUsesWith(function_, instruction, result);
      instruction->eraseFromBlock();
      return;
    }
    case OP_FLT:
      builder_.replaceInPlace(instruction, MOP_FLT_S, TY_I32,
                              arg(instruction, 0), arg(instruction, 1));
      annotateLoweredScalarFacts(instruction, oldFacts, op,
                                 instruction->getOp());
      return;
    case OP_FLE:
      builder_.replaceInPlace(instruction, MOP_FLE_S, TY_I32,
                              arg(instruction, 0), arg(instruction, 1));
      annotateLoweredScalarFacts(instruction, oldFacts, op,
                                 instruction->getOp());
      return;
    case OP_FGT:
      builder_.replaceInPlace(instruction, MOP_FLT_S, TY_I32,
                              arg(instruction, 1), arg(instruction, 0));
      annotateLoweredScalarFacts(instruction, oldFacts, op,
                                 instruction->getOp());
      return;
    case OP_FGE:
      builder_.replaceInPlace(instruction, MOP_FLE_S, TY_I32,
                              arg(instruction, 1), arg(instruction, 0));
      annotateLoweredScalarFacts(instruction, oldFacts, op,
                                 instruction->getOp());
      return;
    case OP_ZEXT:
      builder_.setInsertBefore(instruction);
      {
        Inst *result = builder_.emit(MOP_ANDI, TY_I32, arg(instruction, 0));
        result->setImm(1);
        annotateLoweredScalarFacts(result, oldFacts, op, result->getOp());
        replaceAllUsesWith(function_, instruction, result);
      }
      instruction->eraseFromBlock();
      return;
    case OP_LNOT:
      builder_.setInsertBefore(instruction);
      {
        Inst *result = builder_.emit(MOP_SEQZ, TY_I32, arg(instruction, 0));
        annotateLoweredScalarFacts(result, oldFacts, op, result->getOp());
        replaceAllUsesWith(function_, instruction, result);
      }
      instruction->eraseFromBlock();
      return;
    case OP_ICONST: {
      const i32 value = instruction->getImm();
      builder_.replaceInPlace(instruction, MOP_LI, instruction->getType());
      instruction->setImm(value);
      annotateLoweredScalarFacts(instruction, oldFacts, op,
                                 instruction->getOp());
    }
      return;
    case OP_FCONST: {
      builder_.setInsertBefore(instruction);
      u32 bits = 0;
      f32 number = instruction->getFimm();
      std::memcpy(&bits, &number, sizeof(bits));
      Inst *li = builder_.emit(MOP_LI, TY_I32);
      li->setImm(i32FromBits(bits));
      Inst *result = builder_.emit(MOP_FMV_W_X, TY_F32, li);
      replaceAllUsesWith(function_, instruction, result);
      instruction->eraseFromBlock();
      return;
    }
    case OP_GETGLOBAL: {
      Inst *result = materialize(instruction, instruction);
      replaceAllUsesWith(function_, instruction, result);
      instruction->eraseFromBlock();
      return;
    }
    case OP_LOAD: {
      const IRType type = instruction->getMem().elementType;
      const OpCode load = type == TY_F32                       ? MOP_FLW
                          : (type == TY_PTR || type == TY_I64) ? MOP_LD
                                                               : MOP_LW;
      const MemoryAddress address =
          selectMemoryAddress(instruction->getArg(0), instruction);
      // 地址物化可能临时向入口插入LA 必须在其完成后重新锚定使用点
      // 否则恢复旧游标会把访存插到入口LA之前破坏支配关系
      builder_.setInsertBefore(instruction);
      Inst *result = builder_.emit(load, type, address.base);
      result->setImm(address.offset);
      replaceAllUsesWith(function_, instruction, result);
      instruction->eraseFromBlock();
      return;
    }
    case OP_STORE: {
      const IRType type = instruction->getMem().elementType;
      const OpCode store = type == TY_F32                       ? MOP_FSW
                           : (type == TY_PTR || type == TY_I64) ? MOP_SD
                                                                : MOP_SW;
      const MemoryAddress address =
          selectMemoryAddress(instruction->getArg(0), instruction);
      Inst *value = arg(instruction, 1);
      // 地址或待写值都可能在入口物化全局地址 最终访存必须重新定位到原使用点
      builder_.setInsertBefore(instruction);
      Inst *result = builder_.emit(store, TY_VOID, address.base, value);
      result->setImm(address.offset);
      instruction->eraseFromBlock();
      return;
    }
    case OP_GETPTR: {
      const i32 stride = instruction->getStride();
      Inst *base = arg(instruction, 0);
      Inst *index = instruction->getArg(1);
      builder_.setInsertBefore(instruction);
      if ((index->getOp() == OP_ICONST || index->getOp() == MOP_LI) &&
          rv64::fitsImm12(static_cast<i64>(index->getImm()) * stride)) {
        Inst *result = builder_.emit(MOP_ADDI, TY_PTR, base);
        result->setImm(
            static_cast<i32>(static_cast<i64>(index->getImm()) * stride));
        replaceAllUsesWith(function_, instruction, result);
        instruction->eraseFromBlock();
        return;
      }
      Inst *wideIndex =
          builder_.emit(MOP_SEXT_W, TY_I64, materialize(index, instruction));
      Inst *offset = wideIndex;
      if (stride != 1) {
        if (stride > 0 && (stride & (stride - 1)) == 0) {
          offset = builder_.emit(MOP_SLLI, TY_I64, wideIndex);
          offset->setImm(
              static_cast<i32>(__builtin_ctz(static_cast<u32>(stride))));
        } else {
          Inst *scale = builder_.emit(MOP_LI, TY_I64);
          scale->setImm64(stride);
          offset = builder_.emit(MOP_MUL, TY_I64, wideIndex, scale);
        }
      }
      Inst *result = builder_.emit(MOP_ADD, TY_PTR, base, offset);
      replaceAllUsesWith(function_, instruction, result);
      instruction->eraseFromBlock();
      return;
    }
    case OP_ALLOCA: {
      const MemPayload &memory = instruction->getMem();
      const i32 slot = function_->newFrameSlot(
          static_cast<i32>(memory.totalSizeBytes),
          std::max<i32>(1, typeSizeBytes(memory.elementType)),
          Function::FrameSlot::Kind::Local);
      builder_.setInsertBefore(instruction);
      Inst *result = builder_.emit(MOP_ADDI_FRAME, TY_PTR,
                                   function_->module->physicalRegister(SP));
      result->setFrameIndex(slot);
      replaceAllUsesWith(function_, instruction, result);
      instruction->eraseFromBlock();
      return;
    }
    case OP_CALL:
      lowerCall(instruction, oldFacts);
      return;
    case OP_BR:
      lowerBranch(instruction);
      return;
    case OP_JMP: {
      BasicBlock *target = instruction->getJumpTarget();
      builder_.replaceInPlace(instruction, MOP_J, TY_VOID);
      CFGEditor::rewriteJumpTarget(instruction->parentBlock(), target);
      return;
    }
    case OP_RET:
      if (instruction->getOperandCount())
        builder_.replaceInPlace(instruction, MOP_RET, TY_VOID,
                                arg(instruction, 0));
      else
        builder_.replaceInPlace(instruction, MOP_RET, TY_VOID);
      return;
    case OP_SELECT: {
      Inst *condition = arg(instruction, 0);
      Inst *trueOriginal = instruction->getArg(1);
      Inst *falseOriginal = instruction->getArg(2);
      i32 trueConstant = 0;
      i32 falseConstant = 0;
      const bool trueIsConstant = isIntegerConstant(trueOriginal, trueConstant);
      const bool falseIsConstant =
          isIntegerConstant(falseOriginal, falseConstant);
      builder_.setInsertBefore(instruction);
      Inst *result = nullptr;
      if (trueIsConstant && falseIsConstant && trueConstant == 1 &&
          falseConstant == 0) {
        result = condition;
      } else if (trueIsConstant && falseIsConstant && trueConstant == 0 &&
                 falseConstant == 1) {
        result = builder_.emit(MOP_SEQZ, TY_I32, condition);
      } else if (instruction->getType() == TY_I1 && falseIsConstant &&
                 falseConstant == 0) {
        result = builder_.emit(MOP_AND, TY_I32, condition, arg(instruction, 1));
      } else if (instruction->getType() == TY_I1 && trueIsConstant &&
                 trueConstant == 1) {
        result = builder_.emit(MOP_OR, TY_I32, condition, arg(instruction, 2));
      } else if (instruction->getType() == TY_I1 && falseIsConstant &&
                 falseConstant == 1) {
        Inst *inverse = builder_.emit(MOP_SEQZ, TY_I32, condition);
        result = builder_.emit(MOP_OR, TY_I32, inverse, arg(instruction, 1));
      } else if (instruction->getType() == TY_I1 && trueIsConstant &&
                 trueConstant == 0) {
        Inst *inverse = builder_.emit(MOP_SEQZ, TY_I32, condition);
        result = builder_.emit(MOP_AND, TY_I32, inverse, arg(instruction, 2));
      } else if (falseIsConstant && falseConstant == 0) {
        Inst *mask = builder_.emit(MOP_NEGW, TY_I32, condition);
        result = builder_.emit(MOP_AND, TY_I32, arg(instruction, 1), mask);
      } else if (trueIsConstant && trueConstant == 0) {
        Inst *mask = builder_.emit(MOP_NEGW, TY_I32, condition);
        Inst *inverse = builder_.emit(MOP_XORI, TY_I32, mask);
        inverse->setImm(-1);
        result = builder_.emit(MOP_AND, TY_I32, arg(instruction, 2), inverse);
      } else {
        Inst *trueValue = arg(instruction, 1);
        Inst *falseValue = arg(instruction, 2);
        Inst *mask = builder_.emit(MOP_NEGW, TY_I32, condition);
        Inst *inverse = builder_.emit(MOP_XORI, TY_I32, mask);
        inverse->setImm(-1);
        Inst *left = builder_.emit(MOP_AND, TY_I32, trueValue, mask);
        Inst *right = builder_.emit(MOP_AND, TY_I32, falseValue, inverse);
        result = builder_.emit(MOP_OR, instruction->getType(), left, right);
      }
      replaceAllUsesWith(function_, instruction, result);
      instruction->eraseFromBlock();
      return;
    }
    case OP_SWITCH:
      if (!lowerSwitchToRV64(function_, instruction, arg(instruction, 0)))
        failed_ = true;
      return;
    case OP_UNREACHABLE:
      builder_.replaceInPlace(instruction, MOP_RET, TY_VOID);
      return;
    default:
      failed_ = true;
      return;
    }
  }

  Function *function_ = nullptr;
  IRBuilder builder_;
  Inst *entryCursor_ = nullptr; // 入口参数绑定及全局地址物化游标
  const SCEV *scev_ = nullptr;
  bool failed_ = false;
};

} // namespace

std::string_view LowerToRV64Pass::name() const noexcept {
  return "lower-to-rv64";
}

PassResult LowerToRV64Pass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || !function->region ||
      !function->region->first)
    return PassResult::noChange();
  if (function->phase != IRPhase::LIR)
    return PassResult::noChange();
  const SCEV *scev = nullptr;
  if (computePreds(function)) {
    context.functionAnalyses().clear(function);
    scev = &context.get<SCEVAnalysis>(function).info;
  }
  function->phase = IRPhase::MIR;
  function->mirPhase = MIRPhase::SSA;
  Lowering lowering(function, scev);
  const bool ok = lowering.run();
  if (ok)
    MachineDCE(function);
  return ok ? PassResult::changedIR() : PassResult::noChange();
}

} // namespace svm::ir
