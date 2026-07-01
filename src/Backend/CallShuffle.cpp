#include "IR.h"

#include "MIRPass.h"
#include "MoveInfo.h"
#include "RV64.h"

#include <cassert>
#include <vector>

namespace svm::ir {
namespace {

struct CallShuffleMove {
  u32 source = 0;        // 当前实参物理寄存器
  u32 destination = 0;   // 调用约定要求的参数寄存器
  bool floating = false; // 是否使用浮点寄存器搬运
};

void emitPhysicalMove(IRBuilder &builder, Function *function,
                      const CallShuffleMove &move) {
  Inst *source = function->module->physicalRegister(move.source);
  Inst *copy = builder.emit(move.floating ? MOP_FCOPY : MOP_COPY,
                            move.floating ? TY_F32 : TY_I64, source);
  copy->id = move.destination;
}

void emitParallelMoves(IRBuilder &builder, Function *function,
                       std::vector<CallShuffleMove> &moves) {
  while (!moves.empty()) {
    bool progressed = false;
    for (usize index = 0; index < moves.size();) {
      bool destinationStillNeeded = false;
      for (usize other = 0; other < moves.size(); ++other)
        if (other != index && moves[other].source == moves[index].destination) {
          destinationStillNeeded = true;
          break;
        }
      if (destinationStillNeeded) {
        ++index;
        continue;
      }
      emitPhysicalMove(builder, function, moves[index]);
      moves.erase(moves.begin() + static_cast<isize>(index));
      progressed = true;
    }

    if (!progressed) {
      // 所有剩余搬运均在环中 先把一个源保存到该寄存器类的保留临时寄存器
      CallShuffleMove &cycle = moves.front();
      const u32 scratch =
          cycle.floating ? rv64::RESERVED_FPR_TMP : rv64::RESERVED_TMP;
      emitPhysicalMove(builder, function,
                       {cycle.source, scratch, cycle.floating});
      cycle.source = scratch;
    }
  }
}

bool lowerEntryArgumentCopies(Function *function, IRBuilder &builder) {
  BasicBlock *entry = function->region->first;
  std::vector<Inst *> originals;
  std::vector<CallShuffleMove> moves;
  for (Inst *inst = entry->firstInst(); inst; inst = inst->next()) {
    const MoveInfo info = queryMoveInfo(function, inst);
    if (info.kind != MoveKind::ArgCopy)
      continue;
    Inst *source = inst->getArg(0);
    assert(source && source->isPrecoloredDef());
    assert(source->id < rv64::kRegisterCount &&
           inst->id < rv64::kRegisterCount);
    originals.push_back(inst);
    if (source->id != inst->id)
      moves.push_back({source->id, inst->id, inst->getType() == TY_F32});
  }
  if (originals.empty())
    return false;

  builder.setInsertBefore(originals.front());
  builder.setCurrentSourceLocation(originals.front()->sourceLocation);
  emitParallelMoves(builder, function, moves);
  for (Inst *inst : originals)
    inst->eraseFromBlock();
  return true;
}

bool expandVarargPromotions(Function *function, IRBuilder &builder) {
  bool changed = false;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if (inst->getOp() != MOP_F32_TO_GPR64)
        continue;
      Inst *source = inst->getArg(0);
      assert(source && source->id < rv64::kRegisterCount);
      assert(inst->id < rv64::kRegisterCount &&
             rv64::isGPR(static_cast<rv64::PReg>(inst->id)));

      builder.setInsertBefore(inst);
      builder.setCurrentSourceLocation(inst->sourceLocation);
      Inst *convert = builder.emit(MOP_FCVT_D_S, TY_F64, source);
      convert->id = rv64::RESERVED_FPR_TMP;
      builder.replaceInPlace(
          inst, MOP_FMV_X_D, TY_I64,
          function->module->physicalRegister(rv64::RESERVED_FPR_TMP));
      changed = true;
    }
  }
  return changed;
}

void lowerCallShufflesPostRA(Function *function) {
  IRBuilder builder(function->module, function);
  UNUSED(lowerEntryArgumentCopies(function, builder));
  UNUSED(expandVarargPromotions(function, builder));
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *call = block->firstInst(); call;) {
      Inst *next = call->next();
      if (call->getOp() != MOP_CALL || call->getOperandCount() == 0) {
        call = next;
        continue;
      }

      std::vector<CallShuffleMove> moves;
      u32 gprIndex = 0;
      u32 fprIndex = 0;
      for (u32 index = 0; index < call->getOperandCount(); ++index) {
        Inst *argument = call->getArg(index);
        assert(argument && argument->id < rv64::kRegisterCount);
        const bool floating = argument->getType() == TY_F32;
        assert((floating && fprIndex < rv64::kArgumentRegisterCount) ||
               (!floating && gprIndex < rv64::kArgumentRegisterCount));
        const u32 destination =
            floating ? rv64::FPR_ARG[fprIndex++] : rv64::GPR_ARG[gprIndex++];
        if (argument->id != destination)
          moves.push_back({argument->id, destination, floating});
      }

      builder.setInsertBefore(call);
      builder.setCurrentSourceLocation(call->sourceLocation);
      emitParallelMoves(builder, function, moves);

      Function *callee = call->getCallee();
      const u64 mask = call->getRegMask();
      builder.replaceInPlace(call, MOP_CALL, TY_VOID);
      call->setCallee(callee);
      call->setRegMask(mask);
      call = next;
    }
  }
  function->mirPhase = MIRPhase::Emittable;
  return;
}

} // namespace

std::string_view LowerCallShufflesPass::name() const noexcept {
  return "lower-call-shuffles";
}

PassResult LowerCallShufflesPass::run(Function *function, PassContext &) {
  if (!function || function->isExtern || !function->region ||
      !function->region->first || function->phase != IRPhase::MIR ||
      function->mirPhase != MIRPhase::PostRegAlloc)
    return PassResult::noChange();

  lowerCallShufflesPostRA(function);
  return PassResult::changedIR(); // 阶段转换也是 IR 状态变化
}

} // namespace svm::ir
