#include "IR.h"
#include "MIRPass.h"
#include "MoveInfo.h"
#include "RV64.h"
#include "VReg.h"

#include <cassert>
#include <cstring>
#include <vector>

namespace svm::ir {
namespace {

struct ParallelCopy {
  Inst *destination = nullptr; // Phi结果的稳定VReg身份
  Inst *source = nullptr;      // 当前前驱边上的输入值
};

Inst *materialize(Inst *source, IRBuilder &builder, Function *function) {
  assert(source && function);
  if (source->parentBlock() || source->isPrecoloredDef())
    return source;

  if (source->isUndefValue()) {
    assert(source->getType() != TY_F64);
    Inst *zero = builder.emit(
        MOP_LI, source->getType() == TY_F32 ? TY_I32 : source->getType());
    zero->setImm(0);
    assignNewVReg(zero, function);
    if (zero->getType() == TY_I32)
      attachFactBundle(
          function, zero,
          ScalarFactBundle::fromConstant(0, FactSource::LoweringSemantic));
    if (source->getType() != TY_F32)
      return zero;
    Inst *value = builder.emit(MOP_FMV_W_X, TY_F32, zero);
    assignNewVReg(value, function);
    return value;
  }

  switch (source->getOp()) {
  case OP_ICONST:
  case MOP_LI: {
    Inst *value = builder.emit(MOP_LI, source->getType());
    if (source->getOp() == MOP_LI)
      value->setImm64(source->getImm64());
    else
      value->setImm(source->getImm());
    assignNewVReg(value, function);
    if (value->getType() == TY_I32) {
      const i32 constant = source->getOp() == MOP_LI
                               ? i32TruncWrap(source->getImm64())
                               : source->getImm();
      attachFactBundle(function, value,
                       ScalarFactBundle::fromConstant(
                           constant, FactSource::LoweringSemantic));
    }
    return value;
  }
  case OP_FCONST: {
    u32 bits = 0;
    const f32 number = source->getFimm();
    std::memcpy(&bits, &number, sizeof(bits));
    Inst *payload = builder.emit(MOP_LI, TY_I32);
    payload->setImm(i32FromBits(bits));
    assignNewVReg(payload, function);
    attachFactBundle(function, payload,
                     ScalarFactBundle::fromConstant(
                         i32FromBits(bits), FactSource::LoweringSemantic));
    Inst *value = builder.emit(MOP_FMV_W_X, TY_F32, payload);
    assignNewVReg(value, function);
    return value;
  }
  case OP_GETGLOBAL: {
    Global *global = source->getGlobal();
    if (global && global->globalMergeMember) {
      Inst *base = builder.emit(MOP_LA, TY_PTR);
      base->setSymbolRef(SymbolRef::mergedBaseRef(global->globalMergeGroup));
      assignNewVReg(base, function);
      if (!global->globalMergeOffset)
        return base;
      assert(rv64::fitsImm12(global->globalMergeOffset));
      Inst *address = builder.emit(MOP_ADDI, TY_PTR, base);
      address->setImm(global->globalMergeOffset);
      assignNewVReg(address, function);
      return address;
    }
    Inst *address = builder.emit(MOP_LA, TY_PTR);
    address->setGlobal(global);
    assignNewVReg(address, function);
    return address;
  }
  case MOP_LA: {
    Inst *address = builder.emit(MOP_LA, TY_PTR);
    address->setSymbolRef(source->getSymbolRef());
    assignNewVReg(address, function);
    return address;
  }
  case OP_PHI:
    // 自循环incoming有意读取同一个浮空身份 生成的自拷贝是活跃性锚点
    // 只有寄存器分配完成后才能安全删除
    return source;
  default:
    assert(false && "Phi incoming不是可重物化值也不是MIR定义");
    return nullptr;
  }
}

Inst *emitCopy(const ParallelCopy &move, Inst *source, IRBuilder &builder,
               Function *function) {
  assert(move.destination && source);
  const OpCode opcode =
      move.destination->getType() == TY_F32 ? MOP_FCOPY : MOP_COPY;
  Inst *copy = builder.emit(opcode, move.destination->getType(), source);
  copy->id = move.destination->id;
  markMove(function, copy, MoveKind::PhiParallelCopy);
  cloneVRegMetadata(function, move.destination, copy, 0);
  const rv64::PReg forcedColor =
      queryVRegMetadata(function, move.destination).forcedColor;
  if (forcedColor < rv64::NUM_PREGS)
    setForcedColor(function, copy, forcedColor);
  return copy;
}

// 并行Phi赋值先发射目标不再被其他待处理拷贝读取的移动 剩余部分必然是环
// 用一个新的虚拟寄存器保存第一个源值 再旋转环即可实现交换而不覆盖原值
void emitParallelCopies(std::vector<ParallelCopy> &moves, IRBuilder &builder,
                        Function *function) {
  std::vector<bool> done(moves.size(), false);
  bool progress = true;
  while (progress) {
    progress = false;
    for (usize index = 0; index < moves.size(); ++index) {
      if (done[index])
        continue;
      bool blocked = false;
      for (usize other = 0; other < moves.size(); ++other) {
        if (other != index && !done[other] &&
            moves[other].source == moves[index].destination) {
          blocked = true;
          break;
        }
      }
      if (blocked)
        continue;
      emitCopy(moves[index],
               materialize(moves[index].source, builder, function), builder,
               function);
      done[index] = true;
      progress = true;
    }
  }

  for (usize first = 0; first < moves.size(); ++first) {
    if (done[first])
      continue;
    Inst *firstSource = materialize(moves[first].source, builder, function);
    const OpCode opcode =
        moves[first].destination->getType() == TY_F32 ? MOP_FCOPY : MOP_COPY;
    Inst *temporary =
        builder.emit(opcode, moves[first].destination->getType(), firstSource);
    markMove(function, temporary, MoveKind::PhiParallelCopy);
    assignNewVReg(temporary, function);
    cloneVRegMetadata(function, firstSource, temporary, 0);

    usize current = first;
    while (true) {
      done[current] = true;
      usize next = moves.size();
      for (usize candidate = 0; candidate < moves.size(); ++candidate) {
        if (!done[candidate] &&
            moves[candidate].destination == moves[current].source) {
          next = candidate;
          break;
        }
      }
      if (next == moves.size())
        break;
      emitCopy(moves[next], materialize(moves[next].source, builder, function),
               builder, function);
      current = next;
    }
    emitCopy(moves[first], temporary, builder, function);
  }
}

bool eliminatePhis(Function *function) {
  if (!function || function->isExtern || !function->region ||
      !function->region->first)
    return false;
  assert(function->phase == IRPhase::MIR &&
         function->mirPhase == MIRPhase::SSA);

  // DCE必须在拷贝共享Phi身份之前执行 之后的拷贝Inst有意不再建立直接Use节点
  // 而是通过摘下的Phi对象共享id 此时再做普通SSA DCE会误删定义
  MachineDCE(function);
  renumberVRegs(function);
  computePreds(function);

  // args[k]是保存incoming Inst*的InstRef包装 incoming[k]指出选择该值的CFG边
  // 关键边分裂可能重排这两个数组 因此后续查询必须按前驱块指针匹配
  // 不能假定前驱数组下标与Phi槽位下标一致
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (!block->firstPhi())
      continue;
    bool split = true;
    while (split) {
      split = false;
      for (u32 index = 0; index < block->getPredecessorCount(); ++index) {
        BasicBlock *predecessor = block->getPredecessor(index);
        if (successorCount(predecessor) <= 1 ||
            block->getPredecessorCount() <= 1)
          continue;
        BasicBlock *middle =
            CFGEditor::splitCriticalEdge(function, predecessor, block);
        if (!middle)
          return false;
        split = true;
        break;
      }
    }
  }

  IRBuilder builder(function->module, function);
  std::vector<Inst *> phis;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (!block->firstPhi())
      continue;
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      phis.push_back(phi);

    for (u32 index = 0; index < block->getPredecessorCount(); ++index) {
      BasicBlock *predecessor = block->getPredecessor(index);
      std::vector<ParallelCopy> moves;
      for (Inst *phi = block->firstPhi(); phi; phi = phi->next()) {
        Inst *incoming = CFGEditor::getPhiIncomingValue(phi, predecessor);
        assert(incoming && "Phi没有为CFG前驱提供的值");
        if (incoming->isUndefValue() || incoming == phi)
          incoming = phi;
        moves.push_back({phi, incoming});
      }
      assert(predecessor->endsWithTerminator());
      builder.setInsertBefore(predecessor->terminator());
      emitParallelCopies(moves, builder, function);
    }
  }

  // 摘下的Phi不再是指令流中的定义 但仍保留未擦除的Inst, type, id和uses
  // 每条边上的拷贝复用该id 这是当前IR表示离开SSA后多定义VReg的方式
  for (Inst *phi : phis)
    VERIFY(detachPhiAsVRegIdentity(phi));

  computeUses(function);
  renumberVRegs(function);
  function->mirPhase = MIRPhase::OutOfSSA;
  return true;
}

} // namespace

std::string_view EliminatePhisPass::name() const noexcept {
  return "eliminate-phis";
}

PassResult EliminatePhisPass::run(Function *function, PassContext &) {
  return eliminatePhis(function) ? PassResult::changedIR()
                                 : PassResult::noChange();
}

} // namespace svm::ir
