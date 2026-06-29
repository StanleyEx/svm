#include "IR.h"
#include "MIRPass.h"
#include "RV64.h"
#include "Utils.h"

#include <algorithm>
#include <cinttypes>
#include <cstdio>
#include <cstring>
#include <string_view>
#include <vector>

namespace svm::ir {
namespace {

class Emitter {
  FILE *output;

public:
  explicit Emitter(FILE *output) : output(output) {}

  template <typename... Args> void emit(const char *format, Args... args) {
    std::fprintf(output, format, args...);
  }
  void emit(const char *str) { std::fputs(str, output); }
  void emit(char c) { std::fputc(c, output); }

  const char *registerName(const Inst *inst) {
    VERIFY(inst != nullptr, "空寄存器操作数");
    VERIFY(inst->id < rv64::kRegisterCount, "未分配的虚拟寄存器到达发射器");
    return rv64::pregName(static_cast<rv64::PReg>(inst->id));
  }
  const char *functionName(const Function *function) {
    VERIFY(function != nullptr && function->name != nullptr);
    return function->name;
  }

  void emitLabel(const Function *function, const BasicBlock *block) {
    VERIFY(function != nullptr && block != nullptr);
    emit(".LBB_%s_%u", functionName(function), block->id);
  }

  void emitEpilogueLabel(const Function *function) {
    emit(".Lepilogue_%s", functionName(function));
  }

  void emitMergedGlobalLabel(u16 group) {
    emit(".L_MergedGlobals%u", static_cast<unsigned>(group));
  }
  void emitMergedGlobalBaseLabel(u16 group) {
    emit(".L_MergedGlobals%u_base", static_cast<unsigned>(group));
  }

  bool hasMachineReturn(const Function *function) {
    if (!function || !function->region)
      return false;
    for (BasicBlock *block = function->region->first; block;
         block = block->next())
      for (Inst *inst = block->firstInst(); inst; inst = inst->next())
        if (inst->getOp() == MOP_RET)
          return true;
    return false;
  }

  void checkEmittableMIR(const Function *function) {
    if (!function || function->isExtern || !function->region ||
        !function->region->first)
      return;

    VERIFY(function->phase == IRPhase::MIR);
    VERIFY(function->mirPhase == MIRPhase::Emittable);

    for (BasicBlock *block = function->region->first; block;
         block = block->next()) {
      VERIFY(block->firstPhi() == nullptr, "发射时还有 Phi");
      for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
        const OpCode op = inst->getOp();
        VERIFY(isMachineOp(op), "非MIR Op到达发射器");
        VERIFY(!isMachineFrameOp(op), "栈帧伪指令在修复前到达发射器");
        VERIFY(op != MOP_F32_TO_GPR64, "可变参数提升伪指令在展开前到达发射器");
        // 调用实参必须已经由CallShuffle展开成显式拷贝 发射器不重复实现ABI排布
        VERIFY(op != MOP_CALL || inst->getOperandCount() == 0,
               "调用操作数未被 call shuffle 降级");
        if (op == MOP_JT_DISPATCH)
          VERIFY(inst->getJumpTable() != nullptr);
        if (op == MOP_FCVT_D_S)
          // FCVT_D_S 类型防止后续spill/copy按32位处理结果
          VERIFY(inst->getType() == TY_F64, "fcvt.d.s 必须保留其 TY_F64 类型");
        if (!isVoid(inst->getType()) && op != MOP_NOP)
          VERIFY(inst->id < rv64::kRegisterCount,
                 "未分配的虚拟寄存器定义到达发射器");
        for (u32 index = 0; index < inst->getOperandCount(); ++index) {
          Inst *argument = inst->getArg(index);
          if (!argument || argument->isPrecoloredDef())
            continue;
          VERIFY(argument->id < rv64::kRegisterCount,
                 "未分配的虚拟寄存器操作数到达发射器");
        }
      }
    }
  }

  // 按 FrameLayout 约定发射序言 小栈帧直接以 sp 为基址 大栈帧先用 t0 保存旧 sp
  // 确保所有保存槽位仍可用 12 位有符号偏移访问
  static bool canUseSPRelativeFrame(i32 size) noexcept {
    return size > 0 && rv64::fitsImm12(-static_cast<i64>(size)) &&
           rv64::fitsImm12(static_cast<i64>(size) - 8);
  }

  void emitPrologue(const Function *function) {
    if (function->stackSize == 0)
      return;
    VERIFY(function->stackSize > 0);
    const i32 size = function->stackSize;

    if (canUseSPRelativeFrame(size)) {
      emit("\taddi\tsp, sp, %d\n", -size);
      i32 offset = size;
      for (u32 reg = 0; reg < rv64::kRegisterCount; ++reg) {
        if (!((function->calleeSaveMask >> reg) & u64{1}))
          continue;
        offset -= 8;
        if (reg < rv64::F0)
          emit("\tsd\t%s, %d(sp)\n",
               rv64::pregName(static_cast<rv64::PReg>(reg)), offset);
        else
          // RV64 ABI 要求完整保存 callee-save FPR
          emit("\tfsd\t%s, %d(sp)\n",
               rv64::pregName(static_cast<rv64::PReg>(reg)), offset);
      }
      if (!function->isLeaf) {
        offset -= 8;
        emit("\tsd\tra, %d(sp)\n", offset);
      }
      return;
    }

    emit("\tli\tt0, %d\n"
         "\tsub\tsp, sp, t0\n"
         "\tadd\tt0, sp, t0\n",
         size);

    i32 offset = 0;
    for (u32 reg = 0; reg < rv64::kRegisterCount; ++reg) {
      if (!((function->calleeSaveMask >> reg) & u64{1}))
        continue;
      offset -= 8;
      if (reg < rv64::F0)
        emit("\tsd\t%s, %d(t0)\n", rv64::pregName(static_cast<rv64::PReg>(reg)),
             offset);
      else
        // 大栈帧仍按 ABI 保存完整 FPR 这里只改变地址基址
        emit("\tfsd\t%s, %d(t0)\n",
             rv64::pregName(static_cast<rv64::PReg>(reg)), offset);
    }
    if (!function->isLeaf) {
      offset -= 8;
      emit("\tsd\tra, %d(t0)\n", offset);
    }
  }

  // 按与序言相反的顺序恢复 callee-save 寄存器
  // 大栈帧复用 t0 计算旧 sp, 最后用 mv 恢复 sp, 避免超出立即数范围
  void emitEpilogue(const Function *function) {
    if (function->stackSize == 0)
      return;
    VERIFY(function->stackSize > 0, "负的栈大小");
    const i32 size = function->stackSize;

    if (canUseSPRelativeFrame(size)) {
      i32 offset = size;
      for (u32 reg = 0; reg < rv64::kRegisterCount; ++reg) {
        if (!((function->calleeSaveMask >> reg) & u64{1}))
          continue;
        offset -= 8;
        if (reg < rv64::F0)
          emit("\tld\t%s, %d(sp)\n",
               rv64::pregName(static_cast<rv64::PReg>(reg)), offset);
        else
          // 与序言配对使用 fld, 保留 FPR 的 64 位值和 NaN-boxing 高位
          emit("\tfld\t%s, %d(sp)\n",
               rv64::pregName(static_cast<rv64::PReg>(reg)), offset);
      }
      if (!function->isLeaf) {
        offset -= 8;
        emit("\tld\tra, %d(sp)\n", offset);
      }
      if (rv64::fitsImm12(size)) {
        emit("\taddi\tsp, sp, %d\n", size);
      } else {
        // 2048 的负数和最高保存槽偏移都可编码, 正向恢复拆成两条 addi
        VERIFY(size == 2048, "sp 相对栈帧大小无效");
        emit("\taddi\tsp, sp, 1024\n"
             "\taddi\tsp, sp, 1024\n");
      }
      return;
    }

    emit("\tli\tt0, %d\n"
         "\tadd\tt0, sp, t0\n",
         size);
    i32 offset = 0;
    for (u32 reg = 0; reg < rv64::kRegisterCount; ++reg) {
      if (!((function->calleeSaveMask >> reg) & u64{1}))
        continue;
      offset -= 8;
      if (reg < rv64::F0)
        emit("\tld\t%s, %d(t0)\n", rv64::pregName(static_cast<rv64::PReg>(reg)),
             offset);
      else
        // 大栈帧恢复同样必须使用 fld, 不能用 32 位 flw 截断值
        emit("\tfld\t%s, %d(t0)\n",
             rv64::pregName(static_cast<rv64::PReg>(reg)), offset);
    }
    if (!function->isLeaf) {
      offset -= 8;
      emit("\tld\tra, %d(t0)\n", offset);
    }
    emit("\tmv\tsp, t0\n");
  }

  std::string_view sourceLine(const Module *module,
                              const SourceLocation *location) noexcept {
    if (!module || !module->sourceText || module->sourceLength == 0 ||
        !location || !location->isValid() ||
        location->offset >= module->sourceLength)
      return {};
    const std::string_view source(module->sourceText, module->sourceLength);
    usize begin = location->offset;
    while (begin > 0 && source[begin - 1] != '\n' && source[begin - 1] != '\r')
      --begin;
    usize end = location->offset;
    while (end < source.size() && source[end] != '\n' && source[end] != '\r')
      ++end;
    while (begin < end && (source[begin] == ' ' || source[begin] == '\t'))
      ++begin;
    while (end > begin && (source[end - 1] == ' ' || source[end - 1] == '\t'))
      --end;
    return source.substr(begin, end - begin);
  }

  void emitSourceComment(const Module *module, const Inst *inst,
                         u32 &lastSourceLine) {
    const SourceLocation *location = inst ? inst->sourceLocation : nullptr;
    if (!location || location->line == lastSourceLine)
      return;
    const std::string_view line = sourceLine(module, location);
    if (line.empty())
      return;
    emit("\t\t# ");
    std::fwrite(line.data(), 1, line.size(), output);
    emit('\n');
    lastSourceLine = location->line;
  }

  bool emitsInstructionText(const Inst *inst,
                            const BasicBlock *currentBlock) noexcept {
    if (inst->getOp() == MOP_NOP)
      return false;
    if (inst->getOp() == MOP_J)
      return inst->getJumpTarget() != currentBlock->next();
    if (inst->getOp() == MOP_RET) {
      bool needsCopy = false;
      if (inst->getOperandCount() != 0) {
        const Inst *value = inst->getArg(0);
        if (!value)
          return true;
        const u32 destination =
            value->getType() == TY_F32 ? rv64::FA0 : rv64::A0;
        needsCopy = value->id != destination;
      }
      return needsCopy || inst->next() || currentBlock->next();
    }
    return true;
  }

  // 单条机器指令只负责文本映射
  // ABI 归位, 栈帧伪指令和未分配 VReg 均必须完成
  void emitInstruction(const Function *function, const Inst *inst,
                       const BasicBlock *currentBlock) {
    const OpCode op = inst->getOp();
    const auto R = [&](const Inst *value) { return registerName(value); };

    switch (op) {
    case MOP_NOP:
      return;
    case MOP_ADDW:
      emit("\taddw\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_SUBW:
      emit("\tsubw\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_MULW:
      emit("\tmulw\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_DIVW:
      emit("\tdivw\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_REMW:
      emit("\tremw\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_ADD:
      emit("\tadd\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_SUB:
      emit("\tsub\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_MUL:
      emit("\tmul\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_AND:
      emit("\tand\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_OR:
      emit("\tor\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_XOR:
      emit("\txor\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_SLT:
      emit("\tslt\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_ADDIW:
      emit("\taddiw\t%s, %s, %d\n", R(inst), R(inst->getArg(0)),
           inst->getImm());
      return;
    case MOP_ADDI:
      emit("\taddi\t%s, %s, %d\n", R(inst), R(inst->getArg(0)), inst->getImm());
      return;
    case MOP_ANDI:
      emit("\tandi\t%s, %s, %d\n", R(inst), R(inst->getArg(0)), inst->getImm());
      return;
    case MOP_ORI:
      emit("\tori\t%s, %s, %d\n", R(inst), R(inst->getArg(0)), inst->getImm());
      return;
    case MOP_XORI:
      emit("\txori\t%s, %s, %d\n", R(inst), R(inst->getArg(0)), inst->getImm());
      return;
    case MOP_SLLIW:
      emit("\tslliw\t%s, %s, %d\n", R(inst), R(inst->getArg(0)),
           inst->getImm());
      return;
    case MOP_SRAIW:
      emit("\tsraiw\t%s, %s, %d\n", R(inst), R(inst->getArg(0)),
           inst->getImm());
      return;
    case MOP_SRLIW:
      emit("\tsrliw\t%s, %s, %d\n", R(inst), R(inst->getArg(0)),
           inst->getImm());
      return;
    case MOP_SLLI:
      emit("\tslli\t%s, %s, %d\n", R(inst), R(inst->getArg(0)), inst->getImm());
      return;
    case MOP_SRAI:
      emit("\tsrai\t%s, %s, %d\n", R(inst), R(inst->getArg(0)), inst->getImm());
      return;
    case MOP_SRLI:
      emit("\tsrli\t%s, %s, %d\n", R(inst), R(inst->getArg(0)), inst->getImm());
      return;
    case MOP_NEGW:
      emit("\tsubw\t%s, zero, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_SEQZ:
      emit("\tseqz\t%s, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_SNEZ:
      emit("\tsnez\t%s, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_SEXT_W:
      emit("\tsext.w\t%s, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_LUI:
      emit("\tlui\t%s, %d\n", R(inst), inst->getImm());
      return;
    case MOP_LI:
      emit("\tli\t%s, %" PRId64 "\n", R(inst), inst->getImm64());
      return;
    case MOP_LA: {
      const SymbolRef symbol = inst->getSymbolRef();
      emit("\tla\t%s, ", R(inst));
      switch (symbol.kind) {
      case SymbolRef::SymbolRefKind::Global:
        VERIFY(symbol.global != nullptr && symbol.global->name != nullptr);
        emit(symbol.global->name);
        break;
      case SymbolRef::SymbolRefKind::MergedBase:
        emitMergedGlobalBaseLabel(symbol.mergedGroup);
        break;
      case SymbolRef::SymbolRefKind::JumpTable:
        VERIFY(symbol.jumpTable != nullptr &&
               symbol.jumpTable->label != nullptr);
        emit(symbol.jumpTable->label);
        break;
      case SymbolRef::SymbolRefKind::None:
        VERIFY(false);
      }
      emit('\n');
      return;
    }
    case MOP_JT_DISPATCH:
      emit("\tjr\t%s\n", R(inst->getArg(0)));
      return;
    case MOP_LW:
      emit("\tlw\t%s, %d(%s)\n", R(inst), inst->getImm(), R(inst->getArg(0)));
      return;
    case MOP_LD:
      emit("\tld\t%s, %d(%s)\n", R(inst), inst->getImm(), R(inst->getArg(0)));
      return;
    case MOP_SW:
      emit("\tsw\t%s, %d(%s)\n", R(inst->getArg(1)), inst->getImm(),
           R(inst->getArg(0)));
      return;
    case MOP_SD:
      emit("\tsd\t%s, %d(%s)\n", R(inst->getArg(1)), inst->getImm(),
           R(inst->getArg(0)));
      return;
    case MOP_FLW:
      emit("\tflw\t%s, %d(%s)\n", R(inst), inst->getImm(), R(inst->getArg(0)));
      return;
    case MOP_FSW:
      emit("\tfsw\t%s, %d(%s)\n", R(inst->getArg(1)), inst->getImm(),
           R(inst->getArg(0)));
      return;
    case MOP_FLD:
      emit("\tfld\t%s, %d(%s)\n", R(inst), inst->getImm(), R(inst->getArg(0)));
      return;
    case MOP_FSD:
      emit("\tfsd\t%s, %d(%s)\n", R(inst->getArg(1)), inst->getImm(),
           R(inst->getArg(0)));
      return;
    case MOP_COPY:
      emit("\tmv\t%s, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_FCOPY:
      emit("%s%s, %s\n", inst->getType() == TY_F64 ? "\tfmv.d\t" : "\tfmv.s\t",
           R(inst), R(inst->getArg(0)));
      return;
    case MOP_FADD_S:
      emit("\tfadd.s\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_FSUB_S:
      emit("\tfsub.s\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_FMUL_S:
      emit("\tfmul.s\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_FDIV_S:
      emit("\tfdiv.s\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_FNEG_S:
      emit("\tfneg.s\t%s, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_FMV_W_X:
      emit("\tfmv.w.x\t%s, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_FMV_X_W:
      emit("\tfmv.x.w\t%s, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_FCVT_S_W:
      emit("\tfcvt.s.w\t%s, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_FCVT_W_S:
      emit("\tfcvt.w.s\t%s, %s, rtz\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_FCVT_D_S:
      // 结果保留 TY_F64, 后续 vararg 归位依赖完整 64 位 FPR
      emit("\tfcvt.d.s\t%s, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_FMV_X_D:
      emit("\tfmv.x.d\t%s, %s\n", R(inst), R(inst->getArg(0)));
      return;
    case MOP_FEQ_S:
      emit("\tfeq.s\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_FLT_S:
      emit("\tflt.s\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_FLE_S:
      emit("\tfle.s\t%s, %s, %s\n", R(inst), R(inst->getArg(0)),
           R(inst->getArg(1)));
      return;
    case MOP_J:
      // 顺序布局的无条件跳转无需发射, 避免产生多余的 jal x0
      if (inst->getJumpTarget() == currentBlock->next())
        return;
      emit("\tj\t");
      emitLabel(function, inst->getJumpTarget());
      emit('\n');
      return;
    case MOP_BEQ:
    case MOP_BNE:
    case MOP_BLT:
    case MOP_BGE:
    case MOP_BLTU:
    case MOP_BGTU: {
      static constexpr const char *names[] = {"beq", "bne",  "blt",
                                              "bge", "bltu", "bgtu"};
      static constexpr const char *invertedNames[] = {"bne", "beq",  "bge",
                                                      "blt", "bgeu", "bgeu"};
      const u16 raw = static_cast<u16>(op);
      const u16 first = static_cast<u16>(MOP_BEQ);
      VERIFY(raw >= first && raw < first + 6, "无效的机器分支操作码");
      const u16 index = raw - first;
      const BrPayload &branch = inst->getBr();
      VERIFY(branch.trueBB != nullptr && branch.falseBB != nullptr);
      const bool invertForFallthrough = currentBlock->next() == branch.trueBB;
      const bool swapOperands = invertForFallthrough && op == MOP_BGTU;
      emit("\t%s\t%s, %s, ",
           invertForFallthrough ? invertedNames[index] : names[index],
           R(inst->getArg(swapOperands ? 1 : 0)),
           R(inst->getArg(swapOperands ? 0 : 1)));
      emitLabel(function,
                invertForFallthrough ? branch.falseBB : branch.trueBB);
      emit('\n');
      if (!invertForFallthrough && currentBlock->next() != branch.falseBB) {
        emit("\tj\t");
        emitLabel(function, branch.falseBB);
        emit('\n');
      }
      return;
    }
    case MOP_CALL:
      VERIFY(inst->getOperandCount() == 0, "MOP_CALL 仍然有寄存器操作数");
      VERIFY(inst->getCallee() != nullptr);
      emit("\tcall\t%s\n", functionName(inst->getCallee()));
      return;
    case MOP_RET:
      // 所有返回统一跳到函数尾声标签, 只有末尾块可以自然 fallthrough
      if (inst->getOperandCount() != 0) {
        Inst *value = inst->getArg(0);
        VERIFY(value != nullptr, "MOP_RET 有一个空的返回操作数");
        if (value->getType() == TY_F32) {
          if (value->id != rv64::FA0)
            emit("\tfmv.s\tfa0, %s\n", R(value));
        } else if (value->id != rv64::A0) {
          emit("\tmv\ta0, %s\n", R(value));
        }
      }
      if (inst->next() || currentBlock->next()) {
        emit("\tj\t");
        emitEpilogueLabel(function);
        emit('\n');
      }
      return;
    default: {
      char message[32];
      std::snprintf(message, sizeof(message), "发射未知操作码 %u",
                    static_cast<unsigned>(op));
      VERIFY(false, message);
    }
    }
  }

  bool globalAllZero(const Global *global) {
    VERIFY(global != nullptr, "空全局变量");
    for (u32 index = 0; index < global->initSegmentCount; ++index)
      if (global->initSegment[index].data != nullptr)
        return false;
    return true;
  }

  bool emitStringGlobalBodyIfNeeded(const Global *global) {
    if (!global || global->origin != Global::GlobalOrigin::StringLiteral)
      return false;

    VERIFY(global->name != nullptr && global->isConst && global->isArray &&
               global->type == TY_I32,
           "字符串结构无效");
    VERIFY(global->initSegmentCount == 0 || global->initSegment != nullptr,
           "字符串缺少初始化段");
    VERIFY(global->numElements <= global->totalSizeBytes, "字符串大小无效");
    emit("\t.align\t0\n%s:\n", global->name);

    // IR 已包含结尾和嵌入的 NUL, 批量 .byte 不会像 .asciz 一样隐式增添字节
    constexpr u32 bytesPerLine = 16;
    u64 emitted = 0;
    for (u32 segmentIndex = 0; segmentIndex < global->initSegmentCount;
         ++segmentIndex) {
      const GlobalInitSegment &segment = global->initSegment[segmentIndex];
      VERIFY(emitted <= global->numElements &&
                 segment.count <= global->numElements - emitted,
             "字符串初始化段越界");
      emitted += segment.count;
      if (!segment.data) {
        if (segment.count != 0)
          emit("\t.zero\t%u\n", segment.count);
        continue;
      }

      const i32 *data = static_cast<const i32 *>(segment.data);
      for (u32 index = 0; index < segment.count; ++index) {
        VERIFY(data[index] >= 0 && data[index] <= 255);
        emit(index % bytesPerLine == 0 ? "\t.byte\t%d" : ", %d", data[index]);
        if (index % bytesPerLine == bytesPerLine - 1 ||
            index + 1 == segment.count)
          emit('\n');
      }
    }
    if (emitted < global->totalSizeBytes)
      emit("\t.zero\t%u\n", global->totalSizeBytes - static_cast<u32>(emitted));
    return true;
  }

  void emitGlobalBodyOnly(const Global *global, bool inDataSection) {
    const bool allZero = globalAllZero(global);
    const i32 elementSize = typeSizeBytes(global->type);
    VERIFY(elementSize > 0, "全局变量的元素类型无效");
    i32 emitted = 0;
    for (u32 index = 0; index < global->initSegmentCount; ++index) {
      const GlobalInitSegment &segment = global->initSegment[index];
      if (!segment.data) {
        const i32 bytes = static_cast<i32>(segment.count) * elementSize;
        emit("%s%d\n", (allZero && !inDataSection) ? "\t.space\t" : "\t.zero\t",
             bytes);
        emitted += bytes;
      } else if (global->type == TY_F32) {
        const f32 *data = static_cast<const f32 *>(segment.data);
        for (u32 value = 0; value < segment.count; ++value) {
          u32 bits = 0;
          std::memcpy(&bits, &data[value], sizeof(bits));
          emit("\t.word\t%u\t# float %g\n", bits,
               static_cast<double>(data[value]));
        }
        emitted += static_cast<i32>(segment.count) * elementSize;
      } else {
        const i32 *data = static_cast<const i32 *>(segment.data);
        for (u32 value = 0; value < segment.count; ++value)
          emit("\t.word\t%d\n", data[value]);
        emitted += static_cast<i32>(segment.count) * elementSize;
      }
    }
    VERIFY(emitted <= static_cast<i32>(global->totalSizeBytes));
    if (emitted < static_cast<i32>(global->totalSizeBytes))
      emit("%s%d\n", (allZero && !inDataSection) ? "\t.space\t" : "\t.zero\t",
           static_cast<i32>(global->totalSizeBytes) - emitted);
  }

  void emitGlobal(const Global *global) {
    const bool allZero = globalAllZero(global);
    if (global->isConst)
      emit("\t.section\t.rodata\n");
    else
      emit(allZero ? "\t.bss\n" : "\t.data\n");
    emit("\t.globl\t%s\n", global->name);
    if (emitStringGlobalBodyIfNeeded(global))
      return;
    emit("\t.align\t2\n%s:\n", global->name);
    emitGlobalBodyOnly(global, false);
  }

  void emitMergedGlobals(const Module *module) {
    // 合并全局以 2048 为中心建立基址, 使每个成员偏移都落在 signed imm12 范围
    VERIFY(module->mergedGlobalGroupSizes != nullptr);
    emit("\t.data\n");
    for (u16 group = 0; group < module->mergedGlobalGroupCount; ++group) {
      emit("\t.align\t2\n");
      emitMergedGlobalLabel(group);
      emit(":\n");
      std::vector<const Global *> members;
      for (Global *global = module->globalHead; global; global = global->next)
        if (global->globalMergeMember && global->globalMergeGroup == group)
          members.push_back(global);
      std::stable_sort(members.begin(), members.end(),
                       [](const Global *left, const Global *right) {
                         return left->globalMergeOffset <
                                right->globalMergeOffset;
                       });
      i32 cursor = 0;
      for (const Global *global : members) {
        const i32 actual = global->globalMergeOffset + 2048;
        VERIFY(cursor <= actual, "重叠的合并全局变量布局");
        if (cursor < actual) {
          emit("\t.zero\t%d\n", actual - cursor);
          cursor = actual;
        }
        emitGlobalBodyOnly(global, true);
        cursor += static_cast<i32>(global->totalSizeBytes);
      }
      const i32 groupSize = module->mergedGlobalGroupSizes[group];
      VERIFY(cursor <= groupSize, "合并全局变量对象超过组大小");
      if (cursor < groupSize)
        emit("\t.zero\t%d\n", groupSize - cursor);
      emitMergedGlobalBaseLabel(group);
      emit(" = ");
      emitMergedGlobalLabel(group);
      emit("+2048\n");
    }
  }

  void emitMergedGlobalAliases(const Module *module) {
    for (Global *global = module->globalHead; global; global = global->next) {
      if (!global->globalMergeMember)
        continue;
      emit("\t.globl\t%s\n"
           "\t.type\t%s, @object\n"
           "\t.size\t%s, %u\n"
           "%s = ",
           global->name, global->name, global->name, global->totalSizeBytes,
           global->name);
      emitMergedGlobalLabel(global->globalMergeGroup);
      const i32 actual = global->globalMergeOffset + 2048;
      if (actual != 0)
        emit("+%d", actual);
      emit('\n');
    }
  }

  void emitFunction(const Function *function) {
    checkEmittableMIR(function);
    emit("\t.globl\t%s\n"
         "\t.type\t%s, @function\n"
         "%s:\n",
         functionName(function), functionName(function),
         functionName(function));
    emitPrologue(function);
    const bool hasReturn = hasMachineReturn(function);
    u32 lastSourceLine = 0;
    const Inst *fallthroughReturn = nullptr;
    for (BasicBlock *block = function->region->first; block;
         block = block->next()) {
      emitLabel(function, block);
      emit(":\n");
      for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
        if (inst->getOp() == MOP_RET && !inst->next() && !block->next())
          fallthroughReturn = inst;
        const bool emitted = emitsInstructionText(inst, block);
        emitInstruction(function, inst, block);
        if (emitted)
          emitSourceComment(function->module, inst, lastSourceLine);
      }
    }
    if (hasReturn) {
      emitEpilogueLabel(function);
      emit(":\n");
      emitEpilogue(function);
      emit("\tret\n");
      if (fallthroughReturn)
        emitSourceComment(function->module, fallthroughReturn, lastSourceLine);
    }
    emit("\t.size\t%s, .-%s\n", functionName(function), functionName(function));

    if (function->jumpTableHead) {
      emit("\t.section\t.rodata\n");
      for (JumpTable *table = function->jumpTableHead; table;
           table = table->next) {
        VERIFY(table->label != nullptr && table->getDefaultTarget() != nullptr);
        emit("\t.align\t2\n%s:\n", table->label);
        for (u32 index = 0; index < table->getEntryCount(); ++index) {
          BasicBlock *target = table->getTarget(index);
          if (!target)
            target = table->getDefaultTarget();
          emit("\t.word\t");
          // 跳转表保存目标与表首地址的 PC 相对差, dispatch 端负责加回基址
          emitLabel(function, target);
          emit(" - %s\n", table->label);
        }
      }
      emit("\t.text\n");
    }
  }

  void emitAssembly(Module *module) {
    VERIFY(module != nullptr || output != nullptr);
    emit("\t.text\n");
    for (Function *function = module->functionHead; function;
         function = function->next) {
      if (function->isExtern)
        continue;
      VERIFY(function->region != nullptr && function->region->first != nullptr,
             "非外部函数没有函数体");
      emitFunction(function);
      emit('\n');
    }
    if (module->hasMergedGlobals) {
      emitMergedGlobals(module);
      emit('\n');
    }
    for (Global *global = module->globalHead; global; global = global->next) {
      if (global->globalMergeMember)
        continue;
      emitGlobal(global);
      emit('\n');
    }
    if (module->hasMergedGlobals)
      emitMergedGlobalAliases(module);
  }
};
} // namespace

std::string_view EmitAssembly::name() const noexcept { return "emit-assembly"; }

PassResult EmitAssembly::run(Module *module, PassContext &) {
  Emitter(output_).emitAssembly(module);
  return PassResult::noChange();
}

} // namespace svm::ir
