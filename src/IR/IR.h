#ifndef IR_H
#define IR_H

#include "Arena.h"
#include "SourceLocation.h"
#include "Type.h"
#include "Utils.h"

#include <cassert>
#include <initializer_list>
#include <unordered_map>
#include <vector>

namespace svm {
class ASTNode;
class DiagnosticEngine;
class FuncDecl;
struct SourceLocation;

namespace ir {
enum class IRPhase : u8 {
  HIR,
  LIR,
  MIR,
};

enum class MIRPhase : u8 {
  NotMIR,
  SSA,
  OutOfSSA,
  PostRegAlloc,
  Emittable,
};

enum IRType : u8 {
  TY_VOID, // 控制语句
  TY_I1,   // bool
  TY_I32,  // 32位整数
  TY_F32,  // 32位浮点数
  TY_PTR,  // 内存地址
  TY_I64,  // 仅用于MIR地址算术
  TY_F64,  // 仅用于float变参提升
};

inline bool isInt(IRType type) noexcept {
  return type == TY_I1 || type == TY_I32 || type == TY_I64;
}

inline bool isFloat(IRType type) noexcept {
  return type == TY_F32 || type == TY_F64;
}

inline bool isScalar(IRType type) noexcept {
  return type == TY_I1 || type == TY_I32 || type == TY_F32;
}

inline bool isPtr(IRType type) noexcept { return type == TY_PTR; }

inline bool isVoid(IRType type) noexcept { return type == TY_VOID; }

const char *getString(IRType type) noexcept;
i32 typeSizeBytes(IRType type) noexcept;

enum OpCode : u16 {
  // HIR / LIR
  // 常量
  OP_ICONST,    // -> i32/i1 [imm]
  OP_FCONST,    // -> f32 [fimm]
  OP_GETGLOBAL, // -> ptr [gsym] 产生一个指向全局变量/数组的指针
  OP_PARAM,     // -> i32/f32/ptr [argno] 声明函数形参
  // 整数运算
  OP_ADD, // (i32, i32) -> i32
  OP_SUB, // (i32, i32) -> i32
  OP_MUL, // (i32, i32) -> i32
  OP_DIV, // (i32, i32) -> i32
  OP_MOD, // (i32, i32) -> i32
  OP_EQ,  // (i32, i32) -> i1
  OP_NE,  // (i32, i32) -> i1
  OP_LT,  // (i32, i32) -> i1
  OP_LE,  // (i32, i32) -> i1
  OP_GT,  // (i32, i32) -> i1
  OP_GE,  // (i32, i32) -> i1
  OP_NEG, // (i32) -> i32
  // 浮点运算
  OP_FADD, // (f32, f32) -> f32
  OP_FSUB, // (f32, f32) -> f32
  OP_FMUL, // (f32, f32) -> f32
  OP_FDIV, // (f32, f32) -> f32
  OP_FEQ,  // (f32, f32) -> i1
  OP_FNE,  // (f32, f32) -> i1
  OP_FLT,  // (f32, f32) -> i1
  OP_FLE,  // (f32, f32) -> i1
  OP_FGT,  // (f32, f32) -> i1
  OP_FGE,  // (f32, f32) -> i1
  OP_FNEG, // (f32) -> f32
  // 布尔运算
  OP_LNOT, // (i1) -> i1
  // 类型转换
  OP_I2F,  // (i32) -> f32
  OP_F2I,  // (f32) -> i32
  OP_ZEXT, // (i1) -> i32
  // 内存操作
  OP_ALLOCA, // -> ptr [MemPayload]
  OP_LOAD,   // (ptr) -> i32/f32 [MemPayload]
  OP_STORE,  // (ptr, i32/f32) -> void [MemPayload]
  /// @brief 单级数组索引
  ///
  /// byte GETPTR(base, idx) = base + index * stride
  /// arg0 = base : TY_PTR
  /// arg1 = idx : TY_I32
  /// Payload字段: imm_ (stride in bytes)
  OP_GETPTR,
  /// @brief 多级数组索引
  ///
  /// addr = base + idx_0 * stride[0] + ... + idx_{n-1} * stride[n-1]
  /// arg0 = base : TY_PTR
  /// arg1...argn = idx_0..idx_{n-1} : TY_I32
  /// -> TY_PTR
  /// Payload字段: array_ [ArrayPayload]
  /// 在HIR到LIR阶段降级为多条MUL+ADD+GETPTR
  OP_ARRAYIDX,
  // 控制流
  /// @brief 函数调用
  /// arg0...arg{n-1} = 参数列表 : TY_I32/TY_F32/TY_PTR
  /// -> TY_I32/TY_F32/TY_PTR
  /// Payload字段: call_info_ [CallInfoPayload]
  /// clobberMask (u64: 可能被调用者改写的寄存器掩码)
  OP_CALL, // arg0 = value : TY_I32/TY_F32 (可选 VOID函数无返回值) -> 终结符
  OP_RET,
  // HIR
  OP_IF,    // arg0 = cond : TY_I1, [ScfPayload] -> TY_VOID
            // scf.r[0] = then : Region, scf.r[1] = else : Region
  OP_WHILE, // NOARG, [ScfPayload] -> TY_VOID
            // scf.r[0] = cond : Region, scf.r[1] = body : Region
  /// @brief 仿射IV循环 for(; direction(iv, stop); iv += step) { body; }
  ///
  /// arg0 = stop : TY_I32
  /// arg1 = step : TY_I32
  /// arg2 = ivAddr : TY_PTR
  /// -> TY_VOID
  /// Payload字段: body_ [Region]
  /// 常量负步长使用iv > stop，其余步长必须满足正向契约并使用iv < stop。
  /// 在HIR到LIR阶段(expand_for)会被降级为标准的旋转后循环:
  /// [init_bb]:   初始化ivAddr
  /// [header_bb]: load iv, cmp direction(iv, stop), br cond loop_bb / exit_bb
  /// [loop_bb]:   完成后: iv+step -> store ivAddr -> br header_bb
  /// [exit_bb]:   循环退出
  OP_FOR,
  OP_YIELD,    // 终止当前Region返回控制流 arg0 = value : TY_I1 (可选) -> 终结符
               // 转换为OP_BR或OP_JMP
  OP_BREAK,    // NOARG -> 终结符 转换为OP_JMP
  OP_CONTINUE, // NOARG -> 终结符 转换为OP_JMP
  OP_BR,       // 条件跳转 arg0 = cond : TY_I1 -> 终结符 [BrPayload]
  OP_JMP,      // 无条件跳转 NOARG -> 终结符 [jumpTarget_ : BasicBlock*]
  /// @brief Phi
  ///
  /// args()[k] = 来自前驱incoming[k]的Value-SSA值 : ty -> ty
  /// [incoming_ : BasicBlock**]
  /// pred_与incoming_与一一对应
  OP_PHI,
  /// @brief Select 由If-Conversion发射 arg0 ? arg1 : arg2
  ///
  /// arg0 = cond : TY_I1
  /// arg1 = true_val : TY_I1/TY_I32
  /// arg2 = false_val : TY_I1/TY_I32
  OP_SELECT,
  /// @brief Switch 分发
  ///
  /// arg0 = selector : TY_I32/TY_I1 -> TY_VOID [SwitchPayload]
  OP_SWITCH,
  OP_UNREACHABLE, // NOARG -> 终结符
  /// @brief 局部数组单元素初始化
  ///
  /// 把alloca的第idx个元素初始化为value显式挂载到IR中 维护D-U链
  /// arg0 = alloca_ptr, arg1 = idx, arg2 = value
  OP_LOCAL_INIT_VALUE,
  /// @brief 局部数组全零段初始化
  ///
  /// 把alloca从begin_idx起连续count个元素清零显式挂载到IR中
  /// arg0 = alloca_ptr, arg1 = begin_idx, arg2 = count
  OP_LOCAL_INIT_ZERO,

  // MIR RISC-V 64GC
  MOP_START_ = 256,
  // 伪操作
  MOP_NOP,    // 不发射真实指令
  MOP_COPY,   // arg0 = src -> src "mv rd, rs"
  MOP_FCOPY,  // arg0 = src -> src "fmv.s fd, fs"
  MOP_SEXT_W, // 32位符号扩展 "addiw rd, rs, 0"
  /// @brief 加载任意立即数到GPR
  ///
  /// 12位以内[-2048, 2047]: addi rd, x0, imm
  /// 32位以内: lui rd, imm[31:12] + addi rd, rd, imm[11:0]
  /// 超过32位: lui + addi + slli + addi ...
  MOP_LI,
  MOP_LA,          // 加载符号地址 全局变量/GlobalMerge base/Jump-Table label
  MOP_JT_DISPATCH, // 跳转表分发 "jr arg0" [JumpTable*]
  // 32位整数运算
  MOP_ADDW,
  MOP_ADDIW,
  MOP_SUBW,
  MOP_MULW,
  MOP_DIVW,
  MOP_REMW,
  MOP_NEGW, // "subw rd, x0, rs"
  // 64位整数运算 用于地址计算
  MOP_ADD,
  MOP_ADDI,
  MOP_SUB,
  MOP_MUL,
  // 64位位运算
  MOP_AND,
  MOP_ANDI,
  MOP_OR,
  MOP_ORI,
  MOP_XOR,
  MOP_XORI,
  MOP_SLLI,
  MOP_SRLI,
  MOP_SRAI,
  // 32位位运算
  MOP_SLLIW,
  MOP_SRLIW,
  MOP_SRAIW,
  // 比较指令
  MOP_SLT,  // rd = (rs1 < rs2) ? 1 : 0 "slt rd, rs1, rs2"
  MOP_SEQZ, // rd = (rs == 0) ? 1 : 0 "sltiu rd, rs, 1"
  MOP_SNEZ, // rd = (rs != 0) ? 1 : 0 "sltu rd, x0, rs"
  // 高位立即数加载
  MOP_LUI, // rd = imm << 12
  // 浮点运算
  MOP_FLW,
  MOP_FSW,
  MOP_FLD, // vararg
  MOP_FSD, // vararg
  MOP_FADD_S,
  MOP_FSUB_S,
  MOP_FMUL_S,
  MOP_FDIV_S,
  MOP_FNEG_S,
  MOP_FEQ_S,
  MOP_FLT_S,
  MOP_FLE_S,
  MOP_FMV_W_X,      // GPR低32位 -> FPR低32位
  MOP_FMV_X_W,      // FPR低32位 -> GPR低32位
  MOP_FCVT_S_W,     // i32 -> f32
  MOP_FCVT_W_S,     // f32 -> i32
  MOP_FCVT_D_S,     // f32 -> f64
  MOP_FMV_X_D,      // FPR低64位 -> GPR
  MOP_F32_TO_GPR64, // vararg 专用 "fcvt.d.s" + "fmv.x.d"
  // 访存指令
  MOP_LW,
  MOP_LD,
  MOP_SW,
  MOP_SD,
  // 栈帧槽
  // 在frameIdx中编码栈帧槽索引 由fixupStackOffsets替换为普通的MOP_LW/MOP_SW等
  MOP_LW_FRAME,
  MOP_SW_FRAME,
  MOP_LD_FRAME,
  MOP_SD_FRAME,
  MOP_FLW_FRAME,
  MOP_FSW_FRAME,
  MOP_ADDI_FRAME, // alloca降级 "addi rd, sp, <offset>"
  // 分支和跳转
  MOP_BEQ,  // rs1 == rs2 -> PC += imm
  MOP_BNE,  // rs1 != rs2 -> PC += imm
  MOP_BLT,  // rs1 < rs2 -> PC += imm
  MOP_BGE,  // rs1 >= rs2 -> PC += imm
  MOP_BLTU, // rs1 < rs2 -> PC += imm
  MOP_BGTU, // rs1 > rs2 -> PC += imm
  MOP_J,    // jal x0, imm
  // 调用
  /// @brief 函数调用 auipc + jalr [CallInfoPayload]
  ///
  /// auipc t1, %pcrel_hi(callee) + jalr ra, t1, %pcrel_lo(callee)
  /// t1为临时寄存器, ra为返回地址寄存器
  MOP_CALL,
  MOP_RET,
};

const char *getString(OpCode op) noexcept;

inline bool isIConst(OpCode op) noexcept { return op == OP_ICONST; }
inline bool isFConst(OpCode op) noexcept { return op == OP_FCONST; }
inline bool isConstant(OpCode op) noexcept {
  return op == OP_ICONST || op == OP_FCONST || op == OP_GETGLOBAL ||
         op == OP_PARAM;
}
inline bool isIntArithmetic(OpCode op) noexcept {
  return op >= OP_ADD && op <= OP_NEG;
}
inline bool isIntCompare(OpCode op) noexcept {
  return op >= OP_EQ && op <= OP_GE;
}
inline bool isFloatArithmetic(OpCode op) noexcept {
  return op >= OP_FADD && op <= OP_FNEG;
}
inline bool isFloatCompare(OpCode op) noexcept {
  return op >= OP_FEQ && op <= OP_FGE;
}
inline bool isCompare(OpCode op) noexcept {
  return isIntCompare(op) || isFloatCompare(op);
}
inline bool isArithmetic(OpCode op) noexcept {
  return isIntArithmetic(op) || isFloatArithmetic(op);
}
inline bool isUnaryArithmetic(OpCode op) noexcept {
  return op == OP_NEG || op == OP_FNEG || op == OP_LNOT;
}
inline bool isBinaryArithmetic(OpCode op) noexcept {
  return (op >= OP_ADD && op <= OP_MOD) || (op >= OP_FADD && op <= OP_FDIV);
}
inline bool isConversion(OpCode op) noexcept {
  return op == OP_I2F || op == OP_F2I || op == OP_ZEXT;
}
inline bool isMemoryOp(OpCode op) noexcept {
  return op >= OP_ALLOCA && op <= OP_ARRAYIDX;
}
inline bool isAddressingOp(OpCode op) noexcept {
  return op == OP_GETPTR || op == OP_ARRAYIDX;
}
inline bool isCall(OpCode op) noexcept { return op == OP_CALL; }
inline bool isStructuredControl(OpCode op) noexcept {
  return op == OP_IF || op == OP_WHILE || op == OP_FOR;
}
inline bool isLoopOp(OpCode op) noexcept {
  return op == OP_WHILE || op == OP_FOR;
}
inline bool isHIRTerminator(OpCode op) noexcept {
  return op == OP_YIELD || op == OP_BREAK || op == OP_CONTINUE || op == OP_RET;
}
inline bool isLIRTerminator(OpCode op) noexcept {
  return op == OP_BR || op == OP_JMP || op == OP_RET || op == OP_SWITCH ||
         op == OP_UNREACHABLE;
}
inline bool isLocalInitAnchor(OpCode op) noexcept {
  return op == OP_LOCAL_INIT_VALUE || op == OP_LOCAL_INIT_ZERO;
}
inline bool isSelect(OpCode op) noexcept { return op == OP_SELECT; }
inline bool isMachineOp(OpCode op) noexcept { return op > MOP_START_; }
inline bool isMachineBranch(OpCode op) noexcept {
  return op >= MOP_BEQ && op <= MOP_BGTU;
}
inline bool isMachineJump(OpCode op) noexcept { return op == MOP_J; }
inline bool isJumpTableDispatch(OpCode op) noexcept {
  return op == MOP_JT_DISPATCH;
}
inline bool isMachineCall(OpCode op) noexcept { return op == MOP_CALL; }
inline bool isMachineReturn(OpCode op) noexcept { return op == MOP_RET; }
inline bool isMachineTerminator(OpCode op) noexcept {
  return isMachineBranch(op) || isMachineJump(op) || isJumpTableDispatch(op) ||
         isMachineReturn(op);
}
inline bool isMachineLoad(OpCode op) noexcept {
  return op == MOP_LW || op == MOP_LD || op == MOP_FLW || op == MOP_FLD;
}
inline bool isMachineStore(OpCode op) noexcept {
  return op == MOP_SW || op == MOP_SD || op == MOP_FSW || op == MOP_FSD;
}
inline bool isMachineFrameOp(OpCode op) noexcept {
  return op >= MOP_LW_FRAME && op <= MOP_ADDI_FRAME;
}
inline bool isMachineCopy(OpCode op) noexcept {
  return op == MOP_COPY || op == MOP_FCOPY;
}
inline bool isMachineFloat(OpCode op) noexcept {
  return (op >= MOP_FLW && op <= MOP_F32_TO_GPR64) || op == MOP_FCOPY ||
         op == MOP_FLW_FRAME || op == MOP_FSW_FRAME;
}
inline bool isTerminator(OpCode op) noexcept {
  return isHIRTerminator(op) || isLIRTerminator(op) || isMachineTerminator(op);
}

struct InstRef;
struct Use;
class Inst;
class BasicBlock;
struct Region;
struct Function;
struct Module;
class IRBuilder;
class CFGEditor;
class DeepCopy;

struct InstRef {
  Inst *inst = nullptr; // 被引用的定义
};

struct Use {
  Use *next = nullptr;  // 同一定义的下一个Use
  Inst *user = nullptr; // 使用者
  u16 argNo = 0;        // 使用者操作数下标
};

struct LocalInitSegment {
  // 数据段: values[k]指向OP_LOCAL_INIT_VALUE 真实值在values[k]->getArg(2)
  // 全零段: values为空, zeroAnchor指向OP_LOCAL_INIT_ZERO
  std::vector<Inst *> values;
  u32 count = 0;
  Inst *zeroAnchor = nullptr; // OP_LOCAL_INIT_ZERO
};

struct LocalInitInfo {
  std::vector<LocalInitSegment> segments;
  IRType elementType = TY_I32;
};

struct GlobalInitSegment {
  u32 count = 0;
  void *data = nullptr;
};

class SwitchCase {
public:
  SwitchCase() noexcept = default;
  SwitchCase(i32 value, BasicBlock *target) noexcept
      : value_(value), target_(target) {}

  i32 getValue() const noexcept { return value_; }
  BasicBlock *getTarget() const noexcept { return target_; }

private:
  i32 value_ = 0;                // case 常量
  BasicBlock *target_ = nullptr; // case CFG 目标

  friend class IRBuilder;
  friend class Inst;
  friend class CFGEditor;
  friend class DeepCopy;
};

class SwitchPayload {
public:
  u32 getCaseCount() const noexcept { return caseCount_; }
  const SwitchCase &getCase(u32 index) const noexcept {
    assert(index < caseCount_);
    return cases_[index];
  }
  BasicBlock *getDefaultTarget() const noexcept { return defaultTarget_; }

private:
  u32 caseCount_ = 0;                   // case 数量
  SwitchCase *cases_ = nullptr;         // 按 value 升序的 case 数组
  BasicBlock *defaultTarget_ = nullptr; // 非空默认 CFG 目标

  friend class IRBuilder;
  friend class Inst;
  friend class CFGEditor;
  friend class DeepCopy;
};

/// @brief JumpTable
///
/// 原OP_SWITCH块拆成两个相邻块：
/// BoundsCheckBlock: idx = selector - min;
///                   bgtu idx,(count-1) -> defaultTarget
///                   not-taken fallthrough -> TableLookupBlock
///
/// TableLookupBlock: base = la .LJTI;
///                   delta = lw (base + idx*4);
///                   addr = base + delta;
///                   jr addr (MOP_JT_DISPATCH)
struct JumpTable {
  const char *label = nullptr;            // 汇编标号
  i32 minValue = 0;                       // 最小 case 值
  BasicBlock *boundsCheckBlock = nullptr; // 边界检查块
  BasicBlock *tableLookupBlock = nullptr; // 表查找块
  JumpTable *next = nullptr;              // 函数内下一张表

  BasicBlock *getDefaultTarget() const noexcept { return defaultTarget_; }
  u32 getEntryCount() const noexcept { return entryCount_; }

  BasicBlock *getTarget(u32 k) const noexcept {
    assert(k < entryCount_);
    return target_ ? target_[k] : nullptr;
  }
  void configure(Function *function, i32 minValue, BasicBlock *defaultTarget,
                 BasicBlock *boundsCheckBlock, BasicBlock *tableLookupBlock,
                 BasicBlock *const *targets, u32 count); // 一次性配置表

private:
  u32 entryCount_ = 0;                  // 表项数量
  BasicBlock *defaultTarget_ = nullptr; // 非空 默认CFG目标
  BasicBlock **target_ = nullptr;       // 表项目标数组

  void resetTargets(Arena *arena, u32 n, BasicBlock *fill) noexcept {
    assert(arena);
    entryCount_ = n;
    target_ = arena->createArray<BasicBlock *>(n ? n : 1);
    for (u32 k = 0; k < n; ++k)
      target_[k] = fill;
  }

  void setTarget(u32 k, BasicBlock *target) noexcept {
    assert(k < entryCount_ && target_);
    target_[k] = target;
  }

  friend class IRBuilder;
  friend class Inst;
  friend class CFGEditor;
  friend class DeepCopy;
};

struct Global {
  enum class GlobalOrigin : u8 {
    SourceGlobal, // 源码定义的全局变量
    StringLiteral,
  };
  Global *prev = nullptr, *next = nullptr;
  const char *name = nullptr;
  IRType type = TY_I32;
  u32 totalSizeBytes = 0;
  u32 numElements = 0; // 对于数组类型
  bool isConst = false, isArray = false;
  GlobalInitSegment *initSegment = nullptr;
  u32 initSegmentCount = 0;
  GlobalOrigin origin = GlobalOrigin::SourceGlobal;

  // GlobalMerge相关:
  bool globalMergeEligible = false; // 通过候选
  bool globalMergeMember = false;   // 进入.L_MergedGlobals<group>合并块
  u16 globalMergeGroup = 0;         // 合并组号<group>
  i32 globalMergeOffset = 0;        // 合并块内偏移 对centered base
  i32 abiAlignment = 4;             // ABI对齐要求
};

struct SymbolRef {
  enum class SymbolRefKind : u8 {
    None,
    Global,
    MergedBase,
    JumpTable,
  };
  SymbolRefKind kind;
  u16 mergedGroup;
  union {
    Global *global;       // kind == Global
    JumpTable *jumpTable; // kind == JumpTable
  };

  static SymbolRef globalRef(Global *g) noexcept {
    return SymbolRef{SymbolRefKind::Global, 0, {g}};
  }

  static SymbolRef mergedBaseRef(u16 group) noexcept {
    return SymbolRef{SymbolRefKind::MergedBase, group, {nullptr}};
  }

  static SymbolRef jumpTableRef(JumpTable *jt) noexcept {
    SymbolRef ref{SymbolRefKind::JumpTable, 0, {nullptr}};
    ref.jumpTable = jt;
    return ref;
  }

  bool operator==(const SymbolRef &other) const noexcept {
    if (kind != other.kind)
      return false;
    switch (kind) {
    case SymbolRefKind::None:
      return true;
    case SymbolRefKind::Global:
      return global == other.global;
    case SymbolRefKind::MergedBase:
      return mergedGroup == other.mergedGroup;
    case SymbolRefKind::JumpTable:
      return jumpTable == other.jumpTable;
    }
    return false;
  }
};

struct MemPayload {
  u32 totalSizeBytes = 0;
  IRType elementType = TY_I32;
  i16 paramIdx = -1;
  LocalInitInfo *initInfo = nullptr;
};

struct ArrayPayload {
  IRType elementType = TY_I32;
  u16 nDims = 0;
  u32 *dims = nullptr;
  u32 *strides = nullptr;
};

struct CallInfoPayload {
  Function *callee = nullptr;
  u64 clobberMask = 0;
};

struct BrPayload {
  BasicBlock *trueBB = nullptr;
  BasicBlock *falseBB = nullptr;
};

struct ScfPayload {
  Region *r[2] = {}; // r[0] = then/cond, r[1] = else/body
};

class Inst {
public:
  Arena *arena = nullptr;                         // 所属Arena
  u32 id = 0;                                     // 指令或虚拟寄存器编号
  const SourceLocation *sourceLocation = nullptr; // 非拥有源码位置

  Inst() noexcept;                        // 构造清零的僵尸态指令
  Inst(const Inst &) = delete;            // 禁止复制
  Inst &operator=(const Inst &) = delete; // 禁止复制赋值

  bool isErased() const noexcept { return erased_; }
  bool isUndefValue() const noexcept { return undefValue_; }
  OpCode getOp() const noexcept { return op_; }
  IRType getType() const noexcept { return type_; }
  void setType(IRType type) noexcept { type_ = type; }
  u16 getOperandCount() const noexcept { return operandCount_; }
  Inst *getArg(u32 index) const noexcept;
  void setArg(u32 index, Inst *value) noexcept;
  bool eraseFromBlock() noexcept;                    // 从块中删除
  const Use *uses() const noexcept { return uses_; } // 只读Use链
  bool hasUses() const noexcept { return uses_ != nullptr; }
  bool hasNoUses() const noexcept { return uses_ == nullptr; }
  bool hasOneUse() const noexcept { return uses_ && !uses_->next; }
  bool tracksUses() const noexcept;                 // 是否跟踪 SSA Use
  Inst *previous() const noexcept { return prev_; } // 读取链表前项
  Inst *next() const noexcept { return next_; }     // 读取链表后项
  BasicBlock *parentBlock() const noexcept { return block_; } // 读取所属块

  i32 getImm() const noexcept;
  void setImm(i32 value) noexcept { imm_ = value; }
  i64 getImm64() const noexcept;
  void setImm64(i64 value) noexcept;
  f32 getFimm() const noexcept;
  void setFimm(f32 value) noexcept { fimm_ = value; }
  i32 getArgNo() const noexcept;
  void setArgNo(i32 value) noexcept { argNo_ = value; }
  Global *getGlobal() const noexcept;
  void setGlobal(Global *global) noexcept;
  SymbolRef getSymbolRef() const noexcept;
  void setSymbolRef(SymbolRef symbol) noexcept;
  MemPayload &getMem() noexcept;
  const MemPayload &getMem() const noexcept;
  ArrayPayload &getArray() noexcept;
  const ArrayPayload &getArray() const noexcept;
  Function *getCallee() const noexcept;
  void setCallee(Function *callee) noexcept;
  u64 getRegMask() const noexcept;
  void setRegMask(u64 mask) noexcept;
  const BrPayload &getBr() const noexcept;
  ScfPayload &getScf() noexcept;
  const ScfPayload &getScf() const noexcept;
  BasicBlock *getJumpTarget() const noexcept;
  u32 getSuccessorSlotCount() const noexcept;             // 获取原始后继槽数量
  BasicBlock *getSuccessorSlot(u32 index) const noexcept; // 获取原始后继槽
  Region *getBody() const noexcept;
  void setBody(Region *body) noexcept { body_ = body; }
  const SwitchPayload &getSwitch() const noexcept;
  JumpTable *getJumpTable() const noexcept;
  BasicBlock *getIncomingBlock(u32 index) const noexcept;
  i32 getStride() const noexcept;                        // 读取GETPTR步长
  void setStride(i32 stride) noexcept { imm_ = stride; } // 设置GETPTR步长
  i32 getFrameIndex() const noexcept;
  void setFrameIndex(i32 index) noexcept { frameIndex_ = index; }
  bool isMachine() const noexcept { return isMachineOp(op_); }
  bool isPrecoloredDef() const noexcept;         // 是否物理寄存器哨兵
  Inst *def() noexcept { return getArg(0); }     // 读取约定首操作数
  bool atFront() const noexcept;                 // 是否在链表首部
  bool atBack() const noexcept;                  // 是否在链表尾部
  Inst *getParentOp() const noexcept;            // 获取父结构化指令
  bool inside(const Inst *outer) const noexcept; // 是否位于指定指令内部
  void moveBefore(Inst *anchor) noexcept;        // 移到锚点前
  void moveAfter(Inst *anchor) noexcept;         // 移到锚点后

  friend class IRBuilder;
  friend class BasicBlock;
  friend class CFGEditor;
  friend class DeepCopy;
  friend struct Module;
  friend bool computePreds(Function *function);
  friend void computeUses(Function *function);
  friend void replaceAllUsesWith(Function *function, Inst *from, Inst *to);

private:
  static constexpr usize kPayloadSize = 24; // Payload稳定大小

  OpCode op_ = OP_ICONST;       // 操作码
  IRType type_ = TY_VOID;       // 结果类型
  u16 operandCount_ = 0;        // 操作数数量
  bool erased_ = true;          // 是否已删除
  bool undefValue_ = false;     // 是否为undef值
  InstRef inlineArgs_[2] = {};  // 小操作数存储
  InstRef *args_ = inlineArgs_; // 操作数存储
  Use *uses_ = nullptr;         // Use链表头
  Inst *prev_ = nullptr;        // 指令链表前项
  Inst *next_ = nullptr;        // 指令链表后项
  BasicBlock *block_ = nullptr; // 所属基本块

  union {
    i64 imm_;             // OP_ICONST只用低32位 但是MOP_LI可承载64位立即数
    f32 fimm_;            // OP_FCONST
    i32 argNo_;           // OP_PARAM
    Global *global_;      // OP_GETGLOBAL
    SymbolRef symbol_;    // OP_LA
    MemPayload *mem_;     // OP_ALLOCA/OP_LOAD/OP_STORE
    ArrayPayload *array_; // OP_ARRAYIDX
    CallInfoPayload *callInfo_;  // OP_CALL/MOP_CALL
    BrPayload *branch_;          // OP_BR/MOP_BEQ等
    BasicBlock *jumpTarget_;     // OP_JMP
    ScfPayload *scf_;            // OP_IF/OP_WHILE
    Region *body_;               // OP_FOR
    BasicBlock **incoming_;      // OP_PHI
    i32 frameIndex_;             // MOP_*_FRAME
    SwitchPayload *switch_;      // OP_SWITCH
    JumpTable *jumpTable_;       // MOP_JT_DISPATCH
    byte payload_[kPayloadSize]; // 清零和复制
  };

  BrPayload &mutableBranch() noexcept;                    // 分支写入口
  void setOp(OpCode op, IRPhase phase) noexcept;          // 设置构造期操作码
  SwitchPayload &mutableSwitch() noexcept;                // Switch写入口
  void setSwitchPayload(SwitchPayload *payload) noexcept; // 设置Switch载荷
  void setJumpTarget(BasicBlock *target) noexcept;        // 设置跳转目标
  void setSuccessorSlot(u32 index, BasicBlock *target) noexcept; // 改写后继槽
  void setJumpTable(JumpTable *table) noexcept;                  // 设置跳转表
  void setIncomingArray(BasicBlock **incoming) noexcept; // 设置Phi前驱数组
  void setIncomingBlock(u32 index, BasicBlock *block) noexcept; // 设置Phi前驱
  void dropOperand(u32 index) noexcept;                         // 卸载单个 Use
  void dropAllOperands() noexcept;                              // 卸载全部 Use
  BasicBlock *unlinkFromBlock() noexcept;                       // 从指令链摘除
  void linkBefore(Inst *anchor) noexcept;                       // 链入锚点前
  void linkAfter(Inst *anchor) noexcept;                        // 链入锚点后

  friend bool cleanupDeadBlocks(Function *function);
};

class BasicBlock {
public:
  Region *parentRegion = nullptr; // 所属Region
  u32 id = 0;                     // 块编号

  // RA所需内的活性分析信息
  u64 *lvDef = nullptr;     // 活性def集合
  u64 *lvUse = nullptr;     // 活性use集合
  u64 *lvLiveIn = nullptr;  // live-in集合
  u64 *lvLiveOut = nullptr; // live-out集合
  u32 lvWordCount = 0;      // 活性集合字数

  u32 getPredecessorCount() const noexcept { return predecessorCount_; }
  BasicBlock *getPredecessor(u32 index) const noexcept;
  BasicBlock *previous() const noexcept { return prev_; }
  BasicBlock *next() const noexcept { return next_; }
  Inst *firstPhi() const noexcept { return phiFirst_; }
  Inst *lastPhi() const noexcept { return phiLast_; }
  Inst *firstInst() const noexcept { return instFirst_; }
  Inst *lastInst() const noexcept { return instLast_; }
  bool empty() const noexcept;
  bool endsWithTerminator() const noexcept;
  Inst *terminator() const noexcept;
  void moveBefore(BasicBlock *anchor) noexcept;
  void moveAfter(BasicBlock *anchor) noexcept;
  void moveToStart(Region *region) noexcept;   // 移到Region首部
  void moveToEnd(Region *region) noexcept;     // 移到Region尾部
  void takeInstructionSuffixFrom(Inst *first); // 移动first及其后指令到当前空块
  void takeInstructionSuffixAfter(Inst *anchor); // 移动anchor后指令到当前空块
  void takeSingleBlockRegion(Region *source);    // 接管单块Region内容
  bool atFront() const noexcept;                 // 是否Region首块
  bool atBack() const noexcept;                  // 是否Region尾块

private:
  BasicBlock *prev_ = nullptr;                  // Region前一块
  BasicBlock *next_ = nullptr;                  // Region后一块
  Inst *phiFirst_ = nullptr;                    // Phi链表头
  Inst *phiLast_ = nullptr;                     // Phi链表尾
  Inst *instFirst_ = nullptr;                   // 指令链表头
  Inst *instLast_ = nullptr;                    // 指令链表尾
  u32 predecessorCount_ = 0;                    // 前驱数量
  BasicBlock **predecessors_ = nullptr;         // 前驱数组
  void spliceIntoBefore(Inst *anchor) noexcept; // 把指令链并入锚点前
  Region *unlinkFromRegion() noexcept;          // 从Region链摘除
  void linkBefore(BasicBlock *anchor) noexcept; // 链入锚点块前
  void linkAfter(BasicBlock *anchor) noexcept;  // 链入锚点块后
  friend class IRBuilder;
  friend class Inst;
  friend class CFGEditor;
  friend class DeepCopy;
  friend struct Region;
  friend bool computePreds(Function *);
};

struct Region {
  BasicBlock *first = nullptr;  // 块链表头
  BasicBlock *last = nullptr;   // 块链表尾
  Inst *owner = nullptr;        // 结构化所有者
  Region *parent = nullptr;     // 父Region
  Function *function = nullptr; // 所属函数

  void spliceBlocks(Region *source) noexcept;  // 接管全部块
  void adoptBlock(BasicBlock *block) noexcept; // 追加单个块
};

struct IConstKey {
  IRType type;
  i32 value;
  bool operator==(const IConstKey &other) const noexcept {
    return type == other.type && value == other.value;
  }
};

struct IConstKeyHash {
  usize operator()(const IConstKey &key) const noexcept {
    const u64 bits =
        (static_cast<u64>(key.type) << 32) | static_cast<u32>(key.value);
    return std::hash<u64>{}(bits);
  }
};

struct ConstPools {
  std::unordered_map<IConstKey, Inst *, IConstKeyHash> iConstPool;
  std::unordered_map<u32, Inst *> fConstPool;
  std::unordered_map<Global *, Inst *> globalPtrPool;
};

struct Function {
  struct FrameSlot {
    enum class Kind : u8 { Local, Spill, CalleeSave, ArgPass };
    i32 size = 0;            // 槽大小
    i32 alignment = 1;       // 槽对齐
    i32 offset = 0;          // 最终栈偏移
    Kind kind = Kind::Local; // 槽用途
  };

  Arena *arena = nullptr;
  Function *next = nullptr;             // 模块函数链表下一项
  const char *name = nullptr;           // 函数名
  Module *module = nullptr;             // 所属模块
  Region *region = nullptr;             // 顶层Region
  u32 paramCount = 0;                   // 形参数量
  IRType *paramTypes = nullptr;         // 形参类型数组
  Inst **params = nullptr;              // 形参值数组
  IRType returnType = TY_VOID;          // 返回类型
  ConstPools constPools;                // 常量驻留池
  bool isExtern = false;                // 是否外部函数
  FunctionType *functionType = nullptr; // 前端函数类型
  u32 instCount = 0;                    // 指令编号计数
  u32 blockCount = 0;                   // 块编号计数
  IRPhase phase = IRPhase::HIR;         // 当前IR阶段
  MIRPhase mirPhase = MIRPhase::NotMIR; // 当前MIR形态
  u32 virtualRegisterCount = 0;         // 虚拟寄存器数
  u8 *virtualRegisterClasses = nullptr; // 虚拟寄存器类别
  std::vector<FrameSlot> frameSlots;    // 栈帧槽表
  i32 stackSize = 0;                    // 栈帧大小
  bool isLeaf = true;                   // 是否叶函数
  u64 calleeSaveMask = 0;               // 被调用者保存掩码
  i32 maxCallArgStack = 0;              // 最大出参栈空间
  void *mirMoveInfo = nullptr;          // MIR移动侧表
  void *mirVRegFlags = nullptr;         // MIR虚拟寄存器侧表
  void *ipraInfo = nullptr;             // IPRA摘要
  JumpTable *jumpTableHead = nullptr;   // 跳转表链表头

  JumpTable *newJumpTable();                                       // 创建跳转表
  i32 newFrameSlot(i32 size, i32 alignment, FrameSlot::Kind kind); // 创建帧槽
};

struct Module {
  Arena *arena = nullptr;
  DiagnosticEngine *diagnostics = nullptr;
  const char *sourceText = nullptr;                           // 完整源码
  usize sourceLength = 0;                                     // 源码长度
  std::unordered_map<const ASTNode *, Global *> declToGlobal; // AST全局映射
  std::unordered_map<const FuncDecl *, Function *>
      declToFunction;                    // AST函数映射
  Function *functionHead = nullptr;      // 函数链表头
  Function *functionTail = nullptr;      // 函数链表尾
  Global *globalHead = nullptr;          // 全局链表头
  Global *globalTail = nullptr;          // 全局链表尾
  bool hasMergedGlobals = false;         // 是否有合并全局
  u16 mergedGlobalGroupCount = 0;        // 合并组数
  i32 *mergedGlobalGroupSizes = nullptr; // 各组合并大小
  i32 mergedGlobalAlignment = 4;         // 合并块对齐
  Inst *physicalRegisterDefs[64] = {};   // 物理寄存器哨兵

  Inst *physicalRegister(u32 reg) const noexcept; // 读取物理寄存器哨兵
  void initPregDefs();                            // 初始化物理寄存器哨兵
  static Module *create(Arena &arena);            // 创建模块
  Function *newFunction(const char *name, IRType returnType,
                        const IRType *paramTypes, u32 paramCount,
                        FunctionType *functionType, bool isExtern); // 创建函数
  Global *newGlobal(const char *name, IRType elementType, u32 totalSizeBytes,
                    u32 numElements, bool isConst,
                    bool isArray); // 创建全局对象
};

class IRBuilder {
public:
  struct Coerced {
    Inst *left = nullptr;  // 转换后的左值
    Inst *right = nullptr; // 转换后的右值
    IRType type = TY_VOID; // 公共类型
  };

  IRBuilder(Module *module, Function *function) noexcept;
  Module *module() const noexcept { return module_; }
  Function *function() const noexcept { return function_; }
  Arena *arena() const noexcept { return function_->arena; }
  BasicBlock *insertBlock() const noexcept { return insertBlock_; }
  Inst *insertAfter() const noexcept { return insertAfter_; }
  void setInsertAtEnd(BasicBlock *block) noexcept;   // 插入到块尾
  void setInsertAtStart(BasicBlock *block) noexcept; // 插入到块首
  void setInsertAfter(Inst *inst) noexcept;          // 插入到指令后
  void setInsertBefore(Inst *inst) noexcept;         // 插入到指令前
  void setCurrentSourceLocation(const SourceLocation *location) noexcept {
    currentSourceLocation_ = location;
  }

  Region *newRegion(Inst *owner, Region *parent); // 创建Region
  BasicBlock *newBlockAtEnd(Region *region);      // 创建尾块
  BasicBlock *newBlockAfter(BasicBlock *anchor);  // 创建后继布局块
  void bindJumpTable(Inst *inst, JumpTable *table) const noexcept;
  Inst *iConst(i32 value);
  Inst *i1Const(bool value);
  Inst *fConst(f32 value);
  Inst *getGlobalPtr(Global *global);
  Inst *makeUndef(IRType type);
  Inst *emit(OpCode op, IRType type);
  Inst *emit(OpCode op, IRType type, Inst *arg0);
  Inst *emit(OpCode op, IRType type, Inst *arg0, Inst *arg1);
  Inst *emitN(OpCode op, IRType type, Inst *const *args, u32 count);
  Inst *tryFoldConstant(OpCode op, IRType type, Inst *left,
                        Inst *right = nullptr);
  Inst *emitPhi(IRType type, BasicBlock *block, Inst *initialValue);
  Inst *emitLoad(Inst *address, IRType elementType);
  Inst *emitStore(Inst *address, Inst *value, IRType elementType);
  Inst *emitAlloca(u32 totalSizeBytes, IRType elementType);
  Inst *emitAllocaParam(u32 totalSizeBytes, IRType elementType, i16 paramIndex);
  Inst *emitGetPtr(Inst *base, Inst *index, i32 stride = 1);
  Inst *emitArrayIndex(Inst *base, Inst *const *indices, u32 count,
                       IRType elementType, const u32 *strides, const u32 *dims);
  Inst *emitFor(Inst *stop, Inst *step, Inst *ivAddress, Region *body);
  Inst *emitCall(Function *callee, Inst *const *args, u32 count,
                 IRType returnType);
  Inst *replaceInPlace(Inst *victim, OpCode op, IRType type);
  Inst *replaceInPlace(Inst *victim, OpCode op, IRType type, Inst *arg0);
  Inst *replaceInPlace(Inst *victim, OpCode op, IRType type, Inst *arg0,
                       Inst *arg1);
  Inst *castTo(Inst *value, IRType target);
  Inst *toI1(Inst *value);
  Coerced coercePair(Inst *left, Inst *right);
  Inst *emitJump(BasicBlock *target);
  Inst *emitBranch(Inst *condition, BasicBlock *trueBlock,
                   BasicBlock *falseBlock);
  Inst *emitReturn(Inst *value = nullptr);
  Inst *emitYield(Inst *condition = nullptr);
  Inst *emitBreak();
  Inst *emitContinue();
  Inst *emitIf(Inst *condition, Region *thenRegion,
               Region *elseRegion = nullptr);
  Inst *emitWhile(Region *conditionRegion, Region *bodyRegion);
  Inst *emitSwitch(Inst *selector, const SwitchCase *cases, u32 caseCount,
                   BasicBlock *defaultTarget);
  Inst *cloneInst(const Inst *source);                     // 克隆单条指令
  Inst *replaceWithJump(Inst *victim, BasicBlock *target); // 替换为跳转
  Inst *replaceWithBranch(Inst *victim, Inst *condition, BasicBlock *trueBlock,
                          BasicBlock *falseBlock); // 替换为分支
  Inst *replaceWithJumpAndEraseSuffix(Inst *victim,
                                      BasicBlock *target); // 替换跳转并删除后缀
  void eraseAfter(Inst *anchor);                           // 删除锚点后指令

private:
  Inst *newInst(OpCode op, IRType type, u32 operandCount);
  void allocatePayload(Inst *inst);                          // 分配操作码载荷
  Inst *replaceHeader(Inst *victim, OpCode op, IRType type); // 重置指令头
  Inst *iConstImpl(i32 value, IRType type);                  // 获取整数常量
  void attach(Inst *inst);                                   // 挂接指令

  Module *module_ = nullptr;                              // 当前模块
  Function *function_ = nullptr;                          // 当前函数
  BasicBlock *insertBlock_ = nullptr;                     // 当前插入块
  Inst *insertAfter_ = nullptr;                           // 当前插入锚点
  const SourceLocation *currentSourceLocation_ = nullptr; // 当前源码位置
};

class CFGEditor {
public:
  struct PhiEdgeValue {
    Inst *phi = nullptr;   // 待更新Phi
    Inst *value = nullptr; // 边值
  };
  struct SplitBlockPredsResult {
    BasicBlock *block = nullptr; // 新建汇合块，失败时为空
    bool createdPhi = false;     // 是否为不同边值创建了中间Phi
  };
  // 分裂单条CFG边
  static BasicBlock *splitCriticalEdge(Function *function, BasicBlock *pred,
                                       BasicBlock *succ);
  // 将一组前驱收束到新块
  static SplitBlockPredsResult
  splitBlockPredecessors(Function *function, BasicBlock *succ,
                         BasicBlock *const *preds, u32 predCount,
                         BasicBlock *insertAfter = nullptr);
  // 查询去重后的语义边
  static bool hasSemanticEdge(BasicBlock *pred, BasicBlock *succ);
  // 查询Phi在指定边上的值
  static Inst *getPhiIncomingValue(Inst *phi, BasicBlock *pred);
  // 校验 predecessor/Phi/Use 对齐
  static bool hasConsistentIncomingState(BasicBlock *block);
  // 重定向边
  static bool redirectEdge(Function *function, BasicBlock *pred,
                           BasicBlock *oldSucc, BasicBlock *newSucc,
                           const std::vector<PhiEdgeValue> &values = {});
  // 便捷重载
  static bool redirectEdge(Function *function, BasicBlock *pred,
                           BasicBlock *oldSucc, BasicBlock *newSucc,
                           std::initializer_list<PhiEdgeValue> values);
  // 替换边值
  static bool setPhiEdgeValues(Function *function, BasicBlock *succ,
                               BasicBlock *pred,
                               const std::vector<PhiEdgeValue> &values);
  static bool setPhiEdgeValues(Function *function, BasicBlock *succ,
                               BasicBlock *pred,
                               std::initializer_list<PhiEdgeValue> values);
  // 为终结符中已存在 元数据中尚未登记的新边追加完整Phi列
  static bool addPhiEdgeValues(Function *function, BasicBlock *succ,
                               BasicBlock *pred,
                               const std::vector<PhiEdgeValue> &values);

  // 将终结符及死边元数据折叠为无条件跳转
  static bool foldTerminatorToJump(Function *function, BasicBlock *pred,
                                   BasicBlock *kept);
  // 旁路并删除空跳转块
  static bool bypassTrivialBlock(Function *function, BasicBlock *middle);
  // 将单前驱块合入其前驱
  static bool mergeBlockIntoPredecessor(Function *function, BasicBlock *pred,
                                        BasicBlock *succ);

private:
  // 删除死边元数据
  static void dropIncomingForRemovedEdge(Function *function, BasicBlock *pred,
                                         BasicBlock *succ);
  // 删除完整 Phi 边值列
  static bool removePhiEdgeValues(Function *function, BasicBlock *succ,
                                  BasicBlock *pred);
  // 迁移完整 Phi 边值列
  static bool movePhiEdgeValues(BasicBlock *succ, BasicBlock *oldPred,
                                BasicBlock *newPred);
  // 重定向所有匹配物理槽
  static bool rewriteSuccessorEdges(BasicBlock *pred, BasicBlock *oldSucc,
                                    BasicBlock *newSucc);
  // 将终结符改写为跳转槽
  static bool rewriteTerminatorToJump(Function *function, BasicBlock *pred,
                                      BasicBlock *target);
  // 删除已断开活边的块
  static void eraseBlock(Function *function, BasicBlock *block);
  // 改写分支物理槽
  static bool rewriteBranchSlot(BasicBlock *pred, bool trueEdge,
                                BasicBlock *newTarget);
  // 改写跳转物理槽
  static bool rewriteJumpTarget(BasicBlock *pred, BasicBlock *newTarget);
  // 一次性重建 Phi 槽
  static void rebuildPhiIncomingSlots(Function *function, Inst *phi,
                                      const std::vector<BasicBlock *> &preds,
                                      const std::vector<Inst *> &values);
  // 追加Phi槽
  static void appendPhiIncomingSlot(Function *function, Inst *phi,
                                    BasicBlock *pred, Inst *value);
  // 删除Phi槽
  static void erasePhiIncomingSlot(Function *function, Inst *phi, u32 index);
  // 设置Phi值
  static bool setPhiIncomingValueSlot(Function *function, Inst *phi,
                                      BasicBlock *pred, Inst *value);
  // 查询前驱槽
  static bool hasPredecessorSlot(BasicBlock *succ, BasicBlock *pred);
  // 追加前驱槽
  static void appendPredecessorSlot(Function *function, BasicBlock *succ,
                                    BasicBlock *pred);
  // 删除前驱槽
  static bool erasePredecessorSlot(BasicBlock *succ, BasicBlock *pred);
  // 查找前驱下标
  static u32 findPredecessorIndex(BasicBlock *block, BasicBlock *pred);
  // 替换前驱数组
  static void assignPredecessors(Function *function, BasicBlock *block,
                                 const std::vector<BasicBlock *> &preds);

  friend bool computePreds(Function *function);
  friend bool cleanupDeadBlocks(Function *function);
};

// 重建Use链
void computeUses(Function *function);
void replaceAllUsesWith(Function *function, Inst *from, Inst *to);
const Inst *getEnclosingLoop(const Inst *inst) noexcept; // 查询最内层所属循环
Inst *getEnclosingLoop(Inst *inst) noexcept;
const Inst *getMemoryBase(const Inst *address) noexcept; // 寻址得到基对象
Inst *getMemoryBase(Inst *address) noexcept;
std::vector<BasicBlock *> computeRPO(Function *function);
// 规范化LIR/MIR顶层扁平CFG的前驱和Phi输入
bool computePreds(Function *function);
// 删除LIR/MIR顶层扁平CFG中入口不可达的块
bool cleanupDeadBlocks(Function *function);

template <typename Func>
inline void forEachPhi(BasicBlock *block, Func &&func) {
  for (Inst *inst = block ? block->firstPhi() : nullptr; inst;) {
    Inst *next = inst->next();
    func(inst);
    inst = next;
  }
}

template <typename Func>
inline void forEachInst(BasicBlock *block, Func &&func) {
  for (Inst *inst = block ? block->firstInst() : nullptr; inst;) {
    Inst *next = inst->next();
    func(inst);
    inst = next;
  }
}

template <typename Func> inline void forEachOp(BasicBlock *block, Func &&func) {
  forEachPhi(block, func);
  forEachInst(block, func);
}

template <typename Func>
inline void forEachInstRecursive(Region *region, Func &&func) {
  if (!region)
    return;
  for (BasicBlock *block = region->first; block; block = block->next()) {
    forEachOp(block, [&](Inst *inst) {
      func(inst);
      if (inst->getOp() == OP_FOR) {
        forEachInstRecursive(inst->getBody(), func);
      } else if (inst->getOp() == OP_IF || inst->getOp() == OP_WHILE) {
        forEachInstRecursive(inst->getScf().r[0], func);
        forEachInstRecursive(inst->getScf().r[1], func);
      }
    });
  }
}

template <typename Func>
inline void forEachSuccessor(Inst *terminator, Func &&func) {
  if (!terminator)
    return;

  BasicBlock *inlineSeen[8] = {};
  u32 inlineCount = 0;
  std::vector<BasicBlock *> overflowSeen;
  auto visit = [&](BasicBlock *successor) {
    if (!successor)
      return;
    for (u32 i = 0; i < inlineCount; ++i)
      if (inlineSeen[i] == successor)
        return;
    for (BasicBlock *seen : overflowSeen)
      if (seen == successor)
        return;
    if (inlineCount < 8)
      inlineSeen[inlineCount++] = successor;
    else
      overflowSeen.push_back(successor);
    func(successor);
  };

  for (u32 index = 0; index < terminator->getSuccessorSlotCount(); ++index)
    visit(terminator->getSuccessorSlot(index));
}

template <typename Func>
inline void forEachSuccessor(BasicBlock *block, Func &&func) {
  if (block)
    forEachSuccessor(block->lastInst(), func);
}

inline u32 successorCount(BasicBlock *block) {
  u32 count = 0;
  forEachSuccessor(block, [&](BasicBlock *) { ++count; });
  return count;
}

} // namespace ir
} // namespace svm

#endif // IR_H
