#include "IR.h"

#include <algorithm>
#include <cstring>

namespace svm::ir {

const char *getString(IRType type) noexcept {
  switch (type) {
  case TY_VOID:
    return "void";
  case TY_I1:
    return "i1";
  case TY_I32:
    return "i32";
  case TY_F32:
    return "f32";
  case TY_PTR:
    return "ptr";
  case TY_I64:
    return "i64";
  case TY_F64:
    return "f64";
  }
  return "<invalid-type>";
}

i32 typeSizeBytes(IRType type) noexcept {
  switch (type) {
  case TY_I1:
    return 1;
  case TY_I32:
  case TY_F32:
    return 4;
  case TY_PTR:
  case TY_I64:
  case TY_F64:
    return 8;
  case TY_VOID:
    return 0;
  }
  return 0;
}

const char *getString(OpCode op) noexcept {
  switch (op) {
#define OP_NAME(value, text)                                                   \
  case value:                                                                  \
    return text
    OP_NAME(OP_ICONST, "iconst");
    OP_NAME(OP_FCONST, "fconst");
    OP_NAME(OP_GETGLOBAL, "getglobal");
    OP_NAME(OP_PARAM, "param");
    OP_NAME(OP_ADD, "add");
    OP_NAME(OP_SUB, "sub");
    OP_NAME(OP_MUL, "mul");
    OP_NAME(OP_DIV, "div");
    OP_NAME(OP_MOD, "mod");
    OP_NAME(OP_EQ, "eq");
    OP_NAME(OP_NE, "ne");
    OP_NAME(OP_LT, "lt");
    OP_NAME(OP_LE, "le");
    OP_NAME(OP_GT, "gt");
    OP_NAME(OP_GE, "ge");
    OP_NAME(OP_NEG, "neg");
    OP_NAME(OP_FADD, "fadd");
    OP_NAME(OP_FSUB, "fsub");
    OP_NAME(OP_FMUL, "fmul");
    OP_NAME(OP_FDIV, "fdiv");
    OP_NAME(OP_FEQ, "feq");
    OP_NAME(OP_FNE, "fne");
    OP_NAME(OP_FLT, "flt");
    OP_NAME(OP_FLE, "fle");
    OP_NAME(OP_FGT, "fgt");
    OP_NAME(OP_FGE, "fge");
    OP_NAME(OP_FNEG, "fneg");
    OP_NAME(OP_LNOT, "lnot");
    OP_NAME(OP_I2F, "i2f");
    OP_NAME(OP_F2I, "f2i");
    OP_NAME(OP_ZEXT, "zext");
    OP_NAME(OP_ALLOCA, "alloca");
    OP_NAME(OP_LOAD, "load");
    OP_NAME(OP_STORE, "store");
    OP_NAME(OP_GETPTR, "getptr");
    OP_NAME(OP_ARRAYIDX, "arrayidx");
    OP_NAME(OP_CALL, "call");
    OP_NAME(OP_RET, "ret");
    OP_NAME(OP_IF, "if");
    OP_NAME(OP_WHILE, "while");
    OP_NAME(OP_FOR, "for");
    OP_NAME(OP_YIELD, "yield");
    OP_NAME(OP_BREAK, "break");
    OP_NAME(OP_CONTINUE, "continue");
    OP_NAME(OP_BR, "br");
    OP_NAME(OP_JMP, "jmp");
    OP_NAME(OP_PHI, "phi");
    OP_NAME(OP_SELECT, "select");
    OP_NAME(OP_SWITCH, "switch");
    OP_NAME(OP_UNREACHABLE, "unreachable");
    OP_NAME(OP_LOCAL_INIT_VALUE, "local_init_value");
    OP_NAME(OP_LOCAL_INIT_ZERO, "local_init_zero");
    OP_NAME(MOP_NOP, "nop");
    OP_NAME(MOP_COPY, "mv");
    OP_NAME(MOP_FCOPY, "fmv.s");
    OP_NAME(MOP_SEXT_W, "sext.w");
    OP_NAME(MOP_LI, "li");
    OP_NAME(MOP_LA, "la");
    OP_NAME(MOP_JT_DISPATCH, "jr");
    OP_NAME(MOP_ADDW, "addw");
    OP_NAME(MOP_ADDIW, "addiw");
    OP_NAME(MOP_SUBW, "subw");
    OP_NAME(MOP_MULW, "mulw");
    OP_NAME(MOP_DIVW, "divw");
    OP_NAME(MOP_REMW, "remw");
    OP_NAME(MOP_NEGW, "negw");
    OP_NAME(MOP_ADD, "add");
    OP_NAME(MOP_ADDI, "addi");
    OP_NAME(MOP_SUB, "sub");
    OP_NAME(MOP_MUL, "mul");
    OP_NAME(MOP_AND, "and");
    OP_NAME(MOP_ANDI, "andi");
    OP_NAME(MOP_OR, "or");
    OP_NAME(MOP_ORI, "ori");
    OP_NAME(MOP_XOR, "xor");
    OP_NAME(MOP_XORI, "xori");
    OP_NAME(MOP_SLLI, "slli");
    OP_NAME(MOP_SRLI, "srli");
    OP_NAME(MOP_SRAI, "srai");
    OP_NAME(MOP_SLLIW, "slliw");
    OP_NAME(MOP_SRLIW, "srliw");
    OP_NAME(MOP_SRAIW, "sraiw");
    OP_NAME(MOP_SLT, "slt");
    OP_NAME(MOP_SEQZ, "seqz");
    OP_NAME(MOP_SNEZ, "snez");
    OP_NAME(MOP_LUI, "lui");
    OP_NAME(MOP_FLW, "flw");
    OP_NAME(MOP_FSW, "fsw");
    OP_NAME(MOP_FLD, "fld");
    OP_NAME(MOP_FSD, "fsd");
    OP_NAME(MOP_FADD_S, "fadd.s");
    OP_NAME(MOP_FSUB_S, "fsub.s");
    OP_NAME(MOP_FMUL_S, "fmul.s");
    OP_NAME(MOP_FDIV_S, "fdiv.s");
    OP_NAME(MOP_FNEG_S, "fneg.s");
    OP_NAME(MOP_FEQ_S, "feq.s");
    OP_NAME(MOP_FLT_S, "flt.s");
    OP_NAME(MOP_FLE_S, "fle.s");
    OP_NAME(MOP_FMV_W_X, "fmv.w.x");
    OP_NAME(MOP_FMV_X_W, "fmv.x.w");
    OP_NAME(MOP_FCVT_S_W, "fcvt.s.w");
    OP_NAME(MOP_FCVT_W_S, "fcvt.w.s");
    OP_NAME(MOP_FCVT_D_S, "fcvt.d.s");
    OP_NAME(MOP_FMV_X_D, "fmv.x.d");
    OP_NAME(MOP_F32_TO_GPR64, "f32.to.gpr64");
    OP_NAME(MOP_LW, "lw");
    OP_NAME(MOP_LD, "ld");
    OP_NAME(MOP_SW, "sw");
    OP_NAME(MOP_SD, "sd");
    OP_NAME(MOP_LW_FRAME, "lw.frame");
    OP_NAME(MOP_SW_FRAME, "sw.frame");
    OP_NAME(MOP_LD_FRAME, "ld.frame");
    OP_NAME(MOP_SD_FRAME, "sd.frame");
    OP_NAME(MOP_FLW_FRAME, "flw.frame");
    OP_NAME(MOP_FSW_FRAME, "fsw.frame");
    OP_NAME(MOP_ADDI_FRAME, "addi.frame");
    OP_NAME(MOP_BEQ, "beq");
    OP_NAME(MOP_BNE, "bne");
    OP_NAME(MOP_BLT, "blt");
    OP_NAME(MOP_BGE, "bge");
    OP_NAME(MOP_BLTU, "bltu");
    OP_NAME(MOP_BGTU, "bgtu");
    OP_NAME(MOP_J, "j");
    OP_NAME(MOP_CALL, "call");
    OP_NAME(MOP_RET, "ret");
#undef OP_NAME
  default:
    return "<invalid-op>";
  }
}

Inst::Inst() noexcept { std::memset(payload_, 0, sizeof(payload_)); }

void Inst::setOp(OpCode op, IRPhase phase) noexcept {
  assert((phase == IRPhase::MIR) == isMachineOp(op));
  UNUSED(phase);
  op_ = op;
  erased_ = false;
  undefValue_ = false;
}

Inst *Inst::getArg(u32 index) const noexcept {
  assert(!erased_ && index < operandCount_);
  return args_[index].inst;
}

BrPayload &Inst::mutableBranch() noexcept {
  assert(op_ == OP_BR || isMachineBranch(op_));
  return *branch_;
}
SwitchPayload &Inst::mutableSwitch() noexcept {
  assert(op_ == OP_SWITCH && switch_);
  return *switch_;
}
void Inst::setSwitchPayload(SwitchPayload *payload) noexcept {
  assert(op_ == OP_SWITCH);
  switch_ = payload;
}
void Inst::setJumpTarget(BasicBlock *target) noexcept {
  assert(op_ == OP_JMP || op_ == MOP_J);
  jumpTarget_ = target;
}
void Inst::setJumpTable(JumpTable *table) noexcept {
  if (op_ == MOP_LA)
    symbol_ = SymbolRef::jumpTableRef(table);
  else {
    assert(op_ == MOP_JT_DISPATCH);
    jumpTable_ = table;
  }
}
void Inst::setIncomingArray(BasicBlock **incoming) noexcept {
  assert(op_ == OP_PHI);
  incoming_ = incoming;
}
void Inst::setIncomingBlock(u32 index, BasicBlock *blockValue) noexcept {
  assert(op_ == OP_PHI && index < operandCount_);
  incoming_[index] = blockValue;
}

i32 Inst::getImm() const noexcept {
  assert(op_ == OP_ICONST || (isMachineOp(op_) && !isMachineFrameOp(op_)));
  assert(imm_ >= INT32_MIN && imm_ <= INT32_MAX);
  return static_cast<i32>(imm_);
}
i64 Inst::getImm64() const noexcept {
  assert(op_ == MOP_LI);
  return imm_;
}
void Inst::setImm64(i64 value) noexcept {
  assert(op_ == MOP_LI);
  imm_ = value;
}
f32 Inst::getFimm() const noexcept {
  assert(op_ == OP_FCONST);
  return fimm_;
}
i32 Inst::getArgNo() const noexcept {
  assert(op_ == OP_PARAM);
  return argNo_;
}
Global *Inst::getGlobal() const noexcept {
  assert(op_ == OP_GETGLOBAL ||
         (op_ == MOP_LA && symbol_.kind == SymbolRef::SymbolRefKind::Global));
  return op_ == OP_GETGLOBAL ? global_ : symbol_.global;
}
void Inst::setGlobal(Global *global) noexcept {
  if (op_ == MOP_LA)
    symbol_ = SymbolRef::globalRef(global);
  else {
    assert(op_ == OP_GETGLOBAL);
    global_ = global;
  }
}
SymbolRef Inst::getSymbolRef() const noexcept {
  assert(op_ == MOP_LA);
  return symbol_;
}
void Inst::setSymbolRef(SymbolRef symbol) noexcept {
  assert(op_ == MOP_LA);
  symbol_ = symbol;
}
MemPayload &Inst::getMem() noexcept {
  assert(mem_);
  return *mem_;
}
const MemPayload &Inst::getMem() const noexcept {
  assert(mem_);
  return *mem_;
}
ArrayPayload &Inst::getArray() noexcept {
  assert(array_);
  return *array_;
}
const ArrayPayload &Inst::getArray() const noexcept {
  assert(array_);
  return *array_;
}
Function *Inst::getCallee() const noexcept {
  assert(callInfo_);
  return callInfo_->callee;
}
void Inst::setCallee(Function *callee) noexcept {
  assert(callInfo_);
  callInfo_->callee = callee;
}
u64 Inst::getRegMask() const noexcept {
  assert(callInfo_);
  return callInfo_->clobberMask;
}
void Inst::setRegMask(u64 mask) noexcept {
  assert(callInfo_);
  callInfo_->clobberMask = mask;
}
const BrPayload &Inst::getBr() const noexcept {
  assert(branch_);
  return *branch_;
}
ScfPayload &Inst::getScf() noexcept {
  assert(scf_);
  return *scf_;
}
const ScfPayload &Inst::getScf() const noexcept {
  assert(scf_);
  return *scf_;
}
BasicBlock *Inst::getJumpTarget() const noexcept {
  assert(op_ == OP_JMP || op_ == MOP_J);
  return jumpTarget_;
}
Region *Inst::getBody() const noexcept {
  assert(op_ == OP_FOR);
  return body_;
}
const SwitchPayload &Inst::getSwitch() const noexcept {
  assert(op_ == OP_SWITCH && switch_);
  return *switch_;
}
SwitchPayload *Inst::getSwitchPayload() const noexcept {
  assert(op_ == OP_SWITCH);
  return switch_;
}
JumpTable *Inst::getJumpTable() const noexcept {
  assert(op_ == MOP_LA || op_ == MOP_JT_DISPATCH);
  return op_ == MOP_LA ? symbol_.jumpTable : jumpTable_;
}
BasicBlock *Inst::getIncomingBlock(u32 index) const noexcept {
  assert(op_ == OP_PHI && index < operandCount_);
  return incoming_[index];
}
i32 Inst::getStride() const noexcept {
  assert(op_ == OP_GETPTR);
  return static_cast<i32>(imm_);
}
i32 Inst::getFrameIndex() const noexcept {
  assert(isMachineFrameOp(op_));
  return frameIndex_;
}
bool Inst::isPrecoloredDef() const noexcept {
  return !block && id < 64 && op_ == MOP_NOP;
}

bool Inst::atFront() const noexcept {
  return block && (op_ == OP_PHI ? block->phiFirst : block->instFirst) == this;
}
bool Inst::atBack() const noexcept {
  return block && (op_ == OP_PHI ? block->phiLast : block->instLast) == this;
}
Inst *Inst::getParentOp() const noexcept {
  return block && block->parentRegion ? block->parentRegion->owner : nullptr;
}
bool Inst::inside(const Inst *outer) const noexcept {
  if (!outer)
    return false;
  for (const Region *region = block ? block->parentRegion : nullptr; region;
       region = region->parent)
    if (region->owner == outer)
      return true;
  return false;
}

static void unlinkInst(Inst *inst) noexcept {
  Inst *&first =
      inst->getOp() == OP_PHI ? inst->block->phiFirst : inst->block->instFirst;
  Inst *&last =
      inst->getOp() == OP_PHI ? inst->block->phiLast : inst->block->instLast;
  if (inst->prev)
    inst->prev->next = inst->next;
  else
    first = inst->next;
  if (inst->next)
    inst->next->prev = inst->prev;
  else
    last = inst->prev;
}

void Inst::moveBefore(Inst *anchor) noexcept {
  assert(anchor && anchor->block && block && op_ != OP_PHI &&
         anchor->getOp() != OP_PHI);
  if (anchor == this)
    return;
  unlinkInst(this);
  block = anchor->block;
  prev = anchor->prev;
  next = anchor;
  if (prev)
    prev->next = this;
  else
    block->instFirst = this;
  anchor->prev = this;
}

void Inst::moveAfter(Inst *anchor) noexcept {
  assert(anchor && anchor->block && block && op_ != OP_PHI &&
         anchor->getOp() != OP_PHI);
  if (anchor == this)
    return;
  unlinkInst(this);
  block = anchor->block;
  prev = anchor;
  next = anchor->next;
  if (next)
    next->prev = this;
  else
    block->instLast = this;
  anchor->next = this;
}

BasicBlock *BasicBlock::getPredecessor(u32 index) const noexcept {
  assert(index < predecessorCount_);
  return predecessors_[index];
}
bool BasicBlock::empty() const noexcept { return !phiFirst && !instFirst; }
bool BasicBlock::endsWithTerminator() const noexcept {
  return instLast && isTerminator(instLast->getOp());
}
Inst *BasicBlock::terminator() const noexcept {
  assert(endsWithTerminator());
  return instLast;
}

void BasicBlock::erase() noexcept {
  if (!parentRegion)
    return;
  if (prev)
    prev->next = next;
  else
    parentRegion->first = next;
  if (next)
    next->prev = prev;
  else
    parentRegion->last = prev;
  prev = next = nullptr;
  parentRegion = nullptr;
}
void BasicBlock::moveBefore(BasicBlock *anchor) noexcept {
  assert(anchor && anchor->parentRegion);
  if (anchor == this)
    return;
  erase();
  parentRegion = anchor->parentRegion;
  prev = anchor->prev;
  next = anchor;
  if (prev)
    prev->next = this;
  else
    parentRegion->first = this;
  anchor->prev = this;
}
void BasicBlock::moveAfter(BasicBlock *anchor) noexcept {
  assert(anchor && anchor->parentRegion);
  if (anchor == this)
    return;
  erase();
  parentRegion = anchor->parentRegion;
  prev = anchor;
  next = anchor->next;
  if (next)
    next->prev = this;
  else
    parentRegion->last = this;
  anchor->next = this;
}
void BasicBlock::moveToStart(Region *region) noexcept {
  assert(region);
  erase();
  parentRegion = region;
  prev = nullptr;
  next = region->first;
  if (next)
    next->prev = this;
  else
    region->last = this;
  region->first = this;
}
void BasicBlock::moveToEnd(Region *region) noexcept {
  assert(region);
  erase();
  parentRegion = region;
  next = nullptr;
  prev = region->last;
  if (prev)
    prev->next = this;
  else
    region->first = this;
  region->last = this;
}
bool BasicBlock::atFront() const noexcept {
  return parentRegion && parentRegion->first == this;
}
bool BasicBlock::atBack() const noexcept {
  return parentRegion && parentRegion->last == this;
}

void BasicBlock::inlineBefore(Inst *anchor) noexcept {
  assert(anchor && anchor->block && anchor->getOp() != OP_PHI && !phiFirst);
  if (!instFirst) {
    erase();
    return;
  }
  BasicBlock *destination = anchor->block;
  for (Inst *inst = instFirst; inst; inst = inst->next)
    inst->block = destination;
  instFirst->prev = anchor->prev;
  instLast->next = anchor;
  if (anchor->prev)
    anchor->prev->next = instFirst;
  else
    destination->instFirst = instFirst;
  anchor->prev = instLast;
  instFirst = instLast = nullptr;
  erase();
}

void Region::spliceBlocks(Region *source) noexcept {
  if (!source || !source->first)
    return;
  for (BasicBlock *block = source->first; block; block = block->next)
    block->parentRegion = this;
  if (last) {
    last->next = source->first;
    source->first->prev = last;
  } else
    first = source->first;
  last = source->last;
  source->first = source->last = nullptr;
}
void Region::adoptBlock(BasicBlock *block) noexcept {
  assert(block);
  block->moveToEnd(this);
}

JumpTable *Function::newJumpTable() {
  JumpTable *table = arena->create<JumpTable>();
  table->next = jumpTableHead;
  jumpTableHead = table;
  return table;
}
i32 Function::newFrameSlot(i32 size, i32 alignment, FrameSlot::Kind kind) {
  assert(size >= 0 && alignment > 0 && (alignment & (alignment - 1)) == 0);
  frameSlots.push_back({size, alignment, 0, kind});
  return static_cast<i32>(frameSlots.size() - 1);
}

Inst *Module::physicalRegister(u32 reg) const noexcept {
  assert(reg < 64);
  return physicalRegisterDefs[reg];
}
void Module::initPregDefs() {
  for (u32 reg = 0; reg < 64; ++reg) {
    Inst *inst = arena->create<Inst>();
    inst->setOp(MOP_NOP, IRPhase::MIR);
    inst->setType(reg < 32 ? TY_I32 : TY_F32);
    inst->id = reg;
    inst->arena = arena;
    physicalRegisterDefs[reg] = inst;
  }
}
Module *Module::create(Arena &storage) {
  Module *module = storage.create<Module>();
  module->arena = &storage;
  module->initPregDefs();
  return module;
}

Function *Module::newFunction(const char *functionName, IRType resultType,
                              const IRType *types, u32 count,
                              FunctionType *type, bool external) {
  Function *function = arena->create<Function>();
  function->name = functionName;
  function->module = this;
  function->returnType = resultType;
  function->paramCount = count;
  function->functionType = type;
  function->isExtern = external;
  function->arena = arena;
  if (count) {
    function->paramTypes = arena->createArray<IRType>(count);
    function->params = arena->createArray<Inst *>(count);
    std::copy_n(types, count, function->paramTypes);
  }
  if (!external) {
    function->region = arena->create<Region>();
    function->region->function = function;
  }
  for (u32 index = 0; index < count; ++index) {
    Inst *param = arena->create<Inst>();
    param->arena = arena;
    param->setOp(OP_PARAM, IRPhase::HIR);
    param->setType(types[index]);
    param->setArgNo(static_cast<i32>(index));
    param->id = function->instCount++;
    function->params[index] = param;
  }
  if (functionTail)
    functionTail->next = function;
  else
    functionHead = function;
  functionTail = function;
  return function;
}

Global *Module::newGlobal(const char *globalName, IRType elementType, u32 size,
                          u32 elements, bool constant, bool array) {
  Global *global = arena->create<Global>();
  global->name = globalName;
  global->type = elementType;
  global->totalSizeBytes = size;
  global->numElements = elements;
  global->isConst = constant;
  global->isArray = array;
  global->prev = globalTail;
  if (globalTail)
    globalTail->next = global;
  else
    globalHead = global;
  globalTail = global;
  return global;
}

} // namespace svm::ir
