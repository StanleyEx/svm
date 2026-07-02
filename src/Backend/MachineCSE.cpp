#include "Analysis.h"
#include "MIRPass.h"
#include "RV64.h"

#include <algorithm>
#include <cassert>
#include <functional>
#include <unordered_map>
#include <vector>

namespace svm::ir {
namespace {

struct CSEKey {
  OpCode op = MOP_NOP;   // 表达式操作码
  IRType type = TY_VOID; // 结果类型
  Inst *args[3] = {};    // 规范化后的操作数
  u8 argCount = 0;       // 有效操作数个数
  i64 immediate = 0;     // 完整立即数载荷
  SymbolRef symbol{};    // 符号地址载荷

  bool operator==(const CSEKey &other) const noexcept {
    return op == other.op && type == other.type && args[0] == other.args[0] &&
           args[1] == other.args[1] && args[2] == other.args[2] &&
           argCount == other.argCount && immediate == other.immediate &&
           symbol == other.symbol;
  }
};

struct CSEKeyHash {
  auto hashCombine(usize &hash, usize value) const noexcept -> void {
    // boost::hash_combine
    hash ^= value + usize{0x9e3779b97f4a7c15ULL} + (hash << 6) + (hash >> 2);
  }
  usize operator()(const CSEKey &key) const noexcept {
    usize hash = std::hash<u16>{}(static_cast<u16>(key.op));
    hashCombine(hash, std::hash<u8>{}(static_cast<u8>(key.type)));
    hashCombine(hash, std::hash<Inst *>{}(key.args[0]));
    hashCombine(hash, std::hash<Inst *>{}(key.args[1]));
    hashCombine(hash, std::hash<Inst *>{}(key.args[2]));
    hashCombine(hash, std::hash<u8>{}(key.argCount));
    hashCombine(hash, std::hash<i64>{}(key.immediate));
    hashCombine(hash, std::hash<u8>{}(static_cast<u8>(key.symbol.kind)));
    switch (key.symbol.kind) {
    case SymbolRef::SymbolRefKind::Global:
      hashCombine(hash, std::hash<Global *>{}(key.symbol.global));
      break;
    case SymbolRef::SymbolRefKind::MergedBase:
      hashCombine(hash, std::hash<u16>{}(key.symbol.mergedGroup));
      break;
    case SymbolRef::SymbolRefKind::JumpTable:
      hashCombine(hash, std::hash<JumpTable *>{}(key.symbol.jumpTable));
      break;
    case SymbolRef::SymbolRefKind::None:
      break;
    }
    return hash;
  }
};

bool stableValueLess(const Inst *left, const Inst *right) noexcept {
  if (left->isPrecoloredDef() != right->isPrecoloredDef())
    return left->isPrecoloredDef() < right->isPrecoloredDef();
  const bool leftFloat = isFloat(left->getType());
  const bool rightFloat = isFloat(right->getType());
  if (leftFloat != rightFloat)
    return leftFloat < rightFloat;
  return left->id < right->id;
}

bool isCommutative(OpCode op) noexcept {
  switch (op) {
  case MOP_ADDW:
  case MOP_ADD:
  case MOP_MULW:
  case MOP_MUL:
  case MOP_AND:
  case MOP_OR:
  case MOP_XOR:
  case MOP_FADD_S:
  case MOP_FMUL_S:
  case MOP_FEQ_S:
    return true;
  default:
    return false;
  }
}

bool hasImmediate(OpCode op) noexcept {
  switch (op) {
  case MOP_LI:
  case MOP_LUI:
  case MOP_ADDIW:
  case MOP_ADDI:
  case MOP_ANDI:
  case MOP_ORI:
  case MOP_XORI:
  case MOP_SLLIW:
  case MOP_SRAIW:
  case MOP_SRLIW:
  case MOP_SLLI:
  case MOP_SRAI:
  case MOP_SRLI:
    return true;
  default:
    return false;
  }
}

bool isCandidate(OpCode op) noexcept {
  switch (op) {
  case MOP_ADDW:
  case MOP_ADDIW:
  case MOP_SUBW:
  case MOP_MULW:
  case MOP_DIVW:
  case MOP_REMW:
  case MOP_NEGW:
  case MOP_ADD:
  case MOP_ADDI:
  case MOP_SUB:
  case MOP_MUL:
  case MOP_AND:
  case MOP_ANDI:
  case MOP_OR:
  case MOP_ORI:
  case MOP_XOR:
  case MOP_XORI:
  case MOP_SLLIW:
  case MOP_SRAIW:
  case MOP_SRLIW:
  case MOP_SLLI:
  case MOP_SRAI:
  case MOP_SRLI:
  case MOP_SLT:
  case MOP_SEQZ:
  case MOP_SNEZ:
  case MOP_SEXT_W:
  case MOP_LUI:
  case MOP_LI:
  case MOP_LA:
  case MOP_FADD_S:
  case MOP_FSUB_S:
  case MOP_FMUL_S:
  case MOP_FDIV_S:
  case MOP_FNEG_S:
  case MOP_FMV_W_X:
  case MOP_FMV_X_W:
  case MOP_FCVT_S_W:
  case MOP_FCVT_W_S:
  case MOP_FEQ_S:
  case MOP_FLT_S:
  case MOP_FLE_S:
    return true;
  default:
    return false;
  }
}

bool isCheapAcrossBlocks(const Inst *inst) noexcept {
  switch (inst->getOp()) {
  case MOP_ADDI:
  case MOP_ADDIW:
    return rv64::fitsImm12(inst->getImm());
  case MOP_ANDI:
  case MOP_ORI:
  case MOP_XORI:
  case MOP_SLLI:
  case MOP_SRAI:
  case MOP_SRLI:
  case MOP_SLLIW:
  case MOP_SRAIW:
  case MOP_SRLIW:
  case MOP_SEQZ:
  case MOP_SNEZ:
  case MOP_SEXT_W:
    return true;
  case MOP_LI:
    return rv64::fitsImm12(inst->getImm64());
  default:
    return false;
  }
}

bool makeKey(Inst *inst, CSEKey &key) noexcept {
  if (!inst || isVoid(inst->getType()) || inst->getType() == TY_F64 ||
      !isCandidate(inst->getOp()) || inst->getOperandCount() > 3)
    return false;

  key = {};
  key.op = inst->getOp();
  key.type = inst->getType();
  key.argCount = static_cast<u8>(inst->getOperandCount());
  for (u32 index = 0; index < inst->getOperandCount(); ++index)
    key.args[index] = inst->getArg(index);
  if (key.argCount == 2 && isCommutative(key.op) &&
      stableValueLess(key.args[1], key.args[0]))
    std::swap(key.args[0], key.args[1]);

  if (key.op == MOP_LI)
    key.immediate = inst->getImm64();
  else if (hasImmediate(key.op))
    key.immediate = inst->getImm();
  if (key.op == MOP_LA)
    key.symbol = inst->getSymbolRef();
  return true;
}

struct Binding {
  CSEKey key;             // 被压入作用域的表达式
  Inst *leader = nullptr; // 当前表达式定义
};

class MachineCSEImpl {
public:
  MachineCSEImpl(Function *function, const DominatorTree &dominators)
      : function_(function), builder_(function->module, function),
        dominators_(dominators), children_(dominators.children()) {}

  bool run() {
    visit(function_->region->first);
    return changed_;
  }

private:
  bool canReuse(Inst *leader, Inst *candidate) const noexcept { // 判断复用收益
    if (!leader || leader == candidate)
      return false;
    if (leader->parentBlock() == candidate->parentBlock())
      return true;
    return dominators_.dominates(leader->parentBlock(),
                                 candidate->parentBlock()) &&
           !isCheapAcrossBlocks(candidate);
  }

  void rollback(usize mark) { // 撤销离开支配子树后的定义
    while (undo_.size() > mark) {
      Binding binding = undo_.back();
      undo_.pop_back();
      auto found = table_.find(binding.key);
      assert(found != table_.end() && !found->second.empty() &&
             found->second.back() == binding.leader);
      found->second.pop_back();
      if (found->second.empty())
        table_.erase(found);
    }
  }

  void visit(BasicBlock *block) {
    if (!block || dominators_.getDepth(block) < 0)
      return;
    const usize mark = undo_.size();
    for (Inst *inst = block->firstInst(); inst;) {
      Inst *next = inst->next();
      CSEKey key;
      if (!makeKey(inst, key)) {
        inst = next;
        continue;
      }
      Inst *leader = nullptr;
      const auto found = table_.find(key);
      if (found != table_.end() && !found->second.empty())
        leader = found->second.back();
      if (canReuse(leader, inst)) {
        // Candidate上的事实可能只在当前支配路径成立 不能提升到更早的leader
        if (builder_.replace(inst, leader)) {
          changed_ = true;
          inst = next;
          continue;
        }
      }
      table_[key].push_back(inst);
      undo_.push_back({key, inst});
      inst = next;
    }
    const auto children = children_.find(block);
    if (children != children_.end())
      for (BasicBlock *child : children->second)
        visit(child);
    rollback(mark);
  }

  Function *function_ = nullptr;
  IRBuilder builder_;
  const DominatorTree &dominators_;
  const DomChildrenMap &children_;
  std::unordered_map<CSEKey, std::vector<Inst *>, CSEKeyHash> table_; // 值表
  std::vector<Binding> undo_; // 作用域撤销栈
  bool changed_ = false;
};

} // namespace

std::string_view MachineCSEPass::name() const noexcept { return "machine-cse"; }

PassResult MachineCSEPass::run(Function *function, PassContext &context) {
  if (!function || function->phase != IRPhase::MIR ||
      function->mirPhase != MIRPhase::SSA || function->isExtern ||
      !function->region || !function->region->first)
    return PassResult::noChange();

  computeUses(function);
  const DominatorTree &dominators = context.get<DomAnalysis>(function).tree;
  const bool changed = MachineCSEImpl(function, dominators).run();
  if (!changed)
    return PassResult::noChange();

  MachineDCE(function);
  PreservedAnalyses preserved = PreservedAnalyses::none();
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
