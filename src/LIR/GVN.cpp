#include "Analysis.h"
#include "LIRPass.h"
#include "MemDep.h"

#include <functional>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

bool isGVNCandidate(OpCode op) noexcept {
  return isBinaryArithmetic(op) || isUnaryArithmetic(op) || isCompare(op) ||
         isConversion(op) || op == OP_GETPTR || op == OP_ARRAYIDX ||
         op == OP_LOAD || op == OP_CALL || op == OP_SELECT;
}

bool isCommutative(OpCode op) noexcept {
  switch (op) {
  case OP_ADD:
  case OP_MUL:
  case OP_EQ:
  case OP_NE:
  case OP_FADD:
  case OP_FMUL:
  case OP_FEQ:
  case OP_FNE:
    return true;
  default:
    return false;
  }
}

struct ValueKey {
  OpCode op = OP_ICONST;         // 指令操作码
  IRType type = TY_VOID;         // 结果类型
  Function *callee = nullptr;    // 调用目标
  i32 stride = 0;                // GETPTR字节步长
  IRType elementType = TY_VOID;  // 数组或访存元素类型
  u32 memorySize = 0;            // LOAD访问宽度
  std::vector<Inst *> operands;  // 归约到leader的操作数
  std::vector<u32> arrayStrides; // ARRAYIDX各维步长

  bool operator==(const ValueKey &other) const noexcept {
    return op == other.op && type == other.type && callee == other.callee &&
           stride == other.stride && elementType == other.elementType &&
           memorySize == other.memorySize && operands == other.operands &&
           arrayStrides == other.arrayStrides;
  }
};

struct ValueKeyHash {
  usize operator()(const ValueKey &key) const noexcept {
    auto mix = [](usize hash, usize value) noexcept {
      return hash ^ (value + usize{0x9e3779b9U} + (hash << 6) + (hash >> 2));
    };

    usize hash = std::hash<u16>{}(static_cast<u16>(key.op));
    hash = mix(hash, std::hash<u8>{}(static_cast<u8>(key.type)));
    hash = mix(hash, std::hash<Function *>{}(key.callee));
    hash = mix(hash, std::hash<i32>{}(key.stride));
    hash = mix(hash, std::hash<u8>{}(static_cast<u8>(key.elementType)));
    hash = mix(hash, std::hash<u32>{}(key.memorySize));
    for (Inst *operand : key.operands)
      hash = mix(hash, std::hash<Inst *>{}(operand));
    for (u32 stride : key.arrayStrides)
      hash = mix(hash, std::hash<u32>{}(stride));
    return hash;
  }
};

class ScopedValueTable {
public:
  void enter() { undoScopes_.emplace_back(); }
  void leave() {
    VERIFY(!undoScopes_.empty(), "GVN leave() without enter()");
    std::vector<Undo> &undo = undoScopes_.back();
    for (auto it = undo.rbegin(); it != undo.rend(); ++it) {
      if (it->hadPrevious)
        values_[it->key] = it->previous;
      else
        values_.erase(it->key);
    }
    undoScopes_.pop_back();
  }
  Inst *lookup(const ValueKey &key) const { // 查询当前可见leader
    const auto found = values_.find(key);
    return found == values_.end() ? nullptr : found->second;
  }
  void insert(ValueKey key, Inst *leader) { // 插入leader并记录撤销信息
    VERIFY(!undoScopes_.empty() && leader, "invalid GVN insertion");
    const auto found = values_.find(key);
    if (found != values_.end()) {
      undoScopes_.back().push_back({found->first, found->second, true});
      found->second = leader;
      return;
    }
    undoScopes_.back().push_back({key, nullptr, false});
    values_.emplace(std::move(key), leader);
  }

private:
  struct Undo {
    ValueKey key;             // 被修改的值编号键
    Inst *previous = nullptr; // 被遮蔽的leader
    bool hadPrevious = false; // 修改前是否存在键
  };

  std::unordered_map<ValueKey, Inst *, ValueKeyHash> values_; // 可见leader表
  std::vector<std::vector<Undo>> undoScopes_;                 // 分层撤销日志
};

class GVNContext {
public:
  GVNContext(Function *function, const DomChildrenMap &children,
             const AliasInfo &aliasInfo, const GlobalSummaryResult *summary,
             const MemDepOracle &memDep) noexcept
      : function_(function), children_(children), aliasInfo_(aliasInfo),
        summary_(summary), memDep_(memDep) {}

  bool run(BasicBlock *entry) {
    struct Frame {
      BasicBlock *block = nullptr; // 当前支配树节点
      usize nextChild = 0;         // 下一个待访问子节点
      bool entered = false;        // 是否已处理当前节点
    };

    std::vector<Frame> stack{{entry, 0, false}};
    while (!stack.empty()) {
      Frame &frame = stack.back();
      if (!frame.entered) {
        valueTable_.enter();
        processBlock(frame.block);
        frame.entered = true;
      }

      const auto found = children_.find(frame.block);
      if (found != children_.end() && frame.nextChild < found->second.size()) {
        stack.push_back({found->second[frame.nextChild++], 0, false});
        continue;
      }

      valueTable_.leave();
      stack.pop_back();
    }

    for (Inst *dead : dead_) {
      const auto found = remap_.find(dead);
      VERIFY(found != remap_.end() && found->second);
      replaceAllUsesWith(function_, dead, found->second);
      VERIFY(dead->eraseFromBlock());
    }
    return !dead_.empty();
  }

private:
  // 递归查找最终leader
  Inst *resolveLeader(Inst *value) const noexcept {
    const auto found = remap_.find(value);
    return found == remap_.end() ? value : found->second;
  }
  // 构造包含全部语义payload的键
  ValueKey buildKey(Inst *inst) const {
    ValueKey key;
    key.op = inst->getOp();
    key.type = inst->getType();
    key.operands.reserve(inst->getOperandCount());
    for (u32 index = 0; index < inst->getOperandCount(); ++index)
      key.operands.push_back(resolveLeader(inst->getArg(index)));

    if (isCommutative(key.op) && key.operands.size() == 2 &&
        std::less<Inst *>{}(key.operands[1], key.operands[0]))
      std::swap(key.operands[0], key.operands[1]);

    switch (key.op) {
    case OP_CALL:
      key.callee = inst->getCallee();
      break;
    case OP_GETPTR:
      key.stride = inst->getStride();
      break;
    case OP_ARRAYIDX: {
      const ArrayPayload &array = inst->getArray();
      key.elementType = array.elementType;
      if (array.nDims != 0) {
        VERIFY(array.strides, "ARRAYIDX requires strides");
        key.arrayStrides.assign(array.strides, array.strides + array.nDims);
      }
      break;
    }
    case OP_LOAD:
      key.elementType = inst->getMem().elementType;
      key.memorySize = inst->getMem().totalSizeBytes;
      break;
    default:
      break;
    }
    return key;
  }
  // 记录延迟RAUW目标
  void markRedundant(Inst *inst, Inst *leader) {
    VERIFY(inst && leader && inst != leader, "invalid GVN replacement");
    remap_.emplace(inst, resolveLeader(leader));
    dead_.push_back(inst);
  }
  // 查询调用写内存
  bool mayWriteCall(Inst *call, const MemoryLocation &location) const {
    if (!summary_)
      return aliasInfo_.mayWriteMemory(call, location);
    return aliasInfo_.mayWriteMemory(call, location,
                                     summary_->calleeEffect(call->getCallee()));
  }
  // 判定可值编号调用
  bool isGVNableCall(Inst *call) const noexcept {
    return call && call->getOp() == OP_CALL && !isVoid(call->getType()) &&
           call->getCallee() && summary_ &&
           summary_->calleeEffect(call->getCallee()).isReadOnly();
  }
  // 查询实参指向内存读取
  bool callReadsPointerArg(Inst *call, const EffectSummary &effects,
                           u32 index) const noexcept {
    return index < call->getOperandCount() && call->getArg(index) &&
           isPtr(call->getArg(index)->getType()) &&
           effects.readsParam(static_cast<i32>(index));
  }
  // 查询writer是否污染调用读集
  bool writeMayAffectCallResult(Inst *writer, Inst *call,
                                const EffectSummary &callEffects) const {
    if (!writer || !call)
      return false;

    if (writer->getOp() == OP_STORE) {
      Inst *address = writer->getArg(0);
      const PointerInfo info = aliasInfo_.info(address);
      if (!(callEffects.flags & EffectSummary::F_NO_READ_GLOBAL)) {
        if (info.kind == PointerKind::Global && info.root &&
            info.root->getOp() == OP_GETGLOBAL) {
          if (callEffects.readsGlobal(info.root->getGlobal()))
            return true;
        } else if (info.kind == PointerKind::Param ||
                   info.kind == PointerKind::Opaque) {
          return true;
        }
      }

      for (u32 index = 0; index < call->getOperandCount(); ++index)
        if (callReadsPointerArg(call, callEffects, index) &&
            aliasInfo_.alias(address, call->getArg(index)) !=
                AliasResult::NoAlias)
          return true;
      return false;
    }

    if (!writer->isCallInstruction())
      return false;
    const EffectSummary &writerEffects =
        summary_ ? summary_->calleeEffect(writer->getCallee())
                 : conservativeEffectSummary();

    if (!(callEffects.flags & EffectSummary::F_NO_READ_GLOBAL)) {
      if (callEffects.readsUnknownGlobal) {
        if (!(writerEffects.flags & EffectSummary::F_NO_WRITE_GLOBAL))
          return true;
      } else {
        if (writerEffects.writesUnknownGlobal)
          return true;
        for (Global *global : callEffects.readGlobals)
          if (writerEffects.writesGlobal(global))
            return true;
      }

      for (u32 index = 0; index < writer->getOperandCount(); ++index) {
        if (!writerEffects.writesParam(static_cast<i32>(index)))
          continue;
        Inst *actual = writer->getArg(index);
        if (!actual || !isPtr(actual->getType()))
          continue;
        const PointerInfo info = aliasInfo_.info(actual);
        if (info.kind == PointerKind::Global && info.root &&
            info.root->getOp() == OP_GETGLOBAL) {
          if (callEffects.readsGlobal(info.root->getGlobal()))
            return true;
        } else if (info.kind == PointerKind::Param ||
                   info.kind == PointerKind::Opaque) {
          return true;
        }
      }
    }

    for (u32 index = 0; index < call->getOperandCount(); ++index)
      if (callReadsPointerArg(call, callEffects, index) &&
          aliasInfo_.mayWriteMemory(writer, call->getArg(index), writerEffects))
        return true;
    return false;
  }
  // 查询同块最近调用结果污染
  Inst *findCallClobberInBlock(Inst *call, const EffectSummary &effects) const {
    for (Inst *cursor = call->previous(); cursor; cursor = cursor->previous())
      if (writeMayAffectCallResult(cursor, call, effects))
        return cursor;
    return nullptr;
  }
  // 查询单前驱路径调用污染
  Inst *findCallClobberOnLinearPath(Inst *call, const EffectSummary &effects,
                                    BasicBlock *start, BasicBlock *stop,
                                    bool &gaveUp) const {
    gaveUp = false;
    std::unordered_set<BasicBlock *> visited;
    for (BasicBlock *block = start; block;) {
      if (!visited.insert(block).second) {
        gaveUp = true;
        return nullptr;
      }
      for (Inst *cursor = block->lastInst(); cursor;
           cursor = cursor->previous())
        if (writeMayAffectCallResult(cursor, call, effects))
          return cursor;
      if (block == stop || block->getPredecessorCount() == 0)
        return nullptr;
      if (block->getPredecessorCount() != 1) {
        gaveUp = true;
        return nullptr;
      }
      block = block->getPredecessor(0);
    }
    return nullptr;
  }
  // 证明两次调用之间读集未被写入
  bool isCallForwardingSafe(Inst *leader, Inst *call,
                            const EffectSummary &effects,
                            Inst *localClobber) const {
    if (effects.isReadNoneNoSideEffect())
      return true;

    BasicBlock *block = call->parentBlock();
    if (localClobber) {
      if (leader->parentBlock() != block)
        return false;
      for (Inst *cursor = call->previous(); cursor && cursor != localClobber;
           cursor = cursor->previous())
        if (cursor == leader)
          return true;
      return false;
    }

    if (leader->parentBlock() == block)
      return true;
    if (block->getPredecessorCount() != 1)
      return false;

    bool gaveUp = false;
    Inst *pathClobber = findCallClobberOnLinearPath(
        call, effects, block->getPredecessor(0), leader->parentBlock(), gaveUp);
    if (gaveUp)
      return false;
    if (!pathClobber)
      return true;
    if (pathClobber->parentBlock() != leader->parentBlock())
      return false;
    for (Inst *cursor = leader->previous(); cursor; cursor = cursor->previous())
      if (cursor == pathClobber)
        return true;
    return false;
  }
  // 执行load值编号和store转发
  void processLoad(Inst *load) {
    BasicBlock *block = load->parentBlock();
    Inst *pointer = resolveLeader(load->getArg(0));
    MemoryLocation location = MemoryLocation::fromMemoryInstruction(load);
    location.pointer = pointer;

    Inst *localClobber = nullptr;
    for (Inst *cursor = load->previous(); cursor; cursor = cursor->previous()) {
      if (cursor->getOp() == OP_STORE) {
        MemoryLocation stored = MemoryLocation::fromMemoryInstruction(cursor);
        stored.pointer = resolveLeader(stored.pointer);
        if (aliasInfo_.alias(location, stored) != AliasResult::NoAlias) {
          localClobber = cursor;
          break;
        }
      }
      if (cursor->isCallInstruction() && mayWriteCall(cursor, location)) {
        localClobber = cursor;
        break;
      }
    }

    if (localClobber && localClobber->getOp() == OP_STORE) {
      MemoryLocation stored =
          MemoryLocation::fromMemoryInstruction(localClobber);
      stored.pointer = resolveLeader(stored.pointer);
      if (aliasInfo_.alias(location, stored) == AliasResult::MustAlias &&
          localClobber->getArg(1)->getType() == load->getType()) {
        markRedundant(load, resolveLeader(localClobber->getArg(1)));
        return;
      }
    }

    ValueKey key = buildKey(load);
    if (Inst *leader = valueTable_.lookup(key)) {
      bool safe = false;
      if (localClobber) {
        if (leader->parentBlock() == block)
          for (Inst *cursor = load->previous();
               cursor && cursor != localClobber; cursor = cursor->previous())
            if (cursor == leader) {
              safe = true;
              break;
            }
      } else if (leader->parentBlock() == block) {
        safe = true;
      } else if (block->getPredecessorCount() == 1) {
        bool gaveUp = false;
        Inst *pathClobber = memDep_.findClobberOnLinearPath(
            location, block->getPredecessor(0), leader->parentBlock(), gaveUp);
        if (!gaveUp && !pathClobber) {
          safe = true;
        } else if (!gaveUp &&
                   pathClobber->parentBlock() == leader->parentBlock()) {
          for (Inst *cursor = leader->previous(); cursor;
               cursor = cursor->previous())
            if (cursor == pathClobber) {
              safe = true;
              break;
            }
        }
      }

      if (safe) {
        markRedundant(load, leader);
        return;
      }
    }

    if (!localClobber && block->getPredecessorCount() == 1) {
      bool gaveUp = false;
      Inst *pathClobber = memDep_.findClobberOnLinearPath(
          location, block->getPredecessor(0), nullptr, gaveUp);
      if (!gaveUp && pathClobber && pathClobber->getOp() == OP_STORE) {
        MemoryLocation stored =
            MemoryLocation::fromMemoryInstruction(pathClobber);
        stored.pointer = resolveLeader(stored.pointer);
        if (aliasInfo_.alias(location, stored) == AliasResult::MustAlias &&
            pathClobber->getArg(1)->getType() == load->getType()) {
          markRedundant(load, resolveLeader(pathClobber->getArg(1)));
          return;
        }
      }
    }

    valueTable_.insert(std::move(key), load);
  }
  // 执行readonly/readnone调用值编号
  void processCall(Inst *call) {
    if (!isGVNableCall(call))
      return;
    const EffectSummary &effects = summary_->calleeEffect(call->getCallee());
    Inst *localClobber = effects.isReadNoneNoSideEffect()
                             ? nullptr
                             : findCallClobberInBlock(call, effects);
    ValueKey key = buildKey(call);
    if (Inst *leader = valueTable_.lookup(key))
      if (isCallForwardingSafe(leader, call, effects, localClobber)) {
        markRedundant(call, leader);
        return;
      }
    valueTable_.insert(std::move(key), call);
  }
  // 扫描单个基本块的候选指令
  void processBlock(BasicBlock *block) {
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      if (!isGVNCandidate(inst->getOp()))
        continue;
      if (inst->getOp() == OP_LOAD) {
        processLoad(inst);
        continue;
      }
      if (inst->getOp() == OP_CALL) {
        processCall(inst);
        continue;
      }

      ValueKey key = buildKey(inst);
      if (Inst *leader = valueTable_.lookup(key))
        markRedundant(inst, leader);
      else
        valueTable_.insert(std::move(key), inst);
    }
  }

  Function *function_ = nullptr;
  const DomChildrenMap &children_;
  const AliasInfo &aliasInfo_;
  const GlobalSummaryResult *summary_ = nullptr;
  const MemDepOracle &memDep_;
  std::unordered_map<Inst *, Inst *> remap_; // 冗余值到最终leader
  std::vector<Inst *> dead_;                 // 延迟删除指令
  ScopedValueTable valueTable_;              // 支配作用域leader表
};

} // namespace

std::string_view GVNPass::name() const noexcept { return "gvn"; }

PassResult GVNPass::run(Function *function, PassContext &context) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();

  const DominatorTree &dom = context.get<DomAnalysis>(function).tree;
  const AliasInfo &aliasInfo = context.get<AliasAnalysis>(function).info;
  const GlobalSummaryResult *summary =
      function->module
          ? &context.get<GlobalSummaryAnalysis>(function->module).result
          : nullptr;
  MemDepOracle memDep(&aliasInfo, summary);
  GVNContext gvn(function, dom.children(), aliasInfo, summary, memDep);
  if (!gvn.run(function->region->first))
    return PassResult::noChange();

  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
