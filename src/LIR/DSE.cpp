#include "Analysis.h"
#include "LIRPass.h"
#include "MemDep.h"

#include <limits>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace svm::ir {
namespace {

struct GlobalReadLocation {
  i64 offset = 0; // 相对全局对象起点的字节偏移
  u64 size = 0;   // 本次读取的字节宽度
};

bool allocaAddressIsObservable(Inst *root, const GlobalSummaryResult &summary) {
  VERIFY(root && root->getOp() == OP_ALLOCA);
  std::vector<Inst *> worklist{root};
  std::unordered_set<Inst *> visited{root};

  while (!worklist.empty()) {
    Inst *pointer = worklist.back();
    worklist.pop_back();
    for (const Use *use = pointer->uses(); use; use = use->next) {
      Inst *user = use->user;
      if (!user || user->isErased())
        continue;

      switch (user->getOp()) {
      case OP_LOAD:
        break;
      case OP_STORE:
        if (use->argNo != 0)
          return true;
        break;
      case OP_RET:
        return true;
      case OP_CALL:
      case MOP_CALL: {
        const EffectSummary &effect = summary.calleeEffect(user->getCallee());
        const i32 argument = static_cast<i32>(use->argNo);
        if (effect.readsParam(argument) || effect.escapesParam(argument))
          return true;
        break;
      }
      case OP_GETPTR:
      case OP_ARRAYIDX:
      case OP_PHI:
      case OP_SELECT:
        if (user->getType() != TY_PTR)
          return true;
        if (visited.insert(user).second)
          worklist.push_back(user);
        break;
      default:
        return true;
      }
    }
  }
  return false;
}

class GlobalReaderModel {
public:
  // 记录无法归约到具体全局对象的读取
  void disable() noexcept { disabled_ = true; }
  // 记录对具体全局对象但未知偏移的读取
  void addUnknown(Global *global) {
    if (global)
      unknownReaders_.insert(global);
  }
  // 记录对具体全局对象的精确读取区间
  void addExact(Global *global, i64 offset, u64 size) {
    if (global)
      exactReaders_[global].push_back({offset, size});
  }
  // 判断给定全局写区间在全模块内是否没有任何潜在读者
  bool hasNoReader(Global *global, std::optional<i64> offset,
                   std::optional<u64> size) const {
    if (!global || disabled_ || unknownReaders_.count(global))
      return false;
    const auto found = exactReaders_.find(global);
    if (found == exactReaders_.end())
      return true;
    if (!offset || !size || *size == 0 ||
        *size > static_cast<u64>(std::numeric_limits<i64>::max()))
      return false;
    i64 storeEnd = 0;
    if (!checkedAdd(*offset, static_cast<i64>(*size), storeEnd))
      return false;
    for (const GlobalReadLocation &reader : found->second) {
      if (reader.size == 0 ||
          reader.size > static_cast<u64>(std::numeric_limits<i64>::max()))
        return false;
      i64 readerEnd = 0;
      if (!checkedAdd(reader.offset, static_cast<i64>(reader.size),
                      readerEnd) ||
          !(storeEnd <= reader.offset || readerEnd <= *offset))
        return false;
    }
    return true;
  }

private:
  // 是否存在读取任意全局的操作
  bool disabled_ = false;
  // 含未知偏移读者的全局集合
  std::unordered_set<Global *> unknownReaders_;
  // 每个全局对象的精确读取区间
  std::unordered_map<Global *, std::vector<GlobalReadLocation>> exactReaders_;
};

GlobalReaderModel buildGlobalReaderModel(Module *module, PassContext &context,
                                         const GlobalSummaryResult &summary) {
  GlobalReaderModel readers;
  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (function->isExtern || !function->region)
      continue;
    if (function->phase != IRPhase::LIR) {
      readers.disable();
      continue;
    }

    if (summary.effectOf(function).readsUnknownGlobal)
      readers.disable();
    const AliasInfo &aliases = context.get<AliasAnalysis>(function).info;
    for (BasicBlock *block = function->region->first; block;
         block = block->next()) {
      forEachInst(block, [&](Inst *inst) {
        const OpCode op = inst->getOp();
        if (op == OP_LOAD) {
          const MemoryLocation location =
              MemoryLocation::fromMemoryInstruction(inst);
          const PointerInfo pointer = aliases.info(location.pointer);
          if (pointer.kind == PointerKind::Opaque) {
            readers.disable();
            return;
          }
          if (pointer.kind != PointerKind::Global)
            return;
          if (!pointer.root || pointer.root->getOp() != OP_GETGLOBAL) {
            readers.disable();
            return;
          }
          Global *global = pointer.root->getGlobal();
          if (pointer.constantOffset && location.accessSize)
            readers.addExact(global, *pointer.constantOffset,
                             *location.accessSize);
          else
            readers.addUnknown(global);
          return;
        }
        if (op != OP_CALL && op != MOP_CALL)
          return;

        Function *callee = inst->getCallee();
        const EffectSummary &effect = summary.calleeEffect(callee);
        const bool scannable = callee && !callee->isExtern && callee->region &&
                               callee->phase == IRPhase::LIR;
        if (!scannable) {
          if (effect.readsUnknownGlobal)
            readers.disable();
          for (Global *global : effect.readGlobals)
            readers.addUnknown(global);
        }
        for (u32 index = 0; index < inst->getOperandCount(); ++index) {
          Inst *actual = inst->getArg(index);
          if (!actual || actual->getType() != TY_PTR ||
              !effect.readsParam(static_cast<i32>(index)))
            continue;
          const PointerInfo pointer = aliases.info(actual);
          if (pointer.kind == PointerKind::Global && pointer.root &&
              pointer.root->getOp() == OP_GETGLOBAL)
            readers.addUnknown(pointer.root->getGlobal());
          else if (pointer.kind == PointerKind::Param ||
                   pointer.kind == PointerKind::Opaque)
            readers.disable();
        }
      });
    }
  }
  return readers;
}

class DeadStoreFinder {
public:
  DeadStoreFinder(Function *function, const AliasInfo &aliases,
                  const GlobalSummaryResult &summary,
                  const GlobalReaderModel &globalReaders)
      : aliases_(aliases), summary_(summary), globalReaders_(globalReaders),
        memoryDependencies_(&aliases, &summary) {
    for (BasicBlock *block = function->region->first; block;
         block = block->next())
      forEachInst(block, [&](Inst *inst) {
        if (inst->getOp() == OP_LOAD)
          loads_.push_back(inst);
      });
  }

  // 判断当前写是否无人读取或在任何观察前被后续写完整覆盖
  bool isDead(Inst *store) {
    VERIFY(store && store->getOp() == OP_STORE);
    const MemoryLocation location =
        MemoryLocation::fromMemoryInstruction(store);
    const PointerInfo pointer = aliases_.info(location.pointer);

    if (pointer.kind == PointerKind::Alloca && pointer.root) {
      if (allocaHasNoReader(pointer.root, location))
        return true;
    } else if (pointer.kind == PointerKind::Global && pointer.root &&
               pointer.root->getOp() == OP_GETGLOBAL) {
      if (globalReaders_.hasNoReader(pointer.root->getGlobal(),
                                     pointer.constantOffset,
                                     location.accessSize))
        return true;
    }
    return memoryDependencies_.findNextKillerStore(store) != nullptr;
  }

private:
  // 判断局部对象未被外部观察且本函数没有重叠读取
  bool allocaHasNoReader(Inst *root, const MemoryLocation &store) {
    const auto found = observableAllocas_.find(root);
    const bool observable =
        found != observableAllocas_.end()
            ? found->second
            : observableAllocas_
                  .emplace(root, allocaAddressIsObservable(root, summary_))
                  .first->second;
    if (observable)
      return false;
    for (Inst *load : loads_)
      if (aliases_.mayOverlapForStoreElim(
              store, MemoryLocation::fromMemoryInstruction(load)))
        return false;
    return true;
  }

  const AliasInfo &aliases_;
  const GlobalSummaryResult &summary_;
  const GlobalReaderModel &globalReaders_;
  MemDepOracle memoryDependencies_;                    // 直线路径内存依赖查询器
  std::vector<Inst *> loads_;                          // 当前函数全部 load
  std::unordered_map<Inst *, bool> observableAllocas_; // alloca 可观察缓存
};

} // namespace

std::string_view DSEPass::name() const noexcept { return "dse"; }

PassResult DSEPass::run(Module *module, PassContext &context) {
  if (!module)
    return PassResult::noChange();

  const GlobalSummaryResult &summary =
      context.get<GlobalSummaryAnalysis>(module).result;
  const GlobalReaderModel globalReaders =
      buildGlobalReaderModel(module, context, summary);
  std::vector<Inst *> deadStores;
  std::vector<Function *> affectedFunctions;

  // 所有判定先基于未修改的同一代完成, 再统一删除
  for (Function *function = module->functionHead; function;
       function = function->next) {
    if (function->isExtern || function->phase != IRPhase::LIR ||
        !function->region || !function->region->first)
      continue;
    const AliasInfo &aliases = context.get<AliasAnalysis>(function).info;
    DeadStoreFinder finder(function, aliases, summary, globalReaders);
    const usize oldSize = deadStores.size();
    for (BasicBlock *block = function->region->first; block;
         block = block->next())
      forEachInst(block, [&](Inst *inst) {
        if (inst->getOp() == OP_STORE && finder.isDead(inst))
          deadStores.push_back(inst);
      });
    if (deadStores.size() != oldSize)
      affectedFunctions.push_back(function);
  }
  if (deadStores.empty())
    return PassResult::noChange();

  for (Inst *store : deadStores)
    VERIFY(store->eraseFromBlock());

  PreservedAnalyses preserved;
  preserved.preserveCFGAnalyses();
  preserved.preserveSSAForm();
  PassResult result = PassResult::changedIR(std::move(preserved));
  result.affectedFunctions = std::move(affectedFunctions);
  return result;
}

} // namespace svm::ir
