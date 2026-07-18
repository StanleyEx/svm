#include "Alias.h"
#include "Analysis.h"
#include "LIRPass.h"
#include "MemDep.h"

#include <algorithm>
#include <cstring>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

constexpr u64 kCommitBufferLimit = 256 * 1024;

struct ConstantValue {
  bool isFloat = false; // 是否保存f32位模式
  u32 bits = 0;         // i32或f32位模式

  bool operator==(const ConstantValue &other) const noexcept {
    return isFloat == other.isFloat && bits == other.bits;
  }
  bool isZero() const noexcept { return bits == 0; }
};

enum class ResolveKind : u8 {
  NotGlobal, // 地址根不是全局
  GlobalOK,  // 已解析为严格有效的全局元素
  GlobalBad, // 根已知但偏移或访问类型不可验证
};

struct ResolveResult {
  ResolveKind kind = ResolveKind::NotGlobal; // 解析结果类别
  Global *global = nullptr;                  // 已识别的全局根
  i64 element = 0;                           // 常量元素下标
};

struct StoreRecord {
  Inst *store = nullptr; // 常量Store指令
  i64 element = 0;       // 被写元素下标
  ConstantValue value;   // 写入的精确位模式
};

struct Observation {
  Inst *inst = nullptr;       // Load或Call
  std::optional<i64> element; // Load的精确元素, Call为未知
};

struct GlobalAccess {
  std::vector<std::pair<Inst *, i64>> loads;     // 全模块可折叠Load
  std::vector<StoreRecord> stores;               // 全模块直接常量Store
  std::vector<Observation> entryReads;           // 入口内读观测
  std::unordered_set<Function *> storeFunctions; // 直接写者函数
  bool escaped = false;                          // 全局地址进入不可控位置
  bool unknownOffset = false;                    // 存在无法验证的全局访存
  bool hasNonConstantStore = false;              // 存在动态值Store
  bool mayBeWrittenByCall = false;               // 存在可能写该对象的Call
};

struct GlobalUseIndex {
  std::unordered_map<Global *, GlobalAccess> accesses; // 每个全局的画像
  std::vector<Inst *> unknownEntryReads; // 入口内可能读任意全局的Call
  bool unknownWrite = false;             // 可达Call可能写任意全局
  bool conservativeAlias = false;        // 可达函数AA规模退化

  GlobalAccess &of(Global *global) { return accesses[global]; }
};

struct CommitItem {
  Global *global = nullptr;          // 待固化全局
  std::vector<ConstantValue> values; // 提交后的逐元素值
  std::vector<Inst *> deadStores;    // 可删除初始化Store
};

Function *functionOf(const Inst *inst) noexcept {
  const BasicBlock *block = inst ? inst->parentBlock() : nullptr;
  return block && block->parentRegion ? block->parentRegion->function : nullptr;
}

Global *globalAddressRoot(const AliasInfo &alias, Inst *pointer) {
  if (!pointer || pointer->getType() != TY_PTR)
    return nullptr;
  const PointerInfo info = alias.info(pointer);
  if (info.kind != PointerKind::Global || !info.root ||
      info.root->getOp() != OP_GETGLOBAL)
    return nullptr;
  return info.root->getGlobal();
}

ResolveResult resolveGlobalElement(const AliasInfo &alias, Inst *memoryInst) {
  ResolveResult result;
  if (!memoryInst ||
      (memoryInst->getOp() != OP_LOAD && memoryInst->getOp() != OP_STORE) ||
      memoryInst->getOperandCount() == 0)
    return result;

  const PointerInfo pointer = alias.info(memoryInst->getArg(0));
  if (pointer.kind != PointerKind::Global || !pointer.root ||
      pointer.root->getOp() != OP_GETGLOBAL)
    return result;
  result.global = pointer.root->getGlobal();
  if (!result.global)
    return result;

  const i32 elementSize = typeSizeBytes(result.global->type);
  const MemPayload &memory = memoryInst->getMem();
  const i32 accessSize = typeSizeBytes(memory.elementType);
  if (elementSize <= 0 || accessSize != elementSize ||
      memory.elementType != result.global->type ||
      (memory.totalSizeBytes != 0 &&
       memory.totalSizeBytes != static_cast<u32>(elementSize)) ||
      !pointer.constantOffset) {
    result.kind = ResolveKind::GlobalBad;
    return result;
  }

  const i64 offset = *pointer.constantOffset;
  if (offset < 0 || offset % elementSize != 0 ||
      static_cast<u64>(offset) + static_cast<u64>(elementSize) >
          result.global->totalSizeBytes) {
    result.kind = ResolveKind::GlobalBad;
    return result;
  }
  result.kind = ResolveKind::GlobalOK;
  result.element = offset / elementSize;
  return result;
}

bool parseStoredConstant(Inst *value, IRType type,
                         ConstantValue &result) noexcept {
  if (!value || value->isUndefValue())
    return false;
  if (type == TY_I32 && value->getOp() == OP_ICONST) {
    result = {false, static_cast<u32>(value->getImm())};
    return true;
  }
  if (type == TY_F32 && value->getOp() == OP_FCONST) {
    u32 bits = 0;
    const f32 immediate = value->getFimm();
    std::memcpy(&bits, &immediate, sizeof(bits));
    result = {true, bits};
    return true;
  }
  return false;
}

bool buildInitialValues(const Global *global,
                        std::vector<ConstantValue> &values) {
  if (!global || (global->type != TY_I32 && global->type != TY_F32) ||
      global->numElements == 0 ||
      global->totalSizeBytes !=
          global->numElements * static_cast<u32>(typeSizeBytes(global->type)) ||
      (global->initSegmentCount != 0 && !global->initSegment))
    return false;

  const bool isFloat = global->type == TY_F32;
  values.assign(global->numElements, ConstantValue{isFloat, 0});
  u64 position = 0;
  for (u32 segmentIndex = 0; segmentIndex < global->initSegmentCount;
       ++segmentIndex) {
    const GlobalInitSegment &segment = global->initSegment[segmentIndex];
    if (position + segment.count > global->numElements)
      return false;
    if (segment.data) {
      for (u32 index = 0; index < segment.count; ++index) {
        ConstantValue value{isFloat, 0};
        if (isFloat) {
          const f32 immediate = static_cast<const f32 *>(segment.data)[index];
          std::memcpy(&value.bits, &immediate, sizeof(value.bits));
        } else {
          value.bits =
              static_cast<u32>(static_cast<const i32 *>(segment.data)[index]);
        }
        values[position + index] = value;
      }
    }
    position += segment.count;
  }
  return true;
}

class AggressiveConstFolder {
public:
  AggressiveConstFolder(Module *module, PassContext &context) noexcept
      : module_(module), context_(context) {}

  bool run();

private:
  // 计算入口可达内部函数
  void computeReachable();
  // 单遍建立全局 Use 画像
  void buildUseIndex();
  void scanFunction(Function *function, const AliasInfo &alias);
  // 记录严格Load
  void handleLoad(Inst *load, const AliasInfo &alias);
  // 记录严格Store
  void handleStore(Function *function, Inst *store, const AliasInfo &alias);
  // 合并Call副作用
  void handleCall(Inst *call, const AliasInfo &alias);
  // 证明候选
  bool proveCommittable(Global *global, CommitItem &item);
  // 约束跨函数读者
  bool readersOnlyCalledByEntry(Global *global) const;
  // 建立同块指令顺序索引
  void ensureEntryOrder();
  // 查询执行先后
  bool dominates(Inst *definition, Inst *observation,
                 const DominatorTree &tree) const;

  bool intervalClean(const StoreRecord &record, Inst *observation,
                     const AliasInfo &alias,
                     const std::unordered_set<Inst *> &candidateStores) const;
  bool
  initializedBefore(const std::vector<const StoreRecord *> &stores,
                    Inst *observation, const DominatorTree &tree,
                    const AliasInfo &alias,
                    const std::unordered_set<Inst *> &candidateStores) const;
  // 重建初值并删除Store
  void applyCommit(CommitItem &item);
  // 压缩初值
  void rebuildSegments(Global *global,
                       const std::vector<ConstantValue> &values);
  // 折叠已const全局的已知元素Load
  bool harvestLoads();

  Module *module_ = nullptr;
  PassContext &context_;
  const GlobalSummaryResult *summary_ = nullptr;
  Function *entryPoint_ = nullptr;
  std::unordered_set<Function *> reachable_;   // 入口可达内部函数
  GlobalUseIndex index_;                       // 单遍全局使用画像
  std::unordered_map<Inst *, u32> entryOrder_; // 入口内指令线性序号
};

void AggressiveConstFolder::computeReachable() {
  if (!entryPoint_ || !summary_)
    return;
  std::vector<Function *> worklist{entryPoint_};
  reachable_.insert(entryPoint_);
  while (!worklist.empty()) {
    Function *function = worklist.back();
    worklist.pop_back();
    CGNode *node = summary_->nodeOf(function);
    if (!node)
      continue;
    for (const CGNode::Edge &edge : node->callees) {
      Function *callee = edge.callee ? edge.callee->function : nullptr;
      if (callee && !callee->isExtern && reachable_.insert(callee).second)
        worklist.push_back(callee);
    }
  }
}

void AggressiveConstFolder::handleLoad(Inst *load, const AliasInfo &alias) {
  const ResolveResult resolved = resolveGlobalElement(alias, load);
  if (resolved.kind == ResolveKind::GlobalBad) {
    index_.of(resolved.global).unknownOffset = true;
    return;
  }
  if (resolved.kind != ResolveKind::GlobalOK)
    return;
  GlobalAccess &access = index_.of(resolved.global);
  access.loads.emplace_back(load, resolved.element);
  if (functionOf(load) == entryPoint_)
    access.entryReads.push_back({load, resolved.element});
}

void AggressiveConstFolder::handleStore(Function *function, Inst *store,
                                        const AliasInfo &alias) {
  if (store->getOperandCount() > 1)
    if (Global *escaped = globalAddressRoot(alias, store->getArg(1)))
      index_.of(escaped).escaped = true;

  const ResolveResult resolved = resolveGlobalElement(alias, store);
  if (resolved.kind == ResolveKind::GlobalBad) {
    index_.of(resolved.global).unknownOffset = true;
    return;
  }
  if (resolved.kind != ResolveKind::GlobalOK)
    return;

  GlobalAccess &access = index_.of(resolved.global);
  access.storeFunctions.insert(function);
  ConstantValue value;
  if (store->getOperandCount() < 2 ||
      !parseStoredConstant(store->getArg(1), resolved.global->type, value)) {
    access.hasNonConstantStore = true;
    return;
  }
  access.stores.push_back({store, resolved.element, value});
}

void AggressiveConstFolder::handleCall(Inst *call, const AliasInfo &alias) {
  const EffectSummary &effects = summary_->calleeEffect(call->getCallee());
  const bool inEntry = functionOf(call) == entryPoint_;
  if (effects.writesUnknownGlobal)
    index_.unknownWrite = true;
  if (effects.readsUnknownGlobal && inEntry)
    index_.unknownEntryReads.push_back(call);
  for (Global *global : effects.writeGlobals)
    index_.of(global).mayBeWrittenByCall = true;
  if (inEntry)
    for (Global *global : effects.readGlobals)
      index_.of(global).entryReads.push_back({call, std::nullopt});

  for (u32 index = 0; index < call->getOperandCount(); ++index) {
    Global *global = globalAddressRoot(alias, call->getArg(index));
    if (!global)
      continue;
    GlobalAccess &access = index_.of(global);
    if (effects.escapesParam(static_cast<i32>(index)))
      access.escaped = true;
    if (effects.writesParam(static_cast<i32>(index)))
      access.mayBeWrittenByCall = true;
    if (effects.readsParam(static_cast<i32>(index)) && inEntry)
      access.entryReads.push_back({call, std::nullopt});
  }
}

void AggressiveConstFolder::scanFunction(Function *function,
                                         const AliasInfo &alias) {
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      for (u32 index = 0; index < phi->getOperandCount(); ++index)
        if (Global *global = globalAddressRoot(alias, phi->getArg(index)))
          index_.of(global).escaped = true;

    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      switch (inst->getOp()) {
      case OP_LOAD:
        handleLoad(inst, alias);
        break;
      case OP_STORE:
        handleStore(function, inst, alias);
        break;
      case OP_CALL:
        handleCall(inst, alias);
        break;
      case OP_RET:
        if (inst->getOperandCount() != 0)
          if (Global *global = globalAddressRoot(alias, inst->getArg(0)))
            index_.of(global).escaped = true;
        break;
      default:
        break;
      }
    }
  }
}

void AggressiveConstFolder::buildUseIndex() {
  for (Function *function = module_->functionHead; function;
       function = function->next) {
    if (function->isExtern || function->phase != IRPhase::LIR ||
        !function->region || !function->region->first ||
        !reachable_.count(function))
      continue;
    const AliasInfo &alias = context_.get<AliasAnalysis>(function).info;
    if (alias.isConservative()) {
      index_.conservativeAlias = true;
      continue;
    }
    scanFunction(function, alias);
  }
}

bool AggressiveConstFolder::readersOnlyCalledByEntry(Global *global) const {
  for (Function *function = module_->functionHead; function;
       function = function->next) {
    if (function == entryPoint_ || function->isExtern || !function->region ||
        !reachable_.count(function) ||
        !summary_->effectOf(function).readsGlobal(global))
      continue;
    CGNode *node = summary_->nodeOf(function);
    if (!node || node->callers.empty())
      return false;
    for (const CGNode::Edge &edge : node->callers)
      if (!edge.callee || edge.callee->function != entryPoint_)
        return false;
  }
  return true;
}

void AggressiveConstFolder::ensureEntryOrder() {
  if (!entryOrder_.empty() || !entryPoint_ || !entryPoint_->region)
    return;
  u32 order = 0;
  for (BasicBlock *block = entryPoint_->region->first; block;
       block = block->next()) {
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      entryOrder_.emplace(phi, order++);
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      entryOrder_.emplace(inst, order++);
  }
}

bool AggressiveConstFolder::dominates(Inst *definition, Inst *observation,
                                      const DominatorTree &tree) const {
  BasicBlock *definitionBlock =
      definition ? definition->parentBlock() : nullptr;
  BasicBlock *observationBlock =
      observation ? observation->parentBlock() : nullptr;
  if (!definitionBlock || !observationBlock)
    return false;
  if (definitionBlock != observationBlock)
    return tree.dominates(definitionBlock, observationBlock);
  const auto definitionOrder = entryOrder_.find(definition);
  const auto observationOrder = entryOrder_.find(observation);
  return definitionOrder != entryOrder_.end() &&
         observationOrder != entryOrder_.end() &&
         definitionOrder->second < observationOrder->second;
}

bool AggressiveConstFolder::intervalClean(
    const StoreRecord &record, Inst *observation, const AliasInfo &alias,
    const std::unordered_set<Inst *> &candidateStores) const {
  BasicBlock *block = record.store ? record.store->parentBlock() : nullptr;
  if (!block || !observation || !observation->parentBlock())
    return false;
  if (block != observation->parentBlock())
    return true;

  const MemoryLocation location =
      MemoryLocation::fromMemoryInstruction(record.store);
  MemDepOracle oracle(&alias, summary_);
  if (oracle.hasClobberBetween(record.store, observation, location) ==
      MemDepOracle::ClobberResult::NoClobber)
    return true;

  const AliasQuery query{block, nullptr, true};
  for (Inst *inst = record.store->next(); inst && inst != observation;
       inst = inst->next()) {
    if (candidateStores.count(inst))
      continue;
    if (inst->getOp() == OP_STORE &&
        alias.alias(location, MemoryLocation::fromMemoryInstruction(inst),
                    query) != AliasResult::NoAlias)
      return false;
    if (inst->getOp() == OP_CALL &&
        alias.mayWriteMemory(inst, location,
                             summary_->calleeEffect(inst->getCallee()), query))
      return false;
  }
  return true;
}

bool AggressiveConstFolder::initializedBefore(
    const std::vector<const StoreRecord *> &stores, Inst *observation,
    const DominatorTree &tree, const AliasInfo &alias,
    const std::unordered_set<Inst *> &candidateStores) const {
  return std::any_of(
      stores.begin(), stores.end(), [&](const StoreRecord *store) {
        return dominates(store->store, observation, tree) &&
               intervalClean(*store, observation, alias, candidateStores);
      });
}

bool AggressiveConstFolder::proveCommittable(Global *global, CommitItem &item) {
  if (!global || global->origin != Global::GlobalOrigin::SourceGlobal ||
      global->isConst || (global->type != TY_I32 && global->type != TY_F32) ||
      global->totalSizeBytes > kCommitBufferLimit || index_.unknownWrite ||
      index_.conservativeAlias)
    return false;

  auto found = index_.accesses.find(global);
  if (found == index_.accesses.end())
    return false;
  GlobalAccess &access = found->second;
  if (access.escaped || access.unknownOffset || access.hasNonConstantStore ||
      access.mayBeWrittenByCall)
    return false;

  std::vector<ConstantValue> initial;
  if (!buildInitialValues(global, initial))
    return false;
  std::vector<ConstantValue> finalValues = initial;

  if (!access.stores.empty()) {
    if (!entryPoint_ || access.storeFunctions.size() != 1 ||
        !access.storeFunctions.count(entryPoint_))
      return false;

    std::unordered_map<i64, ConstantValue> writtenValues;
    std::unordered_map<i64, std::vector<const StoreRecord *>> storesByElement;
    std::unordered_set<Inst *> candidateStores;
    for (const StoreRecord &record : access.stores) {
      if (record.element < 0 ||
          static_cast<u64>(record.element) >= finalValues.size())
        return false;
      const auto [value, inserted] =
          writtenValues.emplace(record.element, record.value);
      if (!inserted && !(value->second == record.value))
        return false;
      storesByElement[record.element].push_back(&record);
      candidateStores.insert(record.store);
      finalValues[record.element] = record.value;
    }

    std::unordered_set<i64> changedElements;
    for (const auto &[element, value] : writtenValues)
      if (!(initial[static_cast<usize>(element)] == value))
        changedElements.insert(element);

    if (!changedElements.empty()) {
      if (!readersOnlyCalledByEntry(global))
        return false;
      ensureEntryOrder();
      const DominatorTree &tree = context_.get<DomAnalysis>(entryPoint_).tree;
      const AliasInfo &alias = context_.get<AliasAnalysis>(entryPoint_).info;
      std::vector<Observation> observations = access.entryReads;
      for (Inst *call : index_.unknownEntryReads)
        observations.push_back({call, std::nullopt});

      for (const Observation &observation : observations) {
        if (!observation.inst || observation.inst->isErased())
          continue;
        if (observation.element) {
          const i64 element = *observation.element;
          if (changedElements.count(element) &&
              !initializedBefore(storesByElement.at(element), observation.inst,
                                 tree, alias, candidateStores))
            return false;
          continue;
        }
        for (i64 element : changedElements)
          if (!initializedBefore(storesByElement.at(element), observation.inst,
                                 tree, alias, candidateStores))
            return false;
      }
    }

    for (const StoreRecord &record : access.stores)
      item.deadStores.push_back(record.store);
  }

  item.global = global;
  item.values = std::move(finalValues);
  return true;
}

void AggressiveConstFolder::rebuildSegments(
    Global *global, const std::vector<ConstantValue> &values) {
  struct SegmentBuild {
    bool zero = true;                  // 是否零填充段
    std::vector<ConstantValue> values; // 数据段元素
    u32 count = 0;                     // 段长度
  };
  std::vector<SegmentBuild> segments;
  for (const ConstantValue &value : values) {
    const bool zero = value.isZero();
    if (segments.empty() || segments.back().zero != zero)
      segments.push_back({zero, {}, 0});
    SegmentBuild &segment = segments.back();
    ++segment.count;
    if (!zero)
      segment.values.push_back(value);
  }

  if (segments.empty()) {
    global->initSegment = nullptr;
    global->initSegmentCount = 0;
    return;
  }
  global->initSegmentCount = static_cast<u32>(segments.size());
  global->initSegment =
      module_->arena->createArray<GlobalInitSegment>(segments.size());
  for (usize segmentIndex = 0; segmentIndex < segments.size(); ++segmentIndex) {
    const SegmentBuild &source = segments[segmentIndex];
    GlobalInitSegment &destination = global->initSegment[segmentIndex];
    destination.count = source.count;
    destination.data = nullptr;
    if (source.zero)
      continue;
    if (global->type == TY_F32) {
      f32 *data = module_->arena->createArray<f32>(source.count);
      for (u32 index = 0; index < source.count; ++index)
        std::memcpy(&data[index], &source.values[index].bits, sizeof(f32));
      destination.data = data;
    } else {
      i32 *data = module_->arena->createArray<i32>(source.count);
      for (u32 index = 0; index < source.count; ++index)
        data[index] = i32FromBits(source.values[index].bits);
      destination.data = data;
    }
  }
}

void AggressiveConstFolder::applyCommit(CommitItem &item) {
  for (Inst *store : item.deadStores)
    if (store && !store->isErased())
      VERIFY(store->eraseFromBlock());
  rebuildSegments(item.global, item.values);
  item.global->isConst = true;
}

bool AggressiveConstFolder::harvestLoads() {
  struct LoadReplacement {
    Inst *load = nullptr; // 被替换Load
    ConstantValue value;  // 对应全局初值
  };
  std::unordered_map<Function *, std::vector<LoadReplacement>> replacements;
  for (const auto &[global, access] : index_.accesses) {
    if (!global->isConst)
      continue;
    std::vector<ConstantValue> values;
    if (!buildInitialValues(global, values))
      continue;
    for (const auto &[load, element] : access.loads) {
      Function *function = functionOf(load);
      if (function && load && !load->isErased() && element >= 0 &&
          static_cast<u64>(element) < values.size())
        replacements[function].push_back(
            {load, values[static_cast<usize>(element)]});
    }
  }

  bool changed = false;
  for (auto &[function, loads] : replacements) {
    IRBuilder builder(function->module, function);
    for (const LoadReplacement &replacement : loads) {
      Inst *constant = nullptr;
      if (replacement.value.isFloat) {
        f32 immediate = 0.0F;
        std::memcpy(&immediate, &replacement.value.bits, sizeof(immediate));
        constant = builder.fConst(immediate);
      } else {
        constant = builder.iConst(i32FromBits(replacement.value.bits));
      }
      VERIFY(builder.replace(replacement.load, constant));
      changed = true;
    }
  }
  return changed;
}

bool AggressiveConstFolder::run() {
  if (!module_)
    return false;
  summary_ = &context_.get<GlobalSummaryAnalysis>(module_).result;
  entryPoint_ = summary_->getEntryPoint();
  if (!entryPoint_)
    return false;
  computeReachable();
  buildUseIndex();

  std::vector<CommitItem> commits;
  for (Global *global = module_->globalHead; global; global = global->next) {
    CommitItem item;
    if (proveCommittable(global, item))
      commits.push_back(std::move(item));
  }
  for (CommitItem &item : commits)
    applyCommit(item);
  const bool harvested = harvestLoads();
  return !commits.empty() || harvested;
}

} // namespace

std::string_view AggressiveConstFoldPass::name() const noexcept {
  return "aggressive-const-fold";
}

PassResult AggressiveConstFoldPass::run(Module *module, PassContext &context) {
  AggressiveConstFolder folder(module, context);
  return folder.run() ? PassResult::changedIR() : PassResult::noChange();
}

} // namespace svm::ir
