#include "Analysis.h"
#include "LIRPass.h"

#include <algorithm>
#include <cstring>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

// 本Pass只处理大型分叉整数DP 不承担通用调用结果缓存
constexpr u32 kMaxParams = 8;
constexpr u32 kMinSlots = 1024;
constexpr u32 kMaxCacheBytes = 1U << 20;
constexpr u64 kModuleCacheBytes = 8ULL << 20;
constexpr u32 kMaxMemoizedFunctions = 8;
constexpr u32 kMaxFunctionInstructions = 8000;
constexpr u32 kMaxReturns = 64;
constexpr u32 kMaxAddedInstructions = 1024;

constexpr i32 kMix[] = {1009, 917, 811, 727, 661, 593, 541, 499};

enum class PointerRootKind : u8 { Unknown, Alloca, Global, Param };

struct PointerRoot {
  PointerRootKind kind = PointerRootKind::Unknown; // 可追溯的指针根类别
  Global *global = nullptr;                        // Global根对应的全局对象
};

PointerRoot classifyPointerRoot(Inst *value) noexcept {
  for (u32 depth = 0; value && depth != 64; ++depth) {
    switch (value->getOp()) {
    case OP_ALLOCA:
      return {PointerRootKind::Alloca, nullptr};
    case OP_GETGLOBAL:
      return {PointerRootKind::Global, value->getGlobal()};
    case OP_PARAM:
      return {PointerRootKind::Param, nullptr};
    case OP_GETPTR:
    case OP_ARRAYIDX:
      value = value->getArg(0);
      break;
    default:
      return {};
    }
  }
  return {};
}

bool touchesFloat(const Inst *inst) noexcept {
  if (!inst)
    return false;
  const OpCode op = inst->getOp();
  if (isFloatArithmetic(op) || isFloatCompare(op) || op == OP_I2F ||
      op == OP_F2I || isFloat(inst->getType()))
    return true;
  for (u32 index = 0; index < inst->getOperandCount(); ++index) {
    const Inst *arg = inst->getArg(index);
    if (arg && isFloat(arg->getType()))
      return true;
  }
  return false;
}

bool isConstRead(Global *global) noexcept {
  return global && global->isConst &&
         (global->origin == Global::GlobalOrigin::SourceGlobal ||
          global->origin == Global::GlobalOrigin::StringLiteral);
}

bool isMemoGlobal(const Global *global) noexcept {
  if (!global || !global->name ||
      global->origin != Global::GlobalOrigin::Unknown)
    return false;
  constexpr const char prefix[] = "__memo_cache_";
  return std::strncmp(global->name, prefix, sizeof(prefix) - 1) == 0;
}

struct LocalInfo {
  bool clean = true;                         // 本地无可观察副作用
  bool hasFloat = false;                     // 函数签名/指令触碰浮点
  bool entryPhi = false;                     // 入口存在Phi
  bool entryAllocasPrefix = true;            // 入口alloca均位于前缀
  bool malformed = false;                    // CFG或指令结构不完整
  u32 selfCalls = 0;                         // 直接自递归调用数
  u32 bodyInstructions = 0;                  // Phi和普通指令总数
  u32 returnCount = 0;                       // 原始返回数
  std::vector<Function *> callees;           // 去重后的内部非self调用目标
  std::unordered_set<Global *> mutableReads; // 需要上下文证明的读取
};

void reject(LocalInfo &info) noexcept { info.clean = false; }

LocalInfo scanLocal(Function *function) {
  LocalInfo info;
  if (!function || !function->region || !function->region->first) {
    info.malformed = true;
    reject(info);
    return info;
  }

  BasicBlock *entry = function->region->first;
  info.entryPhi = entry->firstPhi() != nullptr;
  bool seenNonAlloca = false;
  for (Inst *inst = entry->firstInst(); inst; inst = inst->next()) {
    if (inst->getOp() == OP_ALLOCA) {
      if (seenNonAlloca)
        info.entryAllocasPrefix = false;
    } else {
      seenNonAlloca = true;
    }
  }

  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (!block->endsWithTerminator()) {
      info.malformed = true;
      reject(info);
    }
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next()) {
      ++info.bodyInstructions;
      info.hasFloat |= touchesFloat(phi);
    }
    for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
      ++info.bodyInstructions;
      info.hasFloat |= touchesFloat(inst);
      const OpCode op = inst->getOp();
      if (isMachineOp(op) || op == MOP_START_) {
        reject(info);
        continue;
      }
      switch (op) {
      case OP_RET:
        ++info.returnCount;
        break;
      case OP_CALL: {
        Function *callee = inst->getCallee();
        if (!callee || callee->isExtern) {
          reject(info);
          break;
        }
        for (u32 index = 0; index < inst->getOperandCount(); ++index) {
          Inst *arg = inst->getArg(index);
          if (!arg || arg->getType() == TY_PTR || isFloat(arg->getType()))
            reject(info);
        }
        if (callee == function) {
          ++info.selfCalls;
          if (inst->getType() != TY_I32 ||
              inst->getOperandCount() != function->paramCount)
            reject(info);
        } else {
          if (std::find(info.callees.begin(), info.callees.end(), callee) ==
              info.callees.end())
            info.callees.push_back(callee);
        }
        break;
      }
      case OP_IF:
      case OP_WHILE:
      case OP_FOR:
      case OP_YIELD:
      case OP_BREAK:
      case OP_CONTINUE:
      case OP_PARAM:
      case OP_UNREACHABLE:
        // LIR函数中不应残留结构化控制流 防御性拒绝不完整的阶段输入
        reject(info);
        break;
      case OP_LOAD: {
        if (inst->getType() != TY_I32) {
          reject(info);
          break;
        }
        PointerRoot root = classifyPointerRoot(inst->getArg(0));
        if (root.kind == PointerRootKind::Alloca)
          break;
        if (root.kind == PointerRootKind::Global && root.global) {
          if (!isConstRead(root.global))
            info.mutableReads.insert(root.global);
          break;
        }
        reject(info);
        break;
      }
      case OP_STORE: {
        PointerRoot root = classifyPointerRoot(inst->getArg(0));
        // 当前调用帧的alloca写入没有外部可观察副作用
        if (root.kind != PointerRootKind::Alloca)
          reject(info);
        if (inst->getOperandCount() < 2 || !inst->getArg(1) ||
            isFloat(inst->getArg(1)->getType()))
          reject(info);
        break;
      }
      case OP_LOCAL_INIT_VALUE:
      case OP_LOCAL_INIT_ZERO: {
        PointerRoot root = classifyPointerRoot(inst->getArg(0));
        if (root.kind != PointerRootKind::Alloca)
          reject(info);
        break;
      }
      default:
        break;
      }
    }
  }
  if (!info.returnCount || info.returnCount > kMaxReturns)
    reject(info);
  return info;
}

bool isMutualRecursive(Function *function, const GlobalSummaryResult &summary) {
  const CGNode *node = summary.nodeOf(function);
  if (!node || node->sccId < 0)
    return false;
  const auto &groups = summary.graph().sccGroups();
  const usize id = static_cast<usize>(node->sccId);
  return id >= groups.size() || groups[id].size() > 1;
}

struct PurityInfo {
  LocalInfo local;                           // 函数自身的扫描结果
  bool transparent = false;                  // 自身及传递callee均透明
  std::unordered_set<Global *> mutableReads; // 传递闭包中的可变全局读取
};

std::unordered_map<Function *, PurityInfo>
computePurity(Module *module, const GlobalSummaryResult &summary) {
  std::unordered_map<Function *, PurityInfo> result;
  for (Function *function = module ? module->functionHead : nullptr; function;
       function = function->next) {
    if (function->isExtern || function->phase != IRPhase::LIR ||
        !function->region)
      continue;
    PurityInfo info;
    info.local = scanLocal(function);
    info.transparent = info.local.clean && !info.local.hasFloat &&
                       !isMutualRecursive(function, summary);
    info.mutableReads = info.local.mutableReads;
    result.emplace(function, std::move(info));
  }

  bool changed = true;
  while (changed) {
    changed = false;
    for (auto &[function, info] : result) {
      for (Function *callee : info.local.callees) {
        const auto found = result.find(callee);
        if (found == result.end()) {
          if (info.transparent) {
            info.transparent = false;
            changed = true;
          }
          continue;
        }
        if (info.transparent && !found->second.transparent) {
          info.transparent = false;
          changed = true;
        }
        for (Global *global : found->second.mutableReads)
          changed |= info.mutableReads.insert(global).second;
      }
    }
  }
  return result;
}

bool validInjectionCFG(Function *function) {
  if (!function || !function->region || !function->region->first)
    return false;
  u32 blockCount = 0;
  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    ++blockCount;
  if (computeRPO(function).size() != blockCount)
    return false;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    if (!block->endsWithTerminator() ||
        !CFGEditor::hasConsistentIncomingState(block))
      return false;
    Inst *term = block->terminator();
    if (term->getOp() == OP_RET &&
        (term->getOperandCount() != 1 || !term->getArg(0) ||
         term->getArg(0)->getType() != TY_I32))
      return false;
  }
  return true;
}

i32 largestPrime(i32 value) noexcept {
  auto prime = [](i32 candidate) noexcept {
    if (candidate < 2)
      return false;
    if ((candidate & 1) == 0)
      return candidate == 2;
    for (i32 divisor = 3; static_cast<i64>(divisor) * divisor <= candidate;
         divisor += 2)
      if (candidate % divisor == 0)
        return false;
    return true;
  };
  for (i32 candidate = value; candidate >= 2; --candidate)
    if (prime(candidate))
      return candidate;
  return 0;
}

struct Capacity {
  u32 entryWords = 0; // 单条缓存项的i32字数
  u32 slots = 0;      // 不超过容量上限的最大素数槽位数
  u32 bytes = 0;      // 缓存对象的实际字节数
};

std::optional<Capacity> capacityFor(u32 params) {
  if (!params || params > kMaxParams)
    return std::nullopt;
  const u32 words = params + 2;
  const u32 entryBytes = words * 4;
  const i32 maxSlots = static_cast<i32>(kMaxCacheBytes / entryBytes);
  const i32 slots = largestPrime(maxSlots);
  if (slots < static_cast<i32>(kMinSlots))
    return std::nullopt;
  return Capacity{words, static_cast<u32>(slots),
                  static_cast<u32>(slots) * entryBytes};
}

i32 instructionCost(OpCode op) noexcept {
  switch (op) {
  case OP_DIV:
  case OP_MOD:
    return 4;
  case OP_MUL:
    return 3;
  case OP_CALL:
    return 4;
  case OP_LOAD:
  case OP_STORE:
    return 2;
  case OP_ADD:
  case OP_SUB:
  case OP_NEG:
  case OP_ZEXT:
  case OP_LNOT:
  case OP_GETPTR:
  case OP_ARRAYIDX:
    return 1;
  default:
    return isCompare(op) ? 1 : 0;
  }
}

i32 bodyCost(Function *function, const LoopInfo &loops) noexcept {
  i32 total = 0;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    i32 factor = 1;
    const i32 depth = loops.getLoopDepth(block);
    for (i32 index = 0; index < depth && index < 3; ++index)
      factor *= 10;
    for (Inst *phi = block->firstPhi(); phi; phi = phi->next())
      total += instructionCost(phi->getOp()) * factor;
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      total += instructionCost(inst->getOp()) * factor;
  }
  return total;
}

i32 fanout(Function *function, const LoopInfo &loops) {
  const std::vector<BasicBlock *> order = computeRPO(function);
  if (order.empty())
    return 0;
  std::unordered_map<BasicBlock *, u32> indices;
  indices.reserve(order.size());
  std::vector<i32> calls(order.size(), 0);
  for (u32 index = 0; index < order.size(); ++index) {
    indices.emplace(order[index], index);
    for (Inst *inst = order[index]->firstInst(); inst; inst = inst->next())
      if (inst->getOp() == OP_CALL && inst->getCallee() == function) {
        if (loops.getLoopDepth(order[index]) > 0)
          return -1;
        ++calls[index];
      }
  }
  std::vector<i32> best(order.size(), -1);
  best[0] = calls[0];
  i32 result = best[0];
  for (u32 index = 0; index < order.size(); ++index) {
    if (best[index] < 0)
      continue;
    result = std::max(result, best[index]);
    forEachSuccessor(order[index], [&](BasicBlock *successor) {
      const auto found = indices.find(successor);
      if (found == indices.end() || found->second <= index)
        return;
      best[found->second] =
          std::max(best[found->second], best[index] + calls[found->second]);
    });
  }
  return result;
}

u32 hashSalt(const Function *function) noexcept {
  u32 hash = 2166136261U;
  if (function && function->name)
    for (const unsigned char *p =
             reinterpret_cast<const unsigned char *>(function->name);
         *p; ++p) {
      hash ^= *p;
      hash *= 16777619U;
    }
  return hash;
}

i32 parameterSalt(u32 index, u32 slots) noexcept {
  return static_cast<i32>((static_cast<u64>(index + 1) * 9176U) % slots);
}

Inst *fieldAddress(IRBuilder &builder, Inst *entry, u32 field) {
  if (!field)
    return entry;
  return builder.emitGetPtr(entry, builder.iConst(static_cast<i32>(field * 4)),
                            1);
}

Inst *emitHash(IRBuilder &builder, Function *function, u32 params, u32 slots) {
  // 发射的IR等价于以下C代码 每个参数先归一化到[0, slots), 再用不同质数混合:
  // i32 hash = hashSalt(function) % slots + 97 * params + 17;
  // for (u32 i = 0; i < params; ++i) {
  //   i32 rem = arg[i] % slots;
  //   i32 normalized = rem + (rem < 0 ? slots : 0);
  //   hash += normalized * kMix[i];
  //   hash += ((i + 1) * 9176) % slots;
  // }
  // return hash % slots;
  Inst *slotCount = builder.iConst(static_cast<i32>(slots));
  Inst *zero = builder.iConst(0);
  const i32 base = static_cast<i32>(hashSalt(function) % slots) +
                   static_cast<i32>(97 * params + 17);
  Inst *hash = builder.iConst(base);
  // slots至多87359 八项累加的全局上界低于7.1e8 不发生i32回绕
  for (u32 index = 0; index < params; ++index) {
    Inst *remainder =
        builder.emit(OP_MOD, TY_I32, function->params[index], slotCount);
    Inst *negative = builder.emit(OP_LT, TY_I1, remainder, zero);
    Inst *flag = builder.emit(OP_ZEXT, TY_I32, negative);
    Inst *correction = builder.emit(OP_MUL, TY_I32, flag, slotCount);
    Inst *normalized = builder.emit(OP_ADD, TY_I32, remainder, correction);
    Inst *term =
        builder.emit(OP_MUL, TY_I32, normalized, builder.iConst(kMix[index]));
    hash = builder.emit(OP_ADD, TY_I32, hash, term);
    hash = builder.emit(OP_ADD, TY_I32, hash,
                        builder.iConst(parameterSalt(index, slots)));
  }
  return builder.emit(OP_MOD, TY_I32, hash, slotCount);
}

bool proveSingleEntryContext(Function *function,
                             const GlobalSummaryResult &summary) {
  const CallSiteSummary *only = nullptr;
  for (const auto &[call, site] : summary.callSites) {
    UNUSED(call);
    if (site.callee != function || site.caller == function || !site.reachable)
      continue;
    if (only)
      return false;
    only = &site;
  }
  if (!only || only->loopDepth != 0)
    return false;
  const ExecSummary *caller = summary.execSummary(only->caller);
  return caller && caller->reachableFromEntry && !caller->recursiveSCC &&
         caller->maxExec.isOnce();
}

struct Candidate {
  Function *function = nullptr; // 待改写的递归DP函数
  Capacity capacity;            // 专属缓存容量
  i32 score = 0;                // 预算排序使用的静态收益分
};

bool alreadyMemoized(Function *function) noexcept {
  if (!function)
    return false;
  for (const auto &[global, pointer] : function->constPools.globalPtrPool) {
    UNUSED(pointer);
    if (isMemoGlobal(global))
      return true;
  }
  for (BasicBlock *block = function ? function->region->first : nullptr; block;
       block = block->next())
    for (Inst *inst = block->firstInst(); inst; inst = inst->next())
      if (inst->getOp() == OP_GETGLOBAL && isMemoGlobal(inst->getGlobal()))
        return true;
  return false;
}

bool buildCandidate(Function *function, const GlobalSummaryResult &summary,
                    const std::unordered_map<Function *, PurityInfo> &purity,
                    const LoopInfo &loops, Candidate &candidate) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->name ||
      summary.getEntryPoint() == function || alreadyMemoized(function) ||
      function->paramCount == 0 || function->paramCount > kMaxParams ||
      function->returnType != TY_I32 || !validInjectionCFG(function))
    return false;
  const auto found = purity.find(function);
  if (found == purity.end() || !found->second.transparent)
    return false;
  const LocalInfo &local = found->second.local;
  if (local.entryPhi || !local.entryAllocasPrefix || local.malformed ||
      local.returnCount == 0 || local.returnCount > kMaxReturns ||
      local.selfCalls < 2 || local.bodyInstructions > kMaxFunctionInstructions)
    return false;
  for (u32 index = 0; index < function->paramCount; ++index)
    if (function->paramTypes[index] != TY_I32)
      return false;

  const CGNode *node = summary.nodeOf(function);
  if (!node || !node->inRecursion || isMutualRecursive(function, summary))
    return false;
  const ExecSummary *execution = summary.execSummary(function);
  if (!execution || !execution->reachableFromEntry)
    return false;

  bool hasExternalEntry = false;
  for (const auto &[call, site] : summary.callSites) {
    UNUSED(call);
    if (site.callee == function && site.caller != function && site.reachable) {
      hasExternalEntry = true;
      break;
    }
  }
  if (!hasExternalEntry)
    return false;

  if (!found->second.mutableReads.empty() &&
      !proveSingleEntryContext(function, summary))
    return false;

  const auto capacity = capacityFor(function->paramCount);
  if (!capacity)
    return false;
  const i32 pathFanout = fanout(function, loops);
  if (pathFanout < 2)
    return false;
  const u32 branchFanout = static_cast<u32>(pathFanout);

  const i32 estimated =
      static_cast<i32>(function->paramCount * 12 + 10 +
                       local.returnCount * (function->paramCount * 2 + 3));
  if (estimated > static_cast<i32>(kMaxAddedInstructions))
    return false;

  const i32 body = bodyCost(function, loops);
  const i32 lookup = static_cast<i32>(function->paramCount * 10 + 28);
  const i32 stores = static_cast<i32>(local.returnCount) *
                     static_cast<i32>(function->paramCount * 2 + 4);
  const i32 cachePenalty = static_cast<i32>(capacity->bytes / 16384U);
  const i64 score = static_cast<i64>(branchFanout - 1) * body * 4 +
                    static_cast<i64>(branchFanout) * 80 - lookup - stores -
                    cachePenalty;
  if (score < 64)
    return false;

  candidate.function = function;
  candidate.capacity = *capacity;
  candidate.score = static_cast<i32>(std::min<i64>(score, INT32_MAX));
  return true;
}

Global *createCacheGlobal(Module *module, Function *function, u32 ordinal,
                          const Capacity &capacity) {
  std::string base = "__memo_cache_";
  base += function->name ? function->name : "anonymous";
  base += "_" + std::to_string(ordinal);
  std::string name = base;
  u32 suffix = 0;
  auto clashes = [&](const std::string &candidate) {
    for (Global *global = module->globalHead; global; global = global->next)
      if (global->name && candidate == global->name)
        return true;
    return false;
  };
  while (clashes(name))
    name = base + "_" + std::to_string(++suffix);

  const u32 elements = capacity.slots * capacity.entryWords;
  Global *global =
      module->newGlobal(module->arena->duplicateString(name.c_str()), TY_I32,
                        capacity.bytes, elements, false, true);
  global->origin = Global::GlobalOrigin::Unknown;
  global->initSegment = nullptr;
  global->initSegmentCount = 0;
  return global;
}

void injectCache(Module *module, const Candidate &candidate, Global *cache) {
  Function *function = candidate.function;
  BasicBlock *entry = function->region ? function->region->first : nullptr;
  VERIFY(entry && entry->terminator());

  std::vector<Inst *> returns;
  for (BasicBlock *block = function->region->first; block;
       block = block->next()) {
    Inst *term = block->terminator();
    if (term && term->getOp() == OP_RET)
      returns.push_back(term);
  }

  IRBuilder builder(module, function);
  Inst *firstBody = entry->firstInst();
  while (firstBody && firstBody->getOp() == OP_ALLOCA)
    firstBody = firstBody->next();
  Inst *anchor = firstBody ? firstBody->previous() : nullptr;
  if (!anchor || anchor->getOp() == OP_PHI || isTerminator(anchor->getOp())) {
    // 空alloca前缀需要一条已挂载的无害锚点供CFG拆块 后续DCE会删除它
    builder.setInsertBefore(firstBody ? firstBody : entry->terminator());
    anchor = builder.emit(OP_ICONST, TY_I32);
  }
  BasicBlock *computeEntry =
      VERIFY(CFGEditor::splitBlockAfter(function, anchor));

  IRBuilder cfgBuilder(module, function);
  BasicBlock *miss = cfgBuilder.newBlockAfter(entry);
  BasicBlock *hit = cfgBuilder.newBlockAfter(entry);
  std::vector<BasicBlock *> checks(candidate.capacity.entryWords - 2);
  for (i32 index = static_cast<i32>(checks.size()) - 1; index >= 0; --index)
    checks[static_cast<usize>(index)] = cfgBuilder.newBlockAfter(entry);

  cfgBuilder.setInsertBefore(entry->terminator());
  Inst *cacheBase = cfgBuilder.getGlobalPtr(cache);
  Inst *slot = emitHash(cfgBuilder, function, function->paramCount,
                        candidate.capacity.slots);
  Inst *byteOffset = cfgBuilder.emit(
      OP_MUL, TY_I32, slot,
      cfgBuilder.iConst(static_cast<i32>(candidate.capacity.entryWords * 4)));
  Inst *entryPointer = cfgBuilder.emitGetPtr(cacheBase, byteOffset, 1);
  Inst *valid =
      cfgBuilder.emitLoad(fieldAddress(cfgBuilder, entryPointer, 0), TY_I32);
  Inst *validSet = cfgBuilder.emit(OP_NE, TY_I1, valid, cfgBuilder.iConst(0));
  cfgBuilder.replaceWithBranch(entry->terminator(), validSet, checks.front(),
                               miss);

  for (u32 index = 0; index < function->paramCount; ++index) {
    cfgBuilder.setInsertAtEnd(checks[index]);
    Inst *saved = cfgBuilder.emitLoad(
        fieldAddress(cfgBuilder, entryPointer, index + 1), TY_I32);
    Inst *equal = cfgBuilder.emit(OP_EQ, TY_I1, saved, function->params[index]);
    BasicBlock *next =
        index + 1 == function->paramCount ? hit : checks[index + 1];
    cfgBuilder.emitBranch(equal, next, miss);
  }

  cfgBuilder.setInsertAtEnd(hit);
  Inst *savedResult = cfgBuilder.emitLoad(
      fieldAddress(cfgBuilder, entryPointer, function->paramCount + 1), TY_I32);
  cfgBuilder.emitReturn(savedResult);

  cfgBuilder.setInsertAtEnd(miss);
  cfgBuilder.emitJump(computeEntry);

  for (Inst *term : returns) {
    VERIFY(term && !term->isErased() && term->getOperandCount() == 1);
    Inst *value = term->getArg(0);
    VERIFY(value && value->getType() == TY_I32);
    cfgBuilder.setInsertBefore(term);
    for (u32 index = 0; index < function->paramCount; ++index)
      cfgBuilder.emitStore(fieldAddress(cfgBuilder, entryPointer, index + 1),
                           function->params[index], TY_I32);
    cfgBuilder.emitStore(
        fieldAddress(cfgBuilder, entryPointer, function->paramCount + 1), value,
        TY_I32);
    cfgBuilder.emitStore(fieldAddress(cfgBuilder, entryPointer, 0),
                         cfgBuilder.iConst(1), TY_I32);
  }

  VERIFY(computePreds(function));
  computeUses(function);
  VERIFY(verifyDominance(function));
}

} // namespace

std::string_view MemoizationPass::name() const noexcept {
  return "memoization";
}

PassResult MemoizationPass::run(Module *module, PassContext &context) {
  if (!module)
    return PassResult::noChange();
  const GlobalSummaryResult &summary =
      context.get<GlobalSummaryAnalysis>(module).result;
  auto purity = computePurity(module, summary);

  std::vector<Candidate> candidates;
  for (Function *function = module->functionHead; function;
       function = function->next) {
    const auto found = purity.find(function);
    if (found == purity.end())
      continue;
    const LoopInfo &loops = context.get<LoopInfoAnalysis>(function).info;
    Candidate candidate;
    if (buildCandidate(function, summary, purity, loops, candidate))
      candidates.push_back(std::move(candidate));
  }
  if (candidates.empty())
    return PassResult::noChange();

  std::stable_sort(candidates.begin(), candidates.end(),
                   [](const Candidate &left, const Candidate &right) {
                     const i64 lhs =
                         static_cast<i64>(left.score) * right.capacity.bytes;
                     const i64 rhs =
                         static_cast<i64>(right.score) * left.capacity.bytes;
                     if (lhs != rhs)
                       return lhs > rhs;
                     return left.score > right.score;
                   });

  // 预算跨多次运行保持有效 防止第二次运行再追加一批缓存
  u64 usedBytes = 0;
  u32 transformed = 0;
  for (Global *global = module->globalHead; global; global = global->next) {
    if (!isMemoGlobal(global))
      continue;
    ++transformed;
    if (usedBytes >= kModuleCacheBytes ||
        global->totalSizeBytes > kModuleCacheBytes - usedBytes)
      usedBytes = kModuleCacheBytes;
    else
      usedBytes += global->totalSizeBytes;
  }
  bool changed = false;
  u32 ordinal = transformed;
  for (const Candidate &candidate : candidates) {
    if (transformed >= kMaxMemoizedFunctions ||
        usedBytes >= kModuleCacheBytes ||
        candidate.capacity.bytes > kModuleCacheBytes - usedBytes)
      break;
    Global *cache = createCacheGlobal(module, candidate.function, ordinal++,
                                      candidate.capacity);
    injectCache(module, candidate, cache);
    usedBytes += candidate.capacity.bytes;
    ++transformed;
    changed = true;
  }
  return changed ? PassResult::changedIR() : PassResult::noChange();
}

} // namespace svm::ir
