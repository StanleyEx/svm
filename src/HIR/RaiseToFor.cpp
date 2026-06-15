#include "PassManager.h"
#include "Utils.h"

#include <limits>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

class RaiseToFor final : public FunctionPass {
public:
  std::string_view name() const noexcept override { return "raise-to-for"; }
  PassResult run(Function *function, PassContext &context) override;
};

struct CondInfo {
  OpCode comparison = OP_NE; // 规范化为IV在左侧的比较
  Inst *ivAddress = nullptr; // 归纳变量的直接地址(通常为Alloca或GetGlbal)
  Inst *bound = nullptr;     // 循环边界 必须是循环不变量
};

struct UpdateInfo {
  Inst *store = nullptr;   // 唯一归纳变量写入 OP_STORE
  Inst *value = nullptr;   // 仿射更新值 OP_ADD或OP_SUB
  Inst *load = nullptr;    // 更新表达式中的IV读取 OP_LOAD
  Inst *rawStep = nullptr; // 尚未规范化符号的步长 必须是循环不变量
  OpCode op = OP_ADD;      // 更新操作码 OP_ADD或OP_SUB
};

// 步长提交动作
enum class StepAction {
  Pass,    // 保持原样通过 (常量正步长 或非常量但已知为正的ADD形步长)
  Negate,  // 需要发射取反指令 (非常量的SUB形步长 将其规范化为负数步长)
  Constant // 常量折叠 (适用于所有常量步长 直接将其折叠并编码为最终符号常量)
};

// 步长生成方案
struct StepPlan {
  StepAction action = StepAction::Pass; // 提交动作
  i32 constant = 0; // 规范化后的常量步长 仅当action == Constant时有效
};

// 判断两个内存地址是否可能别名
bool mayAlias(Inst *left, Inst *right) noexcept {
  if (!left || !right)
    return true;
  if (left == right)
    return true; // 地址完全一致 别名
  const OpCode leftOp = left->getOp();
  const OpCode rightOp = right->getOp();
  if (leftOp == OP_ALLOCA || rightOp == OP_ALLOCA)
    return false; // 局部栈分配空间相互隔离 不与全局变量重叠 非别名
  if (leftOp == OP_GETGLOBAL && rightOp == OP_GETGLOBAL)
    return false; // 两个不同的全局变量 非别名
  return true;
}

// 判断指针是否逃逸
// 追踪内存基址的Ues-Def 链 若存在非GetPtr/ArrayIdx的用户 则认为逃逸
// true表示逃逸 可能被外部函数等写入 false表示未逃逸
bool addressEscapes(Inst *base) {
  std::vector<Inst *> worklist = {base};
  std::unordered_set<Inst *> visited;
  while (!worklist.empty()) {
    Inst *address = worklist.back();
    worklist.pop_back();
    if (!address || !visited.insert(address).second)
      continue;
    for (const Use *use = address->uses(); use; use = use->next) {
      Inst *user = use->user;
      if (!user)
        return true;
      if ((user->getOp() == OP_GETPTR || user->getOp() == OP_ARRAYIDX) &&
          use->argNo == 0) {
        worklist.push_back(user); // 继续追踪基址
      } else if ((user->getOp() == OP_LOAD || user->getOp() == OP_STORE) &&
                 use->argNo == 0) {
        continue; // 允许内存读写
      } else if (user->getOp() == OP_FOR && use->argNo == 2) {
        continue; // 允许作为已经被提升的For循环的归纳变量
      } else {
        return true; // 其他情况一律认为逃逸
      }
    }
  }
  return false;
}

// 判断外部函数调用是否可能破坏指定的内存基址
bool callMayClobber(Inst *base) {
  if (!base)
    return true;
  if (base->getOp() != OP_ALLOCA)
    return true; // 全局变量和参数可能被外部函数修改
  if (addressEscapes(base))
    return true; // 地址已经逃逸
  return false;
}

// 扫描Region中是否存在对指定内存基址的写入
bool regionMayWrite(Region *region, Inst *base) {
  bool writes = false;
  forEachInstRecursive(region, [&](Inst *inst) {
    if (writes)
      return;
    if (inst->getOp() == OP_STORE) {
      Inst *destination = inst->getOperandCount() ? inst->getArg(0) : nullptr;
      if (mayAlias(getMemoryBase(destination), base))
        writes = true; // 存在STORE写入
    } else if (inst->getOp() == OP_CALL && callMayClobber(base)) {
      writes = true; // 存在可能破坏的函数调用
    } else if (inst->getOp() == OP_FOR && inst->getOperandCount() == 3 &&
               mayAlias(getMemoryBase(inst->getArg(2)), base)) {
      writes = true; // 存在嵌套的For循环归纳变量写入
    }
  });
  return writes;
}

bool isPureInvariantOp(OpCode op) noexcept {
  return isArithmetic(op) || isCompare(op) || isConversion(op) ||
         isAddressingOp(op);
}

// 检测IV的Bound和Step是否为循环不变量
class InvariantAnalysis {
public:
  InvariantAnalysis(Inst *loop, Region *condition, Region *body)
      : loop_(loop), condition_(condition), body_(body) {}

  bool analyze(Inst *value) { return analyzeImpl(value, false); }
  bool analyzeStep(Inst *value) { return analyzeImpl(value, true); }
  const std::vector<Inst *> &hoistPlan() const noexcept { return hoist_; }
  bool isHoisted(Inst *inst) const noexcept {
    return planned_.count(inst) != 0;
  }

private:
  bool analyzeImpl(Inst *value, bool allowBody) {
    if (!value)
      return false;
    // 定义在循环外部的指令是循环不变量
    if (!value->inside(loop_))
      return true;
    auto &cache = allowBody ? stepCache_ : conditionCache_;
    auto &visiting = allowBody ? stepVisiting_ : conditionVisiting_;
    const auto cached = cache.find(value);
    if (cached != cache.end())
      return cached->second;

    // 如果再次被访问 则说明存在环形依赖 非法情况
    if (!visiting.insert(value).second)
      return false;

    Region *definitionRegion =
        value->parentBlock() ? value->parentBlock()->parentRegion : nullptr;

    // 定义点必须在Cond或者Body中
    bool invariant = definitionRegion == condition_ ||
                     (allowBody && definitionRegion == body_);
    if (invariant && value->getOp() == OP_LOAD) {
      // 读取型 基址在Body中没有被写入才为循环不变量
      Inst *address =
          value->getOperandCount() == 1 ? value->getArg(0) : nullptr;
      Inst *base = getMemoryBase(address);
      invariant =
          base &&
          (base->getOp() == OP_ALLOCA || base->getOp() == OP_GETGLOBAL ||
           (!allowBody && base->getOp() == OP_PARAM)) &&
          analyzeImpl(address, allowBody) && !bodyMayWrite(base);
    } else if (invariant) {
      // 运算型防止除零 且操作数必须都是循环不变量
      invariant = isPureInvariantOp(value->getOp()) &&
                  (!allowBody ||
                   (value->getOp() != OP_DIV && value->getOp() != OP_MOD));
      for (u32 index = 0; invariant && index < value->getOperandCount();
           ++index)
        invariant = analyzeImpl(value->getArg(index), allowBody);
    }

    visiting.erase(value);
    cache.emplace(value, invariant);

    // 合法不变量加入外提计划
    if (invariant && planned_.insert(value).second)
      hoist_.push_back(value);
    return invariant;
  }

  // 判定循环体中是否存在对指定内存基址的写入
  bool bodyMayWrite(Inst *base) {
    auto [entry, inserted] = bodyWrites_.emplace(base, false);
    if (inserted)
      entry->second = regionMayWrite(body_, base);
    return entry->second;
  }

  Inst *loop_ = nullptr;                            // 被分析的While
  Region *condition_ = nullptr;                     // 条件Region
  Region *body_ = nullptr;                          // 循环体Region
  std::unordered_map<Inst *, bool> conditionCache_; // 条件不变量缓存
  std::unordered_map<Inst *, bool> stepCache_;      // 可投机步长缓存
  std::unordered_set<Inst *> conditionVisiting_;    // 条件递归环
  std::unordered_set<Inst *> stepVisiting_;         // 步长递归环
  std::unordered_set<Inst *> planned_;              // 已加入外提计划的指令
  std::unordered_map<Inst *, bool> bodyWrites_;     // 循环体写入缓存
  std::vector<Inst *> hoist_;                       // 依赖优先的外提计划
};

OpCode flipComparison(OpCode op) noexcept {
  switch (op) {
  case OP_LT:
    return OP_GT;
  case OP_LE:
    return OP_GE;
  case OP_GT:
    return OP_LT;
  case OP_GE:
    return OP_LE;
  default:
    return op;
  }
}

bool supportedComparison(OpCode op) noexcept {
  return op == OP_LT || op == OP_LE || op == OP_GT || op == OP_GE ||
         op == OP_NE;
}

// 限制IV为i32
Inst *directIVLoad(Inst *value) noexcept {
  if (!value || value->getOp() != OP_LOAD || value->getType() != TY_I32 ||
      value->getOperandCount() != 1)
    return nullptr;
  Inst *address = value->getArg(0);
  if (!address)
    return nullptr;
  if (address->getOp() == OP_ALLOCA)
    return address->getMem().elementType == TY_I32 ? address : nullptr;
  if (address->getOp() == OP_GETGLOBAL) {
    Global *global = address->getGlobal();
    return global && global->type == TY_I32 && !global->isArray ? address
                                                                : nullptr;
  }
  return nullptr;
}

bool analyzeCondition(Inst *loop, InvariantAnalysis &invariants,
                      CondInfo &result) {
  auto allUsesInside = [](Inst *value, Region *region) noexcept {
    for (const Use *use = value ? value->uses() : nullptr; use;
         use = use->next) {
      if (!use->user || !use->user->parentBlock())
        return false;
      bool inside = false;
      for (Region *current = use->user->parentBlock()->parentRegion; current;
           current = current->parent)
        if (current == region) {
          inside = true;
          break;
        }
      if (!inside)
        return false;
    }
    return true;
  };
  Region *region = loop->getScf().r[0];
  Region *body = loop->getScf().r[1];
  if (!region || !body || !region->first || region->first != region->last)
    return false;
  BasicBlock *block = region->first;
  Inst *yield = block->lastInst();
  if (!yield || yield->getOp() != OP_YIELD || yield->getOperandCount() != 1)
    return false;
  Inst *comparison = yield->getArg(0);
  if (!comparison || comparison->parentBlock() != block ||
      comparison->getType() != TY_I1 || comparison->getOperandCount() != 2 ||
      !supportedComparison(comparison->getOp()))
    return false;

  OpCode comparisonOp = comparison->getOp();
  Inst *load = comparison->getArg(0);
  Inst *address = directIVLoad(load);
  Inst *bound = comparison->getArg(1);

  // 如果IV在右侧 则翻转比较符号
  if (!address || !invariants.analyze(bound)) {
    load = comparison->getArg(1);
    address = directIVLoad(load);
    bound = comparison->getArg(0);
    if (!address || !invariants.analyze(bound))
      return false; // 左右侧都不合法
    comparisonOp = flipComparison(comparisonOp);
  }

  // Cond内除了IV的Load和Bound之外 不允许存在其他没有被规划外提的指令
  if (bound->getType() != TY_I32 || load->parentBlock() != block ||
      !allUsesInside(load, region) || !allUsesInside(comparison, region))
    return false;

  for (Inst *inst = block->firstInst(); inst; inst = inst->next()) {
    if (inst != yield && inst != comparison && inst != load &&
        !invariants.isHoisted(inst))
      return false;
  }

  result = {comparisonOp, address, bound};
  return true;
}

bool analyzeUpdate(Inst *loop, const CondInfo &condition,
                   InvariantAnalysis &invariants, UpdateInfo &result) {
  // 检查某个读取指令是否是从特定的归纳变量地址中进行加载
  auto sameIVLoad = [](Inst *value, Inst *address) noexcept {
    return value && value->getOp() == OP_LOAD &&
           value->getOperandCount() == 1 && value->getArg(0) == address;
  };
  Region *body = loop->getScf().r[1];
  if (!body || !body->first || body->first != body->last)
    return false; // Body也必须是规整的单基本块形态
  BasicBlock *block = body->first;
  Inst *yield = block->lastInst();
  if (!yield || yield->getOp() != OP_YIELD || yield->getOperandCount() != 0)
    return false;

  Inst *updateStore = nullptr;
  bool valid = true;
  std::optional<bool> callsClobberIV;

  // 扫描Body对IV的写入有且仅有一次
  forEachInstRecursive(body, [&](Inst *inst) {
    if (!valid)
      return;
    if (inst->getOp() == OP_STORE) {
      Inst *destination = inst->getOperandCount() ? inst->getArg(0) : nullptr;
      if (!mayAlias(getMemoryBase(destination), condition.ivAddress))
        return;
      if (destination != condition.ivAddress || updateStore)
        valid = false; // 二次写入
      else
        updateStore = inst;
    } else if (inst->getOp() == OP_CALL) {
      if (!callsClobberIV)
        callsClobberIV = callMayClobber(condition.ivAddress);
      if (*callsClobberIV)
        valid = false; // 函数调用可能破坏归纳变量
    } else if (inst->getOp() == OP_FOR && inst->getOperandCount() == 3 &&
               mayAlias(getMemoryBase(inst->getArg(2)), condition.ivAddress)) {
      valid = false; // 嵌套的For循环可能破坏归纳变量
    }
  });
  // 唯一的更新必须紧邻Yield指令
  if (!valid || !updateStore || updateStore->parentBlock() != block ||
      updateStore->next() != yield || updateStore->getOperandCount() != 2)
    return false;

  Inst *value = updateStore->getArg(1);
  if (!value || value->parentBlock() != block || value->getType() != TY_I32 ||
      value->getOperandCount() != 2 ||
      (value->getOp() != OP_ADD && value->getOp() != OP_SUB))
    return false; // 要求Add或Sub仿射更新
  Inst *load = value->getArg(0);
  Inst *step = value->getArg(1);
  // 如果是Add 允许将IV放在右侧
  if (value->getOp() == OP_ADD && !sameIVLoad(load, condition.ivAddress)) {
    load = value->getArg(1);
    step = value->getArg(0);
  }
  // 用于更新的一整个指令仅服务Store
  if (!sameIVLoad(load, condition.ivAddress) || load->parentBlock() != block ||
      step->getType() != TY_I32 || !value->hasOneUse() ||
      value->uses()->user != updateStore || value->uses()->argNo != 1 ||
      !invariants.analyzeStep(step))
    return false;

  result = {updateStore, value, load, step, value->getOp()};
  return true;
}

// 循环体内不能有Break/Continue指令 IV只能读或者更新 不能参与其他计算
bool verifyLoopBody(Inst *loop, const CondInfo &condition,
                    const UpdateInfo &update) {
  bool valid = true;
  Region *body = loop->getScf().r[1];
  forEachInstRecursive(body, [&](Inst *inst) {
    if (!valid)
      return;
    if ((inst->getOp() == OP_BREAK || inst->getOp() == OP_CONTINUE) &&
        getEnclosingLoop(inst) == loop) {
      valid = false;
      return;
    }
    for (u32 index = 0; index < inst->getOperandCount(); ++index) {
      if (inst->getArg(index) != condition.ivAddress)
        continue;
      if (!((inst->getOp() == OP_LOAD && index == 0) ||
            (inst == update.store && inst->getOp() == OP_STORE && index == 0)))
        valid = false;
    }
  });
  return valid;
}

std::optional<StepPlan> planStep(OpCode comparison, OpCode update,
                                 std::optional<i32> constant) noexcept {
  if (constant) {
    const bool forward = comparison == OP_LT || comparison == OP_LE;
    const bool backward = comparison == OP_GT || comparison == OP_GE;
    // 正向循环步长必须为正 反向循环步长必须为负
    if ((forward && *constant <= 0) || (backward && *constant >= 0))
      return std::nullopt;
    return StepPlan{StepAction::Constant, *constant};
  }
  if (comparison != OP_LT && comparison != OP_LE)
    return std::nullopt;
  // 减法更新规范化为负步长
  return StepPlan{update == OP_SUB ? StepAction::Negate : StepAction::Pass, 0};
}

bool proveNotEqualDirection(Inst *loop, const CondInfo &condition, i32 step,
                            OpCode &replacement) {
  // "while (n)" 经Sema规范化为OP_NE的循环
  // 能靠初值、边界和步长推断方向时 才把!=变为<或>
  if ((step != 1 && step != -1) || condition.bound->getOp() != OP_ICONST)
    return false;
  Inst *initialStore = nullptr;
  std::optional<bool> callsClobberIV;
  for (Inst *previous = loop->previous(); previous;
       previous = previous->previous()) {
    if (previous->getOp() == OP_CALL) {
      if (!callsClobberIV)
        callsClobberIV = callMayClobber(condition.ivAddress);
      if (*callsClobberIV)
        return false;
    }
    if (previous->getOp() != OP_STORE)
      continue;
    Inst *destination =
        previous->getOperandCount() == 2 ? previous->getArg(0) : nullptr;
    if (!mayAlias(getMemoryBase(destination), condition.ivAddress))
      continue;
    if (destination != condition.ivAddress)
      return false;
    initialStore = previous;
    break;
  }
  if (!initialStore || initialStore->getArg(1)->getOp() != OP_ICONST)
    return false;
  const i32 initial = initialStore->getArg(1)->getImm();
  const i32 bound = condition.bound->getImm();
  // 步长为正 且初值小于边界 则循环方向为正 NE->LT
  if (step == 1 && initial < bound) {
    replacement = OP_LT;
    return true;
  }
  // 步长为负 且初值大于边界 则循环方向为负 NE->GT
  if (step == -1 && initial > bound) {
    replacement = OP_GT;
    return true;
  }
  return false;
}

bool validStop(OpCode comparison, Inst *bound) noexcept {
  // For使用半开区间stop 将<=或>=转成bound + 1或bound - 1前
  // 必须排除INT_MAX和INT_MIN防止带等号比较在计算stop时发生整数回绕
  if (comparison != OP_LE && comparison != OP_GE)
    return true;
  if (!bound || bound->getOp() != OP_ICONST)
    return false;
  const i32 value = bound->getImm();
  return comparison == OP_LE ? value != std::numeric_limits<i32>::max()
                             : value != std::numeric_limits<i32>::min();
}

bool tryRaise(Function *function, Inst *loop) {
  if (!loop || !loop->parentBlock() || loop->getOp() != OP_WHILE)
    return false;
  Region *conditionRegion = loop->getScf().r[0];
  Region *bodyRegion = loop->getScf().r[1];
  if (!conditionRegion || !bodyRegion)
    return false;

  // 分析循环条件(CmpOp, ivAddr, bound)
  InvariantAnalysis invariants(loop, conditionRegion, bodyRegion);
  CondInfo condition;
  if (!analyzeCondition(loop, invariants, condition))
    return false;

  // Body中找出唯一归纳变量更新
  UpdateInfo update;
  if (!analyzeUpdate(loop, condition, invariants, update) ||
      !verifyLoopBody(loop, condition, update))
    return false;

  // 分析步长 OP_NE规范化为OP_LT或OP_GT
  std::optional<i32> effectiveConstant = [](Inst *value) -> std::optional<i32> {
    if (!value)
      return std::nullopt;
    if (value->getOp() == OP_ICONST)
      return value->getImm();
    if (value->getOp() == OP_NEG && value->getOperandCount() == 1 &&
        value->getArg(0)->getOp() == OP_ICONST)
      return i32NegWrap(value->getArg(0)->getImm());
    return std::nullopt;
  }(update.rawStep);
  if (effectiveConstant && update.op == OP_SUB)
    *effectiveConstant = i32NegWrap(*effectiveConstant);
  OpCode comparison = condition.comparison;
  if (comparison == OP_NE) {
    // OP_NE没有方向信息 必须结合循环前初始化Store和单位步长证明方向
    if (!effectiveConstant)
      return false;
    if (!proveNotEqualDirection(loop, condition, *effectiveConstant,
                                comparison))
      return false;
  }

  // 规划步长提交动作
  const std::optional<StepPlan> stepPlan =
      planStep(comparison, update.op, effectiveConstant);
  if (!stepPlan || !validStop(comparison, condition.bound))
    return false;

  // 开始执行IR变动
  // 定义在Cond内的所有不变量指令都外提到While前
  for (Inst *inst : invariants.hoistPlan())
    if (inst->parentBlock() && inst->inside(loop))
      inst->moveBefore(loop);

  IRBuilder builder(function->module, function);
  builder.setInsertBefore(loop);
  builder.setCurrentSourceLocation(loop->sourceLocation);

  // 计算For循环的stop: LE -> stop = bound + 1 GE -> stop = bound - 1
  Inst *stop = condition.bound;
  if (comparison == OP_LE)
    stop = builder.iConst(i32AddWrap(condition.bound->getImm(), 1));
  else if (comparison == OP_GE)
    stop = builder.iConst(i32SubWrap(condition.bound->getImm(), 1));

  // 计算规范化后的步长参数
  Inst *step = update.rawStep;
  if (stepPlan->action == StepAction::Constant)
    step = builder.iConst(stepPlan->constant); // 注入常量步长
  else if (stepPlan->action == StepAction::Negate)
    step = builder.emit(OP_NEG, TY_I32, update.rawStep); // 注入取反操作
  loop->getScf().r[0] = nullptr;
  loop->getScf().r[1] = nullptr;
  // 保留循环前的初始化Store RaiseToFor只替换循环控制节点 不主动折叠初始化行为
  // 留给后面的Mem2Reg清理
  builder.emitFor(stop, step, condition.ivAddress, bodyRegion);

  // For已接管归纳变量更新 删除原循环体尾部的更新链和旧条件Region
  update.store->eraseFromBlock();
  if (update.value->hasNoUses())
    update.value->eraseFromBlock();
  if (update.load->hasNoUses())
    update.load->eraseFromBlock();

  // 删除原Cond
  if (conditionRegion) {
    std::vector<Inst *> instructions;
    forEachInstRecursive(conditionRegion,
                         [&](Inst *inst) { instructions.push_back(inst); });
    // 逆序删除指令
    for (auto it = instructions.rbegin(); it != instructions.rend(); ++it)
      if ((*it)->parentBlock())
        (*it)->eraseFromBlock();
    conditionRegion->owner = nullptr;
    conditionRegion->parent = nullptr;
  }

  loop->eraseFromBlock();
  return true;
}

PassResult RaiseToFor::run(Function *function, PassContext &) {
  if (!function || function->isExtern || function->phase != IRPhase::HIR)
    return PassResult::noChange();
  std::vector<Inst *> loops;
  forEachInstRecursive(function->region, [&](Inst *inst) {
    if (inst->getOp() == OP_WHILE)
      loops.push_back(inst);
  });
  bool changed = false;
  // 逆序从深层开始提升
  for (auto it = loops.rbegin(); it != loops.rend(); ++it)
    if ((*it)->parentBlock())
      changed |= tryRaise(function, *it);
  return changed ? PassResult::changedIR() : PassResult::noChange();
}

} // namespace
} // namespace svm::ir

SVM_REGISTER_FUNCTION_PASS("raise-to-for", svm::ir::RaiseToFor)
