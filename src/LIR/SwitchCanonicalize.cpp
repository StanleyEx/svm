#include "IR.h"
#include "LIRPass.h"

#include <algorithm>
#include <unordered_set>
#include <vector>

namespace svm::ir {
namespace {

constexpr u32 kMinSwitchCases = 4;
constexpr i64 kMaxCanonicalRange = 4096;

struct ChainLink {
  BasicBlock *block = nullptr;  // 当前比较块
  i32 value = 0;                // 命中的case常量
  BasicBlock *target = nullptr; // 相等时的目标块
  BasicBlock *next = nullptr;   // 不等时的延续块
};

bool parseComparison(Inst *comparison, Inst *&selector, i32 &value,
                     bool &isEqual) noexcept {
  if (!comparison ||
      (comparison->getOp() != OP_EQ && comparison->getOp() != OP_NE) ||
      comparison->getOperandCount() != 2)
    return false;
  Inst *left = comparison->getArg(0);
  Inst *right = comparison->getArg(1);
  if (!left || !right)
    return false;
  if (left->getOp() == OP_ICONST && right->getOp() != OP_ICONST) {
    value = left->getImm();
    selector = right;
  } else if (right->getOp() == OP_ICONST && left->getOp() != OP_ICONST) {
    value = right->getImm();
    selector = left;
  } else {
    return false;
  }
  isEqual = comparison->getOp() == OP_EQ;
  return selector->getType() == TY_I1 || selector->getType() == TY_I32;
}

bool parseLink(BasicBlock *block, Inst *expectedSelector, bool requirePure,
               ChainLink &link) noexcept {
  Inst *branch = block ? block->terminator() : nullptr;
  if (!branch || branch->getOp() != OP_BR)
    return false;
  Inst *comparison = branch->getArg(0);
  Inst *selector = nullptr;
  i32 value = 0;
  bool isEqual = false;
  if (!parseComparison(comparison, selector, value, isEqual) ||
      (expectedSelector && selector != expectedSelector) ||
      !comparison->hasOneUse())
    return false;
  if (requirePure &&
      (block->firstPhi() || block->getPredecessorCount() != 1 ||
       block->firstInst() != comparison || comparison->next() != branch))
    return false;

  BasicBlock *target =
      isEqual ? branch->getBr().trueBB : branch->getBr().falseBB;
  BasicBlock *next = isEqual ? branch->getBr().falseBB : branch->getBr().trueBB;
  if (!target || !next || target == next)
    return false;
  link = {block, value, target, next};
  return true;
}

std::vector<CFGEditor::PhiEdgeValue>
snapshotPhiValues(BasicBlock *target, BasicBlock *predecessor) {
  std::vector<CFGEditor::PhiEdgeValue> values;
  for (Inst *phi = target->firstPhi(); phi; phi = phi->next()) {
    Inst *value = CFGEditor::getPhiIncomingValue(phi, predecessor);
    if (!value)
      return {};
    values.push_back({phi, value});
  }
  return values;
}

BasicBlock *createLanding(Function *function, IRBuilder &builder,
                          BasicBlock *&anchor, BasicBlock *oldPredecessor,
                          BasicBlock *target) {
  std::vector<CFGEditor::PhiEdgeValue> values =
      snapshotPhiValues(target, oldPredecessor);
  VERIFY(!values.empty());

  // 每条原case边独占landing 保留同一目标上按前驱区分的Phi值
  BasicBlock *landing = builder.newBlockAfter(anchor);
  anchor = landing;
  VERIFY(CFGEditor::redirectEdge(function, oldPredecessor, target, landing));
  builder.setInsertAtEnd(landing);
  builder.setCurrentSourceLocation(
      oldPredecessor->terminator()->sourceLocation);
  builder.emitJump(target);
  VERIFY(CFGEditor::addPhiEdgeValues(function, target, landing, values));
  return landing;
}

bool canonicalizeOneSwitch(Function *function) {
  for (BasicBlock *head = function->region->first; head; head = head->next()) {
    ChainLink first;
    if (!parseLink(head, nullptr, false, first))
      continue;

    Inst *selector = nullptr;
    i32 ignoredValue = 0;
    bool ignoredEqual = false;
    VERIFY(parseComparison(head->terminator()->getArg(0), selector,
                           ignoredValue, ignoredEqual));

    std::vector<ChainLink> links{first};
    std::unordered_set<BasicBlock *> chainBlocks{head};
    BasicBlock *next = first.next;
    while (true) {
      if (!chainBlocks.insert(next).second) {
        next = nullptr;
        break;
      }
      ChainLink link;
      if (!parseLink(next, selector, true, link))
        break;
      links.push_back(link);
      next = link.next;
    }
    if (links.size() < kMinSwitchCases || !next)
      continue;

    std::unordered_set<i32> seenValues;
    i32 minimum = links.front().value;
    i32 maximum = minimum;
    bool valid = true;
    for (const ChainLink &link : links) {
      valid &= seenValues.insert(link.value).second;
      minimum = std::min(minimum, link.value);
      maximum = std::max(maximum, link.value);
    }
    const i64 range = static_cast<i64>(maximum) - minimum + 1;
    if (!valid || range <= 0 || range > kMaxCanonicalRange)
      continue;

    IRBuilder builder(function->module, function);
    BasicBlock *anchor = head;
    std::vector<BasicBlock *> targets;
    targets.reserve(links.size());
    for (const ChainLink &link : links) {
      BasicBlock *target = link.target;
      if (target->firstPhi())
        target = createLanding(function, builder, anchor, link.block, target);
      targets.push_back(target);
    }

    BasicBlock *defaultTarget = next;
    if (next->firstPhi())
      defaultTarget =
          createLanding(function, builder, anchor, links.back().block, next);

    std::vector<SwitchCase> cases;
    cases.reserve(links.size());
    for (usize index = 0; index < links.size(); ++index)
      cases.emplace_back(links[index].value, targets[index]);
    std::sort(cases.begin(), cases.end(),
              [](const SwitchCase &left, const SwitchCase &right) {
                return left.getValue() < right.getValue();
              });

    Inst *oldBranch = head->terminator();
    Inst *oldComparison = oldBranch->getArg(0);
    builder.setCurrentSourceLocation(oldBranch->sourceLocation);
    builder.replaceWithSwitch(oldBranch, selector, cases.data(),
                              static_cast<u32>(cases.size()), defaultTarget);
    if (oldComparison->parentBlock() && oldComparison->hasNoUses())
      VERIFY(oldComparison->eraseFromBlock());

    // 新switch已旁路延续比较块 统一死块清扫同步删除旧边和Use
    VERIFY(cleanupDeadBlocks(function));
    VERIFY(computePreds(function));
    return true;
  }
  return false;
}

} // namespace

std::string_view SwitchCanonicalizePass::name() const noexcept {
  return "switch-canonicalize";
}

PassResult SwitchCanonicalizePass::run(Function *function, PassContext &) {
  if (!function || function->isExtern || function->phase != IRPhase::LIR ||
      !function->region || !function->region->first)
    return PassResult::noChange();
  VERIFY(computePreds(function));

  bool changed = false;
  while (canonicalizeOneSwitch(function))
    changed = true;
  if (!changed)
    return PassResult::noChange();

  PreservedAnalyses preserved;
  preserved.preserveSSAForm();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
