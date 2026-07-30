#include "LSRAddress.h"
#include "Alias.h"
#include "DomAnalysis.h"
#include "LoopShape.h"

#include <algorithm>

namespace svm::ir::lsr_address {
namespace {

bool valueDependsOnAny(Inst *root, const std::unordered_set<Inst *> &values) {
  std::unordered_set<Inst *> visited;
  std::vector<Inst *> worklist;
  if (root)
    worklist.push_back(root);
  while (!worklist.empty()) {
    Inst *value = worklist.back();
    worklist.pop_back();
    if (!value || !visited.insert(value).second)
      continue;
    if (values.count(value))
      return true;
    for (u32 index = 0; index < value->getOperandCount(); ++index)
      worklist.push_back(value->getArg(index));
  }
  return false;
}

bool rootAvailableAtLoopEntry(Inst *root, const Loop *loop,
                              const DominatorTree *dominatorTree) noexcept {
  if (!root || !loop)
    return false;
  BasicBlock *definition = root->parentBlock();
  return !definition || (!loop->contains(definition) && dominatorTree &&
                         dominatorTree->dominates(definition, loop->header()));
}

struct LinearTerm {
  Inst *symbol = nullptr;          // 待分解的 header Phi
  SCEVExpr *coefficient = nullptr; // 对应线性系数
};

struct LinearForm {
  std::vector<LinearTerm> terms; // 非零符号项
  SCEVExpr *constant = nullptr;  // 不含目标符号的残余项
};

Inst *resolveHeaderPhiAlias(Inst *value, const LoopInfo *loopInfo);

struct LinearDecomposeQuery {
  std::vector<Inst *> symbols;        // 允许作为变量的 canonical Phi
  const LoopInfo *loopInfo = nullptr; // LCSSA别名解析所需循环信息
  u32 maxTerms = 4;                   // 最大线性项数
  u32 maxDepth = 64;                  // 最大递归深度
};

std::optional<LinearForm>
decomposeHeaderPhiOffset(const SCEV *scev, SCEVExpr *expression,
                         const LinearDecomposeQuery &query) {
  if (!scev || !expression)
    return std::nullopt;

  const auto canonicalSymbol = [&](Inst *value) noexcept -> Inst * {
    Inst *headerPhi = resolveHeaderPhiAlias(value, query.loopInfo);
    return std::find(query.symbols.begin(), query.symbols.end(), headerPhi) !=
                   query.symbols.end()
               ? headerPhi
               : nullptr;
  };
  const auto hasSymbol = [&](SCEVExpr *expr, const auto &self) -> bool {
    if (!expr)
      return false;
    switch (expr->kind) {
    case SCEVExpr::K_CONSTANT:
      return false;
    case SCEVExpr::K_UNKNOWN:
      return canonicalSymbol(expr->unk.val) != nullptr;
    case SCEVExpr::K_ADD:
    case SCEVExpr::K_MUL:
      for (SCEVExpr *operand : expr->nary.ops)
        if (self(operand, self))
          return true;
      return false;
    case SCEVExpr::K_ADDREC:
      return self(expr->addRec.base, self) || self(expr->addRec.step, self);
    case SCEVExpr::K_SDIV:
    case SCEVExpr::K_SREM:
      return self(expr->bin.lhs, self) || self(expr->bin.rhs, self);
    }
    return false;
  };

  LinearForm form;
  SCEVExpr *constant = scev->getConstant(0, expression->ty);
  const auto addSymbol = [&](Inst *symbol, SCEVExpr *coefficient) {
    for (LinearTerm &term : form.terms) {
      if (term.symbol != symbol)
        continue;
      term.coefficient = scev->getAddExpr(term.coefficient, coefficient);
      return;
    }
    form.terms.push_back({symbol, coefficient});
  };

  bool valid = true;
  u32 visited = 0;
  const auto decompose = [&](SCEVExpr *expr, SCEVExpr *scale, u32 depth,
                             const auto &self) -> void {
    if (!valid)
      return;
    if (!expr || depth > query.maxDepth || ++visited > 4096) {
      valid = false;
      return;
    }
    switch (expr->kind) {
    case SCEVExpr::K_CONSTANT:
      constant = scev->getAddExpr(constant, scev->getMulExpr(scale, expr));
      return;
    case SCEVExpr::K_UNKNOWN:
      if (Inst *symbol = canonicalSymbol(expr->unk.val))
        addSymbol(symbol, scale);
      else
        constant = scev->getAddExpr(constant, scev->getMulExpr(scale, expr));
      return;
    case SCEVExpr::K_ADD:
      for (SCEVExpr *operand : expr->nary.ops)
        self(operand, scale, depth + 1, self);
      return;
    case SCEVExpr::K_MUL: {
      SCEVExpr *symbolFactor = nullptr;
      SCEVExpr *invariantScale = scale;
      for (SCEVExpr *factor : expr->nary.ops) {
        if (hasSymbol(factor, hasSymbol)) {
          if (symbolFactor) {
            valid = false;
            return;
          }
          symbolFactor = factor;
        } else {
          invariantScale = scev->getMulExpr(invariantScale, factor);
        }
      }
      if (symbolFactor)
        self(symbolFactor, invariantScale, depth + 1, self);
      else
        constant = scev->getAddExpr(constant, invariantScale);
      return;
    }
    case SCEVExpr::K_ADDREC:
    case SCEVExpr::K_SDIV:
    case SCEVExpr::K_SREM:
      if (hasSymbol(expr, hasSymbol)) {
        valid = false;
        return;
      }
      constant = scev->getAddExpr(constant, scev->getMulExpr(scale, expr));
      return;
    }
  };

  decompose(expression, scev->getConstant(1, expression->ty), 0, decompose);
  if (!valid)
    return std::nullopt;
  form.terms.erase(std::remove_if(form.terms.begin(), form.terms.end(),
                                  [](const LinearTerm &term) {
                                    return term.coefficient->isZero();
                                  }),
                   form.terms.end());
  if (form.terms.size() > query.maxTerms)
    return std::nullopt;
  form.constant = constant;
  return form;
}

struct AddRecParts {
  Loop *loop = nullptr;          // 已发现的唯一循环
  SCEVExpr *base = nullptr;      // 合并后的递推初值
  SCEVExpr *step = nullptr;      // 合并后的递推步长
  SCEVExpr *invariant = nullptr; // 递推外的不变量
  bool hasRecurrence = false;    // 是否发现 AddRec
};

Inst *resolveHeaderPhiAlias(Inst *value, const LoopInfo *loopInfo) {
  if (!value || value->getOp() != OP_PHI || value->getType() != TY_I32 ||
      !loopInfo)
    return nullptr;
  if (value->parentBlock() && loopInfo->isLoopHeader(value->parentBlock()))
    return value;

  Inst *candidate = nullptr;
  for (u32 index = 0; index < value->getOperandCount(); ++index) {
    Inst *incoming = value->getArg(index);
    if (!incoming || incoming->getOp() != OP_PHI ||
        incoming->getType() != TY_I32 || !incoming->parentBlock() ||
        !loopInfo->isLoopHeader(incoming->parentBlock()))
      return nullptr;
    if (!candidate)
      candidate = incoming;
    else if (candidate != incoming)
      return nullptr;
  }
  return candidate;
}

void collectHeaderOrLCSSAPhiLeaves(SCEVExpr *expression,
                                   const LoopInfo *loopInfo,
                                   std::vector<Inst *> &result) {
  if (!expression)
    return;
  switch (expression->kind) {
  case SCEVExpr::K_UNKNOWN: {
    Inst *headerPhi = resolveHeaderPhiAlias(expression->unk.val, loopInfo);
    if (!headerPhi)
      return;
    for (Inst *symbol : result)
      if (symbol == expression->unk.val || symbol == headerPhi)
        return;
    result.push_back(headerPhi);
    return;
  }
  case SCEVExpr::K_ADD:
  case SCEVExpr::K_MUL:
    for (SCEVExpr *operand : expression->nary.ops)
      collectHeaderOrLCSSAPhiLeaves(operand, loopInfo, result);
    return;
  case SCEVExpr::K_ADDREC:
    collectHeaderOrLCSSAPhiLeaves(expression->addRec.base, loopInfo, result);
    collectHeaderOrLCSSAPhiLeaves(expression->addRec.step, loopInfo, result);
    return;
  case SCEVExpr::K_SDIV:
  case SCEVExpr::K_SREM:
    collectHeaderOrLCSSAPhiLeaves(expression->bin.lhs, loopInfo, result);
    collectHeaderOrLCSSAPhiLeaves(expression->bin.rhs, loopInfo, result);
    return;
  case SCEVExpr::K_CONSTANT:
    return;
  }
}

std::optional<AddRecurrence> findAddRecurrenceForLoop(const SCEV *scev,
                                                      SCEVExpr *expression,
                                                      Loop *preferredLoop) {
  if (!scev || !expression)
    return std::nullopt;

  const auto mergeParts = [&](AddRecParts &destination,
                              const AddRecParts &source) {
    if (source.invariant)
      destination.invariant =
          destination.invariant
              ? scev->getAddExpr(destination.invariant, source.invariant)
              : source.invariant;
    if (!source.hasRecurrence)
      return true;
    if (!source.loop || !source.base || !source.step)
      return false;
    if (!destination.hasRecurrence) {
      destination.loop = source.loop;
      destination.base = source.base;
      destination.step = source.step;
      destination.hasRecurrence = true;
      return true;
    }
    if (destination.loop != source.loop)
      return false;
    destination.base = scev->getAddExpr(destination.base, source.base);
    destination.step = scev->getAddExpr(destination.step, source.step);
    return true;
  };

  const auto decompose = [&](SCEVExpr *expr, Loop *target, AddRecParts &result,
                             const auto &self) -> bool {
    switch (expr->kind) {
    case SCEVExpr::K_ADDREC:
      if (!target || expr->addRec.loop == target) {
        result = {expr->addRec.loop, expr->addRec.base, expr->addRec.step,
                  nullptr, true};
        return result.loop && result.base && result.step;
      }
      if (expr->isLoopInvariant(target)) {
        result.invariant = expr;
        return true;
      }
      return false;
    case SCEVExpr::K_ADD:
      for (SCEVExpr *operand : expr->nary.ops) {
        AddRecParts part;
        if (!self(operand, target, part, self) || !mergeParts(result, part))
          return false;
      }
      return true;
    case SCEVExpr::K_MUL: {
      if (expr->nary.ops.size() == 2) {
        SCEVExpr *constant = nullptr;
        SCEVExpr *other = nullptr;
        if (expr->nary.ops[0]->isConstant()) {
          constant = expr->nary.ops[0];
          other = expr->nary.ops[1];
        } else if (expr->nary.ops[1]->isConstant()) {
          constant = expr->nary.ops[1];
          other = expr->nary.ops[0];
        }
        if (constant && other) {
          AddRecParts inner;
          if (!self(other, target, inner, self))
            return false;
          if (inner.hasRecurrence) {
            inner.base = scev->getMulExpr(inner.base, constant);
            inner.step = scev->getMulExpr(inner.step, constant);
          }
          if (inner.invariant)
            inner.invariant = scev->getMulExpr(inner.invariant, constant);
          result = inner;
          return true;
        }
      }
      result.invariant = expr;
      return true;
    }
    case SCEVExpr::K_UNKNOWN:
      if (expr->unk.val && expr->unk.val->getOp() == OP_PHI) {
        SCEVExpr *current = scev->getSCEV(expr->unk.val);
        if (current && current != expr)
          return self(current, target, result, self);
      }
      result.invariant = expr;
      return true;
    case SCEVExpr::K_CONSTANT:
    case SCEVExpr::K_SDIV:
    case SCEVExpr::K_SREM:
      result.invariant = expr;
      return true;
    }
    return false;
  };

  const auto finalize =
      [&](AddRecParts &parts) -> std::optional<AddRecurrence> {
    if (!parts.hasRecurrence ||
        (parts.invariant && !parts.invariant->isLoopInvariant(parts.loop)))
      return std::nullopt;
    SCEVExpr *base = parts.invariant
                         ? scev->getAddExpr(parts.base, parts.invariant)
                         : parts.base;
    if (!parts.loop || !base || !parts.step)
      return std::nullopt;
    return AddRecurrence{parts.loop, base, parts.step};
  };

  if (preferredLoop) {
    AddRecParts parts;
    if (decompose(expression, preferredLoop, parts, decompose) &&
        parts.hasRecurrence)
      if (auto recurrence = finalize(parts))
        return recurrence;
  }
  AddRecParts parts;
  if (!decompose(expression, nullptr, parts, decompose))
    return std::nullopt;
  return finalize(parts);
}

} // namespace

std::optional<AddRecurrence> findAddRecurrence(const SCEV *scev,
                                               SCEVExpr *expression) {
  return findAddRecurrenceForLoop(scev, expression, nullptr);
}

std::optional<AddressEvolution>
classifyAddressEvolution(const SCEV *scev, const LoopInfo *loopInfo,
                         Inst *getPtr, const LoopShapeInfo *loopShape,
                         const AliasInfo *aliasInfo,
                         const DominatorTree *dominatorTree) {
  if (!scev || !getPtr || getPtr->getOp() != OP_GETPTR)
    return std::nullopt;

  AddressEvolution evolution;
  evolution.getPtr = getPtr;
  evolution.root = aliasInfo ? aliasInfo->info(getPtr).root : nullptr;
  SCEVExpr *address = scev->getSCEV(getPtr);
  Loop *preferred = loopInfo && getPtr->parentBlock()
                        ? loopInfo->getLoopFor(getPtr->parentBlock())
                        : nullptr;

  Inst *baseOperand = getPtr->getOperandCount() ? getPtr->getArg(0) : nullptr;
  if (loopShape && loopInfo && baseOperand && address) {
    SCEVExpr *base = scev->getSCEV(baseOperand);
    SCEVExpr *offset = scev->getAddExpr(
        address, scev->getMulExpr(base, scev->getConstant(-1, base->ty)));
    std::vector<Inst *> symbols;
    collectHeaderOrLCSSAPhiLeaves(offset, loopInfo, symbols);
    if (!symbols.empty()) {
      LinearDecomposeQuery query;
      query.symbols = std::move(symbols);
      query.loopInfo = loopInfo;
      auto form = decomposeHeaderPhiOffset(scev, offset, query);
      if (form && form->terms.size() == 1 &&
          form->terms.front().coefficient->isConstant() &&
          form->constant->isConstant()) {
        Inst *phi = resolveHeaderPhiAlias(form->terms.front().symbol, loopInfo);
        const i64 coefficient = form->terms.front().coefficient->cst.v;
        const i64 constant = form->constant->cst.v;
        Loop *loop = phi && phi->parentBlock()
                         ? loopInfo->getLoopFor(phi->parentBlock())
                         : nullptr;
        const bool inScope =
            loop && getPtr->parentBlock() &&
            (loop->contains(getPtr->parentBlock()) ||
             (dominatorTree &&
              dominatorTree->dominates(loop->header(), getPtr->parentBlock())));
        if (coefficient != 0 && fitsI32(coefficient) && fitsI32(constant) &&
            inScope && loop->header() == phi->parentBlock() &&
            rootAvailableAtLoopEntry(baseOperand, loop, dominatorTree)) {
          const auto transfer = loopShape->getHeaderPhiTransfer(phi);
          if (transfer && transfer->hasNonzeroSelfDelta) {
            evolution.kind = AddressEvolutionKind::EdgeLocalPhi;
            evolution.edgeLocal = {loop, baseOperand, phi, coefficient,
                                   constant};
            return evolution;
          }
        }
      }
    }
  }

  if (auto recurrence = findAddRecurrenceForLoop(scev, address, preferred)) {
    Loop *loop = recurrence->loop;
    bool valid = loop && loop->latches().size() == 1 && loop->getPreheader() &&
                 getPtr->parentBlock() &&
                 loop->contains(getPtr->parentBlock()) &&
                 recurrence->base->isLoopInvariant(loop);
    valid = valid && recurrence->step->isConstant() &&
            fitsI32(recurrence->step->cst.v);
    valid =
        valid && scev->isSafeToExpand(recurrence->base, loop->getPreheader());
    if (valid) {
      evolution.kind = AddressEvolutionKind::CanonicalAddRec;
      evolution.canonical = {loop, recurrence->base, recurrence->step};
      return evolution;
    }
  }
  return std::nullopt;
}

ExpansionSession::ExpansionSession(Function *function,
                                   const SCEV *scev) noexcept
    : scev_(scev), expander_(function, scev),
      builder_(function->module, function) {}

void ExpansionSession::registerAvailableAddRec(SCEVExpr *base, SCEVExpr *step,
                                               Loop *loop, Inst *value) {
  if (!base || !step || !loop || !value)
    return;
  available_.push_back({loop, scev_->getAddRecExpr(base, step, loop), value});
}

Inst *ExpansionSession::expandCodeFor(SCEVExpr *expression,
                                      Inst *insertBefore) {
  if (!expression || !insertBefore || !insertBefore->parentBlock())
    return nullptr;
  for (const Available &available : available_) {
    if (!available.loop || !available.value || !available.addRec ||
        !available.loop->contains(insertBefore->parentBlock()))
      continue;
    const MathBounds delta =
        scev_->getSignedDeltaBounds(expression, available.addRec);
    if (!delta.valid || delta.min != delta.max || !fitsI32(delta.min))
      continue;
    if (delta.min == 0)
      return available.value;
    builder_.setInsertBefore(insertBefore);
    Inst *pointer = builder_.emitGetPtr(
        available.value, builder_.iConst(static_cast<i32>(delta.min)));
    pointer->setStride(1);
    return pointer;
  }
  return expander_.expandCodeFor(expression, insertBefore);
}

bool ExpansionSession::hasAvailableFor(SCEVExpr *expression,
                                       BasicBlock *block) const {
  if (!expression || !block)
    return false;
  for (const Available &available : available_) {
    if (!available.loop || !available.value || !available.addRec ||
        !available.loop->contains(block))
      continue;
    const MathBounds delta =
        scev_->getSignedDeltaBounds(expression, available.addRec);
    if (delta.valid && delta.min == delta.max && fitsI32(delta.min))
      return true;
  }
  return false;
}

bool ExpansionSession::dependsOnAny(
    SCEVExpr *expression, const std::unordered_set<Inst *> &values) const {
  std::unordered_set<SCEVExpr *> visited;
  std::vector<SCEVExpr *> worklist;
  if (expression)
    worklist.push_back(expression);
  while (!worklist.empty()) {
    SCEVExpr *current = worklist.back();
    worklist.pop_back();
    if (!current || !visited.insert(current).second)
      continue;
    for (Inst *value : values)
      if (current->structurallyEquals(scev_->getSCEV(value)))
        return true;
    switch (current->kind) {
    case SCEVExpr::K_UNKNOWN:
      if (valueDependsOnAny(current->unk.val, values))
        return true;
      break;
    case SCEVExpr::K_ADD:
    case SCEVExpr::K_MUL:
      worklist.insert(worklist.end(), current->nary.ops.begin(),
                      current->nary.ops.end());
      break;
    case SCEVExpr::K_ADDREC:
      worklist.push_back(current->addRec.base);
      worklist.push_back(current->addRec.step);
      break;
    case SCEVExpr::K_SDIV:
    case SCEVExpr::K_SREM:
      worklist.push_back(current->bin.lhs);
      worklist.push_back(current->bin.rhs);
      break;
    case SCEVExpr::K_CONSTANT:
      break;
    }
  }
  return false;
}

} // namespace svm::ir::lsr_address
