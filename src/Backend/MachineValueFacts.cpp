#include "MachineValueFacts.h"

#include "RV64.h"
#include "VReg.h"

#include <algorithm>
#include <optional>

namespace svm::ir {
namespace {
constexpr u64 Sign32 = u64{1} << 31;
constexpr u64 Mask32 = UINT32_MAX;
constexpr u32 MaxContextWalk = 8;

void mergeBits(MachineValueFacts &facts, u64 knownZero, u64 knownOne) {
  if (facts.bits.width == 0)
    facts.bits.width = 32;
  const u64 mask = facts.bits.mask();
  facts.bits.knownZero |= knownZero & mask;
  facts.bits.knownOne |= knownOne & mask;
  if (facts.bits.conflict()) {
    facts.meetState = FactMeetState::Bottom;
  } else if (((knownZero | knownOne) & mask) != 0 &&
             facts.meetState == FactMeetState::Unknown) {
    facts.meetState = FactMeetState::Known;
  }
}

void tightenRange(MachineValueFacts &facts, i64 min, i64 max) {
  if (min > max)
    return;
  const I32Range narrowed =
      facts.range.intersectWith(I32Range::fromSigned(min, max));
  if (narrowed.isEmpty()) {
    facts.meetState = FactMeetState::Bottom;
    return;
  }
  facts.range = narrowed;
  if (facts.meetState == FactMeetState::Unknown)
    facts.meetState = FactMeetState::Known;
}

void finalize(MachineValueFacts &facts) {
  if (facts.bits.width == 0)
    facts.bits.width = 32;
  const FactMeetState before = facts.meetState;
  const bool conflict = facts.bits.conflict() || facts.range.isEmpty();

  ScalarFactBundle bundle;
  bundle.valid = true;
  bundle.bitWidth = facts.bits.width;
  bundle.range = facts.range;
  bundle.knownBits = facts.bits;
  bundle.hasNonZero = facts.nonzero;
  bundle.nonzero = facts.nonzero;
  bundle.source = FactSource::MIR_Local;
  canonicalizeBundle(bundle);

  facts.range = bundle.valid ? bundle.range : I32Range::unknown();
  facts.bits = bundle.valid && bundle.knownBits.valid()
                   ? bundle.knownBits
                   : KnownBits::unknown(facts.bits.width);
  facts.nonzero = bundle.valid && bundle.hasNonZero && bundle.nonzero;
  if (before == FactMeetState::Bottom || conflict)
    facts.meetState = FactMeetState::Bottom;
  else if (before == FactMeetState::Known)
    facts.meetState = FactMeetState::Known;
}

void absorbCongruenceSeed(MachineValueFacts &facts, Congruence congruence) {
  if (!congruence.valid || congruence.isUnknown())
    return;
  ScalarFactBundle bundle;
  bundle.valid = true;
  bundle.bitWidth = facts.bits.width == 0 ? 32 : facts.bits.width;
  bundle.range = facts.range;
  bundle.knownBits = facts.bits;
  bundle.congruence = congruence;
  bundle.hasNonZero = facts.nonzero;
  bundle.nonzero = facts.nonzero;
  bundle.source = FactSource::MIR_Local;
  canonicalizeBundle(bundle);
  if (!bundle.valid) {
    facts.meetState = FactMeetState::Bottom;
    return;
  }
  facts.range = bundle.range;
  facts.bits = bundle.knownBits.valid() ? bundle.knownBits
                                        : KnownBits::unknown(bundle.bitWidth);
  facts.nonzero = bundle.hasNonZero && bundle.nonzero;
  if (facts.meetState == FactMeetState::Unknown)
    facts.meetState = FactMeetState::Known;
}

MachineValueFacts factsRec(const Inst *value,
                           const MachineValueFactQuery &query, u32 depth,
                           bool allowContext);

MachineValueFacts childFacts(const Inst *value,
                             const MachineValueFactQuery &query, u32 depth) {
  return factsRec(value, query, depth == 0 ? 0 : depth - 1, query.useContext);
}

MachineValueFacts constantFacts(i64 value, u32 width) {
  MachineValueFacts facts;
  facts.bits = KnownBits::constant(static_cast<u64>(value), width);
  if (width <= 32)
    facts.range = I32Range::constant(i32FromBits(static_cast<u32>(value)));
  facts.nonzero = (static_cast<u64>(value) & KnownBits::maskOfW(width)) != 0;
  facts.meetState = FactMeetState::Known;
  return facts;
}

KnownBits low32Bits(const MachineValueFacts &facts) noexcept {
  KnownBits result = KnownBits::unknown(32);
  result.knownZero = facts.bits.knownZero & Mask32;
  result.knownOne = facts.bits.knownOne & Mask32;
  return result;
}

u64 unsignedMaxLow32(const MachineValueFacts &facts) noexcept {
  return (~facts.bits.knownZero) & Mask32;
}

void deriveInstruction(const Inst *value, const MachineValueFactQuery &query,
                       u32 depth, MachineValueFacts &facts) {
  const u32 width = query.width;
  const u64 mask = KnownBits::maskOfW(width);
  const OpCode op = value->getOp();

  if (isMachineBooleanResult(op)) {
    mergeBits(facts, mask & ~u64{1}, 0);
    tightenRange(facts, 0, 1);
    if ((op == MOP_SEQZ || op == MOP_SNEZ) && value->getOperandCount() >= 1) {
      const MachineValueFacts source =
          childFacts(value->getArg(0), query, depth);
      const bool isSnez = op == MOP_SNEZ;
      if (source.knownNonZero()) {
        tightenRange(facts, isSnez ? 1 : 0, isSnez ? 1 : 0);
        if (isSnez)
          mergeBits(facts, 0, 1);
      } else if (source.knownZeroI32()) {
        tightenRange(facts, isSnez ? 0 : 1, isSnez ? 0 : 1);
        if (!isSnez)
          mergeBits(facts, 0, 1);
      }
    }
    return;
  }

  switch (op) {
  case OP_ICONST:
  case MOP_LI: {
    const i64 immediate = op == MOP_LI ? value->getImm64() : value->getImm();
    const MachineValueFacts constant = constantFacts(immediate, width);
    mergeBits(facts, constant.bits.knownZero, constant.bits.knownOne);
    if (width <= 32) {
      const i32 low = i32FromBits(static_cast<u32>(immediate));
      tightenRange(facts, low, low);
    }
    return;
  }
  case MOP_COPY:
  case MOP_FCOPY:
  case MOP_SEXT_W: {
    if (value->getOperandCount() < 1)
      return;
    const MachineValueFacts source = childFacts(value->getArg(0), query, depth);
    mergeBits(facts, source.bits.knownZero, source.bits.knownOne);
    if (const auto bounds = source.range.signedBounds())
      tightenRange(facts, bounds->min, bounds->max);
    facts.nonzero = facts.nonzero || source.nonzero;
    return;
  }
  case MOP_ANDI: {
    if (value->getOperandCount() < 1)
      return;
    const u32 immediate = static_cast<u32>(value->getImm());
    const MachineValueFacts source = childFacts(value->getArg(0), query, depth);
    const KnownBits result =
        kbAnd(low32Bits(source), KnownBits::constant(immediate, 32));
    mergeBits(facts, result.knownZero, result.knownOne);
    if (value->getImm() >= 0)
      tightenRange(facts, 0, value->getImm());
    return;
  }
  case MOP_AND:
  case MOP_OR:
  case MOP_XOR: {
    if (value->getOperandCount() < 2)
      return;
    const MachineValueFacts left = childFacts(value->getArg(0), query, depth);
    const MachineValueFacts right = childFacts(value->getArg(1), query, depth);
    KnownBits result;
    if (op == MOP_AND)
      result = kbAnd(low32Bits(left), low32Bits(right));
    else if (op == MOP_OR)
      result = kbOr(low32Bits(left), low32Bits(right));
    else
      result = kbXor(low32Bits(left), low32Bits(right));
    mergeBits(facts, result.knownZero, result.knownOne);
    if (op == MOP_AND) {
      if (left.knownNonNegativeI32()) {
        if (const auto bounds = left.range.signedBounds())
          tightenRange(facts, 0, std::max<i32>(0, bounds->max));
      }
      if (right.knownNonNegativeI32()) {
        if (const auto bounds = right.range.signedBounds())
          tightenRange(facts, 0, std::max<i32>(0, bounds->max));
      }
    }
    return;
  }
  case MOP_ORI:
  case MOP_XORI: {
    if (value->getOperandCount() < 1)
      return;
    const MachineValueFacts source = childFacts(value->getArg(0), query, depth);
    const KnownBits immediate =
        KnownBits::constant(static_cast<u32>(value->getImm()), 32);
    const KnownBits result = op == MOP_ORI
                                 ? kbOr(low32Bits(source), immediate)
                                 : kbXor(low32Bits(source), immediate);
    mergeBits(facts, result.knownZero, result.knownOne);
    return;
  }
  case MOP_SLLIW:
  case MOP_SLLI: {
    if (value->getOperandCount() < 1)
      return;
    const MachineValueFacts source = childFacts(value->getArg(0), query, depth);
    KnownBits input = KnownBits::unknown(width);
    input.knownZero = source.bits.knownZero & input.mask();
    input.knownOne = source.bits.knownOne & input.mask();
    const u32 amount =
        static_cast<u32>(value->getImm()) & (op == MOP_SLLIW ? 31U : 63U);
    const KnownBits result = kbShl(input, amount);
    mergeBits(facts, result.knownZero, result.knownOne);
    return;
  }
  case MOP_SRLIW:
  case MOP_SRAIW: {
    if (value->getOperandCount() < 1)
      return;
    const MachineValueFacts source = childFacts(value->getArg(0), query, depth);
    const u32 amount = static_cast<u32>(value->getImm()) & 31U;
    const KnownBits result = op == MOP_SRLIW
                                 ? kbLShr(low32Bits(source), amount)
                                 : kbAShr(low32Bits(source), amount);
    mergeBits(facts, result.knownZero, result.knownOne);
    return;
  }
  case MOP_SRLI:
  case MOP_SRAI: {
    if (width < 64 || value->getOperandCount() < 1)
      return;
    const MachineValueFacts source = childFacts(value->getArg(0), query, depth);
    KnownBits input = KnownBits::unknown(width);
    input.knownZero = source.bits.knownZero & input.mask();
    input.knownOne = source.bits.knownOne & input.mask();
    const u32 amount = static_cast<u32>(value->getImm()) & 63U;
    const KnownBits result =
        op == MOP_SRLI ? kbLShr(input, amount) : kbAShr(input, amount);
    mergeBits(facts, result.knownZero, result.knownOne);
    return;
  }
  case MOP_ADDW:
  case MOP_ADD:
  case MOP_ADDIW:
  case MOP_ADDI: {
    if (value->getOperandCount() < 1)
      return;
    const MachineValueFacts left = childFacts(value->getArg(0), query, depth);
    const bool immediateForm = op == MOP_ADDIW || op == MOP_ADDI;
    if (!immediateForm && value->getOperandCount() < 2)
      return;
    const MachineValueFacts right =
        immediateForm ? constantFacts(value->getImm(), width)
                      : childFacts(value->getArg(1), query, depth);
    const u32 trailing =
        std::min(left.minTrailingZeros(), right.minTrailingZeros());
    mergeBits(facts, KnownBits::maskOfW(trailing) & mask, 0);

    const bool leftZero = (left.bits.knownZero & 1) != 0;
    const bool leftOne = (left.bits.knownOne & 1) != 0;
    const bool rightZero = (right.bits.knownZero & 1) != 0;
    const bool rightOne = (right.bits.knownOne & 1) != 0;
    if ((leftZero && rightZero) || (leftOne && rightOne))
      mergeBits(facts, 1, 0);
    else if ((leftZero && rightOne) || (leftOne && rightZero))
      mergeBits(facts, 0, 1);

    if (left.knownNonNegativeI32() && right.knownNonNegativeI32()) {
      const u64 maximum = unsignedMaxLow32(left) + unsignedMaxLow32(right);
      if (maximum <= static_cast<u64>(INT32_MAX)) {
        mergeBits(facts, Mask32 & ~KnownBits::maskOfW(bitWidth(maximum)), 0);
        tightenRange(facts, 0, static_cast<i64>(maximum));
      }
    }
    facts.range = facts.range.intersectWith(left.range.add(right.range));
    return;
  }
  case MOP_SUBW:
  case MOP_SUB: {
    if (value->getOperandCount() < 2)
      return;
    const MachineValueFacts left = childFacts(value->getArg(0), query, depth);
    const MachineValueFacts right = childFacts(value->getArg(1), query, depth);
    facts.range = facts.range.intersectWith(left.range.sub(right.range));
    return;
  }
  case MOP_NEGW: {
    if (value->getOperandCount() < 1)
      return;
    const MachineValueFacts source = childFacts(value->getArg(0), query, depth);
    facts.range = facts.range.intersectWith(source.range.negate());
    return;
  }
  case MOP_MULW:
  case MOP_MUL: {
    if (value->getOperandCount() < 2)
      return;
    const MachineValueFacts left = childFacts(value->getArg(0), query, depth);
    const MachineValueFacts right = childFacts(value->getArg(1), query, depth);
    if (left.knownZeroI32() || right.knownZeroI32()) {
      tightenRange(facts, 0, 0);
      mergeBits(facts, mask, 0);
      return;
    }
    const u32 trailing = std::min<u32>(width, left.minTrailingZeros() +
                                                  right.minTrailingZeros());
    mergeBits(facts, KnownBits::maskOfW(trailing) & mask, 0);
    const bool leftZero = (left.bits.knownZero & 1) != 0;
    const bool leftOne = (left.bits.knownOne & 1) != 0;
    const bool rightZero = (right.bits.knownZero & 1) != 0;
    const bool rightOne = (right.bits.knownOne & 1) != 0;
    if (leftZero || rightZero)
      mergeBits(facts, 1, 0);
    else if (leftOne && rightOne)
      mergeBits(facts, 0, 1);
    if (left.knownNonNegativeI32() && right.knownNonNegativeI32()) {
      const auto leftBounds = left.range.signedBounds();
      const auto rightBounds = right.range.signedBounds();
      if (leftBounds && rightBounds) {
        const i64 maximum = static_cast<i64>(leftBounds->max) *
                            static_cast<i64>(rightBounds->max);
        if (maximum >= 0 && maximum <= INT32_MAX)
          tightenRange(facts, 0, maximum);
      }
    }
    return;
  }
  default:
    return;
  }
}

bool isZeroRegister(const Inst *value) noexcept {
  return value && value->isPrecoloredDef() && value->id == rv64::ZERO;
}

const Inst *stripPlainCopies(const Inst *value) noexcept {
  for (u32 depth = 0; value && depth < 8; ++depth) {
    if ((value->getOp() != MOP_COPY && value->getOp() != MOP_FCOPY) ||
        value->getOperandCount() < 1)
      break;
    const Inst *source = value->getArg(0);
    if (!source || source->isPrecoloredDef())
      break;
    value = source;
  }
  return value;
}

std::optional<i32> immediateConstant(const Inst *value) noexcept {
  value = stripPlainCopies(value);
  if (!value)
    return std::nullopt;
  if (value->getOp() == OP_ICONST)
    return value->getImm();
  if (value->getOp() != MOP_LI)
    return std::nullopt;
  const i64 immediate = value->getImm64();
  if (immediate < INT32_MIN || immediate > INT32_MAX)
    return std::nullopt;
  return static_cast<i32>(immediate);
}

const BasicBlock *uniquePredecessor(const Function *function,
                                    const BasicBlock *block) {
  const BasicBlock *result = nullptr;
  if (!function || !function->region)
    return nullptr;
  for (const BasicBlock *candidate = function->region->first; candidate;
       candidate = candidate->next()) {
    const Inst *terminator = candidate->lastInst();
    if (!terminator)
      continue;
    bool reaches = false;
    for (u32 index = 0; index < terminator->getSuccessorSlotCount(); ++index)
      reaches = reaches || terminator->getSuccessorSlot(index) == block;
    if (!reaches)
      continue;
    if (result && result != candidate)
      return nullptr;
    result = candidate;
  }
  return result;
}

void applyZeroRelation(MachineValueFacts &facts, i32 relation) {
  switch (relation) {
  case 0:
    tightenRange(facts, 0, 0);
    break;
  case 1:
    tightenRange(facts, 1, INT32_MAX);
    facts.nonzero = true;
    break;
  case -1:
    mergeBits(facts, 0, Sign32);
    tightenRange(facts, INT32_MIN, -1);
    facts.nonzero = true;
    break;
  case 2:
    mergeBits(facts, Sign32, 0);
    tightenRange(facts, 0, INT32_MAX);
    break;
  case -2:
    tightenRange(facts, INT32_MIN, 0);
    break;
  default:
    break;
  }
}

void applyMaskedZeroRelation(MachineValueFacts &facts, u32 mask,
                             bool equalsZero) {
  if (mask == 0)
    return;
  if (equalsZero) {
    mergeBits(facts, mask, 0);
    return;
  }
  if ((mask & (mask - 1)) == 0)
    mergeBits(facts, 0, mask);
  facts.nonzero = true;
}

void extractBranchFact(const Inst *terminator, bool taken, const Inst *value,
                       MachineValueFacts &facts) {
  if (!terminator || terminator->getOperandCount() < 2)
    return;
  value = stripPlainCopies(value);
  const OpCode op = terminator->getOp();
  const Inst *left = stripPlainCopies(terminator->getArg(0));
  const Inst *right = stripPlainCopies(terminator->getArg(1));

  if (op == MOP_BEQ || op == MOP_BNE) {
    if ((left == value && isZeroRegister(right)) ||
        (right == value && isZeroRegister(left))) {
      const bool equalOnEdge = (op == MOP_BEQ) == taken;
      if (equalOnEdge)
        applyZeroRelation(facts, 0);
      else
        facts.nonzero = true;
      return;
    }

    const Inst *tested = nullptr;
    if (isZeroRegister(right))
      tested = left;
    else if (isZeroRegister(left))
      tested = right;
    if (!tested)
      return;
    const bool testedIsZero = (op == MOP_BEQ) == taken;
    if (tested->getOp() == MOP_SLT && tested->getOperandCount() >= 2) {
      const Inst *slLeft = stripPlainCopies(tested->getArg(0));
      const Inst *slRight = stripPlainCopies(tested->getArg(1));
      const bool less = !testedIsZero;
      if (slLeft == value && isZeroRegister(slRight))
        applyZeroRelation(facts, less ? -1 : 2);
      else if (isZeroRegister(slLeft) && slRight == value)
        applyZeroRelation(facts, less ? 1 : -2);

      if (slLeft == value) {
        if (const auto constant = immediateConstant(slRight)) {
          if (less && *constant > INT32_MIN)
            tightenRange(facts, INT32_MIN, static_cast<i64>(*constant) - 1);
          else if (!less)
            tightenRange(facts, *constant, INT32_MAX);
        }
      } else if (slRight == value) {
        if (const auto constant = immediateConstant(slLeft)) {
          if (less && *constant < INT32_MAX)
            tightenRange(facts, static_cast<i64>(*constant) + 1, INT32_MAX);
          else if (!less)
            tightenRange(facts, INT32_MIN, *constant);
        }
      }
      return;
    }
    if (tested->getOp() == MOP_ANDI && tested->getOperandCount() >= 1 &&
        stripPlainCopies(tested->getArg(0)) == value) {
      applyMaskedZeroRelation(facts, static_cast<u32>(tested->getImm()),
                              testedIsZero);
    }
    return;
  }

  if (op == MOP_BLT || op == MOP_BGE) {
    const bool leftLessRight = (op == MOP_BLT) == taken;
    if (left == value && isZeroRegister(right))
      applyZeroRelation(facts, leftLessRight ? -1 : 2);
    else if (isZeroRegister(left) && right == value)
      applyZeroRelation(facts, leftLessRight ? 1 : -2);
    else if (left == value) {
      if (const auto constant = immediateConstant(right)) {
        if (leftLessRight && *constant > INT32_MIN)
          tightenRange(facts, INT32_MIN, static_cast<i64>(*constant) - 1);
        else if (!leftLessRight)
          tightenRange(facts, *constant, INT32_MAX);
      }
    } else if (right == value) {
      if (const auto constant = immediateConstant(left)) {
        if (leftLessRight && *constant < INT32_MAX)
          tightenRange(facts, static_cast<i64>(*constant) + 1, INT32_MAX);
        else if (!leftLessRight)
          tightenRange(facts, INT32_MIN, *constant);
      }
    }
  }
}

void deriveContext(const Inst *value, const MachineValueFactQuery &query,
                   MachineValueFacts &facts) {
  if (!query.context || !query.function || !query.function->region)
    return;
  const BasicBlock *current = query.context->parentBlock();
  for (u32 step = 0; step < MaxContextWalk && current; ++step) {
    const BasicBlock *predecessor = uniquePredecessor(query.function, current);
    if (!predecessor)
      break;
    const Inst *terminator = predecessor->lastInst();
    if (!terminator || !isMachineBranch(terminator->getOp())) {
      current = predecessor;
      continue;
    }
    const bool trueEdge = terminator->getBr().trueBB == current;
    const bool falseEdge = terminator->getBr().falseBB == current;
    if (trueEdge == falseEdge)
      break;
    extractBranchFact(terminator, trueEdge, value, facts);
    current = predecessor;
  }
}

MachineValueFacts factsRec(const Inst *value,
                           const MachineValueFactQuery &query, u32 depth,
                           bool allowContext) {
  MachineValueFacts facts;
  facts.bits = KnownBits::unknown(query.width);
  if (!value)
    return facts;

  if (value->isPrecoloredDef()) {
    if (value->id == rv64::ZERO)
      return constantFacts(0, query.width);
    return facts;
  }

  const ScalarFactBundle seed = queryFactBundle(query.function, value);
  if (seed.valid) {
    if (!seed.range.isUnknown()) {
      const I32Range narrowed = facts.range.intersectWith(seed.range);
      if (narrowed.isEmpty())
        facts.meetState = FactMeetState::Bottom;
      else {
        facts.range = narrowed;
        if (facts.meetState == FactMeetState::Unknown)
          facts.meetState = FactMeetState::Known;
      }
    }
    if (seed.knownBits.valid())
      mergeBits(facts, seed.knownBits.knownZero, seed.knownBits.knownOne);
    if (seed.hasNonZero && seed.nonzero) {
      facts.nonzero = true;
      if (facts.meetState == FactMeetState::Unknown)
        facts.meetState = FactMeetState::Known;
    }
    absorbCongruenceSeed(facts, seed.congruence);
  }

  if (value->getOp() == OP_PHI) {
    if (allowContext && query.useContext)
      deriveContext(value, query, facts);
    finalize(facts);
    return facts;
  }

  if (depth != 0)
    deriveInstruction(value, query, depth, facts);
  if (allowContext && query.useContext)
    deriveContext(value, query, facts);
  finalize(facts);
  return facts;
}
} // namespace

bool MachineValueFacts::knownNonNegativeI32() const noexcept {
  if (meetState == FactMeetState::Bottom)
    return false;
  if (const auto bounds = range.signedBounds(); bounds && bounds->min >= 0)
    return true;
  return bits.valid() && bits.width >= 32 && (bits.knownZero & Sign32) != 0;
}

bool MachineValueFacts::knownNonZero() const noexcept {
  if (meetState == FactMeetState::Bottom)
    return false;
  if (nonzero || bits.knownNonZero())
    return true;
  const auto bounds = range.signedBounds();
  return bounds && (bounds->min > 0 || bounds->max < 0);
}

bool MachineValueFacts::knownZeroI32() const noexcept {
  if (meetState == FactMeetState::Bottom)
    return false;
  if (const auto constant = range.getSingleSigned(); constant && *constant == 0)
    return true;
  return bits.valid() && bits.width >= 32 &&
         (bits.knownZero & Mask32) == Mask32 && (bits.knownOne & Mask32) == 0;
}

u32 MachineValueFacts::minTrailingZeros() const noexcept {
  return meetState == FactMeetState::Bottom ? 0 : bits.minTrailingZeros();
}

MachineValueFactQuery
MachineValueFactQuery::forDefRewriteI32(const Function *function) noexcept {
  MachineValueFactQuery query;
  query.function = function;
  query.useContext = false;
  return query;
}

MachineValueFactQuery
MachineValueFactQuery::forUseSiteI32(const Function *function,
                                     const Inst *context) noexcept {
  MachineValueFactQuery query;
  query.function = function;
  query.context = context;
  query.useContext = true;
  return query;
}

MachineValueFacts computeMachineValueFacts(const Inst *value,
                                           const MachineValueFactQuery &query) {
  if (query.width == 0 || query.width > 64)
    return {};
  return factsRec(value, query, query.maxDepth, query.useContext);
}

} // namespace svm::ir
