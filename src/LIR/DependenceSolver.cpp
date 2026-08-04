#include "DependenceSolver.h"

#include <algorithm>
#include <numeric>

namespace svm::ir {
namespace {

struct Bounds {
  i64 minimum = 0; // 仿射项最小值
  i64 maximum = 0; // 仿射项最大值
};

u64 magnitude(i64 value) noexcept {
  return value < 0 ? static_cast<u64>(-(value + 1)) + 1
                   : static_cast<u64>(value);
}

bool evaluateTerm(i64 sourceCoefficient, i64 sourceIteration,
                  i64 sinkCoefficient, i64 sinkIteration,
                  i64 &result) noexcept {
  i64 source = 0;
  i64 sink = 0;
  return checkedMul(sourceCoefficient, sourceIteration, source) &&
         checkedMul(sinkCoefficient, sinkIteration, sink) &&
         checkedSub(source, sink, result);
}

bool includeValue(i64 value, Bounds &bounds, bool &initialized) noexcept {
  if (!initialized) {
    bounds = {value, value};
    initialized = true;
  } else {
    bounds.minimum = std::min(bounds.minimum, value);
    bounds.maximum = std::max(bounds.maximum, value);
  }
  return true;
}

std::optional<Bounds> directionBounds(i64 sourceCoefficient,
                                      i64 sinkCoefficient,
                                      DependenceDirection direction,
                                      i64 tripCount) noexcept {
  if (tripCount <= 0)
    return std::nullopt;
  const i64 upper = tripCount - 1;
  Bounds result;
  bool initialized = false;
  const auto addPoint = [&](i64 source, i64 sink) {
    i64 value = 0;
    return evaluateTerm(sourceCoefficient, source, sinkCoefficient, sink,
                        value) &&
           includeValue(value, result, initialized);
  };

  switch (direction) {
  case DependenceDirection::Equal:
    if (!addPoint(0, 0) || !addPoint(upper, upper))
      return std::nullopt;
    break;
  case DependenceDirection::Less:
    if (upper == 0)
      return std::nullopt;
    if (!addPoint(0, 1) || !addPoint(0, upper) || !addPoint(upper - 1, upper))
      return std::nullopt;
    break;
  case DependenceDirection::Greater:
    if (upper == 0)
      return std::nullopt;
    if (!addPoint(1, 0) || !addPoint(upper, 0) || !addPoint(upper, upper - 1))
      return std::nullopt;
    break;
  }
  return initialized ? std::optional<Bounds>(result) : std::nullopt;
}

std::optional<Bounds> boxBounds(i64 sourceCoefficient, i64 sinkCoefficient,
                                i64 tripCount) noexcept {
  VERIFY(tripCount > 0);
  const i64 upper = tripCount - 1;
  i64 sourceUpper = 0;
  i64 sinkUpper = 0;
  Bounds result;
  if (!checkedMul(sourceCoefficient, upper, sourceUpper) ||
      !checkedMul(sinkCoefficient, upper, sinkUpper) ||
      !checkedSub(std::min(i64{0}, sourceUpper), std::max(i64{0}, sinkUpper),
                  result.minimum) ||
      !checkedSub(std::max(i64{0}, sourceUpper), std::min(i64{0}, sinkUpper),
                  result.maximum))
    return std::nullopt;
  return result;
}

void enumerateDirections(u32 depth, bool allowEqual,
                         std::vector<DirectionVector> &result) {
  DirectionVector current(depth, DependenceDirection::Equal);
  const auto visit = [&](u32 index, const auto &self) -> void {
    if (index == depth) {
      if (isForwardDirection(current, allowEqual))
        result.push_back(current);
      return;
    }
    for (DependenceDirection direction :
         {DependenceDirection::Less, DependenceDirection::Equal,
          DependenceDirection::Greater}) {
      current[index] = direction;
      self(index + 1, self);
    }
  };
  visit(0, visit);
}

std::optional<usize> singleSIVDimension(const DependenceProblem &problem) {
  if (!problem.localCoefficients.empty())
    return std::nullopt;
  std::optional<usize> active;
  for (usize index = 0; index < problem.source.coefficients.size(); ++index) {
    const i64 source = problem.source.coefficients[index];
    const i64 sink = problem.sink.coefficients[index];
    if (source == 0 && sink == 0)
      continue;
    if (active)
      return std::nullopt;
    active = index;
  }
  return active;
}

struct StrongSIVInfo {
  DependenceDirection direction = DependenceDirection::Equal; // 精确方向
  std::optional<i64> distance; // 可表示的sink-source精确距离
  u64 distanceMagnitude = 0;   // 距离绝对值 可表示2^63
};

std::optional<StrongSIVInfo> solveStrongSIV(i64 coefficient,
                                            i64 rightHandSide) noexcept {
  VERIFY(coefficient != 0);
  const u64 divisor = magnitude(coefficient);
  const u64 dividend = magnitude(rightHandSide);
  if (dividend % divisor != 0)
    return std::nullopt;

  StrongSIVInfo result;
  result.distanceMagnitude = dividend / divisor;
  if (result.distanceMagnitude == 0) {
    result.distance = 0;
    return result;
  }

  const bool quotientIsNegative = (rightHandSide < 0) != (coefficient < 0);
  result.direction = quotientIsNegative ? DependenceDirection::Less
                                        : DependenceDirection::Greater;
  if (quotientIsNegative) {
    if (result.distanceMagnitude <=
        static_cast<u64>(std::numeric_limits<i64>::max()))
      result.distance = static_cast<i64>(result.distanceMagnitude);
  } else if (result.distanceMagnitude ==
             u64{1} << (std::numeric_limits<i64>::digits)) {
    result.distance = std::numeric_limits<i64>::min();
  } else {
    result.distance = -static_cast<i64>(result.distanceMagnitude);
  }
  return result;
}

DependenceSolution unknown(DependenceSolverFailure failure) {
  return {
      DependenceStatus::Unknown, DependenceProof::None, failure, {}, {}, {}};
}

} // namespace

bool isForwardDirection(const DirectionVector &direction,
                        bool allowAllEqual) noexcept {
  const auto first = std::find_if(
      direction.begin(), direction.end(), [](DependenceDirection component) {
        return component != DependenceDirection::Equal;
      });
  return first == direction.end() ? allowAllEqual
                                  : *first == DependenceDirection::Less;
}

DependenceSolution solveDependence(const DependenceProblem &problem) {
  DependenceSolution result;
  const usize depth = problem.tripCounts.size();
  if (problem.source.coefficients.size() != depth ||
      problem.sink.coefficients.size() != depth)
    return unknown(DependenceSolverFailure::InvalidProblem);
  for (const std::optional<i64> &tripCount : problem.tripCounts) {
    if (tripCount && *tripCount < 0)
      return unknown(DependenceSolverFailure::InvalidProblem);
    if (tripCount && *tripCount == 0) {
      result.status = DependenceStatus::NoDependence;
      result.proof = DependenceProof::ZIV;
      return result;
    }
  }

  i64 rightHandSide = 0;
  if (!checkedSub(problem.sink.constant, problem.source.constant,
                  rightHandSide))
    return unknown(DependenceSolverFailure::ArithmeticOverflow);

  u64 divisor = 0;
  for (usize index = 0; index < depth; ++index) {
    const i64 source = problem.source.coefficients[index];
    const i64 sink = problem.sink.coefficients[index];
    divisor = std::gcd(divisor, magnitude(source));
    divisor = std::gcd(divisor, magnitude(sink));
  }
  for (i64 coefficient : problem.localCoefficients)
    divisor = std::gcd(divisor, magnitude(coefficient));
  if (divisor == 0 && rightHandSide != 0) {
    result.status = DependenceStatus::NoDependence;
    result.proof = DependenceProof::ZIV;
    return result;
  }
  if (divisor != 0 && magnitude(rightHandSide) % divisor != 0) {
    result.status = DependenceStatus::NoDependence;
    result.proof = DependenceProof::GCD;
    return result;
  }

  result.distanceMultiples.resize(depth);
  if (rightHandSide == 0) {
    // c*(source-sink)=-rest, rest的GCD给出公共循环距离的整除下界
    for (usize index = 0; index < depth; ++index) {
      const i64 coefficient = problem.source.coefficients[index];
      if (coefficient == 0 || coefficient != problem.sink.coefficients[index])
        continue;
      u64 otherDivisor = 0;
      for (usize other = 0; other < depth; ++other) {
        if (other == index)
          continue;
        otherDivisor = std::gcd(otherDivisor,
                                magnitude(problem.source.coefficients[other]));
        otherDivisor =
            std::gcd(otherDivisor, magnitude(problem.sink.coefficients[other]));
      }
      for (i64 local : problem.localCoefficients)
        otherDivisor = std::gcd(otherDivisor, magnitude(local));
      if (otherDivisor != 0) {
        const u64 multiple =
            otherDivisor / std::gcd(otherDivisor, magnitude(coefficient));
        if (multiple > 1)
          result.distanceMultiples[index] = multiple;
      }
    }
  }

  const std::optional<usize> singleDimension = singleSIVDimension(problem);
  std::optional<StrongSIVInfo> strongSIV;
  if (singleDimension) {
    const usize index = *singleDimension;
    const i64 sourceCoefficient = problem.source.coefficients[index];
    const i64 sinkCoefficient = problem.sink.coefficients[index];
    if (sourceCoefficient == sinkCoefficient) {
      strongSIV = solveStrongSIV(sourceCoefficient, rightHandSide);
      if (!strongSIV) {
        result.status = DependenceStatus::NoDependence;
        result.proof = DependenceProof::SIV;
        return result;
      }
      if (problem.tripCounts[index] &&
          strongSIV->distanceMagnitude >=
              static_cast<u64>(*problem.tripCounts[index])) {
        result.status = DependenceStatus::NoDependence;
        result.proof = DependenceProof::SIV;
        return result;
      }
    }
  }

  bool allBoundsKnown = problem.localCoefficients.empty();
  Bounds boxTotal;
  for (usize index = 0; index < depth; ++index) {
    if (!problem.tripCounts[index]) {
      allBoundsKnown = false;
      break;
    }
    const std::optional<Bounds> term =
        boxBounds(problem.source.coefficients[index],
                  problem.sink.coefficients[index], *problem.tripCounts[index]);
    if (!term)
      return unknown(DependenceSolverFailure::ArithmeticOverflow);
    i64 minimum = 0;
    i64 maximum = 0;
    if (!checkedAdd(boxTotal.minimum, term->minimum, minimum) ||
        !checkedAdd(boxTotal.maximum, term->maximum, maximum))
      return unknown(DependenceSolverFailure::ArithmeticOverflow);
    boxTotal = {minimum, maximum};
  }
  if (allBoundsKnown && depth != 0 &&
      (rightHandSide < boxTotal.minimum || rightHandSide > boxTotal.maximum)) {
    result.status = DependenceStatus::NoDependence;
    result.proof = DependenceProof::Banerjee;
    return result;
  }

  if (depth > problem.maxDirectionDepth)
    return unknown(DependenceSolverFailure::DirectionBudgetExceeded);
  enumerateDirections(static_cast<u32>(depth), problem.allowEqualIterations,
                      result.directions);
  result.distances.resize(depth);

  if (singleDimension && strongSIV) {
    const usize index = *singleDimension;
    result.directions.erase(
        std::remove_if(result.directions.begin(), result.directions.end(),
                       [&](const DirectionVector &direction) {
                         return direction[index] != strongSIV->direction;
                       }),
        result.directions.end());
    result.distances[index] = strongSIV->distance;
    result.proof = DependenceProof::SIV;
    if (result.directions.empty()) {
      result.status = DependenceStatus::NoDependence;
      return result;
    }
  }

  bool overflowed = false;
  bool usedBounds = false;
  result.directions.erase(
      std::remove_if(
          result.directions.begin(), result.directions.end(),
          [&](const DirectionVector &direction) {
            bool fullyBounded = problem.localCoefficients.empty();
            for (usize index = 0; index < depth; ++index) {
              if (!problem.tripCounts[index]) {
                fullyBounded = false;
                continue;
              }
              if (*problem.tripCounts[index] <= 1 &&
                  direction[index] != DependenceDirection::Equal)
                return usedBounds = true;
            }
            if (!fullyBounded)
              return false;

            Bounds total;
            for (usize index = 0; index < depth; ++index) {
              const std::optional<Bounds> term =
                  directionBounds(problem.source.coefficients[index],
                                  problem.sink.coefficients[index],
                                  direction[index], *problem.tripCounts[index]);
              if (!term) {
                overflowed = true;
                return false;
              }
              i64 minimum = 0;
              i64 maximum = 0;
              if (!checkedAdd(total.minimum, term->minimum, minimum) ||
                  !checkedAdd(total.maximum, term->maximum, maximum)) {
                overflowed = true;
                return false;
              }
              total = {minimum, maximum};
            }
            usedBounds = depth != 0;
            return rightHandSide < total.minimum ||
                   rightHandSide > total.maximum;
          }),
      result.directions.end());

  if (overflowed)
    return unknown(DependenceSolverFailure::ArithmeticOverflow);
  if (result.directions.empty()) {
    result.status = DependenceStatus::NoDependence;
    result.proof =
        usedBounds ? DependenceProof::Banerjee : DependenceProof::ZIV;
    return result;
  }
  if (usedBounds && result.proof == DependenceProof::None)
    result.proof = DependenceProof::Banerjee;
  result.status = DependenceStatus::MayDependence;
  return result;
}

} // namespace svm::ir
