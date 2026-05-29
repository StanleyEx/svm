#ifndef SOURCE_LOCATION_H
#define SOURCE_LOCATION_H

#include "Utils.h"

#include <cassert>

namespace svm {
struct SourceLocation {
  usize offset = 0;
  u32 line = 0;   // 1-based
  u32 column = 0; // 1-based
  usize length = 0;

  SourceLocation(usize offset = 0, u32 line = 0, u32 column = 0,
                 usize length = 0)
      : offset(offset), line(line), column(column), length(length) {}

  bool isValid() const noexcept { return line > 0; }

  SourceLocation operator+(const SourceLocation &rhs) const noexcept {
    assert(isValid() && rhs.isValid());
    SourceLocation result;
    if (offset > rhs.offset) {
      result = *this;
      result.length = offset - rhs.offset + rhs.length;
    } else {
      result = rhs;
      result.length = rhs.offset - offset + length;
    }
    return result;
  }
};
} // namespace svm

#endif // SOURCE_LOCATION_H