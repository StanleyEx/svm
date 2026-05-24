#ifndef SOURCE_LOCATION_H
#define SOURCE_LOCATION_H

#include "Types.h"

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
};
} // namespace svm

#endif // SOURCE_LOCATION_H