#ifndef SOURCE_LOCATION_H
#define SOURCE_LOCATION_H

#include "Types.h"
#include <string_view>

namespace svm {
struct SourceLocation {
  std::string_view snapshot;
  u32 line = 0;   // 1-based
  u32 column = 0; // 1-based
  u32 length = 0;

  bool isValid() const noexcept { return !snapshot.empty() && line > 0; }
};
} // namespace svm

#endif // SOURCE_LOCATION_H