#ifndef AST_H
#define AST_H

#include "Token.h"
#include "TypeSystem.h"
#include "Utils/Arena.h"
#include "Utils/SourceLocation.h"
#include "Utils/Types.h"

#include <string>
#include <string_view>

namespace svm {
class Type;

} // namespace svm

// LLVM-style RTTI
template <typename To, typename From> inline bool isa(const From *p) noexcept {
  return p != nullptr && To::classof(p);
}

template <typename To, typename From> inline To *dyn_cast(From *p) noexcept {
  return (p && To::classof(p)) ? static_cast<To *>(p) : nullptr;
}

template <typename To, typename From>
inline const To *dyn_cast(const From *p) noexcept {
  return (p && To::classof(p)) ? static_cast<const To *>(p) : nullptr;
}

template <typename To, typename From> inline To *cast(From *p) noexcept {
  assert(p && To::classof(p) && "cast<> Failed: type mismatch");
  return static_cast<To *>(p);
}

template <typename To, typename From>
inline const To *cast(const From *p) noexcept {
  assert(p && To::classof(p) && "cast<> Failed: type mismatch");
  return static_cast<const To *>(p);
}

#endif // AST_H