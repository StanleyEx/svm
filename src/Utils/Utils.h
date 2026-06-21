#ifndef TYPES_H
#define TYPES_H

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <type_traits>

using u8 = uint8_t;
using u16 = uint16_t;
using u32 = uint32_t;
using u64 = uint64_t;

using i8 = int8_t;
using i16 = int16_t;
using i32 = int32_t;
using i64 = int64_t;

using f32 = float;
using f64 = double;

using byte = std::byte;
using usize = std::size_t;
using isize = std::ptrdiff_t;

using uintptr = std::uintptr_t;
using intptr = std::intptr_t;

template <typename Float,
          std::enable_if_t<std::is_floating_point_v<Float>, int> = 0>
bool canConvertToI32(Float value) noexcept {
  if (!std::isfinite(value))
    return false;

  const long double truncated = std::trunc(static_cast<long double>(value));
  return truncated >=
             static_cast<long double>(std::numeric_limits<i32>::min()) &&
         truncated <= static_cast<long double>(std::numeric_limits<i32>::max());
}

constexpr i32 i32FromBits(u32 bits) noexcept {
  return bits <= static_cast<u32>(INT32_MAX)
             ? static_cast<i32>(bits)
             : static_cast<i32>(static_cast<i64>(bits) - (i64{1} << 32));
}

constexpr i32 i32TruncWrap(i64 value) noexcept {
  return i32FromBits(static_cast<u32>(static_cast<u64>(value)));
}

constexpr i64 i32SignExtendWrap(i64 value) noexcept {
  return static_cast<i64>(i32TruncWrap(value));
}

constexpr i32 i32NegWrap(i32 value) noexcept {
  return i32FromBits(u32{0} - static_cast<u32>(value));
}

constexpr i32 i32AddWrap(i32 left, i32 right) noexcept {
  return i32FromBits(static_cast<u32>(left) + static_cast<u32>(right));
}

constexpr i32 i32SubWrap(i32 left, i32 right) noexcept {
  return i32FromBits(static_cast<u32>(left) - static_cast<u32>(right));
}

constexpr i32 i32MulWrap(i32 left, i32 right) noexcept {
  return i32FromBits(static_cast<u32>(left) * static_cast<u32>(right));
}

#define VERIFY(expr, ...)                                                      \
  ([&](const char *__msg = "operation should succeed") noexcept(               \
       noexcept(expr)) -> decltype(auto) {                                     \
    decltype(auto) __v = (expr);                                               \
    assert(__v && __msg);                                                      \
    return __v;                                                                \
  }(__VA_ARGS__))

#define UNUSED(expr) (void)(expr)

#endif // TYPES_H
