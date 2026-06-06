#ifndef TYPES_H
#define TYPES_H

#include <cstddef>
#include <cstdint>

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

#define UNUSED(x) (void)(x)

#endif // TYPES_H
