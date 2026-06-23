#ifndef BACKEND_RV64_H
#define BACKEND_RV64_H

#include "Utils.h"

namespace svm::ir::rv64 {

enum PReg : u8 {
  X0,
  X1,
  X2,
  X3,
  X4,
  X5,
  X6,
  X7,
  X8,
  X9,
  X10,
  X11,
  X12,
  X13,
  X14,
  X15,
  X16,
  X17,
  X18,
  X19,
  X20,
  X21,
  X22,
  X23,
  X24,
  X25,
  X26,
  X27,
  X28,
  X29,
  X30,
  X31,
  F0,
  F1,
  F2,
  F3,
  F4,
  F5,
  F6,
  F7,
  F8,
  F9,
  F10,
  F11,
  F12,
  F13,
  F14,
  F15,
  F16,
  F17,
  F18,
  F19,
  F20,
  F21,
  F22,
  F23,
  F24,
  F25,
  F26,
  F27,
  F28,
  F29,
  F30,
  F31,
  NUM_PREGS = 64,
};

enum RegClass : u8 { RC_GPR = 0, RC_FPR = 1 };
inline constexpr u32 kRegisterCount = NUM_PREGS;
inline constexpr u32 kArgumentRegisterCount = 8;
inline constexpr PReg ZERO = X0, RA = X1, SP = X2, GP = X3, TP = X4, FP = X8;
inline constexpr PReg A0 = X10, A1 = X11, A2 = X12, A3 = X13;
inline constexpr PReg A4 = X14, A5 = X15, A6 = X16, A7 = X17;
inline constexpr PReg FA0 = F10, FA1 = F11, FA2 = F12, FA3 = F13;
inline constexpr PReg FA4 = F14, FA5 = F15, FA6 = F16, FA7 = F17;
inline constexpr PReg RESERVED_TMP = X5, RESERVED_FPR_TMP = F0;
inline constexpr PReg GPR_ARG[] = {X10, X11, X12, X13, X14, X15, X16, X17};
inline constexpr PReg FPR_ARG[] = {F10, F11, F12, F13, F14, F15, F16, F17};
inline constexpr u32 GPR_ARG_N = kArgumentRegisterCount;
inline constexpr u32 FPR_ARG_N = kArgumentRegisterCount;

inline constexpr u64 GPR_CALLER_MASK =
    (u64{1} << X1) | (u64{1} << X5) | (u64{1} << X6) | (u64{1} << X7) |
    (u64{1} << X10) | (u64{1} << X11) | (u64{1} << X12) | (u64{1} << X13) |
    (u64{1} << X14) | (u64{1} << X15) | (u64{1} << X16) | (u64{1} << X17) |
    (u64{1} << X28) | (u64{1} << X29) | (u64{1} << X30) | (u64{1} << X31);
inline constexpr u64 FPR_CALLER_MASK =
    (u64{1} << F0) | (u64{1} << F1) | (u64{1} << F2) | (u64{1} << F3) |
    (u64{1} << F4) | (u64{1} << F5) | (u64{1} << F6) | (u64{1} << F7) |
    (u64{1} << F10) | (u64{1} << F11) | (u64{1} << F12) | (u64{1} << F13) |
    (u64{1} << F14) | (u64{1} << F15) | (u64{1} << F16) | (u64{1} << F17) |
    (u64{1} << F28) | (u64{1} << F29) | (u64{1} << F30) | (u64{1} << F31);
inline constexpr u64 CALL_CLOBBER_MASK = GPR_CALLER_MASK | FPR_CALLER_MASK;
inline constexpr u64 GPR_CALLEE_MASK =
    (u64{1} << X8) | (u64{1} << X9) | (u64{1} << X18) | (u64{1} << X19) |
    (u64{1} << X20) | (u64{1} << X21) | (u64{1} << X22) | (u64{1} << X23) |
    (u64{1} << X24) | (u64{1} << X25) | (u64{1} << X26) | (u64{1} << X27);
inline constexpr u64 FPR_CALLEE_MASK =
    (u64{1} << F8) | (u64{1} << F9) | (u64{1} << F18) | (u64{1} << F19) |
    (u64{1} << F20) | (u64{1} << F21) | (u64{1} << F22) | (u64{1} << F23) |
    (u64{1} << F24) | (u64{1} << F25) | (u64{1} << F26) | (u64{1} << F27);

constexpr RegClass pregClass(PReg reg) noexcept {
  return reg < F0 ? RC_GPR : RC_FPR;
}
constexpr bool isGPR(PReg reg) noexcept { return reg < F0; }
constexpr bool isFPR(PReg reg) noexcept { return reg >= F0 && reg < NUM_PREGS; }
constexpr bool isAllocatable(PReg reg) noexcept {
  return reg != ZERO && reg != SP && reg != GP && reg != TP &&
         reg != RESERVED_TMP && reg != RESERVED_FPR_TMP;
}
constexpr bool isCalleeSaved(PReg reg) noexcept {
  return reg < NUM_PREGS &&
         (((GPR_CALLEE_MASK | FPR_CALLEE_MASK) >> reg) & u64{1}) != 0;
}
constexpr bool fitsImm12(i64 value) noexcept {
  return value >= -2048 && value <= 2047;
}

inline const char *pregName(PReg reg) noexcept {
  static const char *const names[NUM_PREGS] = {
      "zero", "ra",  "sp",   "gp",  "tp",  "t0",  "t1",  "t2",  "s0",   "s1",
      "a0",   "a1",  "a2",   "a3",  "a4",  "a5",  "a6",  "a7",  "s2",   "s3",
      "s4",   "s5",  "s6",   "s7",  "s8",  "s9",  "s10", "s11", "t3",   "t4",
      "t5",   "t6",  "ft0",  "ft1", "ft2", "ft3", "ft4", "ft5", "ft6",  "ft7",
      "fs0",  "fs1", "fa0",  "fa1", "fa2", "fa3", "fa4", "fa5", "fa6",  "fa7",
      "fs2",  "fs3", "fs4",  "fs5", "fs6", "fs7", "fs8", "fs9", "fs10", "fs11",
      "ft8",  "ft9", "ft10", "ft11"};
  return reg < NUM_PREGS ? names[reg] : "??";
}

} // namespace svm::ir::rv64

#endif // BACKEND_RV64_H
