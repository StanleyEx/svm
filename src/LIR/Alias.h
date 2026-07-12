#ifndef LIR_ALIAS_H
#define LIR_ALIAS_H

#include "IR.h"
#include "PassManager.h"

#include <optional>
#include <unordered_map>

namespace svm::ir {

struct PredicateContext;
class SCEV;
struct EffectSummary;

enum class AliasResult : u8 {
  NoAlias,      // 一定不相交
  MustAlias,    // 完全相同
  PartialAlias, // 部分相交
  MayAlias,
};

enum class PointerKind : u8 {
  Alloca, // 函数栈对象
  Global, // 模块全局对象
  Param,  // 指针形参指向的外部对象
  Opaque, // 无法归约到唯一抽象对象
};

struct PointerInfo {
  PointerKind kind = PointerKind::Opaque;
  Inst *root = nullptr;              // 定义抽象对象的SSA根
  std::optional<i64> constantOffset; // 相对根的常量字节偏移
  std::optional<u64> objectSize;     // 根对象总字节数

  bool hasConstantOffset() const noexcept { return constantOffset.has_value(); }
  bool hasObjectSize() const noexcept { return objectSize.has_value(); }
};

struct MemoryLocation {
  Inst *pointer = nullptr;       // 本次内存访问的地址SSA值
  std::optional<u64> accessSize; // 本次访问宽度而非根对象大小

  // 从Load/Store构造
  static MemoryLocation fromMemoryInstruction(Inst *instruction) noexcept;
};

struct AliasQuery {
  BasicBlock *contextBlock = nullptr;                 // 两个访问共享的块上下文
  const PredicateContext *predicateContext = nullptr; // 两个访问共享的路径事实
  bool allowSCEV = true;                              // 允许 SCEV 增强证明
};

class AliasInfo {
public:
  AliasInfo() = default;

  void build(Function *function, const SCEV *scev,
             ModuleAnalysisManager *moduleAnalyses = nullptr);

  AliasResult alias(const MemoryLocation &left, const MemoryLocation &right,
                    const AliasQuery &query = {}) const;
  AliasResult alias(Inst *left, Inst *right,
                    const AliasQuery &query = {}) const;
  PointerInfo info(Inst *pointer) const;
  // 证明访存区间位于具体栈或全局对象内
  bool isDereferenceable(const MemoryLocation &location,
                         const AliasQuery &query = {}) const;

  // 删除类优化使用的上下文无关保守重叠查询
  bool mayOverlapForStoreElim(const MemoryLocation &writer,
                              const MemoryLocation &reader) const;
  // 未知访问宽度查询
  bool mayOverlapForStoreElim(Inst *writer, Inst *reader) const;
  // 查询covering常量区间是否完整覆盖covered
  bool fullyCovers(const MemoryLocation &covering,
                   const MemoryLocation &covered) const;
  // 查询地址是否与本函数所有栈对象互不别名
  bool isNoAliasWithLocals(Inst *pointer) const;

  // 使用 IPA 摘要查询调用是否可能读取位置
  bool mayReadMemory(Inst *call, const MemoryLocation &location,
                     const EffectSummary &effects,
                     const AliasQuery &query = {}) const {
    return mayAccessMemoryWithIPA(call, location, effects, query, false);
  }
  bool mayReadMemory(Inst *call, Inst *pointer,
                     const EffectSummary &effects) const {
    return mayReadMemory(call, {pointer, std::nullopt}, effects);
  }
  // 使用 IPA 摘要查询调用是否可能写入位置
  bool mayWriteMemory(Inst *call, const MemoryLocation &location,
                      const EffectSummary &effects,
                      const AliasQuery &query = {}) const {
    return mayAccessMemoryWithIPA(call, location, effects, query, true);
  }
  bool mayWriteMemory(Inst *call, Inst *pointer,
                      const EffectSummary &effects) const {
    return mayWriteMemory(call, {pointer, std::nullopt}, effects);
  }

  // 使用可用模块摘要查询调用是否可能读取位置
  bool mayReadMemory(Inst *call, const MemoryLocation &location,
                     const AliasQuery &query = {}) const;
  bool mayReadMemory(Inst *call, Inst *pointer) const {
    return mayReadMemory(call, {pointer, std::nullopt});
  }
  // 使用可用模块摘要查询调用是否可能写入位置
  bool mayWriteMemory(Inst *call, const MemoryLocation &location,
                      const AliasQuery &query = {}) const;
  bool mayWriteMemory(Inst *call, Inst *pointer) const {
    return mayWriteMemory(call, {pointer, std::nullopt});
  }

  // 查询是否因规模保护退化为保守结果
  bool isConservative() const noexcept { return conservative_; }
  // 可分析的指针数上限 超过则一律返回保守结果
  static constexpr u32 kMaxPointerCount = 100000;

private:
  friend struct AliasAnalysis;

  // 递归求解根信息
  PointerInfo computePointerInfo(Inst *pointer) const;
  // 判断抽象根等价
  bool sameRoot(const PointerInfo &left,
                const PointerInfo &right) const noexcept;
  // 对同一根的动态偏移尝试额外证明 NoAlias
  bool proveNoAliasWithSCEV(const MemoryLocation &left,
                            const MemoryLocation &right,
                            const PointerInfo &leftInfo,
                            const PointerInfo &rightInfo,
                            const AliasQuery &query) const;
  // 共享调用点参数绑定与全局对象 Mod/Ref 判定
  bool mayAccessMemoryWithIPA(Inst *call, const MemoryLocation &location,
                              const EffectSummary &effects,
                              const AliasQuery &query, bool writes) const;

  Function *function_ = nullptr;
  const SCEV *scev_ = nullptr;
  ModuleAnalysisManager *moduleAnalyses_ = nullptr;
  mutable std::unordered_map<Inst *, PointerInfo> pointerInfo_; // 根信息缓存
  bool conservative_ = false; // 是否超过阈值全部返回保守结果
};

} // namespace svm::ir

#endif // LIR_ALIAS_H
