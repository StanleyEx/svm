#ifndef LIR_LSR_ADDRESS_H
#define LIR_LSR_ADDRESS_H

#include "SCEV.h"

#include <optional>
#include <unordered_set>
#include <vector>

namespace svm::ir {

class AliasInfo;
class DominatorTree;
class LoopShapeInfo;

namespace lsr_address {

// LSR 私有的一维递推描述 不是通用 SCEV 接口
struct AddRecurrence {
  Loop *loop = nullptr;     // 递推所属循环
  SCEVExpr *base = nullptr; // 第零次迭代地址
  SCEVExpr *step = nullptr; // 每轮字节步长
};

enum class AddressEvolutionKind : u8 {
  None,            // 不可折减
  CanonicalAddRec, // 标准 SCEV AddRec
  EdgeLocalPhi,    // 非规范 header Phi 的边局部递推
};

struct CanonicalAddressEvolution {
  Loop *loop = nullptr;     // 递推所属循环
  SCEVExpr *base = nullptr; // 第零次迭代地址
  SCEVExpr *step = nullptr; // 常量字节步长
};

struct EdgeLocalAddressEvolution {
  Loop *loop = nullptr; // Phi 所属循环
  Inst *root = nullptr; // 循环不变的指针根
  Inst *phi = nullptr;  // header 标量 Phi
  i64 coefficient = 0;  // 标量 Phi 的字节系数
  i64 constant = 0;     // 固定字节偏移
};

struct AddressEvolution {
  AddressEvolutionKind kind = AddressEvolutionKind::None; // 分类结果
  Inst *getPtr = nullptr;                                 // 原 GETPTR
  Inst *root = nullptr;                                   // 别名根
  CanonicalAddressEvolution canonical;                    // 标准递推事实
  EdgeLocalAddressEvolution edgeLocal;                    // 边局部事实
};

// 从表达式中提取唯一线性 AddRec
std::optional<AddRecurrence> findAddRecurrence(const SCEV *scev,
                                               SCEVExpr *expression);

// 判断一条 GETPTR 是否可改写为 pointer recurrence
std::optional<AddressEvolution>
classifyAddressEvolution(const SCEV *scev, const LoopInfo *loopInfo,
                         Inst *getPtr, const LoopShapeInfo *loopShape = nullptr,
                         const AliasInfo *aliasInfo = nullptr,
                         const DominatorTree *dominatorTree = nullptr);

// 在一次 LSR 改写中复用刚创建的 pointer recurrence
class ExpansionSession {
public:
  ExpansionSession(Function *function, const SCEV *scev) noexcept;

  // 登记支配loop查询点的递推
  void registerAvailableAddRec(SCEVExpr *base, SCEVExpr *step, Loop *loop,
                               Inst *value);
  // 物化或复用表达式
  Inst *expandCodeFor(SCEVExpr *expression, Inst *insertBefore);
  // 查询可复用值
  bool hasAvailableFor(SCEVExpr *expression, BasicBlock *block) const;
  // 预检依赖
  bool dependsOnAny(SCEVExpr *expression,
                    const std::unordered_set<Inst *> &values) const;

private:
  struct Available {
    Loop *loop = nullptr;       // 递推所属循环
    SCEVExpr *addRec = nullptr; // 完整递推表达式
    Inst *value = nullptr;      // 已有 pointer Phi
  };

  const SCEV *scev_ = nullptr;
  SCEVExpander expander_;
  IRBuilder builder_;
  std::vector<Available> available_; // 本轮新建递推
};

} // namespace lsr_address
} // namespace svm::ir

#endif // LIR_LSR_ADDRESS_H
