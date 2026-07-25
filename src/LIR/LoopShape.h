#ifndef LIR_LOOP_SHAPE_H
#define LIR_LOOP_SHAPE_H

#include "SCEV.h"

#include <optional>
#include <unordered_map>
#include <vector>

namespace svm::ir {

// 规范化为"满足谓词时继续循环"的分支条件
struct NormalizedLoopPredicate {
  Inst *comparison = nullptr;            // 整数比较指令
  SCEVExpr *testedSCEV = nullptr;        // 被测表达式的SCEV
  Inst *boundValue = nullptr;            // 循环不变边界
  SCEVExpr *boundSCEV = nullptr;         // 边界的SCEV表达式
  OpCode canonicalPredicate = OP_ICONST; // 继续循环时成立的规范谓词
  bool testedIsLHS = true;               // 被测值是否为原比较左操作数
  bool continueOnTrue = true;            // 原分支true边是否继续循环
  i32 boundArgIndex = -1;                // 比较中边界操作数槽位
  BasicBlock *exitTarget = nullptr;      // 不继续时到达的块
};

// Header Phi在preheader和latch两条边上的锚点
struct HeaderPhiShape {
  Inst *phi = nullptr;            // Header Phi
  Inst *preheaderValue = nullptr; // 循环入口值
  Inst *latchValue = nullptr;     // 回边更新值
  bool isControlIV = false;       // 是否为控制归纳变量
};

// 控制IV的SCEV事实与现有IR改写锚点
struct ControlIVShape {
  Inst *phi = nullptr;           // 控制Phi
  Inst *stepInst = nullptr;      // 物化的latch更新
  Inst *stepConstant = nullptr;  // 更新中的常量操作数
  i32 stepConstantArgIndex = -1; // 常量操作数槽位
  OpCode updateOp = OP_ICONST;   // OP_ADD或OP_SUB
  SCEVExpr *baseSCEV = nullptr;  // AddRec初值
  SCEVExpr *stepSCEV = nullptr;  // AddRec步长
  i64 step = 0;                  // 常量步长
};

// Rotated counted-loop
struct CountedLoopShape {
  Loop *loop = nullptr;                   // 自然循环
  BasicBlock *header = nullptr;           // 循环头
  BasicBlock *preheader = nullptr;        // 唯一前置块
  BasicBlock *latch = nullptr;            // 唯一回边块
  BasicBlock *exit = nullptr;             // 唯一退出目标
  std::vector<HeaderPhiShape> headerPhis; // 全部Header Phi
  ControlIVShape iv;                      // 控制IV
  NormalizedLoopPredicate latchTest;      // 规范化latch条件
  SCEVExpr *backedgeTakenCount = nullptr; // 入环后的精确回边次数
  i64 constantTripCount = -1;             // 正常量迭代次数
};

struct LoopShapeReject {
  const char *stableReason = "ok"; // 拒绝原因 "ok"表示成功
};

// 规约branch比较的操作数顺序, 分支极性和循环不变边界
std::optional<NormalizedLoopPredicate>
analyzeLoopPredicate(const SCEV *scev, const Loop *loop, Inst *branch,
                     SCEVExpr *wanted, BasicBlock *continueTarget,
                     BasicBlock *expectedExit,
                     LoopShapeReject *reject = nullptr);

struct LoopShapeQuery {
  bool requireLatchContinueOnTrue = false; // 要求true边回到header
  bool requireLatchCompareInLatch = false; // 要求比较定义在latch
};

enum class HeaderPhiIncomingKind : u8 {
  Reset,    // 该边传入值不能表示为phi加常量
  SelfDelta // 该边传入值等于phi加常量
};

struct HeaderPhiIncomingTransfer {
  // 对应前驱边
  BasicBlock *predecessor = nullptr;
  // 该边传入值
  Inst *incomingValue = nullptr;
  // 边局部递推类别
  HeaderPhiIncomingKind kind = HeaderPhiIncomingKind::Reset;
  // SelfDelta时的常量增量
  i64 delta = 0;
  // Single Latch中间Phi保留的原回边事实
  std::vector<HeaderPhiIncomingTransfer> mergedIncoming;
};

struct HeaderPhiTransferInfo {
  Loop *loop = nullptr;                            // Phi所属循环
  BasicBlock *header = nullptr;                    // 循环头
  Inst *phi = nullptr;                             // 被分析Phi
  std::vector<HeaderPhiIncomingTransfer> incoming; // 逐边事实
  bool hasNonzeroSelfDelta = false;                // 是否存在有收益的递推边
};

class LoopShapeInfo {
public:
  LoopShapeInfo() = default;
  LoopShapeInfo(LoopShapeInfo &&) noexcept = default;
  LoopShapeInfo &operator=(LoopShapeInfo &&) noexcept = default;
  LoopShapeInfo(const LoopShapeInfo &) = delete;
  LoopShapeInfo &operator=(const LoopShapeInfo &) = delete;

  // 返回满足公共形态和附加查询条件的counted loop
  std::optional<CountedLoopShape>
  getCountedLoop(Loop *loop, const LoopShapeQuery &query,
                 LoopShapeReject *reject = nullptr) const;

  // 返回多incoming Header Phi的逐边常量递推事实
  std::optional<HeaderPhiTransferInfo> getHeaderPhiTransfer(Inst *phi) const;

private:
  friend struct LoopShapeAnalysis;

  struct CacheEntry {
    std::optional<CountedLoopShape> shape; // 公共基础形态
    LoopShapeReject reject;                // 构建失败原因
  };

  const SCEV *scev_ = nullptr;
  const LoopInfo *loopInfo_ = nullptr;
  // 循环形态缓存
  mutable std::unordered_map<Loop *, CacheEntry> byLoop_;
  // Header Phi事实缓存
  mutable std::unordered_map<Inst *, std::optional<HeaderPhiTransferInfo>>
      phiTransfers_;

  void build(const SCEV *scev, const LoopInfo *loopInfo) noexcept;
  bool buildBaseShape(Loop *loop, CountedLoopShape &shape,
                      LoopShapeReject &reject) const;
  // 查询或创建缓存项
  const CacheEntry &baseShapeOf(Loop *loop) const;
};

} // namespace svm::ir

#endif // LIR_LOOP_SHAPE_H
