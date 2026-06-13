#ifndef SVM_IR_DEEP_COPY_H
#define SVM_IR_DEEP_COPY_H

#include "DiagnosticEngine.h"
#include "IR.h"

#include <functional>
#include <unordered_map>
#include <vector>

namespace svm {
namespace ir {

enum class ExternalValueMode {
  Keep,          // 同函数克隆保留未映射的外部值
  RequireMapped, // 跨函数克隆要求局部值已显式映射
};

enum class CloneInstAction {
  Clone,        // 克隆指令
  SkipMapped,   // 使用已有映射替代指令
  SkipUnmapped, // 跳过且不建立映射
};

enum class ExternalTargetMode {
  Mirror,   // 集合外目标保持原目标或显式块映射
  Redirect, // 集合外目标统一重定向
};

struct ClonedBlockPair {
  BasicBlock *source = nullptr;
  BasicBlock *clone = nullptr;
};

struct ClonedReturnSite {
  BasicBlock *block = nullptr; // 克隆返回所在块
  Inst *value = nullptr;       // 已翻译返回值
};

struct RegionCloneResult {
  Region *region = nullptr;              // 克隆Region
  BasicBlock *entry = nullptr;           // 克隆入口块
  std::vector<ClonedReturnSite> returns; // 克隆返回点
};

struct BlockCloneConfig {
  // 新块布局锚点
  BasicBlock *insertAfter = nullptr;
  // 自定义建块
  std::function<BasicBlock *(BasicBlock *, BasicBlock *)> createBlock;
  // 指令决策
  std::function<CloneInstAction(BasicBlock *, Inst *, bool)> decideInst;
  // 集合外目标策略
  ExternalTargetMode externalTargetMode = ExternalTargetMode::Mirror;
  // 集合外重定向目标
  BasicBlock *redirectTarget = nullptr;
  // 跳过终结符时的补尾目标
  std::function<BasicBlock *(Inst *)> skippedTerminatorTarget;
  // 自定义操作数翻译
  std::function<Inst *(Inst *, Inst *, Inst *)> translateOperand;
  // 每次调用清空块和跳转表映射
  bool freshBlockMappings = false;
};

struct RegionCloneConfig {
  ExternalValueMode externalValueMode = ExternalValueMode::Keep; // 外部值策略
  std::function<Inst *(Inst *)> remapValueBeforeClone;           // 克隆前值替换
  std::function<void(Inst *, Inst *)> afterCloneInst;            // 克隆后回调
  std::function<bool(Inst *, Inst *)> rewriteTerminator; // 终结符接管回调
  Region *insertInto = nullptr;                          // 可选目标Region
  BasicBlock *insertAfter = nullptr;                     // 目标Region内布局锚点
};

class DeepCopy {
public:
  explicit DeepCopy(Function *function) noexcept; // 创建函数内克隆事务

  void mapInst(Inst *source, Inst *replacement);                 // 注入值映射
  void mapBlock(BasicBlock *source, BasicBlock *replacement);    // 注入块映射
  bool hasInstMapping(const Inst *source) const noexcept;        // 查询值映射
  bool hasBlockMapping(const BasicBlock *source) const noexcept; // 查询块映射
  Inst *translate(Inst *source) const noexcept;                  // 翻译值
  BasicBlock *translateBlock(BasicBlock *source) const noexcept; // 翻译块

  // 创建空Phi映射
  Inst *materializeMappedPhi(Inst *sourcePhi, BasicBlock *destination);
  // 克隆Region
  RegionCloneResult copyRegion(Region *source,
                               const RegionCloneConfig &config = {});
  // 克隆结构指令
  Inst *copyStructuredInstAfter(Inst *source, Inst *insertAfter,
                                const RegionCloneConfig &config = {});
  // 克隆普通指令
  Inst *
  copyInstBefore(Inst *source, Inst *insertBefore,
                 const std::function<Inst *(Inst *)> &translateValue = {});
  // 物化表达式切片
  Inst *
  materializeInstructionSlice(Inst *root, Inst *insertBefore,
                              const std::function<bool(Inst *)> &isSliceLocal,
                              const std::function<bool(Inst *)> &canCloneInst);
  // 克隆任意块集
  std::vector<ClonedBlockPair>
  copyBlocks(const std::vector<BasicBlock *> &blocks,
             const BlockCloneConfig &config = {});
  // 克隆路径块
  BasicBlock *
  copySingleBlockInPath(BasicBlock *source, BasicBlock *insertAfter,
                        BasicBlock *newTerminatorTarget,
                        const std::function<Inst *(Inst *)> &translateValue,
                        const std::function<bool(Inst *)> &valueVisible);
  // 克隆完整函数
  static Function *copyFunction(Function *source,
                                const char *newName = nullptr);
  // 展平Region指令
  void flattenRegionIntoBlock(Region *source, BasicBlock *destination,
                              bool keepTrailingTerminator);
  // 补退出Phi
  void addTranslatedExitPhiIncomings(
      Function *function, const std::vector<ClonedBlockPair> &blocks,
      const std::function<bool(BasicBlock *, BasicBlock *)> &filter = {});

private:
  using BlockTranslator = std::function<BasicBlock *(BasicBlock *)>;

  Function *function_ = nullptr;
  DiagnosticEngine *diagnostics_ = nullptr;
  IRBuilder builder_;
  std::unordered_map<const Inst *, Inst *> instMap_;              // 值映射
  std::unordered_map<const BasicBlock *, BasicBlock *> blockMap_; // 块映射
  std::unordered_map<JumpTable *, JumpTable *> jumpTableMap_;     // 跳转表映射

  void note(const Inst *inst, const char *message) const;
  Inst *lookupInstMapping(const Inst *source) const noexcept; // 查询显式值映射
  Inst *cloneShell(Inst *source); // 克隆指令外壳并登记映射
  void appendShell(BasicBlock *destination, Inst *clone, bool phi);
  void remapPhiIncoming(Inst *clone, const BlockTranslator &translateBlock);
  void remapTerminatorTargets(Inst *clone,
                              const BlockTranslator &translateBlock);
  void remapJumpTable(Inst *clone, const BlockTranslator &translateBlock);
  JumpTable *cloneJumpTable(JumpTable *source,
                            const BlockTranslator &translateBlock);
  void cloneSubregions(Inst *source, Inst *clone,
                       const RegionCloneConfig &config,
                       RegionCloneResult &result);
  Inst *resolveOperand(Inst *source, const RegionCloneConfig &config);
  Inst *rematerializeConstant(Inst *source);
  bool isTargetLocal(const Inst *value) const noexcept;
  Region *cloneRegionInto(Region *source, const RegionCloneConfig &config,
                          RegionCloneResult &result);
  void spliceBlocksAfter(Region *source, Region *destination,
                         BasicBlock *anchor);
};

} // namespace ir
} // namespace svm

#endif // SVM_IR_DEEP_COPY_H
