/// @file IRC.cpp
/// @brief 基于 George-Appel 迭代合并的 RV64 图着色寄存器分配器
//
// 本分配器消费 Phi 消除后的 OutOfSSA MIR, 在 frame layout 之前把所有普通
// VReg 改写为物理寄存器, 主循环实现 Iterated Register Coalescing:
//
//   Build -> MakeWorklist -> (Simplify | Coalesce | Freeze | SelectSpill)*
//         -> AssignColors -> (RewriteProgram 后重建 | Finalize)
//
// George/Briggs 判定只负责证明图收缩是否保守安全, call-site clobber 和 forced
// color 直接形成正确性约束, 多定义 web 还会阻止图级合并; ABI affinity, 热度,
// 重物化和颜色复用距离属于质量策略, 只能在合法边界内改变处理顺序,
// 颜色选择或改写选择
//
// 节点使用紧凑编号
//   - [0, virtualCount) 是普通 VReg 节点
//   - [virtualCount, virtualCount + NUM_PREGS) 是预着色 PReg 节点
//
// 每个普通节点只由 NodeState 表示归属, 每条 move 只由 MoveState 表示归属;
// 工作队列和 move 堆允许保留过期条目, 弹出时按状态过滤, 避免维护多组易失集合;
// finalize 后每个普通节点都保存有序邻接向量;
// 预着色端不展开邻接表, VReg-PReg 真实干涉边只保存在 VReg 端
//
// 正确性不变量如下
//   - 预着色节点颜色固定, 永不进入普通节点工作队列
//   - Coalesce 先排除端点干涉, 类别或颜色冲突和多定义策略,
//     再由 George/Briggs 保守判定决定是否收缩图
//   - AssignColors 只从普通颜色, small spill storage 或 forcedColor 指定的
//     支持颜色中选择未被邻居占用的颜色
//   - ra, t0, ft0 永不作为普通 VReg 颜色; t0 和 ft0 由 RA 后处理作为 scratch;
//     ra 由 call 写入并承载返回地址
//   - s10, s11, fs10, fs11 只作为 small spill storage, 不进入普通颜色集合
//   - spillDepth 单调递增并饱和; 所有保值重写继承稳定 VReg metadata
//   - RewriteProgram 后的图, 活跃性, 编号, 状态和 metadata 投影全部失效,
//     下一轮必须完整重建
//
// "Iterated Register Coalescing" https://c9x.me/compile/bib/irc.pdf

#include "Analysis.h"
#include "IPRAInfo.h"
#include "MIRPass.h"
#include "MoveInfo.h"
#include "RV64.h"
#include "VReg.h"

#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdlib>
#include <limits>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

namespace svm::ir {

using namespace rv64;

namespace {

// 无效节点哨兵值, 用于表示未分配
constexpr u32 kNoNode = std::numeric_limits<u32>::max();
// 无效指令编号哨兵值, 也用于表示颜色尚未出现
constexpr u32 kNoInstruction = std::numeric_limits<u32>::max();
// 稀疏指令编号步长, 同时决定短生命周期保护阈值的尺度
constexpr u32 kInstructionScale = 2;
// 每个寄存器类最多向另一类值借出的跨类槽数
constexpr u32 kMaxCrossClassSlotsPerClass = 2;
// 正常 IRC rewrite 的轮数上限
constexpr u32 kMaxAllocationRounds = 64;
// 全量栈 spill 后允许短生命周期临时值完成着色的额外轮数
constexpr u32 kFinalAllocationRounds = 8;

SourceLocation diagnosticLocation(const Inst *inst) noexcept {
  return inst && inst->sourceLocation ? *inst->sourceLocation
                                      : SourceLocation{};
}

template <typename... Args>
void emitDiagnostic(Function *function, DiagnosticLevel level,
                    SourceLocation location, const char *format, Args... args) {
  DiagnosticEngine *diagnostics =
      function && function->module ? function->module->diagnostics : nullptr;
  if (diagnostics)
    diagnostics->diagEmit(level, location, __FILE__, __func__, __LINE__, format,
                          args...);
}

template <typename... Args>
[[noreturn]] void fatal(Function *function, SourceLocation location,
                        const char *format, Args... args) {
  emitDiagnostic(function, DiagnosticLevel::Fatal, location, format, args...);
  std::abort();
}

// 物理颜色集合, 分配顺序和保留策略的单一事实来源

// IRC 颜色顺序策略
//
// 1. 不提供 x0/zero, x2/sp, x3/gp 和 x4/tp
//    这些 GPR 具有体系结构或 ABI 固定用途, 不能承载普通 VReg
// 2. 禁用 x5/t0 和 f0/ft0
//    fixupStackOffsets 在大偏移时借用 RESERVED_TMP(x5/t0), 发生在 RA 之后
//    CallShuffle 同样在 RA 之后借用 RESERVED_TMP 和 RESERVED_FPR_TMP 解开搬运环
//    若 IRC 把它们分给普通 VReg, 后处理会无条件覆盖仍然活跃的值
// 3. 禁用 ra
//    return/prologue 仍隐式依赖 ra 保存返回地址
// 4. 禁用 s10/s11, fs10/fs11
//    它们作为同寄存器类的 small spill storage, 必须从普通颜色集合中拿掉
//    避免同一物理寄存器同时承担普通 VReg 与 storage 两种身份
// 5. 数组顺序只是最终稳定 tie-break
//    chooseColor 会先处理 ABI 和 copy affinity, 再计入 caller-saved 与已计入
//    callee-saved 颜色成本; 所有分数相同时, FPR 叶函数从 fa0-fa7
//    开始, 非叶函数从 ft 系列开始, 两张表的颜色成员完全相同
constexpr std::array<PReg, 24> kGPRColorOrder = {
    X10, X11, X12, X13, X14, X15, X16, X17, // a0-a7
    X6,  X7,                                // t1-t2
    X28, X29, X30, X31,                     // t3-t6
    X8,  X9,                                // s0-s1
    X18, X19, X20, X21, X22, X23, X24, X25, // s2-s9
};

constexpr std::array<PReg, 29> kFPRColorOrderLeaf = {
    F10, F11, F12, F13, F14, F15, F16, F17, // fa0-fa7
    F1,  F2,  F3,  F4,  F5,  F6,  F7,       // ft1-ft7
    F28, F29, F30, F31,                     // ft8-ft11
    F8,  F9,                                // fs0-fs1
    F18, F19, F20, F21, F22, F23, F24, F25, // fs2-fs9
};

constexpr std::array<PReg, 29> kFPRColorOrderNonLeaf = {
    F1,  F2,  F3,  F4,  F5,  F6,  F7,       // ft1-ft7
    F28, F29, F30, F31,                     // ft8-ft11
    F10, F11, F12, F13, F14, F15, F16, F17, // fa0-fa7
    F8,  F9,                                // fs0-fs1
    F18, F19, F20, F21, F22, F23, F24, F25, // fs2-fs9
};

constexpr std::array<PReg, 2> kGPRSpillStorage = {X26, X27};
constexpr std::array<PReg, 2> kFPRSpillStorage = {F26, F27};

constexpr u64 registerBit(PReg reg) noexcept {
  return u64{1} << static_cast<u32>(reg);
}

template <usize Size>
constexpr u64 registerMask(const std::array<PReg, Size> &registers) noexcept {
  u64 mask = 0;
  for (PReg reg : registers)
    mask |= registerBit(reg);
  return mask;
}

constexpr u64 kGPRColorMask = registerMask(kGPRColorOrder);
constexpr u64 kFPRColorMaskLeaf = registerMask(kFPRColorOrderLeaf);
constexpr u64 kGPRSpillStorageMask = registerMask(kGPRSpillStorage);
constexpr u64 kFPRSpillStorageMask = registerMask(kFPRSpillStorage);
constexpr u64 kGPRRegisterMask = std::numeric_limits<u32>::max();
constexpr u64 kFPRRegisterMask = ~kGPRRegisterMask;

static_assert((kGPRColorMask & kGPRSpillStorageMask) == 0);
static_assert((kFPRColorMaskLeaf & kFPRSpillStorageMask) == 0);
static_assert((kGPRColorMask & registerBit(RESERVED_TMP)) == 0);
static_assert((kFPRColorMaskLeaf & registerBit(RESERVED_FPR_TMP)) == 0);
static_assert((kGPRColorMask & registerBit(RA)) == 0);

/// 返回指定寄存器类的基础普通颜色位集
/// 该集合尚未扣除动态跨类预留 叶函数与非叶函数的基础成员相同,
/// FPR 只在 chooseColor 中调整遍历顺序
u64 baseOrdinaryColorMask(RegClass registerClass) noexcept {
  if (registerClass == RC_FPR)
    return kFPRColorMaskLeaf;
  return kGPRColorMask;
}

/// 返回同寄存器类的 small spill storage 颜色位集
u64 baseStorageColorMask(RegClass registerClass) noexcept {
  return registerClass == RC_FPR ? kFPRSpillStorageMask : kGPRSpillStorageMask;
}

/// 判断物理寄存器是否属于该类 IRC 支持的基础颜色全集
/// 动态跨类预留只改变本轮可分配掩码, 不改变 forcedColor 的合法性
bool isSupportedColor(PReg reg, RegClass registerClass) noexcept {
  if (reg >= NUM_PREGS || pregClass(reg) != registerClass)
    return false;
  const u64 supported = baseOrdinaryColorMask(registerClass) |
                        baseStorageColorMask(registerClass);
  return (supported & registerBit(reg)) != 0;
}

// 稳定块顺序和指令编号

/// 返回入口可达块的 RPO, 并按布局顺序追加不可达块
/// RA 必须给所有仍在 Region 链上的机器指令分配寄存器
/// 不可达块也需要编号和活跃信息, 可达部分仍保持 RPO 以稳定启发式顺序
std::vector<BasicBlock *> completeBlockOrder(Function *function) {
  std::vector<BasicBlock *> order = computeRPO(function);
  for (BasicBlock *block = function->region->first; block;
       block = block->next())
    if (std::find(order.begin(), order.end(), block) == order.end())
      order.push_back(block);
  return order;
}

// 指令编号只服务 move tie-break, 活跃跨度近似和颜色复用距离
// 每轮按固定步长完整重编号, 使 footprint, 短生命周期阈值和距离共用尺度
class InstructionNumbering {
public:
  /// 按完整块顺序重建当前 MIR 的稳定稀疏编号
  /// 编号饱和后使用 kNoInstruction, 避免无符号回绕破坏距离比较
  void compute(Function *function) {
    numbers_.clear();
    numbers_.reserve(function->instCount);
    u32 number = 0;
    for (BasicBlock *block : completeBlockOrder(function))
      forEachOp(block, [&](Inst *inst) {
        numbers_.emplace(inst, number);
        number = number > kNoInstruction - kInstructionScale
                     ? kNoInstruction
                     : number + kInstructionScale;
      });
  }

  /// 查询指令编号, 不属于本轮 MIR 的指令返回 kNoInstruction
  u32 numberOf(const Inst *inst) const noexcept {
    const auto found = numbers_.find(inst);
    return found == numbers_.end() ? kNoInstruction : found->second;
  }

private:
  std::unordered_map<const Inst *, u32> numbers_;
};

// IRC 私有位向量, 只服务活跃性分析和 Build 热循环

u32 bitWordCount(u32 bitCount) noexcept {
  return bitCount / 64 + static_cast<u32>(bitCount % 64 != 0);
}

void setBit(u64 *bits, u32 index) noexcept {
  bits[index / 64] |= u64{1} << (index % 64);
}

void clearBit(u64 *bits, u32 index) noexcept {
  bits[index / 64] &= ~(u64{1} << (index % 64));
}

bool testBit(const u64 *bits, u32 index) noexcept {
  return ((bits[index / 64] >> (index % 64)) & u64{1}) != 0;
}

void unionBits(u64 *destination, const u64 *source, u32 words) noexcept {
  for (u32 word = 0; word < words; ++word)
    destination[word] |= source[word];
}

void assignUnionDifference(u64 *destination, const u64 *use, const u64 *liveOut,
                           const u64 *definition, u32 words) noexcept {
  // 位向量实现 liveIn = use | (liveOut & ~definition)
  for (u32 word = 0; word < words; ++word)
    destination[word] = use[word] | (liveOut[word] & ~definition[word]);
}

bool equalBits(const u64 *left, const u64 *right, u32 words) noexcept {
  for (u32 word = 0; word < words; ++word)
    if (left[word] != right[word])
      return false;
  return true;
}

template <typename FunctionT>
void forEachSetBit(const u64 *bits, u32 bitCount, FunctionT function) {
  // ctz 定位最低置位, x &= x - 1 清除该位, 避免对每个可能 bit 单独测试
  // 总复杂度为 O(wordCount + popcount)
  const u32 words = bitWordCount(bitCount);
  for (u32 word = 0; word < words; ++word) {
    u64 remaining = bits[word];
    while (remaining != 0) {
      const u32 bit = static_cast<u32>(__builtin_ctzll(remaining));
      const u32 index = word * 64 + bit;
      if (index < bitCount)
        function(index);
      remaining &= remaining - 1;
    }
  }
}

// 活跃性 universe 只有 [0, virtualCount) 的普通 VReg
// 物理寄存器 use 不参加 VReg 数据流, call 的隐式破坏在 Build 中转换为
// VReg-PReg 干涉边, 因而这里不需要旧实现的 PReg 前缀位段
class VRegLiveness {
public:
  void compute(Function *function);
  const u64 *liveOut(const BasicBlock *block) const {
    return slice(liveOut_, block);
  }
  u32 wordCount() const noexcept { return wordCount_; }

private:
  u64 *slice(std::vector<u64> &storage, const BasicBlock *block);
  const u64 *slice(const std::vector<u64> &storage,
                   const BasicBlock *block) const;
  void computeLocalSets(BasicBlock *block);
  void solveDataflow();

  Function *function_ = nullptr;
  // 当前轮 VReg 数量
  u32 virtualCount_ = 0;
  // 每个位集切片的有效 u64 数量
  u32 wordCount_ = 0;
  // 每块切片至少占一个 u64, 使空 universe 也有稳定且互不重叠的地址
  u32 stride_ = 1;
  // 完整块顺序, 先是入口可达 RPO, 再是布局中的不可达块
  std::vector<BasicBlock *> order_;
  // 基本块到连续切片下标的映射
  std::unordered_map<const BasicBlock *, usize> blockIndex_;
  // 以下四个数组均按 blockIndex * stride 寻址, 每轮 compute 完整清零
  std::vector<u64> definitions_;
  std::vector<u64> uses_;
  std::vector<u64> liveIn_;
  std::vector<u64> liveOut_;
};

// 重物化只接受无副作用且不读取寄存器的单条定义

enum class RematKind : u8 {
  None, // 不可重物化
  Li,   // 无副作用且只依赖立即数的 LI
  La,   // 无副作用且只依赖符号引用的 LA
};

struct RematInfo {
  RematKind kind = RematKind::None; // 重物化类别
  i64 immediate = 0;                // LI 的立即数值
  SymbolRef symbol{};               // LA 的完整符号引用
  Inst *definition = nullptr;       // 原始定义, 所有使用改写后可据此删除死定义
  IRType type = TY_VOID;            // 重建结果必须保持原始 IR 类型
};

// IRC 节点状态和 move 状态均为唯一语义来源, 队列只保存可过期索引

enum class NodeState : u8 {
  Initial,   // Build 后尚未由 MakeWorklist 分类
  Simplify,  // 等待压栈, 包含低度数节点和乐观 spill 候选
  Freeze,    // 低度数且仍与可合并 move 相关
  Spill,     // 高度数的潜在 spill 候选
  OnStack,   // 已从当前收缩图移除并压入 selectStack
  Coalesced, // 已合并到其它节点, alias 指向代表节点
  Colored,   // 已有颜色, 包含固定颜色的预着色节点
  Spilled,   // AssignColors 未找到颜色, 等待 RewriteProgram
};

enum class MoveState : u8 {
  Worklist,    // 在 move heap 中等待尝试合并
  Active,      // 当前暂不可合并, 等图变化后由 enableMoves 唤醒
  Coalesced,   // 已成功合并或两端 alias 已经相同
  Constrained, // 因干涉, 硬约束或多定义策略不再图级合并, 仍可作为着色 soft hint
  Frozen,      // 被 Freeze 放弃图级合并机会
};

struct MoveRecord {
  // COPY 目标节点
  u32 destination = 0;
  // COPY 源节点, 可以是 VReg 或预着色 PReg
  u32 source = 0;
  // PhiParallelCopy, ArgCopy 或 Normal
  MoveKind kind = MoveKind::Normal;
  // 合并优先级, 等于 move 类别基础权重乘块频率
  double weight = 0.0;
  // 完整块顺序下的指令编号, 用于稳定打破同权重平局
  u32 order = kNoInstruction;
  // move 的唯一归属, moveHeap_ 中的条目只是可过期缓存
  MoveState state = MoveState::Worklist;
};

struct NodeInfo {
  // 寄存器类别, 决定 K, 颜色顺序与 spill storage 集合
  RegClass registerClass = RC_GPR;
  // 当前有效度数, 预着色节点使用不会跌落的高值模拟无穷
  u32 degree = 0;
  // 节点唯一归属, 队列只缓存历史索引
  NodeState state = NodeState::Initial;

  // 是否可零栈槽重物化, 最终只允许单定义 MOP_LI 或 MOP_LA
  bool rematerializable = false;
  // 重物化需要的立即数或符号, 原始定义和类型
  RematInfo remat;

  // spill 派生代数, 保值改写时单调递增并饱和
  u8 spillDepth = 0;
  // 是否主要服务常量存储路径, spill 评分会降低其保留优先级
  bool storeConstant = false;
  // 通用物理颜色硬约束, 当前主要由跨类 storage proxy 使用
  // NUM_PREGS 表示无约束
  PReg forcedColor = NUM_PREGS;

  // 每次 use 或 def 所在块频率的总和
  double useDefWeight = 0.0;
  // 第一次 use 或 def 的指令编号, 未出现时为 kNoInstruction
  u32 firstInstruction = kNoInstruction;
  // 最后一次 use 或 def 的指令编号, 用于估算线性跨度
  u32 lastInstruction = kNoInstruction;
  // 所有出现位置的最大块频率
  double hotness = 1.0;

  // ArgCopy, 返回值或调用实参产生的 ABI 软偏好, NUM_PREGS 表示无偏好
  PReg abiPreference = NUM_PREGS;
  // 当前 VReg web 的真实定义点数量, 多定义时禁用 remat 和跨类槽
  u32 definitionCount = 0;
  // definitionCount 等于 1 时的唯一定义
  Inst *singleDefinition = nullptr;
  // SelectSpill 综合评分, 越小越先成为候选受害者
  double spillCost = 0.0;

  /// 返回基于完整块顺序编号的线性出现跨度近似
  /// 该值不是精确 live range 长度, 跨块时会受 RPO 和布局影响
  /// 最小值为 1, 避免未编号或同点 use-def 导致除零
  u64 footprint() const noexcept {
    return firstInstruction != kNoInstruction &&
                   lastInstruction != kNoInstruction &&
                   lastInstruction > firstInstruction
               ? static_cast<u64>(lastInstruction - firstInstruction)
               : 1;
  }
};

// 干涉图只展开普通节点端的邻接表, VReg-PReg 边也只存入 VReg 端
// Build 阶段允许重复追加, finalize 后及 Coalesce 阶段始终保持有序去重
struct InterferenceGraph {
  /// Build 热循环追加边, 不执行查重或即时 degree 维护
  void addBuildEdge(u32 left, u32 right);
  /// 对普通节点邻接表排序去重, 并从唯一边数初始化 degree
  void finalize(std::vector<NodeInfo> &nodes);
  /// 查询当前收缩图中的干涉关系, 有序邻接表允许使用二分查找
  bool hasEdge(u32 left, u32 right) const;
  /// Coalesce 阶段向单个普通节点端有序插边, 新边同步增加该端 degree
  void insertSorted(u32 owner, u32 other, std::vector<NodeInfo> &nodes);

  // 小于 virtualCount 的节点为普通 VReg, 其余节点为预着色 PReg
  u32 virtualCount = 0;
  // 普通节点保存有序邻接表, 预着色节点对应的向量始终为空
  std::vector<std::vector<u32>> adjacency;
};

// IRC 分配器每轮完成一次标准主循环, spill 改写后丢弃全部轮内状态并重建
class IRCAllocator {
public:
  void run(Function *function, FunctionAnalysisManager &analyses);

private:
  // === 顶层 ===
  // 一轮完整 IRC, 返回 true 表示未着色节点已经过 RewriteProgram
  bool allocateRound();
  // 落地最终颜色, 更新 calleeSaveMask 并记录 IPRA
  void finalizeColoring();
  // 全量栈 spill 安全阀, 仍由后续轮次验证短生命周期 reload 能否着色
  void massSpillFallback();

  // === Build ===
  // 构建干涉图, move 表, 节点统计与 spill cost; 每轮从空图重建
  void build();
  /// 记录一次 use 或 def 出现, 累计块频率权重并更新首末编号和 hotness
  void noteOccurrence(u32 node, double frequency, u32 instruction);

  // === 主迭代 ===
  // 按 degree 与 move-related 分流 Initial 节点到三个队列
  void makeWorklist();
  // 从 Simplify 队列压栈一个低度数节点或乐观 spill 候选
  bool trySimplify();
  // 先检查硬约束和多定义策略, 再按 George 或 Briggs 判定尝试合并
  bool tryCoalesce();
  // 冻结一个低度数 move-related 节点的关联 move
  bool tryFreeze();
  // 从 Spill 队列选最低评分节点, 冻结关联 move 后送入 Simplify
  bool trySelectSpill();

  // === 子过程 ===
  // Simplify, Freeze 和 Spill 三类工作队列的统一入队入口
  void enqueue(u32 node, NodeState state);
  // 弹出仍处于目标状态的节点, 丢弃过期残影
  u32 popNode(std::vector<u32> &queue, NodeState state);

  /// 遍历 node 在当前收缩图中的有效邻居
  /// OnStack 和 Coalesced 节点不属于论文中的 Adjacent(node)
  template <typename FunctionT>
  void forEachAdjacent(u32 node, FunctionT function) const {
    for (u32 adjacent : graph_.adjacency[node]) {
      const NodeState state = nodes_[adjacent].state;
      if (state != NodeState::OnStack && state != NodeState::Coalesced)
        function(adjacent);
    }
  }

  /// 遍历仍可驱动图级合并的关联 move
  /// Frozen, Constrained 和 Coalesced move 仍保留给着色 soft hint
  template <typename FunctionT>
  void forEachNodeMove(u32 node, FunctionT function) {
    for (u32 move : moveLists_[node]) {
      const MoveState state = moves_[move].state;
      if (state == MoveState::Worklist || state == MoveState::Active)
        function(move);
    }
  }

  // n 是否仍有关联 Worklist/Active move
  bool moveRelated(u32 node) const;
  // 逻辑移除一个有效邻居后维护 degree, K-1 边界唤醒并重分类
  void decrementDegree(u32 node);
  // 把 n 关联的 Active move 唤回 Worklist
  void enableMoves(u32 node);
  // 低度数非 move-related 普通节点转入 Simplify
  void addWorklist(u32 node);
  // Briggs 保守条件, 合并邻域中的高度数节点少于 K
  bool briggsConservative(u32 left, u32 right);
  // 检查寄存器类, forcedColor, 预着色支持色域和动态保留色是否兼容
  bool colorConstraintsCompatible(u32 left, u32 right) const;
  // 合并 merged 到 root, 迁移 move 和边, 普通 root 还合并统计
  void combine(u32 root, u32 merged);
  // 冻结关联 move, 使相关低度数节点可继续 Simplify
  void freezeMoves(u32 node);
  // 沿 Coalesced alias 链找当前代表节点
  u32 alias(u32 node) const;

  // === move 优先队列 ===
  // 按权重, 类型, 完整块顺序编号和 move 编号决定堆内尝试顺序
  bool moveWorse(u32 left, u32 right) const;
  // Worklist move 压入优先堆
  void pushMove(u32 move);
  // 弹出当前仍为 Worklist 的最高优先级 move
  u32 popWorklistMove();

  // === 颜色 ===
  // 按 selectStack 的后进先出顺序着色, 失败者进入 spilledNodes_
  void assignColors();
  // 在已排除干涉的普通颜色 available 集合内按启发式择优
  PReg chooseColor(u32 node, u64 available);

  // === Spill / Rewrite ===
  // 计算 SelectSpill 使用的综合评分
  double spillCost(const NodeInfo &node) const;
  // 改写 spilledNodes_, 分派 remat, 跨类 storage 或栈槽
  void rewriteProgram();
  // 零栈槽重物化, 每条 Use 指令前重发 LI 或 LA
  void rewriteRematerialized(u32 node);
  // 尝试用跨类 callee-saved 寄存器保存纯单定义的 32-bit 值
  bool tryCrossClassSlot(u32 node);
  // 检查唯一定义严格支配至少一个同 id use, 并排除自 use
  bool definitionDominatesUses(u32 node, Inst *definition) const;
  // 从另一寄存器类选择可借用的 callee-saved 颜色
  PReg pickCrossClassRegister(RegClass registerClass) const;
  /// 批量栈 spill, 以一次全函数 use pass 和 def pass 替代逐 root 重复扫描
  void applyStackSpill(const std::vector<i32> &vregToSlot,
                       const std::vector<u8> &newDepth);
  // 把最终 VReg assignment 落为 PReg
  void rewriteToPhysicalRegisters(const std::vector<PReg> &assignment);

  // === 元数据 ===
  // 按当前 VReg id 把真实定义上的 metadata 投影到 vregMetadata_
  void loadVRegMetadata();
  /// 为栈 spill 产生的等值定义继承 spillDepth, storeConst 和 scalarFacts
  void attachSpillMetadata(u32 oldVReg, Inst *newDefinition, u8 absoluteDepth);

  /// 返回 n 所属寄存器类的普通颜色数 K, 不含 small spill storage
  u32 colorCount(u32 node) const noexcept {
    return nodes_[node].registerClass == RC_FPR ? fprColorCount_
                                                : gprColorCount_;
  }
  bool isPrecolored(u32 node) const noexcept { return node >= virtualCount_; }

  // === 每轮重建状态 ===
  Function *function_ = nullptr;
  FunctionAnalysisManager *analyses_ = nullptr;
  VRegLiveness liveness_;
  InstructionNumbering numbering_;
  const DominatorTree *dominators_ = nullptr;
  const LoopInfo *loops_ = nullptr;

  // 当前轮 VReg 数量
  u32 virtualCount_ = 0;
  // 图节点数, 等于 virtualCount_ + NUM_PREGS
  u32 nodeCount_ = 0;
  // GPR 普通颜色数 K, 不含 storage
  u32 gprColorCount_ = 0;
  // FPR 普通颜色数 K, 不含 storage
  u32 fprColorCount_ = 0;
  // 已扣除跨类预留的普通颜色位集
  std::array<u64, 2> ordinaryColorMasks_{};
  // 已扣除跨类预留的 storage 颜色位集
  std::array<u64, 2> storageColorMasks_{};

  // 干涉图, Build 后 finalize, Coalesce 动态加边
  InterferenceGraph graph_;
  // 长度为 nodeCount_, 保存节点状态, 度数, 统计和策略
  std::vector<NodeInfo> nodes_;
  // 长度为 virtualCount_, 保存 VReg metadata 的本轮投影
  std::vector<VRegMetadata> vregMetadata_;
  // 长度为 nodeCount_, 保存每个节点关联的 move 索引
  std::vector<std::vector<u32>> moveLists_;
  // 长度为 nodeCount_ 的 Coalesce alias 链, 未合并节点指向自身
  std::vector<u32> aliases_;
  // 长度为 nodeCount_, 预着色节点预置为自身 PReg
  std::vector<PReg> colors_;
  // 当前轮所有 move 记录
  std::vector<MoveRecord> moves_;

  // 懒惰节点队列, pop 时按 NodeState 过滤
  std::vector<u32> simplifyQueue_;
  std::vector<u32> freezeQueue_;
  std::vector<u32> spillQueue_;
  // 简化选择栈, AssignColors 按后进先出顺序弹出
  std::vector<u32> selectStack_;
  // 已合并节点, 最终颜色继承 alias root
  std::vector<u32> coalescedNodes_;
  // 未着色节点, 由 RewriteProgram 消费
  std::vector<u32> spilledNodes_;
  // move 优先堆, 允许过期条目, pop 时按 MoveState 过滤
  std::vector<u32> moveHeap_;

  // Briggs epoch 去重数组
  std::vector<u32> marks_;
  // 当前 epoch, 每次 conservative 判定递增一次
  u32 markEpoch_ = 0;

  // 当前轮 AssignColors 的粗略颜色复用位置, 每轮着色前清零
  std::array<u32, NUM_PREGS> lastColorUse_{};

  // === 函数内跨轮持久状态, 在 run() 开头清零 ===
  // 跨类槽已经借用的颜色, 后续 rewrite 轮次继续保留
  u64 reservedColorMask_ = 0;
};

/// 为当前 VReg 编号空间重建局部集合和全局活跃性
/// scratch 使用分析对象持有的连续 vector, rewrite 轮次不向 Arena 累积位集
void VRegLiveness::compute(Function *function) {
  function_ = function;
  virtualCount_ = function->virtualRegisterCount;
  wordCount_ = bitWordCount(virtualCount_);
  stride_ = std::max(u32{1}, wordCount_);
  order_.clear();
  blockIndex_.clear();

  order_ = completeBlockOrder(function);
  blockIndex_.reserve(order_.size());
  for (usize index = 0; index < order_.size(); ++index) {
    const auto insertion = blockIndex_.emplace(order_[index], index);
    if (!insertion.second)
      fatal(function_, SourceLocation{}, "IRC活跃分析: 遇到重复基本块.");
  }

  // 每个块通过固定 stride 获得四个独立切片, assign 同时清除上轮不动点
  const usize totalWords = order_.size() * stride_;
  definitions_.assign(totalWords, 0);
  uses_.assign(totalWords, 0);
  liveIn_.assign(totalWords, 0);
  liveOut_.assign(totalWords, 0);
  for (BasicBlock *block : order_)
    computeLocalSets(block);
  solveDataflow();
}

u64 *VRegLiveness::slice(std::vector<u64> &storage, const BasicBlock *block) {
  const auto found = blockIndex_.find(block);
  if (found == blockIndex_.end())
    fatal(function_, SourceLocation{}, "IRC活跃分析: 查询了未知基本块.");
  return storage.data() + found->second * stride_;
}

const u64 *VRegLiveness::slice(const std::vector<u64> &storage,
                               const BasicBlock *block) const {
  const auto found = blockIndex_.find(block);
  if (found == blockIndex_.end())
    fatal(function_, SourceLocation{}, "IRC活跃分析: 查询了未知基本块.");
  return storage.data() + found->second * stride_;
}

/// 计算块内 definition 和向上暴露 use 集合
void VRegLiveness::computeLocalSets(BasicBlock *block) {
  u64 *definitions = slice(definitions_, block);
  u64 *uses = slice(uses_, block);

  auto processInstruction = [&](Inst *inst) {
    // 正序扫描维持已见 definition, 只有首次局部定义前的读取才从前驱流入
    // 预着色操作数不属于 VReg universe, call clobber 也不伪装成 definition
    for (u32 argument = 0; argument < inst->getOperandCount(); ++argument) {
      Inst *value = inst->getArg(argument);
      if (!value || value->isPrecoloredDef())
        continue;
      if (value->id >= virtualCount_)
        fatal(function_, diagnosticLocation(inst),
              "IRC活跃分析: 遇到越界VReg: %u.",
              static_cast<unsigned>(value->id));
      if (!testBit(definitions, value->id))
        setBit(uses, value->id);
    }

    if (isVoid(inst->getType()) || inst->getOp() == MOP_NOP ||
        inst->isPrecoloredDef())
      return;
    if (inst->id >= virtualCount_)
      fatal(function_, diagnosticLocation(inst),
            "IRC活跃分析: 遇到越界定义: %u.", static_cast<unsigned>(inst->id));
    setBit(definitions, inst->id);
  };

  forEachOp(block, processInstruction);
}

/// 在有限 VReg 位集格上求解后向 may-liveness 的最小不动点
void VRegLiveness::solveDataflow() {
  // 初始 in 和 out 均为空集, 后继并集和 transfer 函数对包含关系单调
  // universe 只有 virtualCount 个 bit, 因而迭代必然终止并得到最小不动点
  std::vector<u64> nextOut(stride_, 0);
  std::vector<u64> nextIn(stride_, 0);
  bool changed = true;
  while (changed) {
    changed = false;
    // 方程为 out[B] = union(in[S]), S 属于 succ(B)
    //        in[B] = use[B] union (out[B] - definition[B])
    // 无后继块的 nextOut 保持空集, forEachSuccessor 会合并所有 CFG 后继
    for (auto block = order_.rbegin(); block != order_.rend(); ++block) {
      std::fill(nextOut.begin(), nextOut.end(), 0);
      forEachSuccessor(*block, [&](BasicBlock *successor) {
        unionBits(nextOut.data(), slice(liveIn_, successor), wordCount_);
      });
      assignUnionDifference(nextIn.data(), slice(uses_, *block), nextOut.data(),
                            slice(definitions_, *block), wordCount_);

      // 每次访问块都从方程完整重算 in 和 out, 不依赖上轮残留的单调并集
      // 反向完整块顺序只影响循环收敛速度, 不改变有限格上的最终不动点
      u64 *currentOut = slice(liveOut_, *block);
      u64 *currentIn = slice(liveIn_, *block);
      if (!equalBits(currentOut, nextOut.data(), wordCount_)) {
        std::copy_n(nextOut.data(), wordCount_, currentOut);
        changed = true;
      }
      if (!equalBits(currentIn, nextIn.data(), wordCount_)) {
        std::copy_n(nextIn.data(), wordCount_, currentIn);
        changed = true;
      }
    }
  }
}

/// 识别可在任意使用点独立重建的 LI 或 LA
bool rematerializable(Inst *definition, RematInfo &result) {
  result = {};
  if (!definition)
    return false;

  switch (definition->getOp()) {
  case MOP_LI:
    result.kind = RematKind::Li;
    result.immediate = definition->getImm64();
    break;
  case MOP_LA:
    // 只克隆原 LA 的完整 SymbolRef, 不推测或补发后续成员偏移 ADDI
    result.symbol = definition->getSymbolRef();
    if (result.symbol.kind == SymbolRef::SymbolRefKind::None)
      return false;
    result.kind = RematKind::La;
    break;
  default:
    return false;
  }

  result.definition = definition;
  result.type = definition->getType();
  return true;
}

/// 按已验证的重物化摘要发射一条等值定义
Inst *emitRematerialized(IRBuilder &builder, const RematInfo &info) {
  switch (info.kind) {
  case RematKind::Li: {
    Inst *value = builder.emit(MOP_LI, info.type);
    value->setImm64(info.immediate);
    return value;
  }
  case RematKind::La: {
    Inst *value =
        builder.emit(MOP_LA, info.type == TY_VOID ? TY_PTR : info.type);
    value->setSymbolRef(info.symbol);
    return value;
  }
  case RematKind::None:
    return nullptr;
  }
  return nullptr;
}

/// Build 阶段追加一条无向边
/// 逆序扫描可能反复发现同一边, append 避免在热路径即时二分或哈希查重
/// PReg 端不展开邻接表, 重复边延迟到 finalize 统一排序去重
void InterferenceGraph::addBuildEdge(u32 left, u32 right) {
  if (left == right)
    return;
  if (left < virtualCount)
    adjacency[left].push_back(right);
  if (right < virtualCount)
    adjacency[right].push_back(left);
}

/// 排序并去重 Build 边, 唯一邻居数量成为普通节点的初始 degree
void InterferenceGraph::finalize(std::vector<NodeInfo> &nodes) {
  for (u32 node = 0; node < virtualCount; ++node) {
    std::vector<u32> &adjacent = adjacency[node];
    std::sort(adjacent.begin(), adjacent.end());
    adjacent.erase(std::unique(adjacent.begin(), adjacent.end()),
                   adjacent.end());
    nodes[node].degree = static_cast<u32>(adjacent.size());
  }
}

/// 查询两个节点是否干涉
/// 自节点和两个不同固定颜色均按受约束处理, 防止调用方尝试非法收缩
bool InterferenceGraph::hasEdge(u32 left, u32 right) const {
  if (left == right)
    return true;
  const bool leftPrecolored = left >= virtualCount;
  const bool rightPrecolored = right >= virtualCount;
  if (leftPrecolored && rightPrecolored)
    return true;
  if (leftPrecolored)
    return std::binary_search(adjacency[right].begin(), adjacency[right].end(),
                              left);
  if (rightPrecolored)
    return std::binary_search(adjacency[left].begin(), adjacency[left].end(),
                              right);

  // 普通节点两端都保存该边, 搜索较短邻接表减少 Coalesce 热路径比较
  const bool searchLeft = adjacency[left].size() <= adjacency[right].size();
  const std::vector<u32> &adjacent =
      searchLeft ? adjacency[left] : adjacency[right];
  return std::binary_search(adjacent.begin(), adjacent.end(),
                            searchLeft ? right : left);
}

/// 向一个普通节点端动态插入 Coalesce 迁移边
/// 邻接表继续有序去重, 只有真实新边才增加 owner 的有效 degree
void InterferenceGraph::insertSorted(u32 owner, u32 other,
                                     std::vector<NodeInfo> &nodes) {
  if (owner >= virtualCount)
    return;
  std::vector<u32> &adjacent = adjacency[owner];
  const auto position =
      std::lower_bound(adjacent.begin(), adjacent.end(), other);
  if (position != adjacent.end() && *position == other)
    return;
  adjacent.insert(position, other);
  ++nodes[owner].degree;
}

// 基础状态和工作队列

/// 沿 Coalesced alias 链查询当前代表节点
/// 当前实现直接沿单轮增长的链查询, 不维护并查集秩或路径压缩
u32 IRCAllocator::alias(u32 node) const {
  while (nodes_[node].state == NodeState::Coalesced)
    node = aliases_[node];
  return node;
}

/// 更新节点的唯一归属状态, 并把索引追加到对应懒惰队列
void IRCAllocator::enqueue(u32 node, NodeState state) {
  nodes_[node].state = state;
  switch (state) {
  case NodeState::Simplify:
    simplifyQueue_.push_back(node);
    break;
  case NodeState::Freeze:
    freezeQueue_.push_back(node);
    break;
  case NodeState::Spill:
    spillQueue_.push_back(node);
    break;
  default:
    break;
  }
}

/// 弹出仍属于目标状态的节点, 同时丢弃队列中的过期索引
u32 IRCAllocator::popNode(std::vector<u32> &queue, NodeState state) {
  while (!queue.empty()) {
    const u32 node = queue.back();
    queue.pop_back();
    if (nodes_[node].state == state)
      return node;
  }
  return kNoNode;
}

/// 比较两个 move 的合并优先级
/// 权重越大越优先, 同权时按 PhiParallelCopy, ArgCopy, Normal 排序,
/// 再按完整块顺序的指令编号和 move 编号稳定打破平局
/// 比较器在 left 更差时返回 true, 使 push_heap/pop_heap 的堆顶始终是当前最优
bool IRCAllocator::moveWorse(u32 left, u32 right) const {
  const MoveRecord &leftMove = moves_[left];
  const MoveRecord &rightMove = moves_[right];
  if (leftMove.weight != rightMove.weight)
    return leftMove.weight < rightMove.weight;
  if (leftMove.kind != rightMove.kind)
    return static_cast<u8>(leftMove.kind) < static_cast<u8>(rightMove.kind);
  if (leftMove.order != rightMove.order)
    return leftMove.order > rightMove.order;
  return left > right;
}

/// 向允许过期条目的 move 最大堆中加入一个 Worklist move
void IRCAllocator::pushMove(u32 move) {
  moveHeap_.push_back(move);
  std::push_heap(
      moveHeap_.begin(), moveHeap_.end(),
      [this](u32 left, u32 right) { return moveWorse(left, right); });
}

/// 弹出最高优先级的有效 Worklist move, 跳过状态已经变化的历史条目
u32 IRCAllocator::popWorklistMove() {
  const auto compare = [this](u32 left, u32 right) {
    return moveWorse(left, right);
  };
  while (!moveHeap_.empty()) {
    std::pop_heap(moveHeap_.begin(), moveHeap_.end(), compare);
    const u32 move = moveHeap_.back();
    moveHeap_.pop_back();
    if (moves_[move].state == MoveState::Worklist)
      return move;
  }
  return kNoNode;
}

/// 判断节点是否仍有关联的 Worklist 或 Active move
bool IRCAllocator::moveRelated(u32 node) const {
  for (u32 move : moveLists_[node]) {
    const MoveState state = moves_[move].state;
    if (state == MoveState::Worklist || state == MoveState::Active)
      return true;
  }
  return false;
}

// Build 逆序扫描, COPY affinity, IPRA clobber 和 spill 统计

/// 记录一次 use 或 def 出现, 累计块频率权重并更新首末编号和最大 hotness
void IRCAllocator::noteOccurrence(u32 node, double frequency, u32 instruction) {
  if (node >= virtualCount_)
    return;
  NodeInfo &info = nodes_[node];
  info.useDefWeight += frequency;
  info.hotness = std::max(info.hotness, frequency);
  if (instruction == kNoInstruction)
    return;
  info.firstInstruction = info.firstInstruction == kNoInstruction
                              ? instruction
                              : std::min(info.firstInstruction, instruction);
  info.lastInstruction = info.lastInstruction == kNoInstruction
                             ? instruction
                             : std::max(info.lastInstruction, instruction);
}

/// 从本轮空状态构建干涉图, move 表, 节点统计和 spill 评分
void IRCAllocator::build() {
  // 循环深度和支配关系是本轮启发式与跨类 rewrite 的只读 CFG 事实
  // Spill rewrite 不改变 CFG, 因而分析管理器可以跨轮复用这些结果
  const LoopInfoAnalysis &loopAnalysis =
      analyses_->getResult<LoopInfoAnalysis>(function_);
  loops_ = &loopAnalysis.info;
  dominators_ = &analyses_->getResult<DomAnalysis>(function_).tree;

  virtualCount_ = function_->virtualRegisterCount;
  if (virtualCount_ > std::numeric_limits<u32>::max() - NUM_PREGS)
    fatal(function_, SourceLocation{}, "IRC图节点编号空间溢出.");
  nodeCount_ = virtualCount_ + NUM_PREGS;

  // 跨类槽借出的颜色在后续轮次从正常颜色和 small storage 掩码中排除
  // K 只统计当前普通颜色, small storage 不参与 Simplify 或 Coalesce 的证明
  ordinaryColorMasks_[RC_GPR] =
      baseOrdinaryColorMask(RC_GPR) & ~reservedColorMask_;
  ordinaryColorMasks_[RC_FPR] =
      baseOrdinaryColorMask(RC_FPR) & ~reservedColorMask_;
  storageColorMasks_[RC_GPR] =
      baseStorageColorMask(RC_GPR) & ~reservedColorMask_;
  storageColorMasks_[RC_FPR] =
      baseStorageColorMask(RC_FPR) & ~reservedColorMask_;
  gprColorCount_ =
      static_cast<u32>(__builtin_popcountll(ordinaryColorMasks_[RC_GPR]));
  fprColorCount_ =
      static_cast<u32>(__builtin_popcountll(ordinaryColorMasks_[RC_FPR]));

  // 图, 节点状态, move 状态和所有懒惰队列只在当前 rewrite 轮次有效
  nodes_.assign(nodeCount_, {});
  moveLists_.assign(nodeCount_, {});
  aliases_.resize(nodeCount_);
  colors_.assign(nodeCount_, NUM_PREGS);
  moves_.clear();
  moveHeap_.clear();
  simplifyQueue_.clear();
  freezeQueue_.clear();
  spillQueue_.clear();
  selectStack_.clear();
  coalescedNodes_.clear();
  spilledNodes_.clear();
  marks_.assign(nodeCount_, 0);
  markEpoch_ = 0;
  graph_.virtualCount = virtualCount_;
  graph_.adjacency.assign(virtualCount_ + NUM_PREGS, {});

  for (u32 node = 0; node < nodeCount_; ++node)
    aliases_[node] = node;

  // 预着色节点颜色固定, degree 使用高值模拟无穷, 永不进入普通工作队列
  // 它们不展开邻接表, VReg-PReg 约束只存放在普通节点一侧
  for (u32 reg = 0; reg < NUM_PREGS; ++reg) {
    const u32 node = virtualCount_ + reg;
    nodes_[node].registerClass = pregClass(static_cast<PReg>(reg));
    nodes_[node].degree = std::numeric_limits<u32>::max() / 2;
    nodes_[node].state = NodeState::Colored;
    colors_[node] = static_cast<PReg>(reg);
  }

  // 普通节点的类别来自压实后的类别表, 稳定 metadata 来自本轮 VReg 投影
  for (u32 node = 0; node < virtualCount_; ++node) {
    nodes_[node].registerClass =
        function_->virtualRegisterClasses[node] ? RC_FPR : RC_GPR;
    const VRegMetadata &metadata = vregMetadata_[node];
    nodes_[node].spillDepth = metadata.spillDepth;
    nodes_[node].storeConstant = metadata.storeConst;
    nodes_[node].forcedColor = metadata.forcedColor;
  }

  // 每块从数据流求得的 liveOut 开始逆序扫描;
  // 处理一条指令前, live 表示该指令之后仍活跃的 VReg;
  // 处理顺序固定为 copy affinity, def, call clobber, use, 不能随意交换
  const u32 liveWords = liveness_.wordCount();
  std::vector<u64> live(std::max(u32{1}, liveWords), 0);

  for (BasicBlock *block = function_->region->first; block;
       block = block->next()) {
    std::fill(live.begin(), live.end(), 0);
    std::copy_n(liveness_.liveOut(block), liveWords, live.data());
    // 10^loopDepth 是当前唯一的块频率抽象, 将来可在这里接入 PGO 或 BFI
    const double frequency =
        std::pow(10.0, static_cast<double>(loops_->getLoopDepth(block)));

    auto processInstruction = [&](Inst *inst) {
      const u32 instruction = numbering_.numberOf(inst);
      const bool call = isMachineCall(inst->getOp());

      // COPY/FCOPY 表示 destination <- source 的同值 affinity;
      // 在 destination 建干涉边之前移除虚拟 source, 避免人为制造二者的伪干涉;
      // 预着色 source 不在 VReg live 集中, 但仍作为 move 对端参与完整合并判定
      if (isMachineCopy(inst->getOp()) && !isVoid(inst->getType()) &&
          !inst->isPrecoloredDef()) {
        Inst *sourceValue = inst->getArg(0);
        if (sourceValue) {
          if (inst->id >= virtualCount_)
            fatal(function_, diagnosticLocation(inst),
                  "IRC遇到越界COPY目标: %u.", static_cast<unsigned>(inst->id));
          const u32 destination = inst->id;
          const u32 source = sourceValue->isPrecoloredDef()
                                 ? virtualCount_ + sourceValue->id
                                 : sourceValue->id;
          if ((!sourceValue->isPrecoloredDef() && source >= virtualCount_) ||
              source >= nodeCount_)
            fatal(function_, diagnosticLocation(inst), "IRC遇到越界COPY源: %u.",
                  static_cast<unsigned>(source));
          if (nodes_[destination].registerClass != nodes_[source].registerClass)
            fatal(function_, diagnosticLocation(inst), "COPY跨越了寄存器类别.");

          // PhiParallelCopy 对应边上的 Phi 并行赋值, ArgCopy 对应 ABI 绑定,
          // Normal 是普通可消除拷贝; 1000/100/1 只决定尝试顺序和 soft hint
          // 权重; 所有实际图收缩仍必须通过 George 或 Briggs 与强制颜色检查
          const MoveInfo moveInfo = queryMoveInfo(function_, inst);
          double baseWeight = 1.0;
          if (moveInfo.kind == MoveKind::PhiParallelCopy)
            baseWeight = 1000.0;
          else if (moveInfo.kind == MoveKind::ArgCopy)
            baseWeight = 100.0;

          const u32 move = static_cast<u32>(moves_.size());
          moves_.push_back({destination, source, moveInfo.kind,
                            baseWeight * frequency, instruction,
                            MoveState::Worklist});
          moveLists_[destination].push_back(move);
          moveLists_[source].push_back(move);
          pushMove(move);

          // ArgCopy 的 preferredReg 是合法颜色内的软偏好, 不是预着色约束
          if (moveInfo.kind == MoveKind::ArgCopy &&
              moveInfo.preferredReg < NUM_PREGS &&
              isSupportedColor(moveInfo.preferredReg,
                               nodes_[destination].registerClass) &&
              nodes_[destination].abiPreference >= NUM_PREGS)
            nodes_[destination].abiPreference = moveInfo.preferredReg;

          // 虚拟 source 将在统一 use 阶段重新加入 live, 此处只抑制 copy 特例边
          if (!sourceValue->isPrecoloredDef())
            clearBit(live.data(), source);
        }
      }

      // 普通 def 与 live-after 中所有同类值干涉;
      // 建边后从 live 清除 def, 因为继续向前扫描时该定义的值尚未产生
      u32 definition = kNoNode;
      if (!isVoid(inst->getType()) && inst->getOp() != MOP_NOP &&
          !inst->isPrecoloredDef()) {
        if (inst->id >= virtualCount_)
          fatal(function_, diagnosticLocation(inst), "IRC遇到越界定义: %u.",
                static_cast<unsigned>(inst->id));
        definition = inst->id;
        const RegClass registerClass = nodes_[definition].registerClass;
        forEachSetBit(live.data(), virtualCount_, [&](u32 liveNode) {
          if (liveNode != definition &&
              nodes_[liveNode].registerClass == registerClass)
            graph_.addBuildEdge(definition, liveNode);
        });
        noteOccurrence(definition, frequency, instruction);
        NodeInfo &definitionInfo = nodes_[definition];
        ++definitionInfo.definitionCount;
        definitionInfo.singleDefinition =
            definitionInfo.definitionCount == 1 ? inst : nullptr;

        // 先记录单条 LI/LA 候选, 扫描结束后会统一撤销多定义 web 的资格
        RematInfo remat;
        if (rematerializable(inst, remat)) {
          nodes_[definition].rematerializable = true;
          nodes_[definition].remat = remat;
        }
        clearBit(live.data(), definition);
      }

      // 若当前指令是 call, def 已清除且 operands 尚未加入,
      // 此时 live 只含跨该 call 活跃的值
      //
      // 仅由本条 call use 引入的实参尚未进入 live, 不会与参数落位寄存器伪干涉;
      // 同一实参值若在 call 后仍被使用, 它已属于 call 的 live-after 并接受约束
      //
      // ipraCallSiteClobberMask 优先使用完整 callee IPRA 摘要, 摘要不完整时回退
      // ABI 默认破坏集; helper 还加入调用点参数落位会写入的寄存器;
      // regMask 与 CALL_CLOBBER_MASK 不同时作为额外破坏合并, 相等时则视为未精化
      // ABI 上界而忽略, 避免把完整 IPRA 摘要重新扩大为默认破坏集
      if (call) {
        const u64 clobbered = ipraCallSiteClobberMask(inst);
        forEachSetBit(live.data(), virtualCount_, [&](u32 liveNode) {
          NodeInfo &info = nodes_[liveNode];
          // call 的隐式 PReg 写入不伪装成活跃性 definition, 而是在这里转换为
          // live-through VReg 与对应 PReg 的干涉边;
          // 使用基础颜色全集而非扣除预留后的本轮掩码, 使 ordinary, small
          // storage 和已借出的跨类 forced color 都接受显式 call clobber 约束
          u64 colors = clobbered & (baseOrdinaryColorMask(info.registerClass) |
                                    baseStorageColorMask(info.registerClass));
          while (colors != 0) {
            const PReg reg = static_cast<PReg>(__builtin_ctzll(colors));
            colors &= colors - 1;
            graph_.addBuildEdge(liveNode,
                                virtualCount_ + static_cast<u32>(reg));
          }
        });
      }

      // 最后加入所有 VReg use, 得到当前指令之前的 live 集合;
      // MOP_CALL operands 只包含寄存器传参, 栈参数已由 Lower 写入 outgoing
      // area; 参数自然染到 aN/faN 时, PostRA CallShuffle 可以省掉对应搬运;
      // 若存在干涉, 合法颜色约束覆盖该软偏好, CallShuffle 仍负责最终满足 ABI
      u32 gprArgument = 0;
      u32 fprArgument = 0;
      for (u32 argument = 0; argument < inst->getOperandCount(); ++argument) {
        Inst *value = inst->getArg(argument);
        if (!value)
          continue;

        PReg abiRegister = NUM_PREGS;
        if (call) {
          if (value->getType() == TY_F32) {
            if (fprArgument < FPR_ARG_N)
              abiRegister = FPR_ARG[fprArgument];
            ++fprArgument;
          } else {
            if (gprArgument < GPR_ARG_N)
              abiRegister = GPR_ARG[gprArgument];
            ++gprArgument;
          }
        }

        // 预着色实参虽不进入 VReg live, 仍必须推进对应类别的 ABI 参数下标;
        // 否则后续普通 VReg 会错误偏好前一个参数位置
        if (value->isPrecoloredDef())
          continue;
        if (value->id >= virtualCount_)
          fatal(function_, diagnosticLocation(inst), "IRC遇到越界使用: %u.",
                static_cast<unsigned>(value->id));
        setBit(live.data(), value->id);
        noteOccurrence(value->id, frequency, instruction);
        // 当前 Build 遍历首次遇到的有效位置获胜, 多个冲突位置不累计投票
        if (abiRegister < NUM_PREGS &&
            nodes_[value->id].abiPreference >= NUM_PREGS)
          nodes_[value->id].abiPreference = abiRegister;
      }

      // 返回值偏好与调用实参相同, 只在 A0 或 FA0 仍是合法颜色时生效
      if (inst->getOp() == MOP_RET && inst->getOperandCount() > 0) {
        Inst *value = inst->getArg(0);
        if (value && !value->isPrecoloredDef() && value->id < virtualCount_ &&
            nodes_[value->id].abiPreference >= NUM_PREGS)
          nodes_[value->id].abiPreference =
              value->getType() == TY_F32 ? FA0 : A0;
      }

      // 当前 Lower 以 call 后 COPY/FCOPY 物化返回值, 这里保留非 void MOP_CALL
      // 直接定义返回值的通用路径
      if (call && definition != kNoNode &&
          nodes_[definition].abiPreference >= NUM_PREGS)
        nodes_[definition].abiPreference =
            nodes_[definition].registerClass == RC_FPR ? FA0 : A0;
    };

    for (Inst *inst = block->lastInst(); inst; inst = inst->previous())
      processInstruction(inst);
    for (Inst *inst = block->lastPhi(); inst; inst = inst->previous())
      processInstruction(inst);
  }

  // 多定义 web 没有可在每个 use 前等价替换的唯一定义, 禁用 remat 快路径
  for (u32 node = 0; node < virtualCount_; ++node) {
    if (nodes_[node].definitionCount != 1) {
      nodes_[node].rematerializable = false;
      nodes_[node].singleDefinition = nullptr;
    }
  }

  // Build 允许重复 append, 在全部块扫描完毕后一次排序去重并初始化 degree
  graph_.finalize(nodes_);
  for (u32 node = 0; node < virtualCount_; ++node)
    nodes_[node].spillCost = spillCost(nodes_[node]);
}

// MakeWorklist 和 Simplify

/// MakeWorklist 按 degree 与 move-related 状态把 Initial 节点分流到三个队列;
/// degree >= K -> Spill; move-related -> Freeze; 其余 -> Simplify
void IRCAllocator::makeWorklist() {
  for (u32 node = 0; node < virtualCount_; ++node) {
    if (nodes_[node].degree >= colorCount(node))
      enqueue(node, NodeState::Spill);
    else if (moveRelated(node))
      enqueue(node, NodeState::Freeze);
    else
      enqueue(node, NodeState::Simplify);
  }
}

/// 一个邻居离开当前收缩图后递减普通节点的有效 degree;
/// 邻接向量保留历史边, degree 只统计尚未 OnStack 或 Coalesced 的有效邻居;
/// 节点从 K 降到 K - 1 时重新成为低度数节点,
/// 此前因压力过高而 Active 的 move 可能重新满足合并条件;
/// 此时唤醒自身和当前邻居的 move, 但只按 move-related 状态重新分流该节点
void IRCAllocator::decrementDegree(u32 node) {
  if (isPrecolored(node))
    return;
  const u32 previous = nodes_[node].degree;
  assert(previous > 0);
  nodes_[node].degree = previous - 1;
  if (previous != colorCount(node))
    return;

  enableMoves(node);
  forEachAdjacent(node, [&](u32 adjacent) { enableMoves(adjacent); });
  if (nodes_[node].state == NodeState::Spill)
    enqueue(node, moveRelated(node) ? NodeState::Freeze : NodeState::Simplify);
}

/// 把 node 关联的 Active move 唤回 Worklist 并重新入堆;
/// 度数变化可能解除原先约束
void IRCAllocator::enableMoves(u32 node) {
  forEachNodeMove(node, [&](u32 move) {
    if (moves_[move].state != MoveState::Active)
      return;
    moves_[move].state = MoveState::Worklist;
    pushMove(move);
  });
}

/// 从 Simplify 队列移除一个节点并压入 selectStack;
/// 正常候选是低度数且非 move-related, SelectSpill 也会把高度数受害者送入此处;
/// 节点离开当前图后递减邻居有效度数, 可能级联产生更多低度数节点
bool IRCAllocator::trySimplify() {
  const u32 node = popNode(simplifyQueue_, NodeState::Simplify);
  if (node == kNoNode)
    return false;
  nodes_[node].state = NodeState::OnStack;
  selectStack_.push_back(node);
  forEachAdjacent(node, [&](u32 adjacent) { decrementDegree(adjacent); });
  return true;
}

// Coalesce 实现 George 和 Briggs 安全判定

/// 低度数且非 move-related 的普通节点转入 Simplify 队列;
/// Coalesce 处理 move 两端或收缩 root 后调用
void IRCAllocator::addWorklist(u32 node) {
  if (!isPrecolored(node) && !moveRelated(node) &&
      nodes_[node].degree < colorCount(node))
    enqueue(node, NodeState::Simplify);
}

/// 检查普通节点合并的 Briggs 保守充分条件;
/// 合并邻域中 degree >= K 的不同节点少于 K 时才允许收缩;
/// 预着色邻居代表不可消除的固定颜色约束, 会作为高度数节点计数; call 边较多时,
/// 该判定可能拒绝实际仍可着色的合并, 这是保守性代价而非正确性缺陷;
/// 该条件只证明收缩保守安全, 不保证当前图本轮无需 spill;
/// epoch 数组只在本次判定内去重, 避免热路径临时哈希分配
bool IRCAllocator::briggsConservative(u32 left, u32 right) {
  // epoch 回绕时统一清零, 避免旧标记与新判定混淆
  if (markEpoch_ == std::numeric_limits<u32>::max()) {
    std::fill(marks_.begin(), marks_.end(), 0);
    markEpoch_ = 1;
  } else {
    ++markEpoch_;
  }

  u32 highDegree = 0;
  const auto count = [&](u32 adjacent) {
    if (marks_[adjacent] == markEpoch_)
      return;
    marks_[adjacent] = markEpoch_;
    if (nodes_[adjacent].degree >= colorCount(adjacent))
      ++highDegree;
  };
  forEachAdjacent(left, count);
  forEachAdjacent(right, count);
  return highDegree < colorCount(left);
}

/// 检查两个 move 对端的寄存器类和 forcedColor 是否允许收缩;
/// 强制颜色属于正确性约束, 不能像 ABI preference 一样被覆盖;
/// 两个普通节点只有在约束相同或至多一端有约束时才能合并;
/// 普通节点并入预着色节点时, 物理颜色还必须属于 IRC 支持的普通或 storage 颜色;
/// 普通节点直接并入动态保留的预着色槽时, 它本身必须强制到该颜色
bool IRCAllocator::colorConstraintsCompatible(u32 left, u32 right) const {
  if (nodes_[left].registerClass != nodes_[right].registerClass)
    return false;

  const PReg leftColor =
      isPrecolored(left) ? colors_[left] : nodes_[left].forcedColor;
  const PReg rightColor =
      isPrecolored(right) ? colors_[right] : nodes_[right].forcedColor;
  if (leftColor < NUM_PREGS && rightColor < NUM_PREGS &&
      leftColor != rightColor)
    return false;

  const auto precoloredCompatible = [&](u32 precolored, u32 ordinary) {
    if (!isPrecolored(precolored) || isPrecolored(ordinary))
      return true;
    const PReg color = colors_[precolored];
    if (!isSupportedColor(color, nodes_[ordinary].registerClass))
      return false;
    if ((reservedColorMask_ & registerBit(color)) != 0 &&
        nodes_[ordinary].forcedColor != color)
      return false;
    return true;
  };
  return precoloredCompatible(left, right) && precoloredCompatible(right, left);
}

/// 取一条 Worklist move, 按约束和 George 或 Briggs 条件尝试收缩;
/// 预着色端必须作为 root, 两个普通节点则固定以 COPY destination 作为 root
bool IRCAllocator::tryCoalesce() {
  const u32 move = popWorklistMove();
  if (move == kNoNode)
    return false;

  const u32 destination = alias(moves_[move].destination);
  const u32 source = alias(moves_[move].source);
  u32 root = destination;
  u32 merged = source;
  if (isPrecolored(source)) {
    root = source;
    merged = destination;
  }

  // 两端经过既有 alias 已经相同, move 自然成为同色拷贝
  if (root == merged) {
    moves_[move].state = MoveState::Coalesced;
    addWorklist(root);
    return true;
  }

  // 两个不同预着色节点, 已干涉节点或硬颜色不兼容节点都不能图级合并;
  // move 记录仍保留在 moveLists_, AssignColors 可以继续把它作为 soft hint
  if (isPrecolored(merged) || graph_.hasEdge(root, merged) ||
      !colorConstraintsCompatible(root, merged)) {
    moves_[move].state = MoveState::Constrained;
    addWorklist(root);
    addWorklist(merged);
    return true;
  }

  // OutOfSSA 多定义 web 的图级合并不改变路径选择语义, 但可能把循环携带值和
  // 边临时值收缩成更长的活跃 web, 显著增加寄存器压力;
  // 这里保留着色 soft hint, 只禁止扩大 web 的图收缩
  if ((!isPrecolored(root) && nodes_[root].definitionCount > 1) ||
      (!isPrecolored(merged) && nodes_[merged].definitionCount > 1)) {
    moves_[move].state = MoveState::Constrained;
    addWorklist(root);
    addWorklist(merged);
    return true;
  }

  // 普通节点 v 并入预着色节点 u 时使用 George 保守充分条件;
  // v 的每个有效邻居 t 都必须满足
  //   OK(t, u) <=> degree(t) < K || isPrecolored(t) || hasEdge(t, u)
  //
  // 低度数 t 的 t-v 边被 t-u 替代后有效 degree 不增加, 因而仍可保守简化;
  // 预着色 t 不参与普通节点简化; 已有 t-u 边则表示替代不会增加颜色约束;
  // 代码使用否定形式, 存在高度数非预着色且未与 u 干涉的 t 即暂缓合并
  bool safe = true;
  if (isPrecolored(root)) {
    forEachAdjacent(merged, [&](u32 adjacent) {
      if (nodes_[adjacent].degree >= colorCount(adjacent) &&
          !isPrecolored(adjacent) && !graph_.hasEdge(adjacent, root))
        safe = false;
    });
  } else {
    safe = briggsConservative(root, merged);
  }
  if (!safe) {
    // Active move 等后续 degree 下降或 alias 收缩经 enableMoves 重新唤醒
    moves_[move].state = MoveState::Active;
    return true;
  }

  moves_[move].state = MoveState::Coalesced;
  combine(root, merged);
  addWorklist(root);
  return true;
}

/// 把 merged 收缩到 root, 迁移 move 和有效邻边;
/// 普通 root 还合并 spill 统计与颜色偏好, 预着色 root 保持固定节点信息
void IRCAllocator::combine(u32 root, u32 merged) {
  nodes_[merged].state = NodeState::Coalesced;
  coalescedNodes_.push_back(merged);
  aliases_[merged] = root;

  // 只有普通 root 可能参与后续 spill 和启发式选择, 需要合并节点统计
  if (!isPrecolored(root)) {
    NodeInfo &destination = nodes_[root];
    const NodeInfo &source = nodes_[merged];
    if (destination.forcedColor >= NUM_PREGS)
      destination.forcedColor = source.forcedColor;
    if (destination.abiPreference >= NUM_PREGS)
      destination.abiPreference = source.abiPreference;
    destination.useDefWeight += source.useDefWeight;
    destination.hotness = std::max(destination.hotness, source.hotness);
    destination.spillDepth =
        std::max(destination.spillDepth, source.spillDepth);
    destination.storeConstant |= source.storeConstant;

    if (source.firstInstruction != kNoInstruction)
      destination.firstInstruction =
          destination.firstInstruction == kNoInstruction
              ? source.firstInstruction
              : std::min(destination.firstInstruction, source.firstInstruction);
    if (source.lastInstruction != kNoInstruction)
      destination.lastInstruction =
          destination.lastInstruction == kNoInstruction
              ? source.lastInstruction
              : std::max(destination.lastInstruction, source.lastInstruction);

    const u32 destinationDefinitions = destination.definitionCount;
    const u32 sourceDefinitions = source.definitionCount;
    if (sourceDefinitions >
        std::numeric_limits<u32>::max() - destinationDefinitions)
      fatal(function_, SourceLocation{}, "IRC定义计数溢出.");
    destination.definitionCount = destinationDefinitions + sourceDefinitions;
    if (destination.definitionCount == 1) {
      if (destinationDefinitions == 0) {
        destination.singleDefinition = source.singleDefinition;
        destination.rematerializable = source.rematerializable;
        destination.remat = source.remat;
      }
    } else {
      destination.singleDefinition = nullptr;
      destination.rematerializable = false;
    }
  }

  // moveLists_ 保留所有状态的 move, 既驱动后续 Coalesce, 也提供着色 soft hint
  std::vector<u32> &rootMoves = moveLists_[root];
  rootMoves.insert(rootMoves.end(), moveLists_[merged].begin(),
                   moveLists_[merged].end());
  std::sort(rootMoves.begin(), rootMoves.end());
  rootMoves.erase(std::unique(rootMoves.begin(), rootMoves.end()),
                  rootMoves.end());
  enableMoves(merged);

  // 对 merged 的每个有效邻居 adjacent, 逻辑上删除 adjacent-merged 并改为
  // adjacent-root; 邻接向量本身保留旧边, Coalesced 状态会过滤 merged
  //
  // 对普通 adjacent, 若 adjacent-root 原本不存在, 插边增加的 degree 与随后删除
  // adjacent-merged 的 decrementDegree 抵消, adjacent 净值不变; 若替代边已存在,
  // 插边不增度而 decrement 仍执行, adjacent 净减一;
  // 预着色 adjacent 的 degree 从不维护; 预着色 root 不展开邻接表, 但普通
  // adjacent 端仍保存 VReg-PReg 替代边
  forEachAdjacent(merged, [&](u32 adjacent) {
    graph_.insertSorted(adjacent, root, nodes_);
    graph_.insertSorted(root, adjacent, nodes_);
    decrementDegree(adjacent);
  });

  // 普通 root 的 degree 只会保持或增加, 升到 K 时必须从 Freeze 转入 Spill;
  // 调用方随后以 addWorklist 处理仍然低度数且不再 move-related 的 root
  if (!isPrecolored(root)) {
    nodes_[root].spillCost = spillCost(nodes_[root]);
    if (nodes_[root].degree >= colorCount(root) &&
        nodes_[root].state == NodeState::Freeze)
      enqueue(root, NodeState::Spill);
  }
}

// Freeze 和 SelectSpill

/// 冻结 node 的关联 move, Worklist 和 Active 一并冻结为 Frozen;
/// 冻结后仍保留在 moveLists_ 中, AssignColors 的 soft hint 仍会使用;
/// 对方若因此变为非 move-related 低度数, 转入 Simplify
void IRCAllocator::freezeMoves(u32 node) {
  forEachNodeMove(node, [&](u32 move) {
    const u32 destination = alias(moves_[move].destination);
    const u32 source = alias(moves_[move].source);
    const u32 peer = destination == alias(node) ? source : destination;
    moves_[move].state = MoveState::Frozen;
    if (!isPrecolored(peer) && !moveRelated(peer) &&
        nodes_[peer].degree < colorCount(peer))
      enqueue(peer, NodeState::Simplify);
  });
}

/// Freeze 弹出一个低度数 move-related 节点并冻结其关联 move;
/// 该节点必定进入 Simplify, move 对端也可能成为 Simplify 候选;
/// 这是 Coalesce 工作耗尽后的标准退路
bool IRCAllocator::tryFreeze() {
  const u32 node = popNode(freezeQueue_, NodeState::Freeze);
  if (node == kNoNode)
    return false;
  enqueue(node, NodeState::Simplify);
  freezeMoves(node);
  return true;
}

/// 从 Spill 队列选择最低评分节点, 放弃其 move 后送入 Simplify;
/// 下一次主循环才会把它压栈, AssignColors 仍可能在邻居着色后为它找到颜色
bool IRCAllocator::trySelectSpill() {
  // 先选 spill cost 低者; 精确平局依次偏好可重物化, 较深 spillDepth, 较大
  // footprint, 较冷节点和较小编号; 扫描同时压实懒惰队列中的过期条目
  const auto key = [&](u32 node) {
    const NodeInfo &info = nodes_[node];
    return std::make_tuple(
        info.spillCost, -static_cast<i32>(info.rematerializable),
        -static_cast<i32>(info.spillDepth), -static_cast<i64>(info.footprint()),
        info.hotness, node);
  };

  // infinity 仍是可比较评分, 若所有候选均为 infinity 仍会按其余键选择一个;
  // 因而短生命周期保护是强启发式, 不是独立的终止性证明
  u32 best = kNoNode;
  usize write = 0;
  for (u32 node : spillQueue_) {
    if (nodes_[node].state != NodeState::Spill)
      continue;
    spillQueue_[write++] = node;
    if (best == kNoNode || key(node) < key(best))
      best = node;
  }
  spillQueue_.resize(write);
  if (best == kNoNode)
    return false;

  enqueue(best, NodeState::Simplify);
  freezeMoves(best);
  return true;
}

// Spill cost

/// 计算 SelectSpill 使用的综合评分, 越小越适合作为候选受害者
double IRCAllocator::spillCost(const NodeInfo &info) const {
  const u64 tinyFootprint = static_cast<u64>(kInstructionScale) * 4;
  const u64 footprint = info.footprint();
  // Per-use reload, unpark 结果和只向紧邻 park 提供值的原定义通常跨度极短;
  // infinity 评分优先选择其它节点, 降低 spill 产物被立即再次 spill 的概率;
  // 候选全部为 infinity 时 SelectSpill 仍会继续, 持续失败则由硬轮数边界终止编译
  if (footprint <= tinyFootprint)
    return std::numeric_limits<double>::infinity();

  // 热位置访问越多越应保留, 高度数或长跨度节点被移走时通常释放更多图压力
  const double degree = static_cast<double>(std::max(u32{1}, info.degree));
  double cost = info.useDefWeight / (degree * static_cast<double>(footprint));
  // LI 和 LA 可在 use 点重建, 不需要 frame slot, store 或 reload
  if (info.rematerializable)
    cost *= 0.01;
  // 主要喂给常量 store 的值被视为较廉价受害者
  if (info.storeConstant)
    cost *= 0.20;
  // 第一代 spill 产物仍倾向被局部化, 更深代数则提高评分以抑制反复改写
  if (info.spillDepth == 1)
    cost *= 0.10;
  else if (info.spillDepth >= 2)
    cost *= 4.0;
  return cost;
}

// 颜色集合和选择启发式

/// 在已经扣除干涉颜色的 available 集合内按启发式选择普通颜色
PReg IRCAllocator::chooseColor(u32 node, u64 available) {
  if (available == 0)
    return NUM_PREGS;
  const NodeInfo &info = nodes_[node];

  // 第一层是 ABI preference, 它来自入口 ArgCopy, 调用实参和返回值位置,
  // 只在颜色仍合法时采用, 因而不会覆盖 call clobber 或普通干涉约束
  if (info.abiPreference < NUM_PREGS &&
      (available & registerBit(info.abiPreference)) != 0)
    return info.abiPreference;

  // 第二层是免 COPY soft hint; 即使 move 因 George/Briggs, 强制颜色冲突或
  // Freeze 未能图收缩, 两端仍可能自然染成同色; 所有关联 move 按权重累加已着色
  // peer 的颜色, 只在 available 内选择, 后续 PeepholePostRA 可删除同色 COPY
  std::array<double, NUM_PREGS> hints{};
  for (u32 move : moveLists_[node]) {
    const u32 destination = alias(moves_[move].destination);
    const u32 source = alias(moves_[move].source);
    u32 peer = kNoNode;
    if (destination == node)
      peer = source;
    else if (source == node)
      peer = destination;
    if (peer == kNoNode)
      continue;
    const PReg color = colors_[peer];
    if (color < NUM_PREGS && (available & registerBit(color)) != 0)
      hints[color] += moves_[move].weight;
  }

  PReg hinted = NUM_PREGS;
  double bestHint = 0.0;
  for (u32 reg = 0; reg < NUM_PREGS; ++reg)
    if ((available & registerBit(static_cast<PReg>(reg))) != 0 &&
        hints[reg] > bestHint) {
      bestHint = hints[reg];
      hinted = static_cast<PReg>(reg);
    }
  if (hinted < NUM_PREGS)
    return hinted;

  // 第三层在统一颜色表内比较函数级保存成本
  //
  // call 实际破坏的颜色已经由干涉边排除, 剩余 caller-saved 颜色无需保存;
  // callee-saved 则会扩大函数级序言和尾声, 因而只在前者不可用时选择
  const u32 current =
      info.firstInstruction == kNoInstruction ? 0 : info.firstInstruction;

  // caller-saved 成本项为 2^20, 严格高于其它颜色质量项;
  // 已使用 callee-saved 复用项为 2^11, 严格高于最大 2^10 的区间分离项,
  // 从而不相交区间优先复用已由序言保存的颜色, 不扩大 calleeSaveMask;
  // lastColorUse_[reg] 记录最近按着色栈顺序染成 reg 的节点末次指令编号;
  // 着色栈顺序并非程序执行顺序, 因而 distance 只是粗略区间分离 tie-break;
  // 它不构成具体微架构 WAW 或 RAW 收益保证, 完全同分时保持颜色表顺序
  const auto chooseFromOrder = [&](const auto &order) {
    PReg best = NUM_PREGS;
    i64 bestScore = std::numeric_limits<i64>::min();
    for (PReg reg : order) {
      if ((available & registerBit(reg)) == 0)
        continue;
      i64 score = !isCalleeSaved(reg) ? i64{1} << 20 : 0;
      if (isCalleeSaved(reg) && lastColorUse_[reg] != kNoInstruction)
        score += i64{1} << 11;
      i64 distance = i64{1} << 10;
      if (lastColorUse_[reg] != kNoInstruction) {
        distance = current >= lastColorUse_[reg]
                       ? static_cast<i64>(current - lastColorUse_[reg])
                       : 0;
        distance = std::min(distance, i64{1} << 10);
      }
      score += distance;
      if (score > bestScore) {
        bestScore = score;
        best = reg;
      }
    }
    return best;
  };

  if (info.registerClass == RC_GPR)
    return chooseFromOrder(kGPRColorOrder);
  return function_->isLeaf ? chooseFromOrder(kFPRColorOrderLeaf)
                           : chooseFromOrder(kFPRColorOrderNonLeaf);
}

/// 按 selectStack 的后进先出顺序回填颜色, 失败节点进入 spill rewrite
void IRCAllocator::assignColors() {
  lastColorUse_.fill(kNoInstruction);
  while (!selectStack_.empty()) {
    // Simplify 先移除外围低度数节点, LIFO 回填会先着色更接近图核心的节点;
    // 当前节点只需避开已经着色的邻居, 尚未回填的邻居会在自己的回合反向避让
    const u32 node = selectStack_.back();
    selectStack_.pop_back();
    const NodeInfo &info = nodes_[node];
    u64 forbidden = 0;
    // 原始邻接向量保留 Coalesced 边, alias 将成员统一解析到最终代表颜色;
    // 预着色 PReg 从 Build 起已有固定颜色, 与已回填 VReg 一起构成 forbidden
    for (u32 adjacent : graph_.adjacency[node]) {
      const PReg color = colors_[alias(adjacent)];
      if (color < NUM_PREGS)
        forbidden |= registerBit(color);
    }

    PReg chosen = NUM_PREGS;
    if (info.forcedColor < NUM_PREGS) {
      // forcedColor 是硬约束, 可以命中已从普通池移除的跨类保留颜色;
      // 不受支持或与邻居冲突时必须 spill, 不能静默退化为普通偏好
      if (isSupportedColor(info.forcedColor, info.registerClass) &&
          (forbidden & registerBit(info.forcedColor)) == 0)
        chosen = info.forcedColor;
    } else {
      // ABI, copy 和调用惯例启发式只能在普通 available 集合内择优
      chosen = chooseColor(
          node, ordinaryColorMasks_[static_cast<usize>(info.registerClass)] &
                    ~forbidden);
      if (chosen >= NUM_PREGS) {
        // 普通颜色耗尽后才尝试同类 small storage;
        // storage 不计入 K, 不参与 Simplify 或 Coalesce 的可着色性证明, 但仍受
        // 普通邻边和 call-site clobber 边约束, 且不会与普通颜色形成双重身份
        const u64 storage =
            storageColorMasks_[static_cast<usize>(info.registerClass)] &
            ~forbidden;
        if (storage != 0)
          chosen = static_cast<PReg>(__builtin_ctzll(storage));
      }
    }

    if (chosen >= NUM_PREGS) {
      // 乐观 Simplify 的节点最终仍无合法颜色, 下一轮 RewriteProgram 才真正改写
      nodes_[node].state = NodeState::Spilled;
      spilledNodes_.push_back(node);
      continue;
    }

    colors_[node] = chosen;
    nodes_[node].state = NodeState::Colored;
    // 记录该色已着色节点的线性末端, 仅服务本轮后续节点的距离 tie-break
    if (info.lastInstruction != kNoInstruction)
      lastColorUse_[chosen] = info.lastInstruction;
  }

  // Coalesced 成员不独立着色, 成功 root 的颜色或失败哨兵沿 alias 链继承
  for (u32 node : coalescedNodes_)
    colors_[node] = colors_[alias(node)];
}

// VReg metadata, 每轮投影和保值继承

/// 把真实 MIR 定义上的 metadata 按当前 VReg id 折叠到连续投影
void IRCAllocator::loadVRegMetadata() {
  virtualCount_ = function_->virtualRegisterCount;
  vregMetadata_.assign(virtualCount_, {});

  // PhiElim 把 OP_PHI 摘成 parentBlock() == nullptr 的 VReg 身份, 并把结果
  // metadata 克隆到每条前驱 COPY/FCOPY 定义; IRC 只消费当前 MIR 指令流中的
  // 真实定义, 不反向扫描浮空身份, 避免把 RA 重新耦合到已经完成的 SSA 表示
  //
  // 同一 VReg 可以有多个边定义, spillDepth 取最大, storeConstant 取并集,
  // scalarFacts 取首个有效摘要; forcedColor 是硬约束, 多个非哨兵值必须一致
  auto fold = [&](Inst *definition) {
    if (!definition || definition->id >= virtualCount_ ||
        isVoid(definition->getType()) || definition->getOp() == MOP_NOP ||
        definition->isPrecoloredDef())
      return;

    const u32 node = definition->id;
    const VRegMetadata incoming = queryVRegMetadata(function_, definition);
    VRegMetadata &current = vregMetadata_[node];
    current.spillDepth = std::max(current.spillDepth, incoming.spillDepth);
    current.storeConst |= incoming.storeConst;
    if (incoming.scalarFacts.valid && !current.scalarFacts.valid)
      current.scalarFacts = incoming.scalarFacts;

    // NUM_PREGS 是唯一无约束哨兵, 其它值必须属于该 VReg 类别的基础颜色全集
    if (static_cast<u32>(incoming.forcedColor) > NUM_PREGS)
      fatal(function_, diagnosticLocation(definition),
            "VReg %u 的 forcedColor 编号越界: %u.", static_cast<unsigned>(node),
            static_cast<unsigned>(incoming.forcedColor));
    if (incoming.forcedColor == NUM_PREGS)
      return;
    const RegClass registerClass =
        function_->virtualRegisterClasses[node] ? RC_FPR : RC_GPR;
    if (!isSupportedColor(incoming.forcedColor, registerClass))
      fatal(function_, diagnosticLocation(definition),
            "VReg %u 的 forcedColor %s 不属于合法的 %s 颜色.",
            static_cast<unsigned>(node), pregName(incoming.forcedColor),
            registerClass == RC_FPR ? "FPR" : "GPR");
    if (current.forcedColor < NUM_PREGS &&
        current.forcedColor != incoming.forcedColor)
      fatal(function_, diagnosticLocation(definition),
            "VReg %u 的多个定义携带冲突的 forcedColor.",
            static_cast<unsigned>(node));
    current.forcedColor = incoming.forcedColor;
  };

  // forEachOp 不会访问已经摘下的 Phi 身份, 只遍历块内 Phi 和普通指令链
  for (BasicBlock *block = function_->region->first; block;
       block = block->next())
    forEachOp(block, fold);
}

/// 从本轮 VReg 投影向栈 reload 或 store 前短命定义复制稳定 metadata;
/// absoluteDepth 由 spill 计划统一计算, forcedColor 有意不继承
void IRCAllocator::attachSpillMetadata(u32 oldVReg, Inst *newDefinition,
                                       u8 absoluteDepth) {
  // 深度即使在防御性越界路径中也要落到新定义, 避免生成无代数的 spill 产物
  setSpillDepth(function_, newDefinition, absoluteDepth);
  if (oldVReg >= vregMetadata_.size())
    return;

  // storeConstant 影响下一轮 spill 评分, scalarFacts 则属于等值定义的稳定契约;
  // 即使当前流水线没有 RA 后标量事实优化, rewrite 也不能静默制造事实断点;
  // forcedColor 只约束原 storage proxy, 不能传播给普通 reload
  const VRegMetadata &source = vregMetadata_[oldVReg];
  if (source.storeConst)
    setStoreConst(function_, newDefinition, true);
  if (source.scalarFacts.valid) {
    ScalarFactBundle facts = source.scalarFacts;
    facts.source = FactSource::MetadataClone;
    attachFactBundle(function_, newDefinition, facts);
  }
}

// 重物化 rewrite

/// 在每条 Use 指令前重建 LI 或 LA, 不分配 frame slot 也不发出 store
void IRCAllocator::rewriteRematerialized(u32 node) {
  const RematInfo info = nodes_[node].remat;
  IRBuilder builder(function_->module, function_);

  // 调用方已经验证该 root 无 Coalesced 成员且只有一个可重物化定义;
  // LI/LA 无副作用, 同一条 Use 指令的重复引用共享一条结果不会延长到下一条指令
  for (BasicBlock *block = function_->region->first; block;
       block = block->next()) {
    for (Inst *user = block->firstInst(); user; user = user->next()) {
      Inst *rematerializedValue = nullptr;
      for (u32 argument = 0; argument < user->getOperandCount(); ++argument) {
        Inst *value = user->getArg(argument);
        if (!value || value->isPrecoloredDef() || value->id != node)
          continue;
        if (!rematerializedValue) {
          builder.setInsertBefore(user);
          builder.setCurrentSourceLocation(user->sourceLocation);
          rematerializedValue = emitRematerialized(builder, info);
          assert(rematerializedValue);
          // 新值与原定义等价, 克隆稳定事实并增加代数, 不继承 forcedColor
          cloneVRegMetadata(function_, info.definition, rematerializedValue, 1);
        }
        user->setArg(argument, rematerializedValue);
      }
    }
  }

  // setArg 已经增量维护 Use 链, 原 LI/LA 无剩余使用时可以立即删除
  if (info.definition && info.definition->parentBlock() &&
      info.definition->hasNoUses())
    info.definition->eraseFromBlock();
}

// 跨寄存器类虚拟栈槽

/// 从指定 storage 类别选择一个可在后续 rewrite 轮次保留的 callee-saved 颜色
PReg IRCAllocator::pickCrossClassRegister(RegClass registerClass) const {
  const u64 classMask =
      registerClass == RC_FPR ? kFPRRegisterMask : kGPRRegisterMask;
  // 限制每个类别被借出的数量, 避免跨类 storage 吞掉过多普通颜色
  if (static_cast<u32>(__builtin_popcountll(reservedColorMask_ & classMask)) >=
      kMaxCrossClassSlotsPerClass)
    return NUM_PREGS;

  // 从高编号向低编号查找, 优先借用正常颜色顺序中较晚才会选择的寄存器;
  // small spill storage 有独立身份, 不能同时作为跨类槽
  for (i32 value = static_cast<i32>(NUM_PREGS) - 1; value >= 0; --value) {
    const PReg reg = static_cast<PReg>(value);
    if (pregClass(reg) != registerClass || !isCalleeSaved(reg) ||
        ((kGPRSpillStorageMask | kFPRSpillStorageMask) & registerBit(reg)) !=
            0 ||
        (reservedColorMask_ & registerBit(reg)) != 0 ||
        !isSupportedColor(reg, registerClass))
      continue;
    return reg;
  }
  return NUM_PREGS;
}

/// 验证唯一真实定义严格支配全部同 id 使用, 并且至少存在一个使用
bool IRCAllocator::definitionDominatesUses(u32 node, Inst *definition) const {
  if (!definition || !definition->parentBlock() || !dominators_)
    return false;
  bool foundUse = false;
  bool valid = true;
  for (BasicBlock *block = function_->region->first; block;
       block = block->next()) {
    forEachOp(block, [&](Inst *user) {
      if (!valid)
        return;
      for (u32 argument = 0; argument < user->getOperandCount(); ++argument) {
        Inst *value = user->getArg(argument);
        if (!value || value->isPrecoloredDef() || value->id != node)
          continue;
        foundUse = true;
        // OutOfSSA 自循环可能形成 v <- v, park 不能插在这个自 use 之后
        if (user == definition) {
          valid = false;
          return;
        }
        if (block == definition->parentBlock()) {
          // 同块支配退化为严格程序顺序, 稀疏编号同时排除未编号指令
          const u32 definitionNumber = numbering_.numberOf(definition);
          const u32 useNumber = numbering_.numberOf(user);
          if (definitionNumber == kNoInstruction ||
              useNumber == kNoInstruction || useNumber <= definitionNumber)
            valid = false;
        } else if (!dominators_->dominates(definition->parentBlock(), block)) {
          // 跨块使用要求定义块支配使用块
          valid = false;
        }
        if (!valid)
          return;
      }
    });
  }
  return foundUse && valid;
}

/// 尝试用另一 RegClass 的 callee-saved 颜色保存一个 32-bit spilled 值
bool IRCAllocator::tryCrossClassSlot(u32 node) {
  // 调用方已经排除 Coalesced 成员和深代数, 这里重新验证唯一真实定义与支配关系
  if (nodes_[node].definitionCount != 1 || !nodes_[node].singleDefinition)
    return false;

  Inst *definition = nodes_[node].singleDefinition;
  if (!definitionDominatesUses(node, definition))
    return false;

  const RegClass valueClass = nodes_[node].registerClass;
  const IRType valueType = definition->getType();
  // FMV.W.X 和 FMV.X.W 只保证低 32 bit 忠实往返;
  // i32 和 f32 可保持位模式, i64 与 ptr 会丢失高 32 bit, 必须回退栈槽
  if ((valueClass == RC_GPR && valueType != TY_I32) ||
      (valueClass == RC_FPR && valueType != TY_F32))
    return false;

  const RegClass storageClass = valueClass == RC_GPR ? RC_FPR : RC_GPR;
  const PReg storageRegister = pickCrossClassRegister(storageClass);
  if (storageRegister >= NUM_PREGS)
    return false;

  // 保留色只从所属类别的后续可分配池移除, 避免普通值与 proxy 双重占用
  //
  // 下一轮 proxy 重新参加活跃性和 call clobber 建边, forcedColor 再校验冲突;
  // 该机制要求非 call 指令不能任意写 allocatable callee-saved PReg
  reservedColorMask_ |= registerBit(storageRegister);
  OpCode parkOp = MOP_FMV_W_X;
  OpCode unparkOp = MOP_FMV_X_W;
  IRType proxyType = TY_F32;
  IRType unparkType = TY_I32;
  if (valueClass == RC_FPR) {
    parkOp = MOP_FMV_X_W;
    unparkOp = MOP_FMV_W_X;
    proxyType = TY_I32;
    unparkType = TY_F32;
  }

  IRBuilder builder(function_->module, function_);
  // park 紧随原定义, 原定义本身保留并缩短为只向 park 提供值;
  // cloneVRegMetadata 保留稳定事实但不继承颜色, 随后单独施加 storage 硬颜色
  builder.setInsertAfter(definition);
  builder.setCurrentSourceLocation(definition->sourceLocation);
  Inst *proxy = builder.emit(parkOp, proxyType, definition);
  cloneVRegMetadata(function_, definition, proxy, 1);
  setForcedColor(function_, proxy, storageRegister);

  for (BasicBlock *block = function_->region->first; block;
       block = block->next()) {
    for (Inst *user = block->firstInst(); user; user = user->next()) {
      // park 对原值的 use 必须保留, 不能改写成从尚未定义的 proxy 读取
      if (user == proxy)
        continue;
      Inst *unparkedValue = nullptr;
      for (u32 argument = 0; argument < user->getOperandCount(); ++argument) {
        Inst *value = user->getArg(argument);
        if (!value || value->isPrecoloredDef() || value->id != node)
          continue;
        if (!unparkedValue) {
          // 每条 Use 指令共享一个 unpark, 不把结果延长到下一条指令;
          // 新结果继承值事实和增加后的深度, 但不继承 proxy 的 forcedColor
          builder.setInsertBefore(user);
          builder.setCurrentSourceLocation(user->sourceLocation);
          unparkedValue = builder.emit(unparkOp, unparkType, proxy);
          cloneVRegMetadata(function_, definition, unparkedValue, 1);
        }
        user->setArg(argument, unparkedValue);
      }
    }
  }
  return true;
}

// 批量栈 spill

/// 以一次全函数 use pass 和一次 def pass 改写所有计划中的栈 spill;
/// 平坦 VReg 映射避免对每个 spilled root 重复扫描全函数
void IRCAllocator::applyStackSpill(const std::vector<i32> &vregToSlot,
                                   const std::vector<u8> &newDepth) {
  if (vregToSlot.empty())
    return;

  // 第一遍在每条真实 use 前插入 reload 并替换对应 operand;
  // vregToSlot 由紧凑旧 id 直接寻址, 本轮新插入值的单调 id 越界即视为未命中,
  // 因而不会被同一份 spill 计划递归改写
  //
  // reload 有意保持 per-use, 不提升到块头或 preheader; 跨指令共享会重新制造
  // 长活跃区间并提高下一轮重复 spill 风险, 紧邻 use 的短区间则受 spillCost
  // 保护; 这只是收敛启发式, 极端压力下仍由轮数安全阀处理;
  // 同一条指令重复使用同一 spilled VReg 时共享一条 reload, 减少冗余栈访存且
  // 不会把结果延长到下一条指令
  std::vector<std::pair<u32, Inst *>> reloads;
  for (BasicBlock *block = function_->region->first; block;
       block = block->next()) {
    for (Inst *user = block->firstInst(); user; user = user->next()) {
      reloads.clear();
      for (u32 argument = 0; argument < user->getOperandCount(); ++argument) {
        Inst *value = user->getArg(argument);
        if (!value || value->isPrecoloredDef())
          continue;
        const i32 slot =
            value->id < vregToSlot.size() ? vregToSlot[value->id] : -1;
        if (slot < 0)
          continue;

        Inst *reload = nullptr;
        for (const auto &[oldVReg, candidate] : reloads)
          if (oldVReg == value->id) {
            reload = candidate;
            break;
          }
        if (!reload) {
          IRBuilder builder(function_->module, function_);
          builder.setInsertBefore(user);
          builder.setCurrentSourceLocation(user->sourceLocation);
          const IRType type = value->getType();
          assert(type != TY_F64 && "TY_F64不能进入IRC reload.");
          const OpCode load = type == TY_F32 ? MOP_FLW_FRAME
                              : (type == TY_I64 || type == TY_PTR)
                                  ? MOP_LD_FRAME
                                  : MOP_LW_FRAME;
          reload =
              builder.emit(load, type, function_->module->physicalRegister(SP));
          reload->setFrameIndex(slot);
          user->setArg(argument, reload);
          // 绝对深度在 rewrite 计划阶段统一确定, metadata 从旧 VReg 投影继承
          const u8 depth =
              value->id < newDepth.size() ? newDepth[value->id] : 0;
          attachSpillMetadata(value->id, reload, depth);
          reloads.push_back({value->id, reload});
        } else {
          user->setArg(argument, reload);
        }
      }
    }
  }

  // 第二遍在每个原始定义之后写回, 新 store 不再参与已经完成的 use pass;
  // OutOfSSA 的多个前驱 COPY 可以共享旧 VReg id, 每个原定义在 store 前只需短暂
  // 存活; store 建立 operand 后给定义分配新 id, 避免互不相交的短命定义在下一轮
  // 再次折叠为同一跨块 web, 累加邻域并拉大 footprint
  for (BasicBlock *block = function_->region->first; block;
       block = block->next()) {
    for (Inst *definition = block->firstInst(); definition;) {
      Inst *next = definition->next();
      const u32 oldVReg = definition->id;
      const i32 slot = oldVReg < vregToSlot.size() ? vregToSlot[oldVReg] : -1;
      if (slot >= 0 && !isVoid(definition->getType()) &&
          definition->getOp() != MOP_NOP && !definition->isPrecoloredDef()) {
        IRBuilder builder(function_->module, function_);
        builder.setInsertAfter(definition);
        builder.setCurrentSourceLocation(definition->sourceLocation);
        const IRType type = definition->getType();
        assert(type != TY_F64 && "TY_F64不能进入IRC spill.");
        const OpCode store = type == TY_F32 ? MOP_FSW_FRAME
                             : (type == TY_I64 || type == TY_PTR)
                                 ? MOP_SD_FRAME
                                 : MOP_SW_FRAME;
        Inst *spill =
            builder.emit(store, TY_VOID,
                         function_->module->physicalRegister(SP), definition);
        spill->setFrameIndex(slot);
        const u8 depth = oldVReg < newDepth.size() ? newDepth[oldVReg] : 0;
        // 某个边定义可能只通过 VReg 投影拥有 Phi metadata, 重新编号前必须把
        // spillDepth, storeConstant 和 scalarFacts 回填到这个短命真实定义
        attachSpillMetadata(oldVReg, definition, depth);
        assignNewVReg(definition, function_);
      }
      definition = next;
    }
  }
}

// RewriteProgram

/// 为所有实际未着色 root 选择 remat, 跨类 storage 或批量栈 spill
void IRCAllocator::rewriteProgram() {
  // 拥有 Coalesced 成员的 root 代表多个原值, 不能使用依赖唯一定义的 remat 或
  // 跨类快速路径; 平坦标记避免为紧凑 node id 建哈希集合
  std::vector<u8> hasCoalesced(nodeCount_, 0);
  for (u32 node : coalescedNodes_)
    hasCoalesced[alias(node)] = 1;

  // 先按 alias root 规划 frame slot 和绝对新深度, 最后一次投影到全部成员
  std::vector<i32> rootSlot(nodeCount_, -1);
  std::vector<u8> rootDepth(nodeCount_, 0);
  bool hasStackSpill = false;

  for (u32 root : spilledNodes_) {
    const bool pure = !hasCoalesced[root] &&
                      nodes_[root].definitionCount == 1 &&
                      nodes_[root].singleDefinition;
    // 纯 LI/LA 首选零栈槽重物化
    if (pure && nodes_[root].rematerializable) {
      rewriteRematerialized(root);
      continue;
    }

    // 深度小于 2 的纯单值尝试借用另一类别的 callee-saved 颜色;
    // 支配, 类型, 配额或颜色条件失败时自然回退栈槽; 深代数直接使用 per-use
    // reload, 降低继续引入跨类 proxy 后再次 spill 的风险
    if (pure && nodes_[root].spillDepth < 2 && tryCrossClassSlot(root))
      continue;

    rootSlot[root] =
        function_->newFrameSlot(8, 8, Function::FrameSlot::Kind::Spill);
    const u32 depth = nodes_[root].spillDepth;
    rootDepth[root] = static_cast<u8>(depth >= 255 ? 255 : depth + 1);
    hasStackSpill = true;
  }

  if (hasStackSpill) {
    // root slot 经 alias 投影到整个 Coalesced 类, 一次批量扫描完成全部栈改写
    std::vector<i32> vregToSlot(virtualCount_, -1);
    std::vector<u8> depth(virtualCount_, 0);
    for (u32 node = 0; node < virtualCount_; ++node) {
      const u32 root = alias(node);
      if (rootSlot[root] >= 0) {
        vregToSlot[node] = rootSlot[root];
        depth[node] = rootDepth[root];
      }
    }
    applyStackSpill(vregToSlot, depth);
  }
}

// 物理寄存器落地

/// 根据最终 assignment 把所有 VReg operand 和 definition 改为物理寄存器
void IRCAllocator::rewriteToPhysicalRegisters(
    const std::vector<PReg> &assignment) {
  // 最终防线检查颜色范围和寄存器类别, 防止错误 assignment 流入 frame lowering
  const auto checkedColor = [&](Inst *value, PReg color) {
    const RegClass expected = value->getType() == TY_F32 ? RC_FPR : RC_GPR;
    if (color >= NUM_PREGS || !isSupportedColor(color, expected))
      fatal(function_, diagnosticLocation(value), "VReg %u 没有合法的最终颜色.",
            static_cast<unsigned>(value->id));
    return color;
  };

  // 必须先改写所有 use, 此时 operand 指向的 definition 仍保留 VReg id,
  // 可以直接索引 assignment; precolored operand 已经是最终物理寄存器
  for (BasicBlock *block = function_->region->first; block;
       block = block->next()) {
    forEachOp(block, [&](Inst *inst) {
      for (u32 argument = 0; argument < inst->getOperandCount(); ++argument) {
        Inst *value = inst->getArg(argument);
        if (!value || value->isPrecoloredDef())
          continue;
        if (value->id >= function_->virtualRegisterCount)
          fatal(function_, diagnosticLocation(inst),
                "物理寄存器改写遇到越界VReg使用: %u.",
                static_cast<unsigned>(value->id));
        if (value->id >= assignment.size())
          fatal(function_, diagnosticLocation(inst),
                "VReg编号超出IRC assignment范围.");
        const PReg color = checkedColor(value, assignment[value->id]);
        inst->setArg(argument, function_->module->physicalRegister(color));
      }
    });
  }

  // 所有 use 已经脱离 VReg id 后, 第二遍才能把真实 definition id 改为 PReg
  for (BasicBlock *block = function_->region->first; block;
       block = block->next()) {
    forEachOp(block, [&](Inst *inst) {
      if (isVoid(inst->getType()) || inst->getOp() == MOP_NOP ||
          inst->isPrecoloredDef())
        return;
      if (inst->id >= function_->virtualRegisterCount)
        fatal(function_, diagnosticLocation(inst),
              "物理寄存器改写遇到越界VReg定义: %u.",
              static_cast<unsigned>(inst->id));
      if (inst->id >= assignment.size())
        fatal(function_, diagnosticLocation(inst),
              "VReg定义编号超出IRC assignment范围.");
      inst->id = checkedColor(inst, assignment[inst->id]);
    });
  }
}

// 单轮分配和最终落地

/// 单轮完整 IRC, Build -> MakeWorklist -> 主循环 -> AssignColors;
/// 主循环严格保持标准 IRC 的优先级, Simplify > Coalesce > Freeze > SelectSpill;
/// 返回 true 表示已经为未着色节点执行 RewriteProgram, 调用方需要重建下一轮
bool IRCAllocator::allocateRound() {
  build();
  makeWorklist();

  // 主循环严格保持标准 IRC 的优先级; 每个 try* 最多完成一个顶层动作,
  // 动作内部可以唤醒或重分类多个相邻节点和 move;
  // 四类工作都耗尽时, 所有普通节点均已压入选择栈或并入其它节点
  for (;;) {
    if (trySimplify())
      continue;
    if (tryCoalesce())
      continue;
    if (tryFreeze())
      continue;
    if (trySelectSpill())
      continue;
    break;
  }

  assignColors();
  if (spilledNodes_.empty()) {
    finalizeColoring();
    return false;
  }

  rewriteProgram();
  return true;
}

/// 归一化 alias 颜色, 更新 calleeSaveMask, 改写物理寄存器并记录 IPRA 摘要
void IRCAllocator::finalizeColoring() {
  u64 calleeSaved = 0;

  // 所有合并成员从 alias root 继承最终颜色; 这里统一统计普通颜色, small spill
  // storage 以及跨类 storage proxy 使用的 callee-saved 寄存器, 确保 frame
  // lowering 为每一种保值路径生成正确的保存和恢复序列
  for (u32 node = 0; node < virtualCount_; ++node) {
    PReg color = colors_[node];
    if (color >= NUM_PREGS)
      color = colors_[alias(node)];
    if (color >= NUM_PREGS ||
        !isSupportedColor(color, nodes_[node].registerClass))
      fatal(function_, SourceLocation{}, "IRC无法为VReg %u生成合法的最终颜色.",
            static_cast<unsigned>(node));
    colors_[node] = color;
    if (isCalleeSaved(color))
      calleeSaved |= registerBit(color);
  }

  function_->calleeSaveMask |= calleeSaved;
  rewriteToPhysicalRegisters(colors_);

  // IPRA 记录面向分配器支持色域的完整 may-clobber 摘要;
  // 除着色使用的非 callee-saved 颜色外, ipraRecord 还加入非叶函数的 ra,
  // ABI 返回寄存器和内部 call-site clobber 的传递并集; 调用者可据此收紧默认
  // ABI 上界, 自定义调用点的额外 regMask 仍由 ipraCallSiteClobberMask 合入
  ipraRecord(function_, colors_.data(), virtualCount_);
}

// 终止安全阀

/// 为每个当前 VReg 分配独立栈槽, 主动把剩余 live range 改写为局部 reload
void IRCAllocator::massSpillFallback() {
  if (virtualCount_ == 0)
    return;

  // 每个当前 VReg 使用独立槽, 避免安全阀继续依赖本轮干涉或 alias 信息;
  // applyStackSpill 仍沿用正常的 per-use reload 和 metadata 继承路径, 因而只是
  // 主动降低分配质量, 不是另一套语义不同的 spill 实现, 也不单独承诺着色成功
  std::vector<i32> slots(virtualCount_, -1);
  std::vector<u8> depths(virtualCount_, 1);
  for (u32 node = 0; node < virtualCount_; ++node) {
    slots[node] =
        function_->newFrameSlot(8, 8, Function::FrameSlot::Kind::Spill);
    const u32 depth =
        node < vregMetadata_.size() ? vregMetadata_[node].spillDepth : 0;
    depths[node] = static_cast<u8>(depth >= 255 ? 255 : depth + 1);
  }
  applyStackSpill(slots, depths);
}

// 顶层驱动

/// 驱动多轮 IRC rewrite, 并以全量栈 spill 和硬轮数边界处理病态输入
void IRCAllocator::run(Function *function, FunctionAnalysisManager &analyses) {
  function_ = function;
  analyses_ = &analyses;
  reservedColorMask_ = 0;

  if (!function_)
    return;
  // extern 和空函数没有可着色 MIR, 分配器不记录 complete IPRA 摘要;
  // 调用者查询缺失或 incomplete 摘要时会安全回退到 ABI 默认 clobber 上界
  if (function_->isExtern || !function_->region || !function_->region->first) {
    function_->mirPhase = MIRPhase::PostRegAlloc;
    return;
  }
  if (function_->phase != IRPhase::MIR ||
      function_->mirPhase != MIRPhase::OutOfSSA)
    fatal(function_, SourceLocation{}, "IRC只能消费Phi消除后的OutOfSSA MIR.");
  if (!computePreds(function_))
    fatal(function_, SourceLocation{}, "IRC遇到不合法的MIR控制流图.");

  // rewrite 不改变 CFG, 前驱, DominatorTree 和 LoopInfo 可在整个 run 内复用
  //
  // Use 链只在入口重建, 后续由 IRBuilder, setArg 和 eraseFromBlock 增量维护
  computeUses(function_);

  for (u32 round = 0;; ++round) {
    // Rewrite 后 VReg 身份, metadata 投影, 指令距离和活跃不动点全部失效;
    // Use 链与 CFG 仍然有效, 每轮只重建真正依赖 VReg 编号或指令流的信息
    renumberVRegs(function_);
    loadVRegMetadata();
    numbering_.compute(function_);
    liveness_.compute(function_);

    // 完成 64 轮正常尝试后, 把当前所有值批量改写到独立栈槽;
    // continue 让新产生的短生命周期 reload 在下一轮接受正常 IRC 着色
    if (round == kMaxAllocationRounds) {
      emitDiagnostic(function_, DiagnosticLevel::Warn, SourceLocation{},
                     "IRC函数%s超过%u轮, 对当前全部VReg启用栈spill安全阀.",
                     function_->name ? function_->name : "?",
                     static_cast<unsigned>(kMaxAllocationRounds));
      massSpillFallback();
      continue;
    }
    // 全量栈 spill 后再允许 8 轮, 仍失败则明确终止编译;
    // 不能让含未分配 VReg 的 MIR 继续进入 frame layout 或发射
    if (round > kMaxAllocationRounds + kFinalAllocationRounds)
      fatal(function_, SourceLocation{}, "IRC函数%s在全量栈spill后仍未收敛.",
            function_->name ? function_->name : "?");

    if (!allocateRound())
      break;
  }
  // 所有普通 VReg 已经落为物理寄存器, 后续 pass 可以执行 frame 和 call fixup
  function_->mirPhase = MIRPhase::PostRegAlloc;
}

} // namespace

std::string_view IRCAllocPass::name() const noexcept { return "irc-alloc"; }

PassResult IRCAllocPass::run(Function *function, PassContext &context) {
  IRCAllocator allocator;
  allocator.run(function, context.functionAnalyses());

  PreservedAnalyses preserved = PreservedAnalyses::none();
  // 指令和 Use-Def 已彻底改变 但不修改任何 CFG 边或块结构
  preserved.preserveCFGAnalyses();
  return PassResult::changedIR(std::move(preserved));
}

} // namespace svm::ir
