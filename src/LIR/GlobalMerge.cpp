#include "IR.h"
#include "LIRPass.h"

#include <algorithm>
#include <cstring>
#include <vector>

namespace svm::ir {
namespace {

constexpr i32 kGroupSize = 4096;
constexpr i32 kGroupCenter = 2048;

i32 alignUp(i32 value, i32 alignment) noexcept {
  VERIFY(alignment > 0 && (alignment & (alignment - 1)) == 0);
  return (value + alignment - 1) & -alignment;
}

i32 defaultAlignment(const Global *global) noexcept {
  if (!global)
    return 1;
  return 4;
}

bool isMergeCandidate(const Global *global) noexcept {
  return global && !global->globalMergeMember && global->totalSizeBytes != 0 &&
         global->totalSizeBytes <= static_cast<u32>(kGroupSize) &&
         !global->isConst &&
         global->origin == Global::GlobalOrigin::SourceGlobal;
}

} // namespace

std::string_view GlobalMergePass::name() const noexcept {
  return "global-merge";
}

PassResult GlobalMergePass::run(Module *module, PassContext &) {
  if (!module)
    return PassResult::noChange();

  module->hasMergedGlobals = false;
  module->mergedGlobalGroupCount = 0;
  module->mergedGlobalGroupSizes = nullptr;
  module->mergedGlobalAlignment = 4;

  std::vector<Global *> scalars;
  std::vector<Global *> arrays;
  for (Global *global = module->globalHead; global; global = global->next) {
    global->globalMergeEligible = false;
    global->globalMergeMember = false;
    global->globalMergeGroup = 0;
    global->globalMergeOffset = 0;
    global->abiAlignment = defaultAlignment(global);
    if (!isMergeCandidate(global))
      continue;
    global->globalMergeEligible = true;
    if (!global->isArray || global->numElements == 1)
      scalars.push_back(global);
    else
      arrays.push_back(global);
  }

  std::stable_sort(arrays.begin(), arrays.end(),
                   [](const Global *left, const Global *right) {
                     if (left->totalSizeBytes != right->totalSizeBytes)
                       return left->totalSizeBytes < right->totalSizeBytes;
                     return std::strcmp(left->name ? left->name : "",
                                        right->name ? right->name : "") < 0;
                   });

  std::vector<i32> groupSizes;
  u16 group = 0;
  i32 used = 0;
  auto place = [&](Global *global) {
    const i32 alignment = defaultAlignment(global);
    i32 offset = alignUp(used, alignment);
    if (static_cast<u32>(offset) + global->totalSizeBytes >
        static_cast<u32>(kGroupSize)) {
      if (used > 0) {
        groupSizes.push_back(alignUp(used, 4));
        ++group;
        used = 0;
      }
      offset = 0;
    }

    VERIFY(static_cast<u32>(offset) + global->totalSizeBytes <=
           static_cast<u32>(kGroupSize));
    global->globalMergeMember = true;
    global->globalMergeGroup = group;
    global->globalMergeOffset = offset - kGroupCenter;
    global->abiAlignment = alignment;
    used = offset + static_cast<i32>(global->totalSizeBytes);
  };

  for (Global *global : scalars)
    place(global);
  for (Global *global : arrays)
    place(global);
  if (used > 0)
    groupSizes.push_back(alignUp(used, 4));
  if (groupSizes.empty())
    return PassResult::noChange();

  VERIFY(groupSizes.size() <= static_cast<usize>(UINT16_MAX));
  module->hasMergedGlobals = true;
  module->mergedGlobalGroupCount = static_cast<u16>(groupSizes.size());
  module->mergedGlobalGroupSizes =
      module->arena->createArray<i32>(groupSizes.size());
  std::copy(groupSizes.begin(), groupSizes.end(),
            module->mergedGlobalGroupSizes);
  return PassResult::changedIR();
}

} // namespace svm::ir
