#include "IR.h"
#include "PassManager.h"

#include <cassert>
#include <cinttypes>
#include <cstring>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace svm::ir {
namespace {
enum class PrintMode { HIR, LLVM };

class IRPrinter {
public:
  IRPrinter(FILE *out, PrintMode mode, bool printSource) noexcept
      : out_(out ? out : stdout), mode_(mode), printSource_(printSource) {}

  void print(const Module *module) {
    if (!module)
      return;
    module_ = module;
    std::fputs("; ModuleID = 'sysy'\nsource_filename = \"sysy\"\n\n", out_);
    emitGlobals(module);
    for (const Function *function = module->functionHead; function;
         function = function->next)
      if (function->isExtern)
        emitDeclaration(function);
    if (module->functionHead)
      std::fputc('\n', out_);
    for (const Function *function = module->functionHead; function;
         function = function->next)
      if (!function->isExtern)
        emitFunction(function);
  }

private:
  static const char *typeName(IRType type) noexcept {
    switch (type) {
    case TY_VOID:
      return "void";
    case TY_I1:
      return "i1";
    case TY_I32:
      return "i32";
    case TY_F32:
      return "float";
    case TY_PTR:
      return "ptr";
    case TY_I64:
      return "i64";
    case TY_F64:
      return "double";
    }
    return "void";
  }

  static std::string floatLiteral(f32 value) {
    const double widened = static_cast<double>(value);
    u64 bits = 0;
    std::memcpy(&bits, &widened, sizeof(bits));
    char buffer[24];
    std::snprintf(buffer, sizeof(buffer), "0x%016" PRIX64, bits);
    return buffer;
  }

  static std::string escapeBytes(const Global *global) {
    static constexpr char hex[] = "0123456789ABCDEF";
    std::string result;
    for (u32 segmentIndex = 0; segmentIndex < global->initSegmentCount;
         ++segmentIndex) {
      const GlobalInitSegment &segment = global->initSegment[segmentIndex];
      const i32 *values = static_cast<const i32 *>(segment.data);
      for (u32 index = 0; index < segment.count; ++index) {
        const u8 byte = values ? static_cast<u8>(values[index]) : 0;
        if (byte == '"' || byte == '\\' || byte < 0x20 || byte >= 0x7f) {
          result.push_back('\\');
          result.push_back(hex[byte >> 4]);
          result.push_back(hex[byte & 15]);
        } else {
          result.push_back(static_cast<char>(byte));
        }
      }
    }
    return result;
  }

  void assignNames(const Function *function) {
    values_.clear();
    blocks_.clear();
    nextValue_ = nextBlock_ = 0;
    lastSourceLine_ = 0;
    for (u32 index = 0; index < function->paramCount; ++index)
      values_.emplace(function->params[index], "%arg" + std::to_string(index));
    assignRegion(function->region);
  }

  void assignRegion(const Region *region) {
    for (const BasicBlock *block = region ? region->first : nullptr; block;
         block = block->next()) {
      blocks_.emplace(block, "bb" + std::to_string(nextBlock_++));
      forEachOp(const_cast<BasicBlock *>(block), [&](Inst *inst) {
        if (!isVoid(inst->getType()) && inst->getOp() != OP_ICONST &&
            inst->getOp() != OP_FCONST && inst->getOp() != OP_GETGLOBAL &&
            inst->getOp() != OP_PARAM)
          values_.emplace(inst, "%v" + std::to_string(nextValue_++));
        if (mode_ == PrintMode::HIR) {
          if (inst->getOp() == OP_FOR)
            assignRegion(inst->getBody());
          else if (inst->getOp() == OP_IF || inst->getOp() == OP_WHILE) {
            assignRegion(inst->getScf().r[0]);
            assignRegion(inst->getScf().r[1]);
          }
        }
      });
    }
  }

  std::string valueName(const Inst *inst) const {
    if (!inst)
      return "undef";
    if (inst->isUndefValue())
      return "undef";
    if (inst->getOp() == OP_ICONST)
      return std::to_string(inst->getImm());
    if (inst->getOp() == OP_FCONST)
      return floatLiteral(inst->getFimm());
    if (inst->getOp() == OP_GETGLOBAL)
      return "@" + std::string(inst->getGlobal()->name);
    if (inst->getOp() == OP_PARAM)
      return "%arg" + std::to_string(inst->getArgNo());
    const auto found = values_.find(inst);
    return found == values_.end() ? "undef" : found->second;
  }

  const std::string &blockName(const BasicBlock *block) const {
    const auto found = blocks_.find(block);
    assert(found != blocks_.end());
    return found->second;
  }

  void emitGlobals(const Module *module) {
    for (const Global *global = module->globalHead; global;
         global = global->next) {
      if (global->origin == Global::GlobalOrigin::StringLiteral) {
        std::fprintf(
            out_, "@%s = private unnamed_addr constant [%u x i8] c\"%s\"\n",
            global->name, global->numElements, escapeBytes(global).c_str());
        continue;
      }
      const char *kind = global->isConst ? "constant" : "global";
      if (!global->isArray) {
        std::fprintf(out_, "@%s = %s %s ", global->name, kind,
                     typeName(global->type));
        if (!global->initSegmentCount || !global->initSegment[0].data)
          std::fputs(global->type == TY_F32 ? floatLiteral(0.0F).c_str() : "0",
                     out_);
        else if (global->type == TY_F32)
          std::fputs(
              floatLiteral(*static_cast<f32 *>(global->initSegment[0].data))
                  .c_str(),
              out_);
        else
          std::fprintf(out_, "%d",
                       *static_cast<i32 *>(global->initSegment[0].data));
        std::fputc('\n', out_);
        continue;
      }
      std::fprintf(out_, "@%s = %s [%u x %s] ", global->name, kind,
                   global->numElements, typeName(global->type));
      bool allZero = true;
      for (u32 segmentIndex = 0; segmentIndex < global->initSegmentCount;
           ++segmentIndex)
        if (global->initSegment[segmentIndex].data) {
          allZero = false;
          break;
        }
      if (!global->initSegmentCount || allZero) {
        std::fputs("zeroinitializer\n", out_);
        continue;
      }
      std::fputc('[', out_);
      u32 emitted = 0;
      for (u32 segmentIndex = 0; segmentIndex < global->initSegmentCount;
           ++segmentIndex) {
        const GlobalInitSegment &segment = global->initSegment[segmentIndex];
        for (u32 index = 0;
             index < segment.count && emitted < global->numElements;
             ++index, ++emitted) {
          if (emitted)
            std::fputs(", ", out_);
          std::fprintf(out_, "%s ", typeName(global->type));
          if (!segment.data)
            std::fputs(global->type == TY_F32 ? floatLiteral(0.0F).c_str()
                                              : "0",
                       out_);
          else if (global->type == TY_F32)
            std::fputs(
                floatLiteral(static_cast<f32 *>(segment.data)[index]).c_str(),
                out_);
          else
            std::fprintf(out_, "%d", static_cast<i32 *>(segment.data)[index]);
        }
      }
      while (emitted++ < global->numElements) {
        if (emitted > 1)
          std::fputs(", ", out_);
        std::fprintf(out_, "%s %s", typeName(global->type),
                     global->type == TY_F32 ? floatLiteral(0.0F).c_str() : "0");
      }
      std::fputs("]\n", out_);
    }
    if (module->globalHead)
      std::fputc('\n', out_);
  }

  void emitSignature(const Function *function) {
    std::fprintf(out_, "%s @%s(", typeName(function->returnType),
                 function->name);
    for (u32 index = 0; index < function->paramCount; ++index) {
      if (index)
        std::fputs(", ", out_);
      std::fputs(typeName(function->paramTypes[index]), out_);
      if (!function->isExtern)
        std::fprintf(out_, " %%arg%u", index);
    }
    if (function->functionType && function->functionType->isVariadic) {
      if (function->paramCount)
        std::fputs(", ", out_);
      std::fputs("...", out_);
    }
    std::fputc(')', out_);
  }

  void emitDeclaration(const Function *function) {
    std::fputs("declare ", out_);
    emitSignature(function);
    std::fputc('\n', out_);
  }

  void emitFunction(const Function *function) {
    assignNames(function);
    std::fputs("define ", out_);
    emitSignature(function);
    std::fputs(" {\n", out_);
    emitRegion(function->region, 0);
    std::fputs("}\n\n", out_);
  }

  void emitRegion(const Region *region, u32 depth) {
    for (const BasicBlock *block = region ? region->first : nullptr; block;
         block = block->next()) {
      for (u32 index = 0; index < depth; ++index)
        std::fputs("  ", out_);
      std::fprintf(out_, "%s:\n", blockName(block).c_str());
      for (const Inst *phi = block->firstPhi(); phi; phi = phi->next())
        emitInst(phi, depth + 1);
      for (const Inst *inst = block->firstInst(); inst; inst = inst->next())
        emitInst(inst, depth + 1);
      if (mode_ == PrintMode::LLVM && !block->endsWithTerminator())
        std::fputs("  unreachable\n", out_);
    }
  }

  void emitPrefix(const Inst *inst, u32 depth) {
    for (u32 index = 0; index < depth; ++index)
      std::fputs("  ", out_);
    if (!isVoid(inst->getType()))
      std::fprintf(out_, "%s = ", valueName(inst).c_str());
  }

  void emitBinary(const Inst *inst, const char *operation) {
    std::fprintf(
        out_, "%s %s %s, %s", operation, typeName(inst->getArg(0)->getType()),
        valueName(inst->getArg(0)).c_str(), valueName(inst->getArg(1)).c_str());
  }

  // 打印并校验初始化锚点
  void emitLocalInitAnchor(const Inst *alloca, const Inst *anchor,
                           OpCode expected) {
    if (!anchor) {
      std::fputs("<invalid:null>", out_);
      return;
    }
    if (anchor->isErased() || anchor->getOp() != expected ||
        anchor->getOperandCount() < 3 || !anchor->getArg(0) ||
        !anchor->getArg(1) || !anchor->getArg(2)) {
      std::fprintf(out_, "<invalid:%s>", getString(anchor->getOp()));
      return;
    }
    if (expected == OP_LOCAL_INIT_VALUE) {
      std::fprintf(out_, "{base=%s,index=%s,value=%s %s}",
                   anchor->getArg(0) == alloca ? "self" : "mismatch",
                   valueName(anchor->getArg(1)).c_str(),
                   typeName(anchor->getArg(2)->getType()),
                   valueName(anchor->getArg(2)).c_str());
      return;
    }
    std::fprintf(out_, "{base=%s,begin=%s,count=%s}",
                 anchor->getArg(0) == alloca ? "self" : "mismatch",
                 valueName(anchor->getArg(1)).c_str(),
                 valueName(anchor->getArg(2)).c_str());
  }

  // 紧凑打印局部初值元数据
  void emitLocalInitInfo(const Inst *alloca, const LocalInitInfo *info) {
    if (!info)
      return;
    std::fprintf(out_, " ; initInfo={elementType=%s,segments=[",
                 typeName(info->elementType));
    for (usize segmentIndex = 0; segmentIndex < info->segments.size();
         ++segmentIndex) {
      if (segmentIndex)
        std::fputc(',', out_);
      const LocalInitSegment &segment = info->segments[segmentIndex];
      if (!segment.values.empty()) {
        std::fprintf(out_, "#%zu:data{count=%u,values=[", segmentIndex,
                     segment.count);
        for (usize valueIndex = 0; valueIndex < segment.values.size();
             ++valueIndex) {
          if (valueIndex)
            std::fputc(',', out_);
          emitLocalInitAnchor(alloca, segment.values[valueIndex],
                              OP_LOCAL_INIT_VALUE);
        }
        std::fputs("]}", out_);
      } else {
        std::fprintf(out_, "#%zu:zero{count=%u,zeroAnchor=", segmentIndex,
                     segment.count);
        emitLocalInitAnchor(alloca, segment.zeroAnchor, OP_LOCAL_INIT_ZERO);
        std::fputc('}', out_);
      }
    }
    std::fputs("]}", out_);
  }

  std::string_view sourceLine(const SourceLocation *location) const noexcept {
    if (!module_ || !module_->sourceText || !module_->sourceLength ||
        !location || !location->isValid() ||
        location->offset >= module_->sourceLength)
      return {};
    const std::string_view source(module_->sourceText, module_->sourceLength);
    usize begin = location->offset;
    while (begin && source[begin - 1] != '\n' && source[begin - 1] != '\r')
      --begin;
    usize end = location->offset;
    while (end < source.size() && source[end] != '\n' && source[end] != '\r')
      ++end;
    while (begin < end && (source[begin] == ' ' || source[begin] == '\t'))
      ++begin;
    while (end > begin && (source[end - 1] == ' ' || source[end - 1] == '\t'))
      --end;
    return source.substr(begin, end - begin);
  }

  void emitLineEnd(const Inst *inst) { // 打印去重后的源码作为注释
    const SourceLocation *location = inst ? inst->sourceLocation : nullptr;
    if (printSource_ && location && location->line != lastSourceLine_) {
      const std::string_view line = sourceLine(location);
      if (!line.empty()) {
        std::fprintf(out_, "  ; [%u] ", location->line);
        std::fwrite(line.data(), 1, line.size(), out_);
        lastSourceLine_ = location->line;
      }
    }
    std::fputc('\n', out_);
  }

  void emitCall(const Inst *inst, u32 depth) {
    const Function *callee = inst->getCallee();
    const bool variadic =
        callee->functionType && callee->functionType->isVariadic;
    const u32 fixed = callee->functionType ? callee->functionType->paramCount
                                           : callee->paramCount;
    std::vector<std::string> extensions(inst->getOperandCount());
    for (u32 index = fixed; variadic && index < inst->getOperandCount();
         ++index) {
      Inst *argument = inst->getArg(index);
      if (argument->getType() != TY_F32 || argument->getOp() == OP_FCONST)
        continue;
      const std::string temp = "%v" + std::to_string(nextValue_++);
      for (u32 indent = 0; indent < depth; ++indent)
        std::fputs("  ", out_);
      std::fprintf(out_, "%s = fpext float %s to double\n", temp.c_str(),
                   valueName(argument).c_str());
      extensions[index] = temp;
    }
    emitPrefix(inst, depth);
    std::fprintf(out_, "call %s ", typeName(callee->returnType));
    if (variadic) {
      std::fputc('(', out_);
      for (u32 index = 0; index < fixed; ++index) {
        if (index)
          std::fputs(", ", out_);
        const IRType type = index < callee->paramCount
                                ? callee->paramTypes[index]
                                : inst->getArg(index)->getType();
        std::fputs(typeName(type), out_);
      }
      if (fixed)
        std::fputs(", ", out_);
      std::fputs("...) ", out_);
    }
    std::fprintf(out_, "@%s(", callee->name);
    for (u32 index = 0; index < inst->getOperandCount(); ++index) {
      if (index)
        std::fputs(", ", out_);
      Inst *argument = inst->getArg(index);
      std::string rendered = valueName(argument);
      IRType type = argument->getType();
      if (!extensions[index].empty()) {
        rendered = extensions[index];
        type = TY_F64;
      } else if (variadic && index >= fixed && type == TY_F32 &&
                 argument->getOp() == OP_FCONST) {
        type = TY_F64;
      }
      std::fprintf(out_, "%s %s", typeName(type), rendered.c_str());
    }
    std::fputc(')', out_);
    emitLineEnd(inst);
  }

  void emitGetPtr(const Inst *inst, u32 depth) {
    std::string offset = valueName(inst->getArg(1));
    if (inst->getStride() != 1) {
      offset = "%v" + std::to_string(nextValue_++);
      for (u32 indent = 0; indent < depth; ++indent)
        std::fputs("  ", out_);
      std::fprintf(out_, "%s = mul i32 %s, %d\n", offset.c_str(),
                   valueName(inst->getArg(1)).c_str(), inst->getStride());
    }
    emitPrefix(inst, depth);
    std::fprintf(out_, "getelementptr i8, ptr %s, i32 %s",
                 valueName(inst->getArg(0)).c_str(), offset.c_str());
    emitLineEnd(inst);
  }

  void emitStructured(const Inst *inst, u32 depth) {
    emitPrefix(inst, depth);
    if (inst->getOp() == OP_IF) {
      std::fprintf(out_, "hir.if i1 %s {", valueName(inst->getArg(0)).c_str());
      emitLineEnd(inst);
      emitRegion(inst->getScf().r[0], depth + 1);
      for (u32 i = 0; i < depth; ++i)
        std::fputs("  ", out_);
      std::fputs("} else {\n", out_);
      emitRegion(inst->getScf().r[1], depth + 1);
    } else if (inst->getOp() == OP_WHILE) {
      std::fputs("hir.while {", out_);
      emitLineEnd(inst);
      emitRegion(inst->getScf().r[0], depth + 1);
      emitRegion(inst->getScf().r[1], depth + 1);
    } else {
      std::fprintf(out_, "hir.for i32 %s, i32 %s, ptr %s {",
                   valueName(inst->getArg(0)).c_str(),
                   valueName(inst->getArg(1)).c_str(),
                   valueName(inst->getArg(2)).c_str());
      emitLineEnd(inst);
      emitRegion(inst->getBody(), depth + 1);
    }
    for (u32 i = 0; i < depth; ++i)
      std::fputs("  ", out_);
    std::fputs("}\n", out_);
  }

  void emitInst(const Inst *inst, u32 depth) {
    if (mode_ == PrintMode::HIR &&
        (inst->getOp() == OP_IF || inst->getOp() == OP_WHILE ||
         inst->getOp() == OP_FOR)) {
      emitStructured(inst, depth);
      return;
    }
    if (inst->getOp() == OP_CALL) {
      emitCall(inst, depth);
      return;
    }
    if (inst->getOp() == OP_GETPTR) {
      emitGetPtr(inst, depth);
      return;
    }
    emitPrefix(inst, depth);
    switch (inst->getOp()) {
    case OP_ALLOCA: {
      const MemPayload &memory = inst->getMem();
      const u32 size = typeSizeBytes(memory.elementType);
      if (memory.totalSizeBytes == size)
        std::fprintf(out_, "alloca %s", typeName(memory.elementType));
      else if (size && memory.totalSizeBytes % size == 0)
        std::fprintf(out_, "alloca [%u x %s]", memory.totalSizeBytes / size,
                     typeName(memory.elementType));
      else
        std::fprintf(out_, "alloca [%u x i8]", memory.totalSizeBytes);
      if (mode_ == PrintMode::HIR)
        emitLocalInitInfo(inst, memory.initInfo);
      break;
    }
    case OP_LOAD:
      std::fprintf(out_, "load %s, ptr %s", typeName(inst->getType()),
                   valueName(inst->getArg(0)).c_str());
      break;
    case OP_STORE:
      std::fprintf(out_, "store %s %s, ptr %s",
                   typeName(inst->getArg(1)->getType()),
                   valueName(inst->getArg(1)).c_str(),
                   valueName(inst->getArg(0)).c_str());
      break;
    case OP_ARRAYIDX:
      std::fprintf(out_, "hir.arrayidx ptr %s",
                   valueName(inst->getArg(0)).c_str());
      for (u32 index = 1; index < inst->getOperandCount(); ++index)
        std::fprintf(out_, ", i32 %s", valueName(inst->getArg(index)).c_str());
      break;
    case OP_LOCAL_INIT_VALUE:
      std::fprintf(out_, "hir.local_init.value ptr %s, i32 %s, %s %s",
                   valueName(inst->getArg(0)).c_str(),
                   valueName(inst->getArg(1)).c_str(),
                   typeName(inst->getArg(2)->getType()),
                   valueName(inst->getArg(2)).c_str());
      break;
    case OP_LOCAL_INIT_ZERO:
      std::fprintf(out_, "hir.local_init.zero ptr %s, i32 %s, i32 %s",
                   valueName(inst->getArg(0)).c_str(),
                   valueName(inst->getArg(1)).c_str(),
                   valueName(inst->getArg(2)).c_str());
      break;
    case OP_ADD:
      emitBinary(inst, "add");
      break;
    case OP_SUB:
      emitBinary(inst, "sub");
      break;
    case OP_MUL:
      emitBinary(inst, "mul");
      break;
    case OP_DIV:
      emitBinary(inst, "sdiv");
      break;
    case OP_MOD:
      emitBinary(inst, "srem");
      break;
    case OP_FADD:
      emitBinary(inst, "fadd");
      break;
    case OP_FSUB:
      emitBinary(inst, "fsub");
      break;
    case OP_FMUL:
      emitBinary(inst, "fmul");
      break;
    case OP_FDIV:
      emitBinary(inst, "fdiv");
      break;
    case OP_EQ:
    case OP_NE:
    case OP_LT:
    case OP_LE:
    case OP_GT:
    case OP_GE: {
      const char *predicates[] = {"eq", "ne", "slt", "sle", "sgt", "sge"};
      std::fprintf(out_, "icmp %s %s %s, %s", predicates[inst->getOp() - OP_EQ],
                   typeName(inst->getArg(0)->getType()),
                   valueName(inst->getArg(0)).c_str(),
                   valueName(inst->getArg(1)).c_str());
      break;
    }
    case OP_FEQ:
    case OP_FNE:
    case OP_FLT:
    case OP_FLE:
    case OP_FGT:
    case OP_FGE: {
      const char *predicates[] = {"oeq", "une", "olt", "ole", "ogt", "oge"};
      std::fprintf(out_, "fcmp %s float %s, %s",
                   predicates[inst->getOp() - OP_FEQ],
                   valueName(inst->getArg(0)).c_str(),
                   valueName(inst->getArg(1)).c_str());
      break;
    }
    case OP_NEG:
      std::fprintf(out_, "sub i32 0, %s", valueName(inst->getArg(0)).c_str());
      break;
    case OP_FNEG:
      std::fprintf(out_, "fneg float %s", valueName(inst->getArg(0)).c_str());
      break;
    case OP_LNOT:
      std::fprintf(out_, "xor i1 %s, true", valueName(inst->getArg(0)).c_str());
      break;
    case OP_I2F:
    case OP_F2I:
    case OP_ZEXT: {
      const char *operation = inst->getOp() == OP_I2F   ? "sitofp"
                              : inst->getOp() == OP_F2I ? "fptosi"
                                                        : "zext";
      std::fprintf(out_, "%s %s %s to %s", operation,
                   typeName(inst->getArg(0)->getType()),
                   valueName(inst->getArg(0)).c_str(),
                   typeName(inst->getType()));
      break;
    }
    case OP_SELECT:
      std::fprintf(
          out_, "select i1 %s, %s %s, %s %s",
          valueName(inst->getArg(0)).c_str(), typeName(inst->getType()),
          valueName(inst->getArg(1)).c_str(), typeName(inst->getType()),
          valueName(inst->getArg(2)).c_str());
      break;
    case OP_RET:
      if (!inst->getOperandCount())
        std::fputs("ret void", out_);
      else
        std::fprintf(out_, "ret %s %s", typeName(inst->getArg(0)->getType()),
                     valueName(inst->getArg(0)).c_str());
      break;
    case OP_BR:
      std::fprintf(out_, "br i1 %s, label %%%s, label %%%s",
                   valueName(inst->getArg(0)).c_str(),
                   blockName(inst->getBr().trueBB).c_str(),
                   blockName(inst->getBr().falseBB).c_str());
      break;
    case OP_JMP:
      std::fprintf(out_, "br label %%%s",
                   blockName(inst->getJumpTarget()).c_str());
      break;
    case OP_PHI:
      std::fprintf(out_, "phi %s ", typeName(inst->getType()));
      for (u32 i = 0; i < inst->getOperandCount(); ++i) {
        if (i)
          std::fputs(", ", out_);
        std::fprintf(out_, "[%s, %%%s]", valueName(inst->getArg(i)).c_str(),
                     blockName(inst->getIncomingBlock(i)).c_str());
      }
      break;
    case OP_SWITCH: {
      const SwitchPayload &payload = inst->getSwitch();
      const char *selectorType = typeName(inst->getArg(0)->getType());
      std::fprintf(out_, "switch %s %s, label %%%s [", selectorType,
                   valueName(inst->getArg(0)).c_str(),
                   blockName(payload.getDefaultTarget()).c_str());
      for (u32 i = 0; i < payload.getCaseCount(); ++i) {
        const SwitchCase &switchCase = payload.getCase(i);
        std::fprintf(out_, " %s %d, label %%%s", selectorType,
                     switchCase.getValue(),
                     blockName(switchCase.getTarget()).c_str());
      }
      std::fputs(" ]", out_);
      break;
    }
    case OP_UNREACHABLE:
      std::fputs("unreachable", out_);
      break;
    case OP_YIELD:
      std::fputs("hir.yield", out_);
      break;
    case OP_BREAK:
      std::fputs("hir.break", out_);
      break;
    case OP_CONTINUE:
      std::fputs("hir.continue", out_);
      break;
    default:
      std::fprintf(out_, "; unsupported %s", getString(inst->getOp()));
      break;
    }
    emitLineEnd(inst);
  }

  FILE *out_ = stdout;
  const Module *module_ = nullptr;
  PrintMode mode_ = PrintMode::LLVM;
  bool printSource_ = true;                                    // 是否打印源码行
  std::unordered_map<const Inst *, std::string> values_;       // SSA名称表
  std::unordered_map<const BasicBlock *, std::string> blocks_; // 块名称表
  mutable u32 nextValue_ = 0;                                  // 下一个SSA编号
  u32 nextBlock_ = 0;                                          // 下一个块编号
  u32 lastSourceLine_ = 0; // 上次打印的源码行
};

class PrintHIR final : public ModulePass {
public:
  explicit PrintHIR(const PassOptions &options)
      : printSource_(options.getBool("print-hir-source", true)) {}
  std::string_view name() const noexcept override { return "print-hir"; }
  PassResult run(Module *module, PassContext &context) override {
    IRPrinter(context.output(), PrintMode::HIR, printSource_).print(module);
    return PassResult::noChange();
  }

private:
  bool printSource_ = true;
};

class PrintLLVMIR final : public ModulePass {
public:
  explicit PrintLLVMIR(const PassOptions &options)
      : printSource_(options.getBool("print-llvm-ir-source", true)) {}
  std::string_view name() const noexcept override { return "print-llvm-ir"; }
  PassResult run(Module *module, PassContext &context) override {
    IRPrinter(context.output(), PrintMode::LLVM, printSource_).print(module);
    return PassResult::noChange();
  }

private:
  bool printSource_ = true;
};
} // namespace
} // namespace svm::ir

SVM_REGISTER_MODULE_PASS("print-hir", svm::ir::PrintHIR)
SVM_REGISTER_MODULE_PASS("print-llvm-ir", svm::ir::PrintLLVMIR)
