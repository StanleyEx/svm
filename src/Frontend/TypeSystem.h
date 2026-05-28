#ifndef TYPESYSTEM_H
#define TYPESYSTEM_H

#include "Utils/Arena.h"
#include "Utils/Types.h"

#include <unordered_map>

namespace svm {
enum class TypeKind : u8 {
  Int,
  Float,
  Void,

  Array,
  AnyDimArray, // 维数未指定的数组 用于函数参数
  Pointer,
  Function
};

[[maybe_unused]] static const char *typeKindToString(TypeKind type) {
  switch (type) {
  case TypeKind::Int:
    return "int";
  case TypeKind::Float:
    return "float";
  case TypeKind::Void:
    return "void";
  case TypeKind::Array:
    return "array";
  case TypeKind::AnyDimArray:
    return "array[]";
  case TypeKind::Pointer:
    return "pointer";
  case TypeKind::Function:
    return "function";
  default:
    return "<ErrorType>";
  }
}

class Type {
public:
  explicit Type(TypeKind kind) : kind_(kind) {}
  TypeKind getKind() const noexcept { return kind_; }

  static bool classof(const Type *) noexcept { return true; }

private:
  TypeKind kind_;
};

class IntType final : public Type {
public:
  explicit IntType() noexcept : Type(TypeKind::Int) {}
  static bool classof(const Type *type) noexcept {
    return type->getKind() == TypeKind::Int;
  }
};

class FloatType final : public Type {
public:
  FloatType() noexcept : Type(TypeKind::Float) {}
  static bool classof(const Type *type) noexcept {
    return type->getKind() == TypeKind::Float;
  }
};

class VoidType final : public Type {
public:
  VoidType() noexcept : Type(TypeKind::Void) {}
  static bool classof(const Type *type) noexcept {
    return type->getKind() == TypeKind::Void;
  }
};

class ArrayType final : public Type {
public:
  Type *elementType;
  const i32 *dims;
  u32 dimCount;

  ArrayType(Type *elementType, const i32 *dims, u32 dimCount) noexcept
      : Type(TypeKind::Array), elementType(elementType), dims(dims),
        dimCount(dimCount) {}

  u64 totalSize() const noexcept {
    u64 size = 1;
    for (u32 i = 0; i < dimCount; i++) {
      size *= dims[i];
    }
    return size;
  }

  static bool classof(const Type *type) noexcept {
    return type->getKind() == TypeKind::Array;
  }
};

class AnyDimArrayType final : public Type {
public:
  Type *elementType;

  AnyDimArrayType(Type *elementType) noexcept
      : Type(TypeKind::AnyDimArray), elementType(elementType) {}

  static bool classof(const Type *type) noexcept {
    return type->getKind() == TypeKind::AnyDimArray;
  }
};

class PointerType final : public Type {
public:
  Type *pointee; // 标量 / ArrayType / AnyDimArrayType

  PointerType(Type *pointee) noexcept
      : Type(TypeKind::Pointer), pointee(pointee) {}

  static bool classof(const Type *type) noexcept {
    return type->getKind() == TypeKind::Pointer;
  }
};

class FunctionType final : public Type {
public:
  Type *returnType;
  Type **paramTypes;
  u32 paramCount;
  bool isVariadic;

  FunctionType(Type *returnType, Type **paramTypes, u32 paramCount,
               bool isVariadic) noexcept
      : Type(TypeKind::Function), returnType(returnType),
        paramTypes(paramTypes), paramCount(paramCount), isVariadic(isVariadic) {
  }

  static bool classof(const Type *type) noexcept {
    return type->getKind() == TypeKind::Function;
  }
};

inline bool isScalarType(Type *type) noexcept {
  return type && (type->getKind() == TypeKind::Int ||
                  type->getKind() == TypeKind::Float);
}

// TypeContext 管理各种类型的创建和缓存
class TypeContext {
public:
  explicit TypeContext(Arena &arena) noexcept
      : arena_(arena), intType_(arena.create<IntType>()),
        floatType_(arena.create<FloatType>()),
        voidType_(arena.create<VoidType>()) {}

  TypeContext(const TypeContext &) = delete;
  TypeContext &operator=(const TypeContext &) = delete;

  IntType *getIntType() noexcept { return intType_; }
  FloatType *getFloatType() noexcept { return floatType_; }
  VoidType *getVoidType() noexcept { return voidType_; }

  ArrayType *getArrayType(Type *elementType, const i32 *dims,
                          u32 dimCount) noexcept {
    assert(isScalarType(elementType));
    assert(dimCount > 0);

    ArrayKey key{elementType, dims, dimCount};

    auto it = arrayMap_.find(key);
    if (it != arrayMap_.end())
      return it->second;

    i32 *storedDims = arena_.createArray<i32>(dimCount);
    std::memcpy(storedDims, dims, sizeof(i32) * dimCount);
    ArrayType *arrayType =
        arena_.create<ArrayType>(elementType, storedDims, dimCount);
    arrayMap_.insert({key, arrayType});

    return arrayType;
  }

  AnyDimArrayType *getAnyDimArrayType(Type *elementType) noexcept {
    assert(isScalarType(elementType));

    auto it = anyDimArrayMap_.find(elementType);
    if (it != anyDimArrayMap_.end())
      return it->second;

    AnyDimArrayType *anyDimArrayType =
        arena_.create<AnyDimArrayType>(elementType);
    anyDimArrayMap_.insert({elementType, anyDimArrayType});

    return anyDimArrayType;
  }

  PointerType *getPointerType(Type *pointee) noexcept {
    assert(pointee);
    assert(isScalarType(pointee) || pointee->getKind() == TypeKind::Array ||
           pointee->getKind() == TypeKind::AnyDimArray);

    auto it = pointerMap_.find(pointee);
    if (it != pointerMap_.end())
      return it->second;

    PointerType *pointerType = arena_.create<PointerType>(pointee);
    pointerMap_.insert({pointee, pointerType});

    return pointerType;
  }

  FunctionType *getFunctionType(Type *returnType, Type **paramTypes,
                                u32 paramCount, bool isVariadic) noexcept {
    assert(returnType);

    FuncKey key{returnType, paramTypes, paramCount, isVariadic};

    auto it = funcMap_.find(key);
    if (it != funcMap_.end())
      return it->second;

    Type **storedParamTypes =
        arena_.createArray<Type *>(paramCount ? paramCount : 1);
    std::memcpy(storedParamTypes, paramTypes, sizeof(Type *) * paramCount);
    FunctionType *funcType = arena_.create<FunctionType>(
        returnType, storedParamTypes, paramCount, isVariadic);
    funcMap_.insert({key, funcType});

    return funcType;
  }

private:
  Arena &arena_;
  IntType *intType_;
  FloatType *floatType_;
  VoidType *voidType_;

  struct ArrayKey {
    Type *elementType = nullptr;
    const i32 *dims = nullptr;
    u32 dimCount = 0;

    bool operator==(const ArrayKey &other) const noexcept {
      return elementType == other.elementType && dimCount == other.dimCount &&
             std::memcmp(dims, other.dims, sizeof(i32) * dimCount) == 0;
    }
  };

  struct ArrayKeyHash {
    std::size_t operator()(const ArrayKey &key) const noexcept {
      std::size_t hash = std::hash<Type *>()(key.elementType);
      for (u32 i = 0; i < key.dimCount; i++) {
        hash ^= std::hash<i32>()(key.dims[i]);
      }
      return hash;
    }
  };

  struct FuncKey {
    Type *returnType = nullptr;
    Type **paramTypes = nullptr;
    u32 paramCount = 0;
    bool isVariadic = false;

    bool operator==(const FuncKey &other) const noexcept {
      return returnType == other.returnType && paramCount == other.paramCount &&
             isVariadic == other.isVariadic &&
             std::memcmp(paramTypes, other.paramTypes,
                         sizeof(Type *) * paramCount) == 0;
    }
  };

  struct FuncKeyHash {
    std::size_t operator()(const FuncKey &key) const noexcept {
      std::size_t hash = std::hash<Type *>()(key.returnType);
      for (u32 i = 0; i < key.paramCount; i++) {
        hash ^= std::hash<Type *>()(key.paramTypes[i]);
      }
      hash ^= std::hash<bool>()(key.isVariadic);
      return hash;
    }
  };

  std::unordered_map<ArrayKey, ArrayType *, ArrayKeyHash> arrayMap_;
  std::unordered_map<Type *, AnyDimArrayType *> anyDimArrayMap_;
  std::unordered_map<Type *, PointerType *> pointerMap_;
  std::unordered_map<FuncKey, FunctionType *, FuncKeyHash> funcMap_;
};
} // namespace svm

#endif // TYPESYSTEM_H
