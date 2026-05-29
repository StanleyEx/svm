#ifndef ARENA_H
#define ARENA_H

#include "Utils.h"

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <new>
#include <utility>
#include <vector>

class Arena {
private:
  static constexpr usize kAlignment = 16;
  static constexpr usize kMinChunkSize = 8192;     // 8KB
  static constexpr usize kResetPreserveChunks = 4; // reset时保留的块数量

  struct Chunk {
    Chunk *next = nullptr;
    usize capacity = 0; // 头部之后的可用内存大小
    usize offset = 0;   // 数据部分的下一个空闲位置

    byte *data() noexcept { return reinterpret_cast<byte *>(this + 1); }

    const byte *data() const noexcept {
      return reinterpret_cast<const byte *>(this + 1);
    }

    usize remaining() const noexcept { return capacity - offset; }

    static Chunk *create(usize minCapacity, usize alignment) {
      assert(alignment > 0 && (alignment & (alignment - 1)) == 0);

      const usize allocSize = sizeof(Chunk) + minCapacity + alignment;
      void *memory =
          ::operator new(allocSize, std::align_val_t{alignof(Chunk)});

      auto *chunk = new (memory) Chunk();
      chunk->capacity = allocSize - sizeof(Chunk);
      return chunk;
    }
  };

public:
  explicit Arena(usize initialCapacity = 0) {
    const usize capacity =
        initialCapacity > kMinChunkSize ? initialCapacity : kMinChunkSize;
    head_ = current_ = Chunk::create(capacity, kAlignment);
  }
  ~Arena() { destroy(); }

  // 不可拷贝
  Arena(const Arena &) = delete;
  Arena &operator=(const Arena &) = delete;

  // 可移动赋值
  Arena(Arena &&other) noexcept
      : head_(other.head_), current_(other.current_),
        totalAllocated_(other.totalAllocated_),
        destructors_(std::move(other.destructors_)) {
    other.head_ = other.current_ = nullptr;
    other.totalAllocated_ = 0;
  }

  Arena &operator=(Arena &&other) noexcept {
    if (this != &other) {
      destroy();
      head_ = other.head_;
      current_ = other.current_;
      totalAllocated_ = other.totalAllocated_;
      destructors_ = std::move(other.destructors_);
      other.head_ = other.current_ = nullptr;
      other.totalAllocated_ = 0;
    }
    return *this;
  }

  void *allocate(usize size, usize alignment = kAlignment) {
    assert(current_ && alignment > 0);
    assert(alignment > 0 && (alignment & (alignment - 1)) == 0);

    if (size == 0)
      size = 1; // 避免分配0字节导致问题

    // 先尝试在当前块中分配
    auto base =
        reinterpret_cast<std::uintptr_t>(current_->data() + current_->offset);
    auto alignedAddress = alignForward(base, alignment);
    auto padding = alignedAddress - base;

    if (current_->offset + padding + size <= current_->capacity) {
      current_->offset += padding + size;
      totalAllocated_ += size;
      return reinterpret_cast<void *>(alignedAddress);
    }

    // 尝试复用当前块后可能存在的下一个块
    if (current_->next) {
      Chunk *nextChunk = current_->next;
      nextChunk->offset = 0;
      base = reinterpret_cast<std::uintptr_t>(nextChunk->data());
      alignedAddress = alignForward(base, alignment);
      padding = alignedAddress - base;
      if (padding + size <= nextChunk->capacity) {
        current_ = nextChunk;
        current_->offset = padding + size;
        totalAllocated_ += size;
        return reinterpret_cast<void *>(alignedAddress);
      }
    }

    // 分配新块
    const usize growth = (current_->capacity + sizeof(Chunk)) * 2;
    const usize newChunkSize = growth > size ? growth : size;

    Chunk *newChunk = Chunk::create(newChunkSize, alignment);

    newChunk->next = current_->next;
    current_->next = newChunk;
    current_ = newChunk;

    base = reinterpret_cast<std::uintptr_t>(newChunk->data());
    alignedAddress = alignForward(base, alignment);
    padding = alignedAddress - base;
    newChunk->offset = padding + size;
    totalAllocated_ += size;
    return reinterpret_cast<void *>(alignedAddress);
  }

  template <typename T, typename... Args> T *create(Args &&...args) {
    void *memory = allocate(sizeof(T), alignof(T));
    T *obj = new (memory) T(std::forward<Args>(args)...);
    if constexpr (!std::is_trivially_destructible_v<T>) {
      try {
        destructors_.emplace_back([obj]() { obj->~T(); });
      } catch (...) {
        obj->~T();
        throw;
      }
    }
    return obj;
  }

  template <typename T> T *createArray(usize count) {
    assert(count > 0);
    void *memory = allocate(sizeof(T) * count, alignof(T));
    T *array = static_cast<T *>(memory);
    usize constructed = 0;
    try {
      for (; constructed < count; ++constructed) {
        new (array + constructed) T();
      }
    } catch (...) {
      for (usize j = constructed; j > 0; --j) {
        array[j - 1].~T();
      }
      throw;
    }
    if constexpr (!std::is_trivially_destructible_v<T>) {
      try {
        destructors_.emplace_back([array, count]() {
          for (usize i = count; i > 0; --i) {
            array[i - 1].~T();
          }
        });
      } catch (...) {
        for (usize i = count; i > 0; --i) {
          array[i - 1].~T();
        }
        throw;
      }
    }
    return array;
  }

  template <typename T>
  T **storeVectorToArena(const std::vector<T *> &vector,
                         u64 &sizeOut) noexcept {
    sizeOut = vector.size();
    if (vector.empty())
      return nullptr;
    T **buffer = allocate(sizeof(T *) * vector.size(), alignof(T *));
    std::memcpy(buffer, vector.data(), sizeof(T *) * vector.size());
    return buffer;
  }

  char *duplicateString(const char *str) noexcept {
    if (!str) {
      return nullptr;
    }
    return duplicateString(str, std::strlen(str));
  }

  char *duplicateString(const char *str, size_t len) noexcept {
    assert(str != nullptr);
    char *copy = static_cast<char *>(allocate(len + 1, alignof(char)));
    std::memcpy(copy, str, len);
    copy[len] = '\0';
    return copy;
  }

  struct Mark {
    Chunk *chunk = nullptr;
    usize offset = 0;
    usize destructorCount = 0;
    usize totalAllocatedAtMark = 0;
  };

  [[nodiscard]] Mark mark() const noexcept {
    return {current_, current_ ? current_->offset : 0, destructors_.size(),
            totalAllocated_};
  }

  void rewind(const Mark &mark) noexcept {
    assert(current_ && mark.chunk);

    while (destructors_.size() > mark.destructorCount) {
      auto &dtor = destructors_.back();
      dtor();
      destructors_.pop_back();
    }
    current_ = mark.chunk;
    current_->offset = mark.offset;
    totalAllocated_ = mark.totalAllocatedAtMark;

    for (Chunk *chunk = current_->next; chunk; chunk = chunk->next)
      chunk->offset = 0;
  }

  // RAII作用域管理器，离开作用域时自动回滚到标记位置
  class Scope {
  public:
    explicit Scope(Arena &arena) : arena_(arena), mark_(arena.mark()) {}
    ~Scope() { arena_.rewind(mark_); }

    Scope(const Scope &) = delete;
    Scope &operator=(const Scope &) = delete;
    Scope(Scope &&) = delete;
    Scope &operator=(Scope &&) = delete;

    [[nodiscard]] Mark mark() const noexcept { return mark_; }

  private:
    Arena &arena_;
    Mark mark_;
  };

  void reset() noexcept {
    if (!head_) {
      return;
    }

    for (auto it = destructors_.rbegin(); it != destructors_.rend(); ++it) {
      (*it)();
    }
    destructors_.clear();
    head_->offset = 0;
    usize preserved = kResetPreserveChunks;
    Chunk *tail = head_;
    while (tail->next && preserved > 1) {
      tail = tail->next;
      tail->offset = 0;
      --preserved;
    }
    freeChain(tail->next);
    tail->next = nullptr;
    current_ = head_;
    totalAllocated_ = 0;
  }

  [[nodiscard]] usize totalAllocated() const noexcept {
    return totalAllocated_;
  }

  [[nodiscard]] usize totalReserved() const noexcept {
    usize total = 0;
    for (Chunk *chunk = head_; chunk; chunk = chunk->next) {
      total += chunk->capacity;
    }
    return total;
  }

private:
  static constexpr uintptr_t alignForward(uintptr_t size, uintptr_t alignment) {
    return (size + alignment - 1) & ~(alignment - 1);
  }

  static void freeChain(Chunk *head) noexcept {
    while (head) {
      auto *next = head->next;
      head->~Chunk();
      ::operator delete(head, std::align_val_t{alignof(Chunk)});
      head = next;
    }
  }

  void destroy() noexcept {
    for (auto it = destructors_.rbegin(); it != destructors_.rend(); ++it) {
      (*it)();
    }
    destructors_.clear();
    freeChain(head_);
    head_ = current_ = nullptr;
    totalAllocated_ = 0;
  }

  Chunk *head_ = nullptr;
  Chunk *current_ = nullptr;
  usize totalAllocated_ = 0;
  std::vector<std::function<void()>> destructors_;
};

#endif // ARENA_H