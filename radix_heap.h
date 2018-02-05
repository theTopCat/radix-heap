#include <algorithm>
#include <array>
#include <cassert>
#include <climits>
#include <cstdint>
#include <limits>
#include <type_traits>
#include <utility>
#include <vector>
#include <tuple>

namespace radix_heap {
namespace internal {
template<bool Is64bit> class find_impl;

template<>
class find_impl<false> {
 public:
  static inline constexpr int find_bucket(uint32_t x, uint32_t last) {
    return x == last ? 0 : 32 - __builtin_clz(x ^ last);
  }
  static inline constexpr int find_first_non_empty(uint32_t x) {
    return __builtin_ffs(x);
  }
};

template<>
class find_impl<true> {
 public:
  static inline constexpr int find_bucket(uint64_t x, uint64_t last) {
    return x == last ? 0 : 64 - __builtin_clzll(x ^ last);
  }
  static inline constexpr int find_first_non_empty(uint64_t x) {
    return __builtin_ffsll(x);
  }
};

template<typename T>
inline constexpr int find_bucket(T x, T last) {
  return find_impl<sizeof(T) == 8>::find_bucket(x, last);
}

template<typename T>
inline constexpr int find_first_non_empty(T x) {
  return find_impl<sizeof(T) == 8>::find_first_non_empty(x);
}

template<typename KeyType, bool IsSigned> class encoder_impl_integer;

template<typename KeyType>
class encoder_impl_integer<KeyType, false> {
 public:
  typedef KeyType key_type;
  typedef KeyType unsigned_key_type;

  inline static constexpr unsigned_key_type encode(key_type x) {
    return x;
  }

  inline static constexpr key_type decode(unsigned_key_type x) {
    return x;
  }
};

template<typename KeyType>
class encoder_impl_integer<KeyType, true> {
 public:
  typedef KeyType key_type;
  typedef typename std::make_unsigned<KeyType>::type unsigned_key_type;

  inline static constexpr unsigned_key_type encode(key_type x) {
    return static_cast<unsigned_key_type>(x) ^
        (unsigned_key_type(1) << unsigned_key_type(std::numeric_limits<unsigned_key_type>::digits - 1));
  }

  inline static constexpr key_type decode(unsigned_key_type x) {
    return static_cast<key_type>
        (x ^ (unsigned_key_type(1) << (std::numeric_limits<unsigned_key_type>::digits - 1)));
  }
};

template<typename KeyType, typename UnsignedKeyType>
class encoder_impl_decimal {
public:
  typedef KeyType key_type;
  typedef UnsignedKeyType unsigned_key_type;

  inline static constexpr unsigned_key_type encode(key_type x) {
    return raw_cast<key_type, unsigned_key_type>(x) ^
        ((-(raw_cast<key_type, unsigned_key_type>(x) >> (std::numeric_limits<unsigned_key_type>::digits - 1))) |
         (unsigned_key_type(1) << (std::numeric_limits<unsigned_key_type>::digits - 1)));
  }

  inline static constexpr key_type decode(unsigned_key_type x) {
    return raw_cast<unsigned_key_type, key_type>
        (x ^ (((x >> (std::numeric_limits<unsigned_key_type>::digits - 1)) - 1) |
              (unsigned_key_type(1) << (std::numeric_limits<unsigned_key_type>::digits - 1))));
  }

 private:
  template<typename T, typename U>
  union raw_cast {
   public:
    inline constexpr raw_cast(T t) : t_(t) {}
    inline operator U() const { return u_; }

   private:
    T t_;
    U u_;
  };
};

template<typename KeyType>
class encoder : public encoder_impl_integer<KeyType, std::is_signed<KeyType>::value> {};
template<>
class encoder<float> : public encoder_impl_decimal<float, uint32_t> {};
template<>
class encoder<double> : public encoder_impl_decimal<double, uint64_t> {};

template <typename UIntDecType>
class bucket_flags {
 public:
  typedef UIntDecType unsigned_key_type;

  inline bucket_flags() {clear();}

  inline void set_empty(size_t bucket) {
    assert(bucket <= num_buckets);

    flags_ &= ~((unsigned_key_type(1) << (bucket - 1)) & -(!!bucket));
  }

  inline void set_non_empty(unsigned int bucket) {
    assert(bucket <= num_buckets);

    flags_ |= ((unsigned_key_type(1) << (bucket - 1)) & -(!!bucket));
  }

  inline void clear() { flags_ = 0; }

  inline int find_first_non_empty() const {
    return internal::find_first_non_empty(flags_);
  }

  void swap(bucket_flags& a) {
    std::swap(flags_, a.flags_);
  }

private:
  unsigned_key_type flags_;
  enum {
      num_buckets = (sizeof(UIntDecType) == 8 ? 64 : 32)
  };
};
}  // namespace internal

template<typename KeyType, typename EncoderType = internal::encoder<KeyType> >
class radix_heap {
 public:
  typedef KeyType key_type;
  typedef EncoderType encoder_type;
  typedef typename encoder_type::unsigned_key_type unsigned_key_type;

  radix_heap() : size_(0), last_(), buckets_() {
    buckets_min_.fill(std::numeric_limits<unsigned_key_type>::max());
  }

  void push(key_type key) {
    const unsigned_key_type x = encoder_type::encode(key);
    assert(last_ <= x);
    ++size_;
    const size_t k = internal::find_bucket(x, last_);
    buckets_[k].emplace_back(x);
    bucket_flags_.set_non_empty(k);
    buckets_min_[k] = std::min(buckets_min_[k], x);
  }

  key_type top() {
    pull();
    return encoder_type::decode(last_);
  }

  key_type min() const {
    assert(size_ > 0);
    const int i = bucket_flags_.find_first_non_empty() & -(buckets_[0].empty());
    return encoder_type::decode(buckets_min_[i]);
  }

  key_type next() const
  {
    //assert(size_ > 0);
    if (!buckets_[0].empty())
    {
      const int i = bucket_flags_.find_first_non_empty() & -(!(buckets_[0].size() > 1));
      return encoder_type::decode(buckets_min_[i]);
    } else {
      int i = bucket_flags_.find_first_non_empty(), iEnd = 2;
      unsigned_key_type ret = std::numeric_limits<unsigned_key_type>::max();
      const unsigned_key_type min = buckets_min_[i];
      for ( auto it = (buckets_[i].cbegin()), itEnd = buckets_[i].cend(); it != itEnd; ++it) {
          const unsigned_key_type next = (*it);
          if ( min == next && !(--iEnd) ) return encoder_type::decode(min);
          if ( next > min && next < ret ) { ret = next; }
      }
      if (ret < std::numeric_limits<unsigned_key_type>::max())
            return encoder_type::decode(ret);//success

      for (++i, iEnd = static_cast<int>(buckets_.size()); i < iEnd; ++i)
      {
        if (!buckets_[i].empty()) {
          return encoder_type::decode(buckets_min_[i]);//success
        }
      }
      return encoder_type::decode(min);//failed
    }
  }

  void pop() {
    pull();
    buckets_[0].pop_back();
    --size_;
  }

  size_t size() const {
    return size_;
  }

  bool empty() const {
    return !size_;
  }

  void clear() {
    size_ = 0;
    last_ = key_type();
    for (auto &b : buckets_) b.clear();
    bucket_flags_.clear();
    buckets_min_.fill(std::numeric_limits<unsigned_key_type>::max());
  }

  void swap(radix_heap<KeyType, EncoderType> &a) {
    std::swap(size_, a.size_);
    std::swap(last_, a.last_);
    buckets_.swap(a.buckets_);
    buckets_min_.swap(a.buckets_min_);
    bucket_flags_.swap(a.bucket_flags_);
  }

 private:
  size_t size_;
  unsigned_key_type last_;
  std::array<std::vector<unsigned_key_type>,
             std::numeric_limits<unsigned_key_type>::digits + 1> buckets_;
  std::array<unsigned_key_type,
             std::numeric_limits<unsigned_key_type>::digits + 1> buckets_min_;

  internal::bucket_flags<unsigned_key_type> bucket_flags_;

  void pull() {
    assert(size_ > 0);
    if (!buckets_[0].empty()) return;

    const size_t i = bucket_flags_.find_first_non_empty();
    last_ = buckets_min_[i];
    buckets_min_[0] = std::numeric_limits<unsigned_key_type>::max();

    for (unsigned_key_type x : buckets_[i]) {
      const size_t k = internal::find_bucket(x, last_);
      buckets_[k].emplace_back(x);
      bucket_flags_.set_non_empty(k);
      buckets_min_[k] = std::min(buckets_min_[k], x);
    }

    buckets_[i].clear();
    bucket_flags_.set_empty(i);
    buckets_min_[i] = std::numeric_limits<unsigned_key_type>::max();
  }
};

template<typename KeyType, typename ValueType, const bool __FIFO__ = false , typename EncoderType = internal::encoder<KeyType> >
class pair_radix_heap {
 public:
  typedef KeyType key_type;
  typedef ValueType value_type;
  typedef EncoderType encoder_type;
  typedef typename encoder_type::unsigned_key_type unsigned_key_type;
  typedef typename std::vector<std::pair<key_type, value_type> >::const_iterator value_iterator;

  pair_radix_heap() : size_(0), last_(), buckets_() {
    buckets_min_.fill(std::numeric_limits<unsigned_key_type>::max());
  }

  void push(key_type key, const value_type &value) {
    const unsigned_key_type x = encoder_type::encode(key);
    assert(last_ <= x);
    ++size_;
    const size_t k = internal::find_bucket(x, last_);
    buckets_[k].emplace_back(x, value);
    bucket_flags_.set_non_empty(k);
    buckets_min_[k] = std::min(buckets_min_[k], x);
  }

  void push(key_type key, value_type &&value) {
    const unsigned_key_type x = encoder_type::encode(key);
    assert(last_ <= x);
    ++size_;
    const size_t k = internal::find_bucket(x, last_);
    buckets_[k].emplace_back(x, std::move(value));
    bucket_flags_.set_non_empty(k);
    buckets_min_[k] = std::min(buckets_min_[k], x);
  }

  template <class... Args>
  void emplace(key_type key, Args&&... args) {
    const unsigned_key_type x = encoder_type::encode(key);
    assert(last_ <= x);
    ++size_;
    const size_t k = internal::find_bucket(x, last_);
    buckets_[k].emplace_back(std::piecewise_construct,
                             std::forward_as_tuple(x), std::forward_as_tuple(args...));
    bucket_flags_.set_non_empty(k);
    buckets_min_[k] = std::min(buckets_min_[k], x);
  }

  key_type min_key() const {
    assert(size_ > 0);

    const int i = bucket_flags_.find_first_non_empty() & -(buckets_[0].empty());
    return encoder_type::decode(buckets_min_[i]);
  }

  key_type top_key() {
    pull();
    return encoder_type::decode(last_);
  }

  key_type next_key() const
  {
    //assert(size_ > 0);
    if (!buckets_[0].empty())
    {
      const int i = bucket_flags_.find_first_non_empty() & -(!(buckets_[0].size() > 1));
      return encoder_type::decode(buckets_min_[i]);
    } else {
      int i = bucket_flags_.find_first_non_empty(), iEnd = 2;
      unsigned_key_type ret = std::numeric_limits<unsigned_key_type>::max();
      const unsigned_key_type min = buckets_min_[i];
      for ( auto it = (buckets_[i].cbegin()), itEnd = buckets_[i].cend(); it != itEnd; ++it) {
          const unsigned_key_type next = (*it).first;
          if ( min == next && !(--iEnd) ) return encoder_type::decode(min);
          if ( next > min && next < ret ) { ret = next; }
      }
      if ( ret < std::numeric_limits<unsigned_key_type>::max())
            return encoder_type::decode(ret);//success

      for (++i,iEnd = static_cast<int>(buckets_.size()); i < iEnd; ++i)
      {
        if (!buckets_[i].empty()) {
          return encoder_type::decode(buckets_min_[i]);//success
        }
      }
      return encoder_type::decode(min);//failed
    }
  }

  value_type &top_value() {
    pull();
    return (__FIFO__ ? buckets_[0].front().second : buckets_[0].back().second );
  }

  std::tuple<value_iterator, value_iterator> top_values() {
    pull();
    return std::forward_as_tuple(buckets_[0].cbegin(), buckets_[0].cend());
  }

  void pop() {
    pull();
    if (!__FIFO__)
      buckets_[0].pop_back();
    else
      buckets_[0].erase(buckets_[0].begin());
    --size_;
  }

  template <class UnaryPredicate>
  void remove_if( UnaryPredicate p )
  {
    for (size_t i = 0; i < buckets_.size(); ++i)
    {
      if (!buckets_[i].empty()) {
        const size_t size_old = size_;
        bool recalc_min = false;
        for ( auto it = buckets_[i].begin(); it != buckets_[i].end();) {
          if ( p( (*it).second ) ) {
              if (!recalc_min && buckets_min_[i] == (*it).first) recalc_min = true;
              it = buckets_[i].erase(it);
              --size_;
          } else ++it;
        }
        if (size_old != size_)
        {
          if (buckets_[i].empty()) {
            bucket_flags_.set_empty(i);
            buckets_min_[i] = std::numeric_limits<unsigned_key_type>::max();
          } else {
            if (recalc_min)
            	for (auto it = buckets_[i].begin(), itEnd = buckets_[i].end(); it != itEnd; ++it)
                buckets_min_[i] = std::min(buckets_min_[i], (*it).first);
          }
        }
      }
    }
    if (size_) pull();
  }

  size_t size() const {
    return size_;
  }

  bool empty() const {
    return !size_;
  }

  void clear() {
    size_ = 0;
    last_ = key_type();
    for (auto &b : buckets_) b.clear();
    buckets_min_.fill(std::numeric_limits<unsigned_key_type>::max());
    bucket_flags_.clear();
  }

  void swap(pair_radix_heap<KeyType, ValueType, __FIFO__, EncoderType> &a) {
    std::swap(size_, a.size_);
    std::swap(last_, a.last_);
    bucket_flags_.swap(a.bucket_flags_);
    buckets_.swap(a.buckets_);
    buckets_min_.swap(a.buckets_min_);
  }

 private:
  size_t size_;
  unsigned_key_type last_;
  std::array<std::vector<std::pair<unsigned_key_type, value_type>>,
             std::numeric_limits<unsigned_key_type>::digits + 1> buckets_;
  std::array<unsigned_key_type,
             std::numeric_limits<unsigned_key_type>::digits + 1> buckets_min_;

  internal::bucket_flags<unsigned_key_type> bucket_flags_;

  void pull() {
    assert(size_ > 0);
    if (!buckets_[0].empty()) return;

    const size_t i = bucket_flags_.find_first_non_empty();
    last_ = buckets_min_[i];
    buckets_min_[0] = std::numeric_limits<unsigned_key_type>::max();

    for (size_t j = 0, jEnd = buckets_[i].size(); j < jEnd; ++j) {
      const unsigned_key_type x = buckets_[i][j].first;
      const size_t k = internal::find_bucket(x, last_);
      buckets_[k].emplace_back(std::move(buckets_[i][j]));
      bucket_flags_.set_non_empty(k);
      buckets_min_[k] = std::min(buckets_min_[k], x);
    }

    buckets_[i].clear();
    bucket_flags_.set_empty(i);
    buckets_min_[i] = std::numeric_limits<unsigned_key_type>::max();
  }
};
}  // namespace radix_heap
