/*
 * Copyright (c) 2022, Jorropo <jorropo.pgm@gmail.com>
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <AK/String.h>
#include <AK/Types.h>
#include <LibCrypto/Hash/HashFunction.h>
#include <AK/Endian.h>
#include <AK/SIMD.h>

namespace Crypto::Hash {

template<typename wordType, typename vectorType, size_t digestSize, const vectorType IV[2], const u8 sigmas[(sizeof(wordType) == 8) ? 12 : 10][16]>
class Blake2Compressable final: public HashFunction<sizeof(wordType)*16*8, digestSize*8, Digest<digestSize*8>> {
private:
    using hashParrent = HashFunction<sizeof(wordType)*16*8, digestSize*8, Digest<digestSize*8>>;
public:
    using hashParrent::update;
    using DigestType = hashParrent::DigestType;
private:
    constexpr static auto WordBits = sizeof(wordType)*8;
    constexpr static auto BlockSize = sizeof(wordType)*16;
    constexpr static auto Rounds = (WordBits == 64) ? 12 : 10;

    ALWAYS_INLINE wordType load_unaligned_le(const u8 data[sizeof(wordType)]) {
        wordType r;
        for (size_t i = 0; i != sizeof(wordType); i++) {
          r >>= 8;
          r |= data[i] << (sizeof(wordType) - 1) * 8;
        }
        return r;
    }

    ALWAYS_INLINE void ror(vectorType* out, vectorType in, u8 n)
    {
        // Take a value pointer to avoid ABI issues
        // If SIMD is disabled or SIMD registers are too small, trying to return
        // a vectorType by value, doesn't work.

        *out = (in >> n) | (in << (WordBits-n));
    }

    ALWAYS_INLINE void mix(u8 mix, vectorType vector[4], const wordType message[16], const u8 mix_sigma[16])
    {
      vectorType vmessage;
      /*
       * FIXME: Should use vpgatherdd and vpgatherdq on AVX2 cpus that supports it.
       * Or load up the message block in registers then shuffle with sigmas arround.
       * There is not enough registers without using AVX512 and is certainly slower.
       * With AVX512 I don't know if that would actually be faster than gathers.
       */
      for (size_t i = 0; i != 4; i++) {
        vmessage[i] = message[mix_sigma[2*i+mix+0]];
      }
  		vector[0] = vector[0] + vector[1] + vmessage;
  		ror(&vector[3], vector[3] ^ vector[0], 32);
  		vector[2] = vector[2] + vector[3];
  		ror(&vector[1], vector[1] ^ vector[2], 24);

      for (size_t i = 0; i != 4; i++) {
        vmessage[i] = message[mix_sigma[2*i+mix+1]];
      }
  		vector[0] = vector[0] + vector[1] + vmessage;
  		ror(&vector[3], vector[3] ^ vector[0], 16);
  		vector[2] = vector[2] + vector[3];
  		ror(&vector[1], vector[1] ^ vector[2], 63);
    }

    ALWAYS_INLINE void doShuffleX4(vectorType* out, vectorType in, u8 a, u8 b, u8 c, u8 d) {
      #if __has_builtin(__builtin_shufflevector)
        // This is only supported on clang
        *out = __builtin_shufflevector(in, in, a, b, c, d);

      #else
        // Hopefully the optimiser can figure this out correctly
        // should be trivial with the compile time known indexes we use
        (*out)[0] = in[a];
        (*out)[1] = in[b];
        (*out)[2] = in[c];
        (*out)[3] = in[d];
      #endif
    }

    ALWAYS_INLINE void round(u8 round, const wordType message[16], vectorType vector[4])
    {
      auto round_sigma = sigmas[round];
  		mix(0,vector, message, round_sigma);

      // No shuffling for A, it stays in place
      // Shuffling B
      doShuffleX4(&vector[1], vector[1], 1,2,3,0);
      // Shuffling C
      doShuffleX4(&vector[2], vector[2], 2,3,0,1);
      // Shuffling D
      doShuffleX4(&vector[3], vector[3], 3,0,1,2);

  		mix(4,vector, message, round_sigma);

      // No unshuffling for A, it stays in place
      // Unshuffling B
      doShuffleX4(&vector[1], vector[1], 3,0,1,2);
      // Unshuffling C
      doShuffleX4(&vector[2], vector[2], 2,3,0,1);
      // Unshuffling D
      doShuffleX4(&vector[3], vector[3], 1,2,3,0);
    }

    void compress_one_block(const u8* data, wordType increment)
    {
      m_metadata[0] += increment;
      m_metadata[1] += (m_metadata[0] < increment); // Handle two word addition in case of overflow

      vectorType vector[4];
      wordType message[16];

      for (size_t i = 0; i != 16; i++)
        message[i] = load_unaligned_le(data + i*sizeof(wordType));

      vector[0] = m_state[0];
      vector[1] = m_state[1];
      vector[2] = IV[0];
      vector[3] = IV[1] ^ m_metadata;

      for (size_t i = 0; i != Rounds; i++)
        round(i, message, vector);


      m_state[0] = m_state[0] ^ vector[0] ^ vector[2];
      m_state[1] = m_state[1] ^ vector[1] ^ vector[3];
    }

    vectorType m_state[2] {};
    // Pack the block_counter (2 low entries) and finisher (2 high entries) so the compiler can hopefully vectorise xoring it with the IVs
    vectorType m_metadata {};
    u8 m_outstanding_data_buffer[BlockSize] {};
    size_t m_outstanding_data_count { 0 };

public:
    Blake2Compressable()
    {
        reset();
    }

    virtual void update(const u8* data, size_t inlen) override
    {
        if (inlen == 0)
          return;

        if (m_outstanding_data_count > 0) {
          // Data to pad
          size_t total_data = m_outstanding_data_count + inlen;
          if (total_data < BlockSize) {
            // More data to buffer, but not enough to hash
            size_t buffer_offset = m_outstanding_data_count;
            m_outstanding_data_count = total_data;

            memcpy(m_outstanding_data_buffer+buffer_offset, data, inlen);
            return;
          }

          // hash the outstanding buffer
          size_t preHashSize = BlockSize - m_outstanding_data_count;
          memcpy(m_outstanding_data_buffer+m_outstanding_data_count, data, preHashSize);
          inlen -= preHashSize;
          m_outstanding_data_count = 0;
          compress_one_block(m_outstanding_data_buffer, BlockSize);
        }

        // Bulk hashing of data
        while (inlen >= BlockSize) {
          compress_one_block(data, BlockSize);
          data += BlockSize;
          inlen -= BlockSize;
        }

        // Save remaining data if any
        m_outstanding_data_count = inlen;
        memcpy(m_outstanding_data_buffer, data, inlen);
    }

    ALWAYS_INLINE virtual DigestType digest() override {
          // Zero-pad the remaining data.
          m_metadata[2] = -1;
          memset(m_outstanding_data_buffer, 0, BlockSize - m_outstanding_data_count);
          compress_one_block(m_outstanding_data_buffer, m_outstanding_data_count);

          DigestType result;
          for (size_t i = 0; i < digestSize; i++) {
            result.data[i] = (m_state[i/(sizeof(wordType)*4)][(i%sizeof(wordType)*4)/sizeof(wordType)] >> (i%sizeof(wordType))) & 255;
          }

          reset();
          return result;
    };
    virtual DigestType peek() override {
      auto other = *this;
      return other.digest();
    }

    ALWAYS_INLINE static DigestType hash(const u8* data, size_t length)
    {
        Blake2Compressable<wordType, vectorType, digestSize, IV, sigmas> h;
        h.update(data, length);
        return h.digest();
    }

    ALWAYS_INLINE static DigestType hash(const ByteBuffer& buffer) { return hash(buffer.data(), buffer.size()); }
    ALWAYS_INLINE static DigestType hash(StringView buffer) { return hash((const u8*)buffer.characters_without_null_termination(), buffer.length()); }

    virtual String class_name() const override
    {
        return String::formatted("BLAKE2{}-{}", (WordBits == 64) ? "b"sv : "s"sv, digestSize*8);
    }

    ALWAYS_INLINE virtual void reset() override
    {
        reset_shared_part(0);
    }

    void reset_shared_part(wordType keylen)
    {
        m_state[0] = IV[0];
        m_state[0][0] ^= 0x01010000 | (wordType)keylen << 8 | digestSize;
        m_state[1] = IV[1];
        m_metadata = m_metadata ^ m_metadata;
        m_outstanding_data_count = 0;
    }

    void reset_with_key(const u8* key, u8 keylen)
    {
        VERIFY(keylen <= digestSize);
        VERIFY(keylen == 0 || key != nullptr);

        reset_shared_part(keylen);

        if (keylen > 0) {
            u8 keyBlock[BlockSize];
            if (keylen < BlockSize) {
                // Not enough bytes, zeropad
                memcpy(keyBlock, key, keylen);
                memset(keyBlock+keylen, 0, BlockSize - keylen);
                key = keyBlock;
            }
            compress_one_block(key, BlockSize);
      }
    }
};

namespace BLAKE2_constants {
  constexpr static AK::SIMD::u32x4 blake2s_iv[2] = {
  	{0x6A09E667UL, 0xBB67AE85UL, 0x3C6EF372UL, 0xA54FF53AUL },
  	{0x510E527FUL, 0x9B05688CUL, 0x1F83D9ABUL, 0x5BE0CD19UL },
  };

  constexpr static u8 blake2s_sigma[10][16] = {
  	{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
  	{ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 },
  	{ 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 },
  	{ 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 },
  	{ 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 },
  	{ 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 },
  	{ 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 },
  	{ 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 },
  	{ 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 },
  	{ 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 },
  };
}

using BLAKE2s_256 = Blake2Compressable<u32, AK::SIMD::u32x4, 32, BLAKE2_constants::blake2s_iv, BLAKE2_constants::blake2s_sigma>;

}
