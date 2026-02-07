/* Standalone SHA-256 implementation for the dynamic linker.
   Copyright (C) 2024 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <https://www.gnu.org/licenses/>.  */

#ifndef _DL_SHA256_H
#define _DL_SHA256_H

#include <stdint.h>
#include <stddef.h>
#include <string.h>

#define SHA256_BLOCK_SIZE  64
#define SHA256_DIGEST_SIZE 32

struct sha256_ctx
{
  uint32_t state[8];
  uint64_t count;
  uint8_t buf[SHA256_BLOCK_SIZE];
};

static const uint32_t _sha256_k[64] =
{
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

static inline uint32_t
_sha256_rotr (uint32_t x, unsigned int n)
{
  return (x >> n) | (x << (32 - n));
}

static inline uint32_t
_sha256_ch (uint32_t x, uint32_t y, uint32_t z)
{
  return (x & y) ^ (~x & z);
}

static inline uint32_t
_sha256_maj (uint32_t x, uint32_t y, uint32_t z)
{
  return (x & y) ^ (x & z) ^ (y & z);
}

static inline uint32_t
_sha256_sigma0 (uint32_t x)
{
  return _sha256_rotr (x, 2) ^ _sha256_rotr (x, 13) ^ _sha256_rotr (x, 22);
}

static inline uint32_t
_sha256_sigma1 (uint32_t x)
{
  return _sha256_rotr (x, 6) ^ _sha256_rotr (x, 11) ^ _sha256_rotr (x, 25);
}

static inline uint32_t
_sha256_gamma0 (uint32_t x)
{
  return _sha256_rotr (x, 7) ^ _sha256_rotr (x, 18) ^ (x >> 3);
}

static inline uint32_t
_sha256_gamma1 (uint32_t x)
{
  return _sha256_rotr (x, 17) ^ _sha256_rotr (x, 19) ^ (x >> 10);
}

static inline uint32_t
_sha256_load_be32 (const uint8_t *p)
{
  return ((uint32_t) p[0] << 24) | ((uint32_t) p[1] << 16)
	 | ((uint32_t) p[2] << 8) | (uint32_t) p[3];
}

static inline void
_sha256_store_be32 (uint8_t *p, uint32_t v)
{
  p[0] = (uint8_t) (v >> 24);
  p[1] = (uint8_t) (v >> 16);
  p[2] = (uint8_t) (v >> 8);
  p[3] = (uint8_t) v;
}

static void
_sha256_transform (uint32_t state[8], const uint8_t block[SHA256_BLOCK_SIZE])
{
  uint32_t w[64];
  uint32_t a, b, c, d, e, f, g, h;

  for (int i = 0; i < 16; i++)
    w[i] = _sha256_load_be32 (block + i * 4);
  for (int i = 16; i < 64; i++)
    w[i] = _sha256_gamma1 (w[i - 2]) + w[i - 7]
	   + _sha256_gamma0 (w[i - 15]) + w[i - 16];

  a = state[0]; b = state[1]; c = state[2]; d = state[3];
  e = state[4]; f = state[5]; g = state[6]; h = state[7];

  for (int i = 0; i < 64; i++)
    {
      uint32_t t1 = h + _sha256_sigma1 (e) + _sha256_ch (e, f, g)
		     + _sha256_k[i] + w[i];
      uint32_t t2 = _sha256_sigma0 (a) + _sha256_maj (a, b, c);
      h = g; g = f; f = e; e = d + t1;
      d = c; c = b; b = a; a = t1 + t2;
    }

  state[0] += a; state[1] += b; state[2] += c; state[3] += d;
  state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

static inline void
sha256_init (struct sha256_ctx *ctx)
{
  ctx->state[0] = 0x6a09e667;
  ctx->state[1] = 0xbb67ae85;
  ctx->state[2] = 0x3c6ef372;
  ctx->state[3] = 0xa54ff53a;
  ctx->state[4] = 0x510e527f;
  ctx->state[5] = 0x9b05688c;
  ctx->state[6] = 0x1f83d9ab;
  ctx->state[7] = 0x5be0cd19;
  ctx->count = 0;
}

static void
sha256_update (struct sha256_ctx *ctx, const void *data, size_t len)
{
  const uint8_t *p = (const uint8_t *) data;
  size_t buffered = ctx->count % SHA256_BLOCK_SIZE;
  ctx->count += len;

  if (buffered > 0)
    {
      size_t fill = SHA256_BLOCK_SIZE - buffered;
      if (len < fill)
	{
	  memcpy (ctx->buf + buffered, p, len);
	  return;
	}
      memcpy (ctx->buf + buffered, p, fill);
      _sha256_transform (ctx->state, ctx->buf);
      p += fill;
      len -= fill;
    }

  while (len >= SHA256_BLOCK_SIZE)
    {
      _sha256_transform (ctx->state, p);
      p += SHA256_BLOCK_SIZE;
      len -= SHA256_BLOCK_SIZE;
    }

  if (len > 0)
    memcpy (ctx->buf, p, len);
}

static void
sha256_final (struct sha256_ctx *ctx, uint8_t digest[SHA256_DIGEST_SIZE])
{
  uint64_t bits = ctx->count * 8;
  size_t buffered = ctx->count % SHA256_BLOCK_SIZE;

  /* Append the bit '1' (0x80 byte).  */
  ctx->buf[buffered++] = 0x80;

  if (buffered > 56)
    {
      memset (ctx->buf + buffered, 0, SHA256_BLOCK_SIZE - buffered);
      _sha256_transform (ctx->state, ctx->buf);
      buffered = 0;
    }

  memset (ctx->buf + buffered, 0, 56 - buffered);

  /* Append length in bits as big-endian 64-bit integer.  */
  _sha256_store_be32 (ctx->buf + 56, (uint32_t) (bits >> 32));
  _sha256_store_be32 (ctx->buf + 60, (uint32_t) bits);
  _sha256_transform (ctx->state, ctx->buf);

  for (int i = 0; i < 8; i++)
    _sha256_store_be32 (digest + i * 4, ctx->state[i]);
}

#endif /* _DL_SHA256_H */
