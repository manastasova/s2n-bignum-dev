// Copyright (c) 2019, Google Inc.
// SPDX-License-Identifier: ISC

// ***************************************************************************
// Reference for gcm_init_v8 (arm/aes_gcm/gcm_init_v8.S).
//
// gcm_init_v8 expands a 128-bit GHASH key H into a table of twisted powers
// H, H^2, ..., H^8 (interleaved with packed Karatsuba middles) for use by the
// ARMv8 PMULL GHASH. The table layout is opaque, so there is no published
// known-answer vector for it; instead we compare against a portable C
// reference for the SAME field arithmetic, taken verbatim from aws-lc.
//
// What is compared against what (see test_gcm_init_v8 / the KAT in
// tests/test.c): the 8 power slots that gcm_init_v8 writes are checked against
// the powers computed here. gcm_init_nohw gives slot 0 (the twisted H); the
// remaining powers are obtained by repeated GHASH-field multiplication with
// gcm_polyval_nohw, exactly as gcm_gmult_nohw / gcm_ghash_nohw in gcm_nohw.c
// compose that same primitive. The packed-Karatsuba slots (1,4,7,10) have no
// independent C reference and are left to the formal proof.
//
// Provenance (all VERBATIM from aws-lc @ 2df1601d7 unless marked TEST GLUE):
//   u128              : crypto/fipsmodule/modes/internal.h:89
//   gcm_mul64_nohw    : crypto/fipsmodule/modes/gcm_nohw.c:25-69  (uint128 path)
//   gcm_polyval_nohw  : crypto/fipsmodule/modes/gcm_nohw.c:213-264
//   gcm_init_nohw     : crypto/fipsmodule/modes/gcm_nohw.c:184-211
// ***************************************************************************

#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
#include <string.h>

// VERBATIM from crypto/fipsmodule/modes/internal.h:89
typedef struct { uint64_t hi,lo; } u128;

// TEST GLUE: the uint128 path of gcm_nohw.c is selected by BORINGSSL_HAS_UINT128;
// here we name the type directly (clang/gcc __uint128_t) so the verbatim body
// below compiles unchanged inside test.c.
typedef __uint128_t uint128_t;

// VERBATIM from crypto/fipsmodule/modes/gcm_nohw.c:25-69
static void gcm_mul64_nohw(uint64_t *out_lo, uint64_t *out_hi, uint64_t a,
                           uint64_t b) {
  // One term every four bits means the largest term is 64/4 = 16, which barely
  // overflows into the next term. Using one term every five bits would cost 25
  // multiplications instead of 16. It is faster to mask off the bottom four
  // bits of |a|, giving a largest term of 60/4 = 15, and apply the bottom bits
  // separately.
  uint64_t a0 = a & UINT64_C(0x1111111111111110);
  uint64_t a1 = a & UINT64_C(0x2222222222222220);
  uint64_t a2 = a & UINT64_C(0x4444444444444440);
  uint64_t a3 = a & UINT64_C(0x8888888888888880);

  uint64_t b0 = b & UINT64_C(0x1111111111111111);
  uint64_t b1 = b & UINT64_C(0x2222222222222222);
  uint64_t b2 = b & UINT64_C(0x4444444444444444);
  uint64_t b3 = b & UINT64_C(0x8888888888888888);

  uint128_t c0 = (a0 * (uint128_t)b0) ^ (a1 * (uint128_t)b3) ^
                 (a2 * (uint128_t)b2) ^ (a3 * (uint128_t)b1);
  uint128_t c1 = (a0 * (uint128_t)b1) ^ (a1 * (uint128_t)b0) ^
                 (a2 * (uint128_t)b3) ^ (a3 * (uint128_t)b2);
  uint128_t c2 = (a0 * (uint128_t)b2) ^ (a1 * (uint128_t)b1) ^
                 (a2 * (uint128_t)b0) ^ (a3 * (uint128_t)b3);
  uint128_t c3 = (a0 * (uint128_t)b3) ^ (a1 * (uint128_t)b2) ^
                 (a2 * (uint128_t)b1) ^ (a3 * (uint128_t)b0);

  // Multiply the bottom four bits of |a| with |b|.
  uint64_t a0_mask = UINT64_C(0) - (a & 1);
  uint64_t a1_mask = UINT64_C(0) - ((a >> 1) & 1);
  uint64_t a2_mask = UINT64_C(0) - ((a >> 2) & 1);
  uint64_t a3_mask = UINT64_C(0) - ((a >> 3) & 1);
  uint128_t extra = (a0_mask & b) ^ ((uint128_t)(a1_mask & b) << 1) ^
                    ((uint128_t)(a2_mask & b) << 2) ^
                    ((uint128_t)(a3_mask & b) << 3);

  *out_lo = (((uint64_t)c0) & UINT64_C(0x1111111111111111)) ^
            (((uint64_t)c1) & UINT64_C(0x2222222222222222)) ^
            (((uint64_t)c2) & UINT64_C(0x4444444444444444)) ^
            (((uint64_t)c3) & UINT64_C(0x8888888888888888)) ^ ((uint64_t)extra);
  *out_hi = (((uint64_t)(c0 >> 64)) & UINT64_C(0x1111111111111111)) ^
            (((uint64_t)(c1 >> 64)) & UINT64_C(0x2222222222222222)) ^
            (((uint64_t)(c2 >> 64)) & UINT64_C(0x4444444444444444)) ^
            (((uint64_t)(c3 >> 64)) & UINT64_C(0x8888888888888888)) ^
            ((uint64_t)(extra >> 64));
}

// VERBATIM from crypto/fipsmodule/modes/gcm_nohw.c:213-264
static void gcm_polyval_nohw(uint64_t Xi[2], const u128 *H) {
  // Karatsuba multiplication. The product of |Xi| and |H| is stored in |r0|
  // through |r3|. Note there is no byte or bit reversal because we are
  // evaluating POLYVAL.
  uint64_t r0, r1;
  gcm_mul64_nohw(&r0, &r1, Xi[0], H->lo);
  uint64_t r2, r3;
  gcm_mul64_nohw(&r2, &r3, Xi[1], H->hi);
  uint64_t mid0, mid1;
  gcm_mul64_nohw(&mid0, &mid1, Xi[0] ^ Xi[1], H->hi ^ H->lo);
  mid0 ^= r0 ^ r2;
  mid1 ^= r1 ^ r3;
  r2 ^= mid1;
  r1 ^= mid0;

  // Now we multiply our 256-bit result by x^-128 and reduce. |r2| and
  // |r3| shifts into position and we must multiply |r0| and |r1| by x^-128. We
  // have:
  //
  //       1 = x^121 + x^126 + x^127 + x^128
  //  x^-128 = x^-7 + x^-2 + x^-1 + 1
  //
  // This is the GHASH reduction step, but with bits flowing in reverse.

  // The x^-7, x^-2, and x^-1 terms shift bits past x^0, which would require
  // another reduction steps. Instead, we gather the excess bits, incorporate
  // them into |r0| and |r1| and reduce once. See slides 17-19
  // of https://crypto.stanford.edu/RealWorldCrypto/slides/gueron.pdf.
  r1 ^= (r0 << 63) ^ (r0 << 62) ^ (r0 << 57);

  // 1
  r2 ^= r0;
  r3 ^= r1;

  // x^-1
  r2 ^= r0 >> 1;
  r2 ^= r1 << 63;
  r3 ^= r1 >> 1;

  // x^-2
  r2 ^= r0 >> 2;
  r2 ^= r1 << 62;
  r3 ^= r1 >> 2;

  // x^-7
  r2 ^= r0 >> 7;
  r2 ^= r1 << 57;
  r3 ^= r1 >> 7;

  Xi[0] = r2;
  Xi[1] = r3;
}

// VERBATIM from crypto/fipsmodule/modes/gcm_nohw.c:184-211
void gcm_init_nohw(u128 Htable[16], const uint64_t Xi[2]) {
  // We implement GHASH in terms of POLYVAL, as described in RFC 8452. This
  // avoids a shift by 1 in the multiplication, needed to account for bit
  // reversal losing a bit after multiplication, that is,
  // rev128(X) * rev128(Y) = rev255(X*Y).
  //
  // Per Appendix A, we run mulX_POLYVAL. Note this is the same transformation
  // applied by |gcm_init_clmul|, etc. Note |Xi| has already been byteswapped.
  //
  // See also slide 16 of
  // https://crypto.stanford.edu/RealWorldCrypto/slides/gueron.pdf
  Htable[0].lo = Xi[1];
  Htable[0].hi = Xi[0];

  uint64_t carry = Htable[0].hi >> 63;
  carry = 0u - carry;

  Htable[0].hi <<= 1;
  Htable[0].hi |= Htable[0].lo >> 63;
  Htable[0].lo <<= 1;

  // The irreducible polynomial is 1 + x^121 + x^126 + x^127 + x^128, so we
  // conditionally add 0xc200...0001.
  Htable[0].lo ^= carry & 1;
  Htable[0].hi ^= carry & UINT64_C(0xc200000000000000);

  // This implementation does not use the rest of |Htable|.
}

// ---------------------------------------------------------------------------
// TEST GLUE (not from aws-lc). Composes the verbatim primitives above to
// reproduce the twisted powers H^1..H^8 that gcm_init_v8 stores, in the exact
// word order of arm/aes_gcm/gcm_init_v8.S. This is the same style of glue as
// gcm_gmult_nohw / gcm_ghash_nohw (thin wrappers over gcm_polyval_nohw); it
// invents no field arithmetic of its own.
//
// Relationship (verified empirically for many H): gcm_init_v8's slot 0 equals
// gcm_init_nohw's Htable[0] byte-for-byte; each further power is the GHASH
// product of the previous power with H (gcm_polyval_nohw), and gcm_init_v8
// stores a power as the 64-bit-lane swap of gcm_polyval_nohw's accumulator.
// ---------------------------------------------------------------------------

// Word offsets of H^1..H^8 within gcm_init_v8's 32-word (16x u128) table.
static const int gcm_v8_power_offsets[8] = {0, 4, 6, 10, 12, 16, 18, 22};

// Write powers[2*n], powers[2*n+1] = H^(n+1) (n=0..7) in gcm_init_v8 word order.
static void gcm_init_v8_powers_ref(uint64_t powers[16], const uint64_t H[2]) {
  u128 Htable[16];
  memset(Htable, 0, sizeof(Htable));
  gcm_init_nohw(Htable, H);          // Htable[0] = twisted H == gcm_init_v8 slot 0
  uint64_t acc[2];
  acc[0] = Htable[0].lo;             // gcm_polyval_nohw accumulator form of H^1
  acc[1] = Htable[0].hi;
  for (int n = 0; n < 8; n++) {
    powers[2 * n]     = acc[1];      // gcm_init_v8 store order = swap of accumulator
    powers[2 * n + 1] = acc[0];
    gcm_polyval_nohw(acc, &Htable[0]);   // acc <- acc (x) H  =>  next power
  }
}

// TEST GLUE: run one gcm_init_v8 known-answer vector. Runs gcm_init_v8 on the
// fixed key Hin and compares its 8 power slots against the fixed expected words
// exp[16] (H^1..H^8). Returns 1 (printing the divergence) on mismatch, else 0.
static int gcm_init_v8_kat_check(int idx, const uint64_t Hin[2],
                                 const uint64_t exp[16]) {
  uint64_t H[2] = { Hin[0], Hin[1] };
  uint64_t Htable[32];
  memset(Htable, 0, sizeof(Htable));
  gcm_init_v8(Htable, H);
  for (int i = 0; i < 8; i++) {
    uint64_t g0 = Htable[gcm_v8_power_offsets[i]];
    uint64_t g1 = Htable[gcm_v8_power_offsets[i] + 1];
    if (g0 != exp[2 * i] || g1 != exp[2 * i + 1]) {
      printf("Failed known value test %d: H=0x%016" PRIx64 ":%016" PRIx64
             " H^%d = 0x%016" PRIx64 ":%016" PRIx64
             " not 0x%016" PRIx64 ":%016" PRIx64 "\n",
             idx, Hin[0], Hin[1], i + 1, g0, g1, exp[2 * i], exp[2 * i + 1]);
      return 1;
    }
  }
  return 0;
}
