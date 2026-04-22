// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// AES-256-GCM single-block encrypt + GHASH
// Encrypts one 16-byte block using AES-256 in CTR mode and accumulates
// the ciphertext into the GHASH state Xi.
//
//    extern size_t aesv8_gcm_1block_enc_256
//      (const uint8_t *in, size_t bit_len, uint8_t *out,
//       uint8_t *Xi, uint8_t ivec[16], const void *key,
//       const u128 Htable[16]);
//
// This is a single FULL block extraction from AWS-LC's aesv8_gcm_8x_enc_256.
// It implements the .L256_enc_blocks_less_than_1 path for exactly 16 bytes
// using the same register allocation and instruction patterns as the
// 8-block version, including eor3 for GHASH modular reduction.
// bit_len must be 128 (one full block). Partial blocks are NOT supported.
//
// Register allocation follows the 8-block version:
//   v0       = enc_ctr_0 / ct_0 (AES encrypted counter / GHASH input)
//   v8       = ct_1 (ciphertext for XOR and storage)
//   v16      = t0 (GHASH scratch / modulo constant)
//   v17-v19  = acc_h, acc_m, acc_l (GHASH accumulators)
//   v20      = h1 (from Htable[0])
//   v21      = h12k / t11 (from Htable[1] / reduction scratch)
//   v26-v28  = rk0-rk14 (round key loading, reused)
//   v29      = t1 / t12 (reduction scratch)
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aesv8_gcm_1block_enc_256)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aesv8_gcm_1block_enc_256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aesv8_gcm_1block_enc_256)
        .arch armv8.2-a+crypto+sha3
        .text
        .balign 4

S2N_BN_SYMBOL(aesv8_gcm_1block_enc_256):
        CFI_START

// =====================================================================
// Load counter and AES-256 encrypt (14 rounds on v0)
// Matches 8-block version lines 143, 174-347 (for block 0 only)
// =====================================================================

        ldr     q0, [x4]               // load counter from ivec

// Rounds 0-1
        ldp     q26, q27, [x5, #0]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
// Rounds 2-3
        ldp     q26, q27, [x5, #32]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
// Rounds 4-5
        ldp     q26, q27, [x5, #64]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
// Rounds 6-7
        ldp     q26, q27, [x5, #96]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
// Rounds 8-9
        ldp     q26, q27, [x5, #128]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
// Rounds 10-11
        ldp     q26, q27, [x5, #160]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
// Rounds 12-13
        ldp     q26, q27, [x5, #192]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b         // round 13: aese only, no aesmc
// Final XOR with rk14 and plaintext (matches 8-block eor3 pattern)
        ldr     q28, [x5, #224]          // rk14
        ldr     q8, [x0]                // load plaintext into ct_1 (v8)
        eor3    v8.16b, v8.16b, v0.16b, v28.16b  // ct = pt XOR enc_ctr XOR rk14

// Store ciphertext
        str     q8, [x2]

// =====================================================================
// Counter increment (scalar, same as before)
// =====================================================================
        ldr     w10, [x4, #12]
        rev     w10, w10
        add     w10, w10, #1
        rev     w10, w10
        str     w10, [x4, #12]

// =====================================================================
// GHASH: Xi = (Xi XOR CT) * H
// Matches 8-block version .L256_enc_blocks_less_than_1 (lines 1266-1302)
// with acc_h/acc_m/acc_l = 0 (no accumulated prior blocks)
// =====================================================================

// Load Xi, prepare GHASH input
// (matches 8-block: ld1 acc_l; ext; rev64; then rev64 ct; ext acc_l; eor)
        ld1     {v19.16b}, [x3]          // acc_l = Xi (v19)
        ext     v19.16b, v19.16b, v19.16b, #8
        rev64   v19.16b, v19.16b

// rev64 ciphertext for GHASH bit ordering (matches line 1266)
        rev64   v0.16b, v8.16b           // ct_0 = rev64(ct_1)

// XOR with accumulated tag (matches line 1272: eor ct_0, ct_0, t0)
// In 8-block version, t0 holds the partial tag from ext acc_l.
// For single block, acc_l IS the tag. After ext+rev64, swap halves:
        ext     v19.16b, v19.16b, v19.16b, #8  // PRE 0 (matches line 414)
        eor     v0.16b, v0.16b, v19.16b  // ct_0 = ct_0 XOR acc_l

// Load h1 and h12k from Htable (matches lines 1259, prepretail h12k load)
        ldr     q20, [x6]               // h1 = Htable[0]
        ldr     q21, [x6, #16]          // h12k = Htable[1]

// Karatsuba multiply (matches lines 1275-1286)
        ins     v16.d[0], v0.d[1]        // t0.d[0] = ct_0.d[1] (mid)
        pmull2  v17.1q, v0.2d, v20.2d    // acc_h = ct_0[hi] * h1[hi]
        pmull   v19.1q, v0.1d, v20.1d    // acc_l = ct_0[lo] * h1[lo]

        eor     v16.8b, v16.8b, v0.8b    // t0 = ct_0[hi] XOR ct_0[lo] (mid)

        pmull   v16.1q, v16.1d, v21.1d   // t0 = mid * h12k

        mov     v18.16b, v16.16b         // acc_m = t0 (mid result)

// Load modulo constant (matches line 1287)
        mov     x10, #0xc200000000000000
        mov     v16.d[0], x10            // mod_constant in t0 (d16)

// Modular reduction with eor3 (matches lines 1289-1299)
        ext     v21.16b, v17.16b, v17.16b, #8   // t11 = ext(acc_h, #8)

        eor3    v18.16b, v18.16b, v17.16b, v19.16b  // acc_m ^= acc_h ^ acc_l (karatsuba tidy)
        pmull   v29.1q, v17.1d, v16.1d   // t12 = acc_h[lo] * mod_constant

        eor3    v18.16b, v18.16b, v29.16b, v21.16b  // acc_m ^= t12 ^ t11 (fold into mid)

        pmull   v17.1q, v18.1d, v16.1d   // acc_h = acc_m[lo] * mod_constant
        ext     v21.16b, v18.16b, v18.16b, #8   // t11 = ext(acc_m, #8)

        eor3    v19.16b, v19.16b, v17.16b, v21.16b  // acc_l ^= acc_h ^ t11 (fold into low)

// Convert back and store Xi (matches lines 1300-1302)
        ext     v19.16b, v19.16b, v19.16b, #8
        rev64   v19.16b, v19.16b
        st1     {v19.16b}, [x3]

// Return bytes processed
        lsr     x0, x1, #3
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(aesv8_gcm_1block_enc_256)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
