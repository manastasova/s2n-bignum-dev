// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// AES-256-GCM single-block decrypt + GHASH
// Decrypts one 16-byte block using AES-256 in CTR mode and accumulates
// the ciphertext (input) into the GHASH state Xi.
//
//    extern size_t aesv8_gcm_1block_dec_256
//      (const uint8_t *in, size_t bit_len, uint8_t *out,
//       uint8_t *Xi, uint8_t ivec[16], const void *key,
//       const u128 Htable[16]);
//
// Same as encrypt but GHASH operates on the INPUT (ciphertext), not output.
// Uses eor3 (armv8.2-a+sha3) for modular reduction.
// bit_len must be 128 (one full block). Partial blocks are NOT supported.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aesv8_gcm_1block_dec_256)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aesv8_gcm_1block_dec_256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aesv8_gcm_1block_dec_256)
        .arch armv8.2-a+crypto+sha3
        .text
        .balign 4

S2N_BN_SYMBOL(aesv8_gcm_1block_dec_256):
        CFI_START

// Load counter and AES-256 encrypt (14 rounds on v0)
        ldr     q0, [x4]
        ldp     q26, q27, [x5, #0]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
        ldp     q26, q27, [x5, #32]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
        ldp     q26, q27, [x5, #64]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
        ldp     q26, q27, [x5, #96]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
        ldp     q26, q27, [x5, #128]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
        ldp     q26, q27, [x5, #160]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        aesmc   v0.16b, v0.16b
        ldp     q26, q27, [x5, #192]
        aese    v0.16b, v26.16b
        aesmc   v0.16b, v0.16b
        aese    v0.16b, v27.16b
        ldr     q28, [x5, #224]

// Load ciphertext INPUT and decrypt
// KEY DIFFERENCE FROM ENCRYPT: v8 = ciphertext input (for GHASH)
// Plaintext = ciphertext XOR AES(counter) XOR rk14
        ldr     q8, [x0]                // load ciphertext (input)
        eor3    v3.16b, v8.16b, v0.16b, v28.16b  // plaintext = ct XOR enc_ctr XOR rk14
        str     q3, [x2]               // store plaintext (output)

// Counter increment
        ldr     w10, [x4, #12]
        rev     w10, w10
        add     w10, w10, #1
        rev     w10, w10
        str     w10, [x4, #12]

// GHASH: Xi = (Xi XOR CT) * H
// GHASH operates on INPUT (v8 = ciphertext), NOT output
        ld1     {v19.16b}, [x3]
        ext     v19.16b, v19.16b, v19.16b, #8
        rev64   v19.16b, v19.16b

        rev64   v0.16b, v8.16b           // ct_0 = rev64(ciphertext input)

        ext     v19.16b, v19.16b, v19.16b, #8
        eor     v0.16b, v0.16b, v19.16b

        ldr     q20, [x6]
        ldr     q21, [x6, #16]

// Karatsuba multiply
        ins     v16.d[0], v0.d[1]
        pmull2  v17.1q, v0.2d, v20.2d
        pmull   v19.1q, v0.1d, v20.1d
        eor     v16.8b, v16.8b, v0.8b
        pmull   v16.1q, v16.1d, v21.1d
        mov     v18.16b, v16.16b

// Modular reduction with eor3
        mov     x10, #0xc200000000000000
        mov     v16.d[0], x10

        ext     v21.16b, v17.16b, v17.16b, #8
        eor3    v18.16b, v18.16b, v17.16b, v19.16b
        pmull   v29.1q, v17.1d, v16.1d
        eor3    v18.16b, v18.16b, v29.16b, v21.16b
        pmull   v17.1q, v18.1d, v16.1d
        ext     v21.16b, v18.16b, v18.16b, #8
        eor3    v19.16b, v19.16b, v17.16b, v21.16b

// Store Xi
        ext     v19.16b, v19.16b, v19.16b, #8
        rev64   v19.16b, v19.16b
        st1     {v19.16b}, [x3]

        lsr     x0, x1, #3
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(aesv8_gcm_1block_dec_256)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif
