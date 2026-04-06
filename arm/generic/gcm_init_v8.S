// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// GHASH initialization: precompute twisted H and Karatsuba constants
// Inputs Htable[6], H[2]; output Htable[6]
//
//    extern void gcm_init_v8
//      (uint64_t Htable[6], const uint64_t H[2]);
//
// Prepares the Htable for use by gcm_gmult_v8. The raw 128-bit hash key H
// is twisted (bit-reflected via shift and conditional XOR with the reduction
// polynomial) and stored along with Karatsuba pre-processing constants.
//
// Htable layout (48 bytes / 6 uint64_t):
//   [0..1]  = twisted H (16 bytes)
//   [2..3]  = Hhl: Karatsuba pre-processed (Hhi ^ Hlo) (16 bytes)
//   [4..5]  = H^2 twisted (16 bytes)
//
// Standard ARM ABI: X0 = Htable, X1 = H
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(gcm_init_v8)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(gcm_init_v8)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(gcm_init_v8)
        .text
        .balign 4

// Register allocation uses only caller-saved NEON registers:
// v0-v7 and v16-v31 are caller-saved (scratch)
// v8-v15 are callee-saved (must be preserved)
//
// Xl=v0, Xm=v1, Xh=v2, IN=v3
// t0=v16, t1=v17, t2=v18, xC2=v20, H=v21, Hhl=v22, H2=v23

S2N_BN_SYMBOL(gcm_init_v8):
        CFI_START

// Load input H
        ldr     q17, [x1]

// Prepare reduction constant: 0xc2000000000000000000000000000000
        movi    v20.16b, #0xe1
        shl     v20.2d, v20.2d, #57

// Twist H: H <<= 1 with conditional XOR of reduction polynomial
        ext     v3.16b, v17.16b, v17.16b, #8
        ushr    v18.2d, v20.2d, #63
        dup     v17.4s, v17.s[1]
        ext     v16.16b, v18.16b, v20.16b, #8       // t0 = 0xc2....01
        ushr    v18.2d, v3.2d, #63
        sshr    v17.4s, v17.4s, #31                   // broadcast carry bit
        and     v18.16b, v18.16b, v16.16b
        shl     v3.2d, v3.2d, #1
        ext     v18.16b, v18.16b, v18.16b, #8
        and     v16.16b, v16.16b, v17.16b
        orr     v3.16b, v3.16b, v18.16b             // H <<= 1
        eor     v21.16b, v3.16b, v16.16b             // twisted H

// Byte-swap twisted H for storage (swap halves)
        ext     v21.16b, v21.16b, v21.16b, #8
        str     q21, [x0], #16                       // store Htable[0]: twisted H

// Calculate H^2 = H * H (mod P)
        ext     v16.16b, v21.16b, v21.16b, #8        // Karatsuba pre-processing
        pmull2  v0.1q, v21.2d, v21.2d
        eor     v16.16b, v16.16b, v21.16b
        pmull   v2.1q, v21.1d, v21.1d
        pmull   v1.1q, v16.1d, v16.1d

// Karatsuba post-processing
        ext     v17.16b, v0.16b, v2.16b, #8
        eor     v18.16b, v0.16b, v2.16b
        eor     v1.16b, v1.16b, v17.16b
        eor     v1.16b, v1.16b, v18.16b

// 1st phase of reduction
        pmull   v18.1q, v0.1d, v20.1d
        mov     v2.d[0], v1.d[1]
        mov     v1.d[1], v0.d[0]
        eor     v0.16b, v1.16b, v18.16b

// 2nd phase of reduction
        ext     v18.16b, v0.16b, v0.16b, #8
        pmull   v0.1q, v0.1d, v20.1d
        eor     v18.16b, v18.16b, v2.16b
        eor     v17.16b, v0.16b, v18.16b              // H^2

// Karatsuba pre-processing for storage
        ext     v23.16b, v17.16b, v17.16b, #8
        eor     v17.16b, v17.16b, v23.16b
        ext     v22.16b, v16.16b, v17.16b, #8          // pack Karatsuba pre-processed

// Store Hhl and H^2
        str     q22, [x0], #16                        // store Htable[1]: Hhl
        str     q23, [x0], #16                        // store Htable[2]: H^2

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(gcm_init_v8)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
