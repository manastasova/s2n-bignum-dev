// Copyright 2014-2020 The OpenSSL Project Authors. All Rights Reserved.
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Written by Andy Polyakov <appro@openssl.org> for the OpenSSL project.

// ----------------------------------------------------------------------------
// GCM_INIT_V8: expand a GHASH key into the precomputed table (ARMv8 PMULL)
// Input h[2]; output htable[32]
//
//    extern void gcm_init_v8(uint64_t htable[static 32],
//                            const uint64_t h[static 2]);
//
// Given the 128-bit GHASH key H (two 64-bit words), fills the low 12 of the
// 16 128-bit slots of Htable with the twisted powers H, H^2, ..., H^8 and the
// packed Karatsuba middles, in the layout consumed by gcm_gmult_v8 and
// gcm_ghash_v8. The remaining slots are left untouched, and the table layout
// is opaque to callers.
//
// Standard ARM ABI: X0 = Htable, X1 = H
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        .arch	armv8-a+crypto
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(gcm_init_v8)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(gcm_init_v8)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(gcm_init_v8)
        .text
        .balign 4

S2N_BN_SYMBOL(gcm_init_v8):

        # AARCH64_VALID_CALL_TARGET
        CFI_START

        ld1     {v17.2d},[x1]           //load input H
        movi    v19.16b,#0xe1
        shl     v19.2d,v19.2d,#57               //0xc2.0
        movi    v1.16b,#0		// A0b: zero (off the critical path)
        ext     v16.16b,v19.16b,v1.16b,#8		// A0b: swap(t0) lane1 cleared = {0xc2<<56, 0}
        ext     v18.16b,v17.16b,v17.16b,#8		// A0b: swap(H) feeds sri
        sshr    v20.2d,v17.2d,#63		// A0b: per-lane sign masks
        shl     v3.2d,v17.2d,#1		// A0b: lanewise H<<1
        nop		// A0b
        sri     v3.2d,v18.2d,#63		// A0b: cross-lane carry AND the masked 0x..01 bit
        nop		// A0b
        nop		// A0b
        and     v16.16b,v16.16b,v20.16b		// A0b: 0xc2<<56 masked by sign(H.d0)
        nop		// A0b
        eor     v3.16b,v3.16b,v16.16b		// A0b: S = swap(twisted H), computed directly
        ext     v20.16b,v3.16b,v3.16b,#8		// A0b: T = swap(S)
        st1     {v3.2d},[x0],#16                //store Htable[0]

        //calculate H^2
        eor     v16.16b,v20.16b,v3.16b                  //ppH = T ^ S (CSE double-swap)
        pmull2  v0.1q,v3.2d,v3.2d
        nop                                             //CSE: ppH computed at :56 directly
        pmull   v2.1q,v3.1d,v3.1d
        nop                                     //SQ: mid pmull(ppH,ppH) is vacuous for a square

        nop                                     //SQ: Karatsuba post-processing all cancels
        nop                                     //SQ:   (a0^a1)^2 == a0^2 ^ a1^2 in GF(2)[x],
        nop                                     //SQ:   so mid ^ (hi^lo) == 0 and
        nop                                     //SQ:   v1 collapses to ext(hi,lo,8)
        pmull   v18.1q,v0.1d,v19.1d             //1st phase

        nop                                     //SQ: ins v2.d[0],v1.d[1] wrote lo.d[0] over itself
        ext     v1.16b,v0.16b,v0.16b,#8         //SQ: v1 = ext(hi,hi,8), was two ins
        eor     v0.16b,v1.16b,v18.16b

        ext     v18.16b,v0.16b,v0.16b,#8                //2nd phase
        pmull   v0.1q,v0.1d,v19.1d
        eor     v18.16b,v18.16b,v2.16b
        eor     v17.16b,v0.16b,v18.16b

        ext     v22.16b,v17.16b,v17.16b,#8              //Karatsuba pre-processing
        eor     v20.16b,v17.16b,v22.16b                 //ppH2 into freed v20 (full CSE)
        ext     v21.16b,v16.16b,v20.16b,#8              //pack Karatsuba pre-processed
        st1     {v21.2d},[x0],#16       //store Htable[1..2]
        st1     {v22.2d},[x0],#16       //store Htable[1..2]

        //calculate H^3 and H^4
        pmull2  v0.1q,v3.2d, v22.2d
        pmull2  v5.1q,v22.2d,v22.2d
        pmull   v2.1q,v3.1d, v22.1d
        pmull   v7.1q,v22.1d,v22.1d
        pmull   v1.1q,v16.1d,v20.1d
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])

        ext     v16.16b,v0.16b,v2.16b,#8                //Karatsuba post-processing
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        eor     v18.16b,v0.16b,v2.16b
        eor     v1.16b,v1.16b,v16.16b
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        eor     v1.16b,v1.16b,v18.16b
        pmull   v18.1q,v0.1d,v19.1d             //1st phase
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        pmull   v4.1q,v5.1d,v19.1d

        ins     v2.d[0],v1.d[1]
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        ins     v1.d[1],v0.d[0]
        ext     v6.16b,v5.16b,v5.16b,#8		// SQ: folded mid collapses to ext(hi,hi,8)
        eor     v0.16b,v1.16b,v18.16b
        eor     v5.16b,v6.16b,v4.16b

        ext     v18.16b,v0.16b,v0.16b,#8                //2nd phase
        ext     v4.16b,v5.16b,v5.16b,#8
        pmull   v0.1q,v0.1d,v19.1d
        pmull   v5.1q,v5.1d,v19.1d
        eor     v18.16b,v18.16b,v2.16b
        eor     v4.16b,v4.16b,v7.16b

        eor     v16.16b, v0.16b,v18.16b         //H^3
        eor     v17.16b, v5.16b,v4.16b          //H^4

        ext     v23.16b,v16.16b,v16.16b,#8              //Karatsuba pre-processing
        ext     v25.16b,v17.16b,v17.16b,#8
        nop                                     //CSE: ppH2 carried in v20 from :78
        eor     v3.16b,v16.16b,v23.16b          //E1: ppH3 into v3 (S dead after :86)
        eor     v21.16b,v17.16b,v25.16b         //E1: ppH4 into v21 (dead after :80 store)
        nop
        ext     v24.16b,v3.16b,v21.16b,#8       //pack Karatsuba pre-processed
        st1     {v23.2d,v24.2d,v25.2d},[x0],#48 //store Htable[3..5]

        //calculate H^5 and H^6
        pmull2  v0.1q,v22.2d, v23.2d
        pmull2  v5.1q,v23.2d,v23.2d
        pmull   v2.1q,v22.1d, v23.1d
        pmull   v7.1q,v23.1d,v23.1d
        pmull   v1.1q,v3.1d,v20.1d              //E1: ppH3 now in v3
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])

        ext     v16.16b,v0.16b,v2.16b,#8                //Karatsuba post-processing
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        eor     v18.16b,v0.16b,v2.16b
        eor     v1.16b,v1.16b,v16.16b
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        eor     v1.16b,v1.16b,v18.16b
        pmull   v18.1q,v0.1d,v19.1d             //1st phase
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        pmull   v4.1q,v5.1d,v19.1d

        ins     v2.d[0],v1.d[1]
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        ins     v1.d[1],v0.d[0]
        ext     v6.16b,v5.16b,v5.16b,#8		// SQ: folded mid collapses to ext(hi,hi,8)
        eor     v0.16b,v1.16b,v18.16b
        eor     v5.16b,v6.16b,v4.16b

        ext     v18.16b,v0.16b,v0.16b,#8                //2nd phase
        ext     v4.16b,v5.16b,v5.16b,#8
        pmull   v0.1q,v0.1d,v19.1d
        pmull   v5.1q,v5.1d,v19.1d
        eor     v18.16b,v18.16b,v2.16b
        eor     v4.16b,v4.16b,v7.16b

        eor     v16.16b,v0.16b,v18.16b              //H^5
        eor     v17.16b,v5.16b,v4.16b               //H^6

        ext     v26.16b, v16.16b, v16.16b,#8            //Karatsuba pre-processing
        ext     v28.16b, v17.16b, v17.16b,#8
        nop                                     //CSE: ppH2 carried in v20 from :78
        eor     v16.16b,v16.16b,v26.16b
        eor     v17.16b,v17.16b,v28.16b
        nop
        ext     v27.16b,v16.16b,v17.16b,#8      //pack Karatsuba pre-processed
        st1     {v26.2d,v27.2d,v28.2d},[x0],#48 //store Htable[6..8]

        //calculate H^7 and H^8
        pmull2  v0.1q,v23.2d,v25.2d             //E1: H^7 = H^3*H^4 (was H^2*H^5)
        pmull2  v5.1q,v25.2d,v25.2d             //E1: H^8 = H^4*H^4 (was H^2*H^6)
        pmull   v2.1q,v23.1d,v25.1d
        pmull   v7.1q,v25.1d,v25.1d
        pmull   v1.1q,v3.1d,v21.1d              //E1: mid = ppH3*ppH4
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])

        ext     v16.16b,v0.16b,v2.16b,#8                //Karatsuba post-processing
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        eor     v18.16b,v0.16b,v2.16b
        eor     v1.16b,v1.16b,v16.16b
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        eor     v1.16b,v1.16b,v18.16b
        pmull   v18.1q,v0.1d,v19.1d             //1st phase
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        pmull   v4.1q,v5.1d,v19.1d

        ins     v2.d[0],v1.d[1]
        nop		// SQ: dead for a squaring (mid == hi^lo in GF(2)[x])
        ins     v1.d[1],v0.d[0]
        ext     v6.16b,v5.16b,v5.16b,#8		// SQ: folded mid collapses to ext(hi,hi,8)
        eor     v0.16b,v1.16b,v18.16b
        eor     v5.16b,v6.16b,v4.16b

        ext     v18.16b,v0.16b,v0.16b,#8                //2nd phase
        ext     v4.16b,v5.16b,v5.16b,#8
        pmull   v0.1q,v0.1d,v19.1d
        pmull   v5.1q,v5.1d,v19.1d
        eor     v18.16b,v18.16b,v2.16b
        eor     v4.16b,v4.16b,v7.16b
        eor     v16.16b,v0.16b,v18.16b              //H^7
        eor     v17.16b,v5.16b,v4.16b               //H^8

        ext     v29.16b,v16.16b,v16.16b,#8              //Karatsuba pre-processing
        ext     v31.16b,v17.16b,v17.16b,#8
        eor     v16.16b,v16.16b,v29.16b
        eor     v17.16b,v17.16b,v31.16b
        ext     v30.16b,v16.16b,v17.16b,#8      //pack Karatsuba pre-processed
        st1     {v29.2d,v30.2d,v31.2d},[x0]             //store Htable[9..11]

        CFI_RET
S2N_BN_SIZE_DIRECTIVE(gcm_init_v8)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
