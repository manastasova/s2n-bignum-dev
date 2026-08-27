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
        ext     v3.16b,v17.16b,v17.16b,#8
        ushr    v18.2d,v19.2d,#63
        dup     v17.4s,v17.s[1]
        ext     v16.16b,v18.16b,v19.16b,#8              //t0=0xc2....01
        ushr    v18.2d,v3.2d,#63
        sshr    v17.4s,v17.4s,#31               //broadcast carry bit
        and     v18.16b,v18.16b,v16.16b
        shl     v3.2d,v3.2d,#1
        ext     v18.16b,v18.16b,v18.16b,#8
        and     v16.16b,v16.16b,v17.16b
        orr     v3.16b,v3.16b,v18.16b           //H<<<=1
        eor     v20.16b,v3.16b,v16.16b          //twisted H
        ext     v20.16b, v20.16b, v20.16b, #8
        st1     {v20.2d},[x0],#16               //store Htable[0]

        //calculate H^2
        ext     v16.16b,v20.16b,v20.16b,#8              //Karatsuba pre-processing
        pmull2  v0.1q,v20.2d,v20.2d
        eor     v16.16b,v16.16b,v20.16b
        pmull   v2.1q,v20.1d,v20.1d
        pmull   v1.1q,v16.1d,v16.1d

        ext     v17.16b,v0.16b,v2.16b,#8                //Karatsuba post-processing
        eor     v18.16b,v0.16b,v2.16b
        eor     v1.16b,v1.16b,v17.16b
        eor     v1.16b,v1.16b,v18.16b
        pmull   v18.1q,v0.1d,v19.1d             //1st phase

        ins     v2.d[0],v1.d[1]
        ins     v1.d[1],v0.d[0]
        eor     v0.16b,v1.16b,v18.16b

        ext     v18.16b,v0.16b,v0.16b,#8                //2nd phase
        pmull   v0.1q,v0.1d,v19.1d
        eor     v18.16b,v18.16b,v2.16b
        eor     v17.16b,v0.16b,v18.16b

        ext     v22.16b,v17.16b,v17.16b,#8              //Karatsuba pre-processing
        eor     v17.16b,v17.16b,v22.16b
        ext     v21.16b,v16.16b,v17.16b,#8              //pack Karatsuba pre-processed
        st1     {v21.2d},[x0],#16       //store Htable[1..2]
        st1     {v22.2d},[x0],#16       //store Htable[1..2]

        //calculate H^3 and H^4
        pmull2  v0.1q,v20.2d, v22.2d
        pmull2  v5.1q,v22.2d,v22.2d
        pmull   v2.1q,v20.1d, v22.1d
        pmull   v7.1q,v22.1d,v22.1d
        pmull   v1.1q,v16.1d,v17.1d
        pmull   v6.1q,v17.1d,v17.1d

        ext     v16.16b,v0.16b,v2.16b,#8                //Karatsuba post-processing
        ext     v17.16b,v5.16b,v7.16b,#8
        eor     v18.16b,v0.16b,v2.16b
        eor     v1.16b,v1.16b,v16.16b
        eor     v4.16b,v5.16b,v7.16b
        eor     v6.16b,v6.16b,v17.16b
        eor     v1.16b,v1.16b,v18.16b
        pmull   v18.1q,v0.1d,v19.1d             //1st phase
        eor     v6.16b,v6.16b,v4.16b
        pmull   v4.1q,v5.1d,v19.1d

        ins     v2.d[0],v1.d[1]
        ins     v7.d[0],v6.d[1]
        ins     v1.d[1],v0.d[0]
        ins     v6.d[1],v5.d[0]
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
        ext     v18.16b,v22.16b,v22.16b,#8
        eor     v16.16b,v16.16b,v23.16b
        eor     v17.16b,v17.16b,v25.16b
        eor     v18.16b,v18.16b,v22.16b
        ext     v24.16b,v16.16b,v17.16b,#8      //pack Karatsuba pre-processed
        st1     {v23.2d,v24.2d,v25.2d},[x0],#48 //store Htable[3..5]

        //calculate H^5 and H^6
        pmull2  v0.1q,v22.2d, v23.2d
        pmull2  v5.1q,v23.2d,v23.2d
        pmull   v2.1q,v22.1d, v23.1d
        pmull   v7.1q,v23.1d,v23.1d
        pmull   v1.1q,v16.1d,v18.1d
        pmull   v6.1q,v16.1d,v16.1d

        ext     v16.16b,v0.16b,v2.16b,#8                //Karatsuba post-processing
        ext     v17.16b,v5.16b,v7.16b,#8
        eor     v18.16b,v0.16b,v2.16b
        eor     v1.16b,v1.16b,v16.16b
        eor     v4.16b,v5.16b,v7.16b
        eor     v6.16b,v6.16b,v17.16b
        eor     v1.16b,v1.16b,v18.16b
        pmull   v18.1q,v0.1d,v19.1d             //1st phase
        eor     v6.16b,v6.16b,v4.16b
        pmull   v4.1q,v5.1d,v19.1d

        ins     v2.d[0],v1.d[1]
        ins     v7.d[0],v6.d[1]
        ins     v1.d[1],v0.d[0]
        ins     v6.d[1],v5.d[0]
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
        ext     v18.16b,v22.16b,v22.16b,#8
        eor     v16.16b,v16.16b,v26.16b
        eor     v17.16b,v17.16b,v28.16b
        eor     v18.16b,v18.16b,v22.16b
        ext     v27.16b,v16.16b,v17.16b,#8      //pack Karatsuba pre-processed
        st1     {v26.2d,v27.2d,v28.2d},[x0],#48 //store Htable[6..8]

        //calculate H^7 and H^8
        pmull2  v0.1q,v22.2d,v26.2d
        pmull2  v5.1q,v22.2d,v28.2d
        pmull   v2.1q,v22.1d,v26.1d
        pmull   v7.1q,v22.1d,v28.1d
        pmull   v1.1q,v16.1d,v18.1d
        pmull   v6.1q,v17.1d,v18.1d

        ext     v16.16b,v0.16b,v2.16b,#8                //Karatsuba post-processing
        ext     v17.16b,v5.16b,v7.16b,#8
        eor     v18.16b,v0.16b,v2.16b
        eor     v1.16b,v1.16b,v16.16b
        eor     v4.16b,v5.16b,v7.16b
        eor     v6.16b,v6.16b,v17.16b
        eor     v1.16b,v1.16b,v18.16b
        pmull   v18.1q,v0.1d,v19.1d             //1st phase
        eor     v6.16b,v6.16b,v4.16b
        pmull   v4.1q,v5.1d,v19.1d

        ins     v2.d[0],v1.d[1]
        ins     v7.d[0],v6.d[1]
        ins     v1.d[1],v0.d[0]
        ins     v6.d[1],v5.d[0]
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
