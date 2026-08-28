// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// GCM_INIT_V8: expand the GHASH hash key H into the PMULL/v8 power table.
//
//    extern void gcm_init_v8(uint64_t htable[static 32], const uint64_t h[static 2]);
//
// AWS-LC's native prototype is "u128 Htable[16]", where "u128" is
// "struct { uint64_t hi, lo; }" (16 bytes); that is the same 256-byte buffer as
// uint64_t htable[32]. The output buffer is 16 u128 entries (256 bytes), but
// this routine only writes the first 12 entries (192 bytes = Htable[0..11]):
// the twisted hash
// key H, then packed Karatsuba pre-processed forms of H^1..H^8 laid out as
// four groups of three 128-bit words. The remaining Htable[12..15] are left
// untouched (they serve other GHASH variants, not this one).
//
// In s2n-bignum's uint64_t view the output is Htable[32] and only the first
// 24 words (Htable[0..23]) are written.
//
// Imported verbatim from AWS-LC's pre-generated little-endian AArch64 output
// aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/ghashv8-armx.S, itself
// generated from crypto/fipsmodule/modes/asm/ghashv8-armx.pl (BoringSSL). The
// instruction stream is unchanged; only the symbol/ABI wrapper macros and CFI
// annotations follow s2n-bignum house style, and the AArch64 BTI landing-pad
// macro (AARCH64_VALID_CALL_TARGET) is dropped.
//
// Standard ARM ABI: X0 = Htable, X1 = H
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        .arch   armv8-a+crypto
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(gcm_init_v8)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(gcm_init_v8)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(gcm_init_v8)
        .text
        .balign 4

S2N_BN_SYMBOL(gcm_init_v8):
    // AARCH64_VALID_CALL_TARGET
        CFI_START

	ld1	{v17.2d},[x1]		//load input H = {w0,w1}
	movi	v19.16b,#0xe1
	movi	v2.16b,#0
	shl	v19.2d,v19.2d,#57		//0xc2.0
	ushr	v18.2d,v17.2d,#63
	dup	v3.4s,v17.s[1]
	ushr	v1.2d,v19.2d,#63
	ext	v18.16b,v18.16b,v2.16b,#8	//carry-in bit for the low lane
	shl	v20.2d,v17.2d,#1
	ext	v16.16b,v19.16b,v1.16b,#8		//t0=0xc2....01, store-lane order
	sshr	v3.4s,v3.4s,#31		//broadcast carry bit
	orr	v20.16b,v20.16b,v18.16b		//H<<<=1
	and	v16.16b,v16.16b,v3.16b
	eor	v20.16b,v20.16b,v16.16b		//twisted H, already store-lane order

	//calculate H^2 = H.H (a square)
	ext	v3.16b,v20.16b,v20.16b,#8	//H in multiplicand (algebraic) lane order
	pmull2	v0.1q,v20.2d,v20.2d		//p_lo
	eor	v16.16b,v3.16b,v20.16b		//Karatsuba fold of H
	pmull	v2.1q,v20.1d,v20.1d		//p_hi
	ext	v1.16b,v0.16b,v0.16b,#8		//low 128 bits = p_lo, word-swapped
	pmull	v18.1q,v0.1d,v19.1d		//1st phase
	eor	v0.16b,v1.16b,v18.16b
	ext	v18.16b,v0.16b,v0.16b,#8		//2nd phase
	pmull	v0.1q,v0.1d,v19.1d
	eor	v18.16b,v18.16b,v2.16b
	eor	v17.16b,v0.16b,v18.16b		//H^2
	ext	v22.16b,v17.16b,v17.16b,#8	//store Htable[2]
	eor	v1.16b,v17.16b,v22.16b		//Karatsuba fold of H^2
	ext	v21.16b,v16.16b,v1.16b,#8	//pack Karatsuba pre-processed
	stp	q20,q21,[x0]			//store Htable[0..1]

	//calculate H^3 = H.H^2 and H^4 = H^2.H^2
	pmull	v0.1q,v3.1d,v17.1d		//p_lo  = a_lo . b_lo
	pmull2	v2.1q,v3.2d,v17.2d		//p_hi  = a_hi . b_hi
	pmull2	v1.1q,v20.2d,v17.2d		//cross = a_lo . b_hi
	pmull	v16.1q,v20.1d,v17.1d		//cross = a_hi . b_lo
	pmull	v5.1q,v17.1d,v17.1d		//p_lo (a square's middle vanishes)
	pmull2	v7.1q,v17.2d,v17.2d		//p_hi

	eor	v1.16b,v1.16b,v16.16b		//schoolbook middle M
	ext	v16.16b,v0.16b,v0.16b,#8		//p_lo, word-swapped
	pmull	v18.1q,v0.1d,v19.1d		//1st phase
	eor	v1.16b,v1.16b,v18.16b
	eor	v1.16b,v1.16b,v16.16b		//1st-phase result, + M_hi in its high
						//lane -- which cancels against the
						//M_hi the high 128 bits would have
						//carried, so neither is materialized
	ext	v18.16b,v1.16b,v1.16b,#8		//2nd phase
	pmull	v1.1q,v1.1d,v19.1d
	eor	v18.16b,v18.16b,v2.16b
	eor	v21.16b,v1.16b,v18.16b
	ext	v6.16b,v5.16b,v5.16b,#8		//low 128 bits = p_lo, word-swapped
	pmull	v4.1q,v5.1d,v19.1d		//1st phase
	eor	v5.16b,v6.16b,v4.16b
	ext	v4.16b,v5.16b,v5.16b,#8		//2nd phase
	pmull	v5.1q,v5.1d,v19.1d
	eor	v4.16b,v4.16b,v7.16b
	eor	v20.16b,v5.16b,v4.16b

	ext	v23.16b,v21.16b,v21.16b,#8	//store Htable[3]
	ext	v25.16b,v20.16b,v20.16b,#8	//store Htable[5]
	eor	v16.16b,v21.16b,v23.16b		//Karatsuba fold of H^3
	eor	v18.16b,v20.16b,v25.16b		//Karatsuba fold of H^4
	ext	v24.16b,v16.16b,v18.16b,#8	//pack Karatsuba pre-processed
	stp	q22,q23,[x0,#32]		//store Htable[2..3]
	stp	q24,q25,[x0,#64]		//store Htable[4..5]

	//calculate H^5 = H^2.H^3 and H^6 = H^3.H^3
	pmull	v0.1q,v17.1d,v21.1d		//p_lo  = a_lo . b_lo
	pmull2	v2.1q,v17.2d,v21.2d		//p_hi  = a_hi . b_hi
	pmull2	v1.1q,v22.2d,v21.2d		//cross = a_lo . b_hi
	pmull	v16.1q,v22.1d,v21.1d		//cross = a_hi . b_lo
	pmull	v5.1q,v21.1d,v21.1d		//p_lo (a square's middle vanishes)
	pmull2	v7.1q,v21.2d,v21.2d		//p_hi

	eor	v1.16b,v1.16b,v16.16b		//schoolbook middle M
	ext	v16.16b,v0.16b,v0.16b,#8		//p_lo, word-swapped
	pmull	v18.1q,v0.1d,v19.1d		//1st phase
	eor	v1.16b,v1.16b,v18.16b
	eor	v1.16b,v1.16b,v16.16b		//1st-phase result, + M_hi in its high
						//lane -- which cancels against the
						//M_hi the high 128 bits would have
						//carried, so neither is materialized
	ext	v18.16b,v1.16b,v1.16b,#8		//2nd phase
	pmull	v1.1q,v1.1d,v19.1d
	eor	v18.16b,v18.16b,v2.16b
	eor	v16.16b,v1.16b,v18.16b
	ext	v6.16b,v5.16b,v5.16b,#8		//low 128 bits = p_lo, word-swapped
	pmull	v4.1q,v5.1d,v19.1d		//1st phase
	eor	v5.16b,v6.16b,v4.16b
	ext	v4.16b,v5.16b,v5.16b,#8		//2nd phase
	pmull	v5.1q,v5.1d,v19.1d
	eor	v4.16b,v4.16b,v7.16b
	eor	v17.16b,v5.16b,v4.16b

	ext	v26.16b,v16.16b,v16.16b,#8	//store Htable[6]
	ext	v28.16b,v17.16b,v17.16b,#8	//store Htable[8]
	eor	v16.16b,v16.16b,v26.16b		//Karatsuba fold of H^5
	eor	v17.16b,v17.16b,v28.16b		//Karatsuba fold of H^6
	ext	v27.16b,v16.16b,v17.16b,#8	//pack Karatsuba pre-processed
	stp	q26,q27,[x0,#96]		//store Htable[6..7]

	//calculate H^7 = H^4.H^3 and H^8 = H^4.H^4 (depth 3: both feed off H^3/H^4)
	pmull	v0.1q,v20.1d,v21.1d		//p_lo  = a_lo . b_lo
	pmull2	v2.1q,v20.2d,v21.2d		//p_hi  = a_hi . b_hi
	pmull2	v1.1q,v25.2d,v21.2d		//cross = a_lo . b_hi
	pmull	v16.1q,v25.1d,v21.1d		//cross = a_hi . b_lo
	pmull	v5.1q,v20.1d,v20.1d		//p_lo (a square's middle vanishes)
	pmull2	v7.1q,v20.2d,v20.2d		//p_hi

	eor	v1.16b,v1.16b,v16.16b		//schoolbook middle M
	ext	v16.16b,v0.16b,v0.16b,#8		//p_lo, word-swapped
	pmull	v18.1q,v0.1d,v19.1d		//1st phase
	eor	v1.16b,v1.16b,v18.16b
	eor	v1.16b,v1.16b,v16.16b		//1st-phase result, + M_hi in its high
						//lane -- which cancels against the
						//M_hi the high 128 bits would have
						//carried, so neither is materialized
	ext	v18.16b,v1.16b,v1.16b,#8		//2nd phase
	pmull	v1.1q,v1.1d,v19.1d
	eor	v18.16b,v18.16b,v2.16b
	eor	v16.16b,v1.16b,v18.16b
	ext	v6.16b,v5.16b,v5.16b,#8		//low 128 bits = p_lo, word-swapped
	pmull	v4.1q,v5.1d,v19.1d		//1st phase
	eor	v5.16b,v6.16b,v4.16b
	ext	v4.16b,v5.16b,v5.16b,#8		//2nd phase
	pmull	v5.1q,v5.1d,v19.1d
	eor	v4.16b,v4.16b,v7.16b
	eor	v17.16b,v5.16b,v4.16b

	ext	v29.16b,v16.16b,v16.16b,#8	//store Htable[9]
	ext	v31.16b,v17.16b,v17.16b,#8	//store Htable[11]
	eor	v16.16b,v16.16b,v29.16b		//Karatsuba fold of H^7
	eor	v17.16b,v17.16b,v31.16b		//Karatsuba fold of H^8
	ext	v30.16b,v16.16b,v17.16b,#8	//pack Karatsuba pre-processed
	stp	q28,q29,[x0,#128]		//store Htable[8..9]
	stp	q30,q31,[x0,#160]		//store Htable[10..11]
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(gcm_init_v8)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
