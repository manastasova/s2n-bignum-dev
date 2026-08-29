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
// PROVENANCE. This routine STARTED as AWS-LC's pre-generated little-endian
// AArch64 output aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/
// ghashv8-armx.S (itself generated from crypto/fipsmodule/modes/asm/
// ghashv8-armx.pl, BoringSSL), imported verbatim at 152 instructions. It has
// since been optimized IN TREE and the instruction stream is NO LONGER that of
// AWS-LC: Karatsuba -> schoolbook cross products, a depth-3 addition chain
// (H^7 = H^3.H^4, H^8 = H^4.H^4), Frobenius-free squares, the two-phase
// Gueron reduction expanded by linearity rather than iterated (for H^2 all the
// way through the twist, so that H^2 needs neither of the two products the
// twisted key would have fed), a store-lane-order twist, `trn1`/`trn2` mid
// packing and `stp`-based stores.  For the current size, shape and the exact
// sequence of optimizations, read the code below and
// `git log arm/gcm/gcm_init_v8.S` -- do not trust a count quoted here.
// The symbol/ABI wrapper macros and CFI annotations follow s2n-bignum house
// style, and the AArch64 BTI landing-pad macro (AARCH64_VALID_CALL_TARGET) is
// dropped.
//
// The FUNCTION computed is unchanged, and that is checked two ways: the
// verbatim AWS-LC C reference is retained as the differential-test oracle in
// tests/ref_gcm_init.c, and arm/proofs/gcm_init_v8.ml proves this instruction
// stream against the algebraic spec in common/polyval_ghash.ml.
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

	// TWIST AND SQUARE, FUSED.  With S = H<<1 (per lane), u = H>>63 (per lane)
	// and w = 0xc2000000_00000000, the twisted key's two 64-bit lanes are XORs
	// of DISJOINT summands
	//     h.d[1] = S.d[1] ^ u.d[0]                            (the low  factor)
	//     h.d[0] = S.d[0] ^ u.d[1] ^ (u.d[0] ? w : 0)         (the high factor)
	// and H^2 = L(h.d[1] (*) h.d[1]) ^ (h.d[0] (*) h.d[0]) where the Gueron
	// two-phase reduce
	//     L(x) = x ^ (x.d[1] (*) w) ^ ext(x.d[0] (*) w) ^ (((x.d[0] (*) w).d[0]) (*) w)
	// is GF(2)-LINEAR.  A carryless SQUARE is additive (cross terms cancel), so
	// both squares distribute over those summands and every u-term squares to
	// itself; collecting the u.d[0]-conditional pieces gives L(1) ^ w^2 = Q,
	// the POLYVAL modulus 0xc2000000_00000000_00000000_00000001.  Hence
	//     H^2 = L(S.d[1]^2) ^ S.d[0]^2 ^ u.d[1] ^ (u.d[0] ? Q : 0)
	// -- neither of the twisted key's own products is ever formed, and the
	// whole XOR tree hangs off the RAW key.  S.d[1] comes through the GP pipe
	// (4-cycle load + 1-cycle shift + 2-cycle fmov) so its square issues two
	// cycles before the vector shl could have delivered it.
	ldr	x3,[x1,#8]		//w1, through the GP pipe
	ld1	{v17.2d},[x1]		//load input H = {w0,w1}
	movi	v19.16b,#0xe1
	movi	v2.16b,#0
	movi	v22.16b,#0xff
	lsl	x3,x3,#1			//S.d[1]
	shl	v19.2d,v19.2d,#57		//w = {0xc2.0, 0xc2.0}
	fmov	d7,x3
	ushr	v18.2d,v17.2d,#63		//u = {bit63 w0, bit63 w1}
	sshr	v3.2d,v17.2d,#63		//lane 0 = the carry bit's mask
	ushr	v22.2d,v22.2d,#63		//{1,1}
	shl	v6.2d,v17.2d,#1			//S = {w0<<1, w1<<1}
	ext	v23.16b,v22.16b,v19.16b,#8	//Q = {1, 0xc2....00}, the modulus
	trn1	v24.2d,v3.2d,v3.2d		//carry bit's mask in BOTH lanes
	pmull	v0.1q,v7.1d,v7.1d		//A  = S.d[1]^2
	pmull	v5.1q,v6.1d,v6.1d		//     S.d[0]^2
	pmull2	v4.1q,v18.2d,v18.2d		//     u.d[1]^2 = u.d[1]
	ext	v18.16b,v18.16b,v18.16b,#8	//{bit63 w1, bit63 w0}
	and	v24.16b,v23.16b,v24.16b		//F  = carry ? Q : 0
	eor	v5.16b,v5.16b,v4.16b		//E  = S.d[0]^2 ^ u.d[1]
	pmull2	v25.1q,v0.2d,v19.2d		//B  = A.d[1] . w
	pmull	v7.1q,v0.1d,v19.1d		//aw = A.d[0] . w

	//L(A) ^ E ^ F: the five leaves A/B/ext(aw)/aw.d[0].w and E/F land two
	//cycles apart, and this tree roots one level earlier than iterating the
	//reduction would.  Of the several shapes with that same depth, THIS one
	//(the two aw-derived leaves paired first, into R(aw)) measures fastest --
	//it puts the pair whose inputs arrive LAST on its own branch, so the two
	//independent halves of the tree issue in parallel.
	ext	v1.16b,v7.16b,v7.16b,#8		//ext(aw)
	pmull	v7.1q,v7.1d,v19.1d		//aw.d[0] . w
	eor	v0.16b,v0.16b,v25.16b		//A ^ B
	eor	v5.16b,v5.16b,v24.16b		//E ^ F
	eor	v1.16b,v1.16b,v7.16b		//R(aw)
	eor	v0.16b,v0.16b,v5.16b
	eor	v17.16b,v0.16b,v1.16b		//H^2
	//the twisted key itself is only needed from here on, so it is finished
	//here, out of the head's crowded issue slots; its conditional constant is
	//F's own high lane, so no separate mask-and is needed
	orr	v20.16b,v6.16b,v18.16b		//H<<<=1 AND the low lane's 0x..01
	ext	v16.16b,v24.16b,v2.16b,#8	//C = {carry ? 0xc2.0 : 0, 0} = {F.d[1],0}
	eor	v20.16b,v20.16b,v16.16b		//twisted H, already store-lane order
	ext	v3.16b,v20.16b,v20.16b,#8	//H in multiplicand (algebraic) lane order
	ext	v22.16b,v17.16b,v17.16b,#8	//store Htable[2]
	trn1	v21.2d,v20.2d,v17.2d		//{H.d[0], H^2.d[0]}
	trn2	v1.2d,v20.2d,v17.2d		//{H.d[1], H^2.d[1]}
	eor	v21.16b,v21.16b,v1.16b		//pack Karatsuba folds, 1 level cheaper
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
	eor	v0.16b,v16.16b,v18.16b		//t = R(p_lo): M kept OFF this chain
	ext	v16.16b,v1.16b,v1.16b,#8		//R is GF(2)-linear, so the middle's
	pmull	v1.1q,v1.1d,v19.1d		//  contribution R(M) splits off and
	ext	v18.16b,v0.16b,v0.16b,#8		//  runs beside R(t) instead of ahead
	pmull	v0.1q,v0.1d,v19.1d		//  of it -- one level shorter
	eor	v1.16b,v1.16b,v16.16b		//R(M)
	eor	v18.16b,v18.16b,v0.16b		//ext(t) ^ 2nd phase
	eor	v1.16b,v1.16b,v2.16b		//R(M) ^ p_hi
	eor	v21.16b,v18.16b,v1.16b
	eor	v6.16b,v5.16b,v7.16b		//p_lo ^ p_hi   (see R-SPLIT note below)
	pmull2	v4.1q,v5.2d,v19.2d		//p_lo.d[1] . w
	pmull	v5.1q,v5.1d,v19.1d		//aw = p_lo.d[0] . w
	eor	v6.16b,v6.16b,v4.16b
	ext	v4.16b,v5.16b,v5.16b,#8
	pmull	v5.1q,v5.1d,v19.1d		//aw.d[0] . w
	eor	v4.16b,v4.16b,v5.16b
	eor	v20.16b,v6.16b,v4.16b

	ext	v23.16b,v21.16b,v21.16b,#8	//store Htable[3]
	ext	v25.16b,v20.16b,v20.16b,#8	//store Htable[5]
	trn1	v24.2d,v21.2d,v20.2d		//{H^3.d[0], H^4.d[0]}
	trn2	v18.2d,v21.2d,v20.2d		//{H^3.d[1], H^4.d[1]}
	eor	v24.16b,v24.16b,v18.16b		//pack Karatsuba folds, 1 level cheaper
	stp	q22,q23,[x0,#32]		//store Htable[2..3]
	stp	q24,q25,[x0,#64]		//store Htable[4..5]

	//H^8 = H^4.H^4 hoisted here: it needs only H^4, and block 5's issue
	//slots are the scarcest in the routine while this region's are free
	pmull	v3.1q,v20.1d,v20.1d		//p_lo (a square's middle vanishes)
	pmull2	v23.1q,v20.2d,v20.2d		//p_hi
	eor	v23.16b,v3.16b,v23.16b		//p_lo ^ p_hi
	pmull2	v24.1q,v3.2d,v19.2d		//p_lo.d[1] . w
	pmull	v3.1q,v3.1d,v19.1d		//aw = p_lo.d[0] . w
	eor	v23.16b,v23.16b,v24.16b
	ext	v24.16b,v3.16b,v3.16b,#8
	pmull	v3.1q,v3.1d,v19.1d		//aw.d[0] . w
	eor	v24.16b,v24.16b,v3.16b
	eor	v23.16b,v23.16b,v24.16b		//H^8
	ext	v31.16b,v23.16b,v23.16b,#8	//store Htable[11]
	eor	v24.16b,v23.16b,v31.16b		//Karatsuba fold of H^8, hoisted too

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
	eor	v6.16b,v5.16b,v7.16b		//p_lo ^ p_hi   (see R-SPLIT note below)
	pmull2	v4.1q,v5.2d,v19.2d		//p_lo.d[1] . w
	pmull	v5.1q,v5.1d,v19.1d		//aw = p_lo.d[0] . w
	eor	v6.16b,v6.16b,v4.16b
	ext	v4.16b,v5.16b,v5.16b,#8
	pmull	v5.1q,v5.1d,v19.1d		//aw.d[0] . w
	eor	v4.16b,v4.16b,v5.16b
	eor	v17.16b,v6.16b,v4.16b

	ext	v26.16b,v16.16b,v16.16b,#8	//store Htable[6]
	ext	v28.16b,v17.16b,v17.16b,#8	//store Htable[8]
	trn1	v27.2d,v16.2d,v17.2d		//{H^5.d[0], H^6.d[0]}
	trn2	v18.2d,v16.2d,v17.2d		//{H^5.d[1], H^6.d[1]}
	eor	v27.16b,v27.16b,v18.16b		//pack Karatsuba folds, 1 level cheaper
	stp	q26,q27,[x0,#96]		//store Htable[6..7]

	//calculate H^7 = H^4.H^3 and H^8 = H^4.H^4 (depth 3: both feed off H^3/H^4)
	pmull	v0.1q,v20.1d,v21.1d		//p_lo  = a_lo . b_lo
	pmull2	v2.1q,v20.2d,v21.2d		//p_hi  = a_hi . b_hi
	pmull2	v1.1q,v25.2d,v21.2d		//cross = a_lo . b_hi
	pmull	v16.1q,v25.1d,v21.1d		//cross = a_hi . b_lo

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

	ext	v29.16b,v16.16b,v16.16b,#8	//store Htable[9]
	eor	v18.16b,v16.16b,v29.16b		//Karatsuba fold of H^7
	ext	v30.16b,v18.16b,v24.16b,#8	//pack Karatsuba pre-processed
	stp	q28,q29,[x0,#128]		//store Htable[8..9]
	stp	q30,q31,[x0,#160]		//store Htable[10..11]
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(gcm_init_v8)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
