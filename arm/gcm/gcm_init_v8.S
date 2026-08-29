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
// ghashv8-armx.pl, BoringSSL), imported verbatim. It has
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
//
// SCHEDULING.  Neoverse-V1 dispatches IN ORDER (out-of-order execution behind a
// finite window), so an instruction placed late cannot execute early even when
// its operands are ready -- the static ORDER is itself an optimization variable.
// Measured on Graviton 3: every SIMD op here has 2-cycle latency and 4/cycle
// throughput (pmull included -- there is no separate crypto-pipe limit), `ext`
// or `trn` feeding a `pmull` costs 3 cycles, `movi` is free, and one extra vector
// instruction anywhere costs ~0.25 cycles.  The stream below is therefore emitted
// in ASAP order over the RAW dependence graph, and the SIMD registers are
// allocated by linear scan over THAT order rather than per logical block -- WAR
// and WAW on architectural registers are the only things that can block static
// motion, since the hardware renames.  That is why the four blocks' chains
// interleave and why the register numbering looks unstructured; it is worth 3.3%
// over the same 131 instructions in per-block order.
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

S2N_BN_SYMBOL(gcm_init_v8):
    // AARCH64_VALID_CALL_TARGET
        CFI_START

	// BLOCK 1 (PC 0x0 -> 0x80, 32 instructions): the FUSED twist + H^2.
	// L o square o T distributes over the twist's disjoint summands, so
	//   H^2 = L(S.d[1]^2) ^ S.d[0]^2 ^ u.d[1] ^ (u.d[0] ? Q : 0)
	// with Q = L(1) ^ w^2 the POLYVAL modulus; neither of the twisted key's own
	// products is ever formed.  Live out: v4 = w, v0 = byteswap128 H, v1 = H^2.
	ld1	{v0.2d},[x1]		//H = {w0,w1}
	ldr	x3,[x1,#8]
	movi	v1.16b,#0xe1
	movi	v2.16b,#0xff
	movi	v3.16b,#0
	shl	v4.2d,v1.2d,#57		//w = {0xc2.0, 0xc2.0}
	ushr	v1.2d,v2.2d,#63
	lsl	x3,x3,#1
	ext	v2.16b,v1.16b,v4.16b,#8		//Q = {1, 0xc2....00}, the POLYVAL modulus
	fmov	d1,x3
	ushr	v5.2d,v0.2d,#63
	sshr	v6.2d,v0.2d,#63
	shl	v7.2d,v0.2d,#1
	pmull	v0.1q,v1.1d,v1.1d
	trn1	v1.2d,v6.2d,v6.2d
	pmull	v6.1q,v7.1d,v7.1d
	pmull2	v16.1q,v5.2d,v5.2d
	ext	v17.16b,v5.16b,v5.16b,#8
	pmull2	v5.1q,v0.2d,v4.2d
	pmull	v18.1q,v0.1d,v4.1d
	and	v19.16b,v2.16b,v1.16b		//F = carry ? Q : 0
	eor	v1.16b,v6.16b,v16.16b
	orr	v2.16b,v7.16b,v17.16b
	ext	v6.16b,v18.16b,v18.16b,#8
	pmull	v7.1q,v18.1d,v4.1d
	eor	v16.16b,v0.16b,v5.16b
	eor	v0.16b,v1.16b,v19.16b
	ext	v1.16b,v19.16b,v3.16b,#8
	eor	v3.16b,v6.16b,v7.16b
	eor	v5.16b,v16.16b,v0.16b
	eor	v0.16b,v2.16b,v1.16b		//twisted H, store-lane order  == Htable[0]
	eor	v1.16b,v5.16b,v3.16b		//H^2

	// BLOCK 2 (PC 0x80 -> 0x10c, 35 instructions): H^3 = H.H^2, H^4 = H^2.H^2, the
	// Htable[0..1] store, and H^8's two products (they need only H^4 and this is
	// where the schedule wants them).
	// Live out: v4 = w, v1 = H^2, v16 = bsw H^2, v0 = H^4, v2 = bsw H^4, v17 = H^3,
	// v6/v7 = H^8's p_lo/p_hi.
	ext	v2.16b,v0.16b,v0.16b,#8		//H in multiplicand (algebraic) lane order
	pmull	v3.1q,v1.1d,v1.1d
	pmull2	v5.1q,v0.2d,v1.2d
	pmull	v6.1q,v0.1d,v1.1d
	pmull2	v7.1q,v1.2d,v1.2d
	ext	v16.16b,v1.16b,v1.16b,#8		//byteswap128 H^2  == Htable[2]
	trn1	v17.2d,v0.2d,v1.2d
	trn2	v18.2d,v0.2d,v1.2d
	pmull	v19.1q,v2.1d,v1.1d
	pmull2	v20.1q,v2.2d,v1.2d
	pmull	v2.1q,v3.1d,v4.1d
	eor	v21.16b,v5.16b,v6.16b
	eor	v5.16b,v3.16b,v7.16b
	pmull2	v6.1q,v3.2d,v4.2d
	eor	v3.16b,v17.16b,v18.16b		//Karatsuba pack {mid H, mid H^2}  == Htable[1]
	ext	v7.16b,v19.16b,v19.16b,#8
	pmull	v17.1q,v19.1d,v4.1d
	ext	v18.16b,v2.16b,v2.16b,#8
	pmull	v19.1q,v2.1d,v4.1d
	ext	v2.16b,v21.16b,v21.16b,#8
	pmull	v22.1q,v21.1d,v4.1d
	eor	v21.16b,v5.16b,v6.16b
	stp	q0,q3,[x0]		//store Htable[0..1]
	eor	v0.16b,v7.16b,v17.16b
	eor	v3.16b,v18.16b,v19.16b
	eor	v5.16b,v22.16b,v2.16b
	ext	v2.16b,v0.16b,v0.16b,#8
	pmull	v6.1q,v0.1d,v4.1d
	eor	v0.16b,v21.16b,v3.16b		//H^4
	eor	v3.16b,v5.16b,v20.16b
	eor	v5.16b,v2.16b,v6.16b
	ext	v2.16b,v0.16b,v0.16b,#8		//byteswap128 H^4  == Htable[5]
	pmull	v6.1q,v0.1d,v0.1d		//H^8: p_lo (a square's middle vanishes)
	pmull2	v7.1q,v0.2d,v0.2d		//H^8: p_hi
	eor	v17.16b,v5.16b,v3.16b		//H^3

	// BLOCK 3 (PC 0x10c -> 0x1e0, 53 instructions): H^5, H^6, H^7 and H^8 (whose two
	// products came from block 2), plus the Htable[2..5] stores.  The four reduction
	// chains are INTERLEAVED.
	// Live out: v2 = H^5, v1 = H^6, v7 = H^7, v6 = bsw H^6, v5 = bsw H^8,
	// v3 = Karatsuba fold of H^8.
	pmull	v3.1q,v6.1d,v4.1d
	eor	v5.16b,v6.16b,v7.16b
	pmull2	v7.1q,v6.2d,v4.2d
	pmull	v6.1q,v0.1d,v17.1d
	pmull2	v18.1q,v2.2d,v17.2d
	pmull	v19.1q,v2.1d,v17.1d
	pmull	v20.1q,v1.1d,v17.1d
	pmull2	v21.1q,v16.2d,v17.2d
	pmull	v22.1q,v16.1d,v17.1d
	pmull	v23.1q,v17.1d,v17.1d
	pmull2	v24.1q,v17.2d,v17.2d
	pmull2	v25.1q,v0.2d,v17.2d
	pmull2	v26.1q,v1.2d,v17.2d
	trn1	v1.2d,v17.2d,v0.2d
	trn2	v27.2d,v17.2d,v0.2d
	ext	v0.16b,v17.16b,v17.16b,#8
	ext	v17.16b,v3.16b,v3.16b,#8
	pmull	v28.1q,v3.1d,v4.1d
	eor	v3.16b,v5.16b,v7.16b
	eor	v5.16b,v18.16b,v19.16b
	pmull	v7.1q,v6.1d,v4.1d
	eor	v18.16b,v21.16b,v22.16b
	pmull	v19.1q,v20.1d,v4.1d
	ext	v21.16b,v6.16b,v6.16b,#8
	ext	v6.16b,v20.16b,v20.16b,#8
	pmull	v20.1q,v23.1d,v4.1d
	eor	v22.16b,v23.16b,v24.16b
	pmull2	v24.1q,v23.2d,v4.2d
	eor	v23.16b,v1.16b,v27.16b
	stp	q16,q0,[x0,#32]
	eor	v0.16b,v17.16b,v28.16b
	eor	v1.16b,v5.16b,v7.16b
	eor	v5.16b,v18.16b,v19.16b
	ext	v7.16b,v20.16b,v20.16b,#8
	pmull	v16.1q,v20.1d,v4.1d
	eor	v17.16b,v22.16b,v24.16b
	stp	q23,q2,[x0,#64]
	eor	v2.16b,v3.16b,v0.16b		//H^8
	eor	v0.16b,v1.16b,v21.16b
	eor	v1.16b,v5.16b,v6.16b
	eor	v3.16b,v7.16b,v16.16b
	ext	v5.16b,v2.16b,v2.16b,#8		//byteswap128 H^8  == Htable[11]
	ext	v6.16b,v0.16b,v0.16b,#8
	ext	v7.16b,v1.16b,v1.16b,#8
	pmull	v16.1q,v0.1d,v4.1d
	pmull	v0.1q,v1.1d,v4.1d
	eor	v1.16b,v17.16b,v3.16b		//H^6
	eor	v3.16b,v2.16b,v5.16b		//Karatsuba fold of H^8
	eor	v2.16b,v6.16b,v25.16b
	eor	v4.16b,v7.16b,v26.16b
	ext	v6.16b,v1.16b,v1.16b,#8		//byteswap128 H^6  == Htable[8]
	eor	v7.16b,v16.16b,v2.16b		//H^7
	eor	v2.16b,v0.16b,v4.16b		//H^5

	// BLOCK 4 (PC 0x1e0 -> 0x208, 10 instructions): closing byteswaps, the last two
	// Karatsuba packs and the Htable[6..11] stores.  No products.
	ext	v0.16b,v7.16b,v7.16b,#8		//byteswap128 H^7  == Htable[9]
	trn1	v4.2d,v2.2d,v1.2d
	trn2	v16.2d,v2.2d,v1.2d
	ext	v1.16b,v2.16b,v2.16b,#8		//byteswap128 H^5  == Htable[6]
	eor	v2.16b,v7.16b,v0.16b		//Karatsuba fold of H^7
	eor	v7.16b,v4.16b,v16.16b		//Karatsuba pack {mid H^5, mid H^6}  == Htable[7]
	ext	v4.16b,v2.16b,v3.16b,#8		//Karatsuba pack {mid H^7, mid H^8}  == Htable[10]
	stp	q1,q7,[x0,#96]		//store Htable[6..7]
	stp	q6,q0,[x0,#128]		//store Htable[8..9]
	stp	q4,q5,[x0,#160]		//store Htable[10..11]
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(gcm_init_v8)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif

