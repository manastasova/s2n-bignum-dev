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
// (H^5 = H.H^4, H^6 = H^3.H^3, H^7 = H^3.H^4, H^8 = H^4.H^4), Frobenius-free
// squares, the two-phase
// Gueron reduction expanded by linearity rather than iterated (for H^2 all the
// way through the twist, so that H^2 needs neither of the two products the
// twisted key would have fed), a store-lane-order twist, Karatsuba mids packed
// from the folds x ^ byteswap128 x (the byteswaps the table needs anyway) and
// `stp`-based stores.  For the current size, shape and the exact
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
// The stream below is therefore NOT a hand schedule and not ASAP order either:
// it is the best topological order of the whole RAW dependence graph found by a
// stochastic list-scheduling search scored on hardware, with every SIMD register
// re-allocated by linear scan over that order -- WAR and WAW on architectural
// registers are the only things that can block static motion, since the hardware
// renames.  That is why the six power chains interleave and why the register
// numbering looks unstructured; ordering alone (no algebra change) is worth about
// 4.5% over the same instructions in 018's ASAP order, and the folds plus
// H^5 = H.H^4 take it to 7.8%.
//
// Do not "tidy" it back into per-power blocks, and do not perturb it casually:
// measured on Graviton 3 against benchmarks/benchmark.c, this order sits in a
// SHARP local optimum.  Swapping the two adjacent, independent, register-safe
// `ext`s near the end costs 4.8%; each of the 33 legal single-instruction moves
// in the tail costs between 0.18% and 5%; one `nop` inserted before the `ret`
// costs 1.9%, while four `nop`s inserted together at one particular mid-stream
// point cost only 0.17% (at another mid-stream point they cost 5.9%) -- the cost
// of an instruction here is strongly POSITIONAL, not uniform.  Freeing any
// single instruction's operands -- all 124 probed -- gains at most 0.11%, so no
// one latency edge gates it either.  The sensitivity is not even confined to
// timing: changing ONE source register of ONE `pmull` to a register that holds
// an equally-early value costs 4.7%, with the opcode, the position, the register
// allocation and the dependence height all unchanged (session 021, reproduced by
// full rebuild), while renaming every register, swapping a commutative operand
// pair, or changing the VALUES a node computes are all free to within 0.15%.
// So: re-search the whole order after any edit here; never hand-patch it.
// (An earlier version of this comment claimed the routine was near a RESOURCE
// floor derived from a dependency-free clone.  That was measured with a harness
// later shown to be anti-correlated with the benchmark; re-measured properly the
// clone is 11% SLOWER than this code, because stripping the dependences also
// strips operand forwarding, so it is not a floor at all.)
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

	// ---BODY-BEGIN---   (markers for the benchmarking harnesses: everything
	// between them is the routine body, with no prologue/epilogue and no `ret`.
	// An extractor anchored on the first `ldr`/`ld1` instead silently drops the
	// leading `movi`s whenever the schedule moves them, and then benchmarks the
	// wrong code -- that cost session 019 a whole screening pass.)

	// BLOCK 1 (PC 0x0 -> 0x80, 32 instructions): the FUSED twist + H^2.
	// L o square o T distributes over the twist's disjoint summands, so
	//   H^2 = L(S.d[1]^2) ^ S.d[0]^2 ^ u.d[1] ^ (u.d[0] ? Q : 0)
	// with Q = L(1) ^ w^2 the POLYVAL modulus; neither of the twisted key's own
	// products is ever formed.  Live out: v4 = w, v0 = byteswap128 H, v1 = H^2.
	ld1	{v0.2d},[x1]
	ldr	x3,[x1,#8]
	movi	v1.16b,#0xe1
	movi	v2.16b,#0xff
	movi	v3.16b,#0x0
	shl	v4.2d,v1.2d,#57		//w = {0xc2..0, 0xc2..0}
	ushr	v1.2d,v2.2d,#63
	ushr	v2.2d,v0.2d,#63
	lsl	x4,x3,#1
	ext	v5.16b,v1.16b,v4.16b,#8		//Q = {1, 0xc2....00}, the POLYVAL modulus
	fmov	d1,x4
	sshr	v6.2d,v0.2d,#63
	shl	v7.2d,v0.2d,#1
	pmull	v0.1q,v1.1d,v1.1d
	trn1	v1.2d,v6.2d,v6.2d
	pmull	v6.1q,v7.1d,v7.1d
	pmull2	v16.1q,v2.2d,v2.2d
	ext	v17.16b,v2.16b,v2.16b,#8
	pmull2	v2.1q,v0.2d,v4.2d
	pmull	v18.1q,v0.1d,v4.1d
	and	v19.16b,v5.16b,v1.16b		//F = carry ? Q : 0
	eor	v1.16b,v6.16b,v16.16b		//(S.d[0] ^ u.d[1])^2 -- a carryless square is ADDITIVE
	orr	v5.16b,v7.16b,v17.16b
	ext	v6.16b,v18.16b,v18.16b,#8
	pmull	v7.1q,v18.1d,v4.1d
	eor	v16.16b,v0.16b,v2.16b
	eor	v0.16b,v1.16b,v19.16b
	ext	v1.16b,v19.16b,v3.16b,#8
	eor	v2.16b,v6.16b,v7.16b
	eor	v3.16b,v16.16b,v0.16b
	eor	v0.16b,v5.16b,v1.16b		//twisted H, store-lane order  == Htable[0]
	eor	v1.16b,v3.16b,v2.16b		//H^2

	// BLOCK 2 (PC 0x80 -> 0x1e4, 89 instructions): ALL SIX remaining powers --
	// H^3 = H.H^2, H^4 = H^2.H^2, H^5 = H.H^4, H^6 = H^3.H^3, H^7 = H^4.H^3,
	// H^8 = H^4.H^4 -- plus the Htable[0..5] stores.  The six reduction chains are
	// fully INTERLEAVED because the order is a search over topological orders of the
	// whole dependence graph, and the exit is the only PC in here at which every
	// live value is a NAMED quantity.  Live out: v1 = H^5, v3 = H^6, v16 = H^7,
	// v6 = bsw H^5, v5 = bsw H^6, v0 = bsw H^8, v4 = fold(H^8).
	ext	v2.16b,v0.16b,v0.16b,#8		//H in multiplicand (algebraic) lane order
	pmull	v3.1q,v1.1d,v1.1d
	pmull	v5.1q,v0.1d,v1.1d
	pmull2	v6.1q,v0.2d,v1.2d
	pmull2	v7.1q,v1.2d,v1.2d
	ext	v16.16b,v1.16b,v1.16b,#8		//byteswap128 H^2  == Htable[2]
	eor	v17.16b,v0.16b,v2.16b		//fold(H) = {mid H, mid H}
	pmull2	v18.1q,v2.2d,v1.2d
	pmull	v19.1q,v2.1d,v1.1d
	pmull	v20.1q,v3.1d,v4.1d
	eor	v21.16b,v6.16b,v5.16b
	pmull2	v5.1q,v3.2d,v4.2d
	eor	v6.16b,v3.16b,v7.16b
	eor	v3.16b,v1.16b,v16.16b		//fold(H^2)
	ext	v1.16b,v19.16b,v19.16b,#8
	pmull	v7.1q,v19.1d,v4.1d
	ext	v19.16b,v20.16b,v20.16b,#8
	pmull	v22.1q,v20.1d,v4.1d
	ext	v20.16b,v21.16b,v21.16b,#8
	pmull	v23.1q,v21.1d,v4.1d
	eor	v21.16b,v6.16b,v5.16b
	ext	v5.16b,v17.16b,v3.16b,#8		//Karatsuba pack {mid H, mid H^2}  == Htable[1]
	eor	v3.16b,v1.16b,v7.16b
	eor	v1.16b,v19.16b,v22.16b
	eor	v6.16b,v23.16b,v20.16b
	stp	q0,q5,[x0]		//store Htable[0..1]
	ext	v5.16b,v3.16b,v3.16b,#8
	pmull	v7.1q,v3.1d,v4.1d
	eor	v3.16b,v21.16b,v1.16b		//H^4
	eor	v1.16b,v6.16b,v18.16b
	eor	v6.16b,v5.16b,v7.16b
	ext	v5.16b,v3.16b,v3.16b,#8		//byteswap128 H^4  == Htable[5]
	pmull2	v7.1q,v0.2d,v3.2d
	pmull	v17.1q,v2.1d,v3.1d
	pmull	v18.1q,v0.1d,v3.1d
	pmull	v0.1q,v3.1d,v3.1d		//H^8: p_lo (a square's middle vanishes)
	pmull2	v19.1q,v3.2d,v3.2d		//H^8: p_hi
	pmull2	v20.1q,v2.2d,v3.2d
	eor	v2.16b,v6.16b,v1.16b		//H^3
	eor	v1.16b,v7.16b,v18.16b
	pmull	v6.1q,v17.1d,v4.1d
	ext	v7.16b,v17.16b,v17.16b,#8
	pmull	v17.1q,v0.1d,v4.1d
	eor	v18.16b,v0.16b,v19.16b
	pmull2	v19.1q,v0.2d,v4.2d
	eor	v0.16b,v3.16b,v5.16b		//fold(H^4)
	pmull	v21.1q,v3.1d,v2.1d
	pmull2	v22.1q,v5.2d,v2.2d
	pmull	v23.1q,v5.1d,v2.1d
	pmull	v24.1q,v2.1d,v2.1d
	pmull2	v25.1q,v2.2d,v2.2d
	pmull2	v26.1q,v3.2d,v2.2d
	eor	v3.16b,v1.16b,v6.16b
	ext	v1.16b,v17.16b,v17.16b,#8
	pmull	v6.1q,v17.1d,v4.1d
	ext	v17.16b,v2.16b,v2.16b,#8		//byteswap128 H^3  == Htable[3]
	eor	v27.16b,v22.16b,v23.16b
	eor	v22.16b,v18.16b,v19.16b
	ext	v18.16b,v21.16b,v21.16b,#8
	pmull	v19.1q,v21.1d,v4.1d
	pmull	v21.1q,v24.1d,v4.1d
	eor	v23.16b,v24.16b,v25.16b
	pmull2	v25.1q,v24.2d,v4.2d
	eor	v24.16b,v2.16b,v17.16b		//fold(H^3)
	stp	q16,q17,[x0,#32]		//store Htable[2..3]
	eor	v2.16b,v3.16b,v7.16b
	eor	v3.16b,v1.16b,v6.16b
	eor	v1.16b,v27.16b,v19.16b
	ext	v6.16b,v21.16b,v21.16b,#8
	pmull	v7.1q,v21.1d,v4.1d
	eor	v16.16b,v23.16b,v25.16b
	ext	v17.16b,v24.16b,v0.16b,#8		//Karatsuba pack {mid H^3, mid H^4}  == Htable[4]
	ext	v0.16b,v2.16b,v2.16b,#8
	pmull	v19.1q,v2.1d,v4.1d
	eor	v2.16b,v22.16b,v3.16b		//H^8
	eor	v3.16b,v1.16b,v18.16b
	eor	v1.16b,v6.16b,v7.16b
	stp	q17,q5,[x0,#64]		//store Htable[4..5]
	eor	v5.16b,v0.16b,v20.16b
	ext	v0.16b,v2.16b,v2.16b,#8		//byteswap128 H^8  == Htable[11]
	ext	v6.16b,v3.16b,v3.16b,#8
	pmull	v7.1q,v3.1d,v4.1d
	eor	v3.16b,v16.16b,v1.16b		//H^6
	eor	v1.16b,v19.16b,v5.16b		//H^5
	eor	v4.16b,v2.16b,v0.16b		//fold(H^8)
	eor	v2.16b,v6.16b,v26.16b
	ext	v5.16b,v3.16b,v3.16b,#8		//byteswap128 H^6  == Htable[8]
	ext	v6.16b,v1.16b,v1.16b,#8		//byteswap128 H^5  == Htable[6]
	eor	v16.16b,v7.16b,v2.16b		//H^7

	// BLOCK 3 (PC 0x1e4 -> 0x208, 9 instructions): byteswap128 H^7, the last two
	// Karatsuba packs and the Htable[6..11] stores.  No products.
	eor	v2.16b,v3.16b,v5.16b		//fold(H^6)
	eor	v3.16b,v1.16b,v6.16b		//fold(H^5)
	ext	v1.16b,v16.16b,v16.16b,#8		//byteswap128 H^7  == Htable[9]
	ext	v7.16b,v3.16b,v2.16b,#8		//Karatsuba pack {mid H^5, mid H^6}  == Htable[7]
	eor	v2.16b,v16.16b,v1.16b		//fold(H^7)
	stp	q5,q1,[x0,#128]		//store Htable[8..9]
	ext	v1.16b,v2.16b,v4.16b,#8		//Karatsuba pack {mid H^7, mid H^8}  == Htable[10]
	stp	q6,q7,[x0,#96]		//store Htable[6..7]
	stp	q1,q0,[x0,#160]		//store Htable[10..11]
	// ---BODY-END---
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(gcm_init_v8)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
