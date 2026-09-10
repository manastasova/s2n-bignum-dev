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
// twisted key would have fed), a store-lane-order twist whose conditional
// modulus is a single `pmull` by the carry bit rather than a masked constant,
// Karatsuba mids packed as trn1(A,B) ^ trn2(A,B) off the two RAW powers, and
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
// 4.5% over the same instructions in 018's ASAP order, and the algebra changes
// on top of that take the whole routine from 37.3 ns at import to 16.35 ns.
//
// The last two of those changes are worth stating as a rule, because they are
// what session 021 found and they cut BOTH size and depth: (a) the twist's
// conditional modulus does not have to be materialised -- `u = H >>u 63` already
// holds the carry as an integer 0/1, so `pmull(u.d[0], w)` IS the masked constant
// and `trn1(u ^ ext(u), that)` is the whole thing (-7 instructions); and (b) a
// Karatsuba mid pack is `trn1(A,B) ^ trn2(A,B)`, exactly as many instructions as
// building it out of the folds A ^ byteswap128 A but TWO CYCLES shallower,
// because it reads the powers raw instead of waiting on their byteswaps.  Since
// the last pack is the last thing the routine computes, that is 2 cycles off the
// dependence height of the whole function.  Measured on Graviton 3, one cycle of
// dependence height at CONSTANT instruction count is worth 0.5-0.8% of runtime.
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
//
// And do not assume a re-search will get the speed back.  Sampling INDEPENDENT
// topological orders of a graph (one official benchmark evaluation each) finds
// this ~42.3-cycle steady state for about 0.3% of the orders of THIS graph -- 20
// hits in 6000 draws, best -0.13% -- so it is findable, and it is a plateau, not
// a continuum: nothing faster exists for this graph.  But the same sampler, run
// on fifteen correct algebraic variants (including every one that lowers the
// dependence height to the Kraft floor of 48), does not reach it even once in
// ~55000 draws; the best order of the best variant is +4%.  Deleting three
// instructions while keeping every survivor in its exact relative order here is
// +10.2%.  The fast steady state is a property of this exact instruction
// sequence, not of a lucky permutation, so measure a candidate graph by sampling
// ~500 orders of it (with this one as a control in the same batch) before
// spending hours of search on it.
// (An earlier version of this comment claimed the routine was near a RESOURCE
// floor derived from a dependency-free clone.  That was measured with a harness
// later shown to be anti-correlated with the benchmark, and the clone itself was
// built wrong: rewiring every source to a register the function never writes
// caps issue at exactly 2.00 ops/cycle -- against 3.9 for the same ops reading
// values produced in the same call -- so such a clone measures ~36% SLOWER than
// this code and bounds nothing.  A clone must source from in-body registers.)
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

	// BLOCK 1 (PC 0x0 -> 0x64, 25 instructions): the FUSED twist + H^2.
	// L o square o T distributes over the twist's disjoint summands, so
	//   H^2 = L(S.d[1]^2) ^ S.d[0]^2 ^ u.d[1] ^ (u.d[0] ? Q : 0)
	// with Q = L(1) ^ w^2 the POLYVAL modulus; neither of the twisted key's own
	// products is ever formed.  And the modulus is never BUILT either: u = H >>u 63
	// already holds the carry as the integer 0/1 in lane 0, so pmull(u.d[0], w) IS
	// {carry ? 0xc2..00 : 0, 0} and trn1(u ^ ext(u), that) is the masked modulus
	// with u.d[1] already folded in -- which retires the 0xff and 0x0 `movi`s, the
	// {1,1}, the `ext` that assembled Q, the `sshr` mask and its `trn1` broadcast,
	// the `and`, and one `eor`.  Live out: v2 = w, v0 = byteswap128 H, v3 = H^2.
	ld1	{v0.2d},[x1]
	ldr	x3,[x1,#8]
	movi	v1.16b,#0xe1
	shl	v2.2d,v1.2d,#57		//w = {0xc2..0, 0xc2..0}
	ushr	v1.2d,v0.2d,#63		//u = H >>u 63 per lane: the carry as an INTEGER 0/1 in lane 0
	lsl	x4,x3,#1
	fmov	d3,x4
	shl	v4.2d,v0.2d,#1
	pmull	v0.1q,v3.1d,v3.1d		//(S.d[1])^2 -- via the GP pipe, two cycles before a vector shl could
	pmull	v3.1q,v4.1d,v4.1d		//(S.d[0])^2
	ext	v5.16b,v1.16b,v1.16b,#8
	pmull2	v6.1q,v0.2d,v2.2d
	pmull	v7.1q,v0.1d,v2.1d
	orr	v16.16b,v4.16b,v5.16b
	ext	v4.16b,v7.16b,v7.16b,#8
	pmull	v17.1q,v7.1d,v2.1d
	pmull	v7.1q,v1.1d,v2.1d		//pmull(u.d[0], w) IS {carry ? 0xc2..00 : 0, 0} -- no mask, no modulus
	eor	v18.16b,v1.16b,v5.16b
	eor	v1.16b,v0.16b,v3.16b
	eor	v0.16b,v16.16b,v7.16b		//twisted H, store-lane order  == Htable[0]
	trn1	v3.2d,v18.2d,v7.2d		//{carry ^ u.d[1], carry ? 0xc2..00 : 0} == the masked POLYVAL modulus ^ u.d[1]
	eor	v5.16b,v6.16b,v1.16b
	eor	v1.16b,v4.16b,v17.16b
	eor	v4.16b,v3.16b,v5.16b
	eor	v3.16b,v1.16b,v4.16b		//H^2

	// BLOCK 2 (PC 0x64 -> 0x1c4, 88 instructions): ALL SIX remaining powers --
	// H^3 = H.H^2, H^4 = H^2.H^2, H^5 = H.H^4, H^6 = H^3.H^3, H^7 = H^4.H^3,
	// H^8 = H^4.H^4 -- plus Htable[0..5].  The six reduction chains are fully
	// INTERLEAVED because the order is a search over topological orders of the
	// whole dependence graph, and the exit is the only PC in here at which every
	// live value is a NAMED quantity.  Live out: v2 = H^5, v4 = H^6, v16 = H^7,
	// v0 = H^8, v7 = bsw H^5, v5 = bsw H^6, v3 = bsw H^8.
	ext	v1.16b,v0.16b,v0.16b,#8		//H in multiplicand (algebraic) lane order
	pmull	v4.1q,v3.1d,v3.1d
	pmull	v5.1q,v0.1d,v3.1d
	pmull2	v6.1q,v0.2d,v3.2d
	pmull2	v7.1q,v3.2d,v3.2d
	ext	v16.16b,v3.16b,v3.16b,#8		//byteswap128 H^2  == Htable[2]
	pmull2	v17.1q,v1.2d,v3.2d
	pmull	v18.1q,v1.1d,v3.1d
	pmull	v19.1q,v4.1d,v2.1d
	eor	v20.16b,v6.16b,v5.16b
	pmull	v5.1q,v19.1d,v2.1d
	pmull2	v6.1q,v4.2d,v2.2d
	eor	v21.16b,v4.16b,v7.16b
	ext	v4.16b,v18.16b,v18.16b,#8
	pmull	v7.1q,v18.1d,v2.1d
	ext	v18.16b,v19.16b,v19.16b,#8
	ext	v19.16b,v20.16b,v20.16b,#8
	pmull	v22.1q,v20.1d,v2.1d
	eor	v20.16b,v21.16b,v6.16b
	trn1	v6.2d,v0.2d,v3.2d
	trn2	v21.2d,v0.2d,v3.2d
	eor	v3.16b,v6.16b,v21.16b		//{mid H, mid H^2}  == Htable[1]
	eor	v6.16b,v4.16b,v7.16b
	eor	v4.16b,v18.16b,v5.16b
	eor	v5.16b,v22.16b,v19.16b
	stp	q0,q3,[x0]		//store Htable[0..1]
	ext	v3.16b,v6.16b,v6.16b,#8
	pmull	v7.1q,v6.1d,v2.1d
	eor	v6.16b,v20.16b,v4.16b		//H^4
	eor	v4.16b,v5.16b,v17.16b
	eor	v5.16b,v3.16b,v7.16b
	ext	v3.16b,v6.16b,v6.16b,#8		//byteswap128 H^4  == Htable[5]
	pmull	v7.1q,v0.1d,v6.1d
	pmull2	v17.1q,v0.2d,v6.2d
	pmull	v0.1q,v1.1d,v6.1d
	pmull	v18.1q,v6.1d,v6.1d		//H^8: p_lo (a square's middle vanishes)
	pmull2	v19.1q,v6.2d,v6.2d		//H^8: p_hi
	pmull2	v20.1q,v1.2d,v6.2d
	eor	v1.16b,v5.16b,v4.16b		//H^3
	eor	v4.16b,v17.16b,v7.16b
	pmull	v5.1q,v0.1d,v2.1d
	ext	v7.16b,v0.16b,v0.16b,#8
	pmull	v0.1q,v18.1d,v2.1d
	eor	v17.16b,v18.16b,v19.16b
	pmull2	v19.1q,v18.2d,v2.2d
	pmull	v18.1q,v6.1d,v1.1d
	pmull2	v21.1q,v3.2d,v1.2d
	pmull	v22.1q,v3.1d,v1.1d
	pmull	v23.1q,v1.1d,v1.1d
	pmull2	v24.1q,v1.2d,v1.2d
	pmull2	v25.1q,v6.2d,v1.2d
	eor	v26.16b,v4.16b,v5.16b
	ext	v4.16b,v0.16b,v0.16b,#8
	pmull	v5.1q,v0.1d,v2.1d
	ext	v0.16b,v1.16b,v1.16b,#8		//byteswap128 H^3  == Htable[3]
	eor	v27.16b,v17.16b,v19.16b
	ext	v17.16b,v18.16b,v18.16b,#8
	pmull	v19.1q,v18.1d,v2.1d
	pmull	v18.1q,v23.1d,v2.1d
	eor	v28.16b,v23.16b,v24.16b
	pmull2	v24.1q,v23.2d,v2.2d
	stp	q16,q0,[x0,#32]		//store Htable[2..3]
	eor	v0.16b,v26.16b,v7.16b
	eor	v7.16b,v4.16b,v5.16b
	ext	v4.16b,v18.16b,v18.16b,#8
	pmull	v5.1q,v18.1d,v2.1d
	eor	v16.16b,v28.16b,v24.16b
	trn1	v18.2d,v1.2d,v6.2d
	trn2	v23.2d,v1.2d,v6.2d
	eor	v1.16b,v18.16b,v23.16b		//{mid H^3, mid H^4}  == Htable[4]
	ext	v6.16b,v0.16b,v0.16b,#8
	pmull	v18.1q,v0.1d,v2.1d
	eor	v0.16b,v27.16b,v7.16b		//H^8
	eor	v7.16b,v21.16b,v22.16b
	eor	v21.16b,v17.16b,v19.16b
	eor	v17.16b,v7.16b,v21.16b
	eor	v7.16b,v4.16b,v5.16b
	stp	q1,q3,[x0,#64]		//store Htable[4..5]
	eor	v1.16b,v6.16b,v20.16b
	ext	v3.16b,v0.16b,v0.16b,#8		//byteswap128 H^8  == Htable[11]
	eor	v4.16b,v16.16b,v7.16b		//H^6
	ext	v5.16b,v17.16b,v17.16b,#8
	pmull	v6.1q,v17.1d,v2.1d
	eor	v2.16b,v18.16b,v1.16b		//H^5
	eor	v1.16b,v5.16b,v25.16b
	ext	v5.16b,v4.16b,v4.16b,#8		//byteswap128 H^6  == Htable[8]
	ext	v7.16b,v2.16b,v2.16b,#8		//byteswap128 H^5  == Htable[6]
	eor	v16.16b,v6.16b,v1.16b		//H^7

	// BLOCK 3 (PC 0x1c4 -> 0x1ec, 10 instructions): byteswap128 H^7, the last two
	// Karatsuba packs and Htable[6..11].  No products.
	ext	v1.16b,v16.16b,v16.16b,#8		//byteswap128 H^7  == Htable[9]
	trn1	v6.2d,v2.2d,v4.2d
	trn2	v17.2d,v2.2d,v4.2d
	eor	v2.16b,v6.16b,v17.16b		//{mid H^5, mid H^6}  == Htable[7]
	stp	q5,q1,[x0,#128]		//store Htable[8..9]
	trn1	v1.2d,v16.2d,v0.2d
	trn2	v4.2d,v16.2d,v0.2d
	eor	v0.16b,v1.16b,v4.16b		//{mid H^7, mid H^8}  == Htable[10]
	stp	q7,q2,[x0,#96]		//store Htable[6..7]
	stp	q0,q3,[x0,#160]		//store Htable[10..11]
	// ---BODY-END---
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(gcm_init_v8)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
