// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ==========================================================================
// GHASH implementation for ARM64 (AArch64) using ARMv8 Crypto Extensions
// ==========================================================================
//
// This file implements the GHASH operation used in AES-GCM (Galois/Counter
// Mode) authenticated encryption. GHASH is a universal hash function that
// operates over GF(2^128), the Galois field with 2^128 elements.
//
// The irreducible polynomial used for GF(2^128) reduction is:
//   x^128 + x^7 + x^2 + x + 1  (represented as 0xE1 in the high byte)
//
// Three functions are provided:
//   1. gcm_init_v8   - Precomputes powers of H (H^1 through H^8) and stores
//                      them in an Htable for use by gmult and ghash.
//   2. gcm_gmult_v8  - Multiplies a single 128-bit block Xi by H in GF(2^128).
//   3. gcm_ghash_v8  - Processes multiple input blocks, computing the GHASH
//                      incrementally using precomputed H powers for parallelism.
//
// Key algorithmic techniques used:
//   - Karatsuba multiplication: Reduces a 128x128-bit polynomial multiplication
//     from 4 partial products to 3, by computing:
//       (a0 + a1) * (b0 + b1) = a0*b0 + a1*b1 + a0*b1 + a1*b0
//     where the cross terms are derived from the middle product minus the
//     high and low products.
//   - Montgomery-style reduction: The 256-bit product is reduced modulo the
//     GF(2^128) polynomial in two phases using pmull with the constant 0xC2.
//   - "Twisted" H representation: H is stored with its halves swapped (via
//     ext #8) to facilitate efficient multiply-and-reduce operations.
//
// ARM NEON/Crypto instructions used:
//   pmull/pmull2  - Polynomial multiply (carryless multiply) of 64-bit halves
//   ext           - Extract/concatenate bytes from two vectors (used for
//                   byte rotation, swapping halves, and Karatsuba post-processing)
//   eor           - Bitwise XOR (addition in GF(2))
//   ins           - Insert element from one vector into another
//   rev64         - Reverse bytes within each 64-bit doubleword (endian swap)
//   shl/ushr/sshr - Shift left/right (logical/arithmetic) on vector elements
//   movi/dup      - Move immediate / duplicate element across vector
//   ld1/st1       - Load/store vector registers
//
// Register conventions:
//   v19 - Holds the reduction constant 0xC2 (0xE1 << 57) used in both phases
//         of modular reduction
//   v20 - Twisted H (H^1 with halves swapped)
//   v21 - Karatsuba pre-processed value for H (H.lo XOR H.hi packed with H^2's)
//   v22 - Twisted H^2
//   v23-v25 - H^3 related (twisted, Karatsuba pre-processed)
//   v26-v28 - H^5/H^6 related (or H^3/H^4 in 4x path)
//   v29-v31 - H^7/H^8 related (or accumulator partials in 4x path)
//
// ==========================================================================

#include "_internal_s2n_bignum_arm.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(gcm_gmult_v8)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(gcm_gmult_v8)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(gcm_gmult_v8)
        .balign 4

S2N_BN_SYMBOL(gcm_gmult_v8):
        CFI_START

	ld1	{v17.2d},[x0]			// Load current Xi (GHASH accumulator) from memory

	movi	v19.16b,#0xe1		// Begin constructing reduction constant

	ld1	{v20.2d,v21.2d},[x1]	// Load from Htable:
								//   v20 = twisted H (Htable[0])
								//   v21 = packed Karatsuba helpers (Htable[1])
								//   v21.d[0] contains H^2_lo XOR H^2_hi
								//   v21.d[1] contains H_lo XOR H_hi

	ext	v20.16b,v20.16b,v20.16b,#8
								// Un-twist H (swap halves back to normal order)
								// Now v20 = {H_lo, H_hi} in the working representation

	shl	v19.2d,v19.2d,#57	// Complete reduction constant: 0xE1 << 57 = 0xC200..00

#ifndef __AARCH64EB__
	rev64	v17.16b,v17.16b		// Reverse bytes within each 64-bit lane
								// GHASH uses big-endian byte order, but ARM is
								// little-endian, so we need to byte-swap.
								// rev64 reverses bytes within each doubleword.
#endif

	ext	v3.16b,v17.16b,v17.16b,#8
								// Swap the two 64-bit halves of Xi
								// Combined with the rev64 above, this effectively
								// does a full 128-bit byte reversal, converting
								// from big-endian to the internal representation.
								// v3 = {Xi_lo, Xi_hi} in polynomial bit order

	// ------------------------------------------------------------------
	// Karatsuba multiplication: compute H * Xi as three partial products
	// ------------------------------------------------------------------
	// Let H = {H_hi, H_lo} and Xi = {Xi_hi, Xi_lo}
	// We compute:
	//   low  = H_lo * Xi_lo
	//   high = H_hi * Xi_hi
	//   mid  = (H_lo + H_hi) * (Xi_lo + Xi_hi)
	// Then: full_product = high:low, with middle term derived from mid

	pmull	v0.1q,v20.1d,v3.1d	// v0 = H_lo * Xi_lo (low partial product)

	eor	v17.16b,v17.16b,v3.16b	// v17 = Xi_lo XOR Xi_hi (Karatsuba pre-processing)
								// This is (Xi_lo + Xi_hi) for the middle product

	pmull2	v2.1q,v20.2d,v3.2d	// v2 = H_hi * Xi_hi (high partial product)

	pmull	v1.1q,v21.1d,v17.1d	// v1 = (H_lo+H_hi) * (Xi_lo+Xi_hi)
								// Middle Karatsuba product using pre-computed
								// H_lo+H_hi from v21 (the Karatsuba helper)

	// ------------------------------------------------------------------
	// Karatsuba post-processing: extract the middle 128 bits
	// ------------------------------------------------------------------

	ext	v17.16b,v0.16b,v2.16b,#8
								// v17 = {v2_lo, v0_hi} (boundary extraction)

	eor	v18.16b,v0.16b,v2.16b	// v18 = low XOR high products

	eor	v1.16b,v1.16b,v17.16b	// Adjust middle product (step 1)

	eor	v1.16b,v1.16b,v18.16b	// Adjust middle product (step 2)
								// v1 now contains the true cross terms
								// The 256-bit product is v2:v1:v0

	// ------------------------------------------------------------------
	// Phase 1 of modular reduction
	// ------------------------------------------------------------------

	pmull	v18.1q,v0.1d,v19.1d	// Multiply low product's low half by 0xC200..00
								// This is the first step of folding the high 128 bits
								// back into the low 128 bits

	ins	v2.d[0],v1.d[1]			// Move middle_hi to v2's low lane
								// v2 = {v2_hi, v1_hi}

	ins	v1.d[1],v0.d[0]			// Move low_lo to v1's high lane
								// v1 = {v0_lo, v1_lo}

	eor	v0.16b,v1.16b,v18.16b	// Combine rearranged middle with phase 1 reduction

	// ------------------------------------------------------------------
	// Phase 2 of modular reduction
	// ------------------------------------------------------------------

	ext	v18.16b,v0.16b,v0.16b,#8
								// Swap halves of intermediate result

	pmull	v0.1q,v0.1d,v19.1d	// Second reduction: multiply low half by 0xC200..00

	eor	v18.16b,v18.16b,v2.16b	// Combine swapped intermediate with remaining high bits

	eor	v0.16b,v0.16b,v18.16b	// Final XOR: v0 = H * Xi mod p(x)
					// v0 now contains the reduced 128-bit GHASH result

	// ------------------------------------------------------------------
	// Convert back to big-endian and store result
	// ------------------------------------------------------------------

#ifndef __AARCH64EB__
	rev64	v0.16b,v0.16b		// Reverse bytes within each 64-bit lane
								// (convert back to big-endian byte order)
#endif

	ext	v0.16b,v0.16b,v0.16b,#8
								// Swap halves to complete the 128-bit byte reversal
								// Combined with rev64, this gives big-endian output

	st1	{v0.2d},[x0]			// Write the updated Xi back to memory

    CFI_RET

S2N_BN_SIZE_DIRECTIVE(gcm_gmult_v8)

// ============================================================================
// Mark the stack as non-executable (security hardening for Linux ELF binaries)
// ============================================================================
#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
