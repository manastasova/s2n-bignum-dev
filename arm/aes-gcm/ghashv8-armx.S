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

// ============================================================================
// gcm_init_v8: Initialize GHASH Htable from the hash key H
//
// C prototype:
//   void gcm_init_v8(uint8_t Htable[192], const uint8_t H[16])
//
// Parameters:
//   x0 - pointer to output Htable (192 bytes = 12 × 16-byte entries)
//        The table stores twisted (half-swapped) powers of H along with
//        Karatsuba pre-processed helper values for efficient multiplication.
//        Layout: [H^1, H^1_kpre|H^2_kpre, H^2,
//                 H^3, H^3_kpre|H^4_kpre, H^4,
//                 H^5, H^5_kpre|H^6_kpre, H^6,
//                 H^7, H^7_kpre|H^8_kpre, H^8]
//   x1 - pointer to 16-byte hash key H (as received from AES encryption of
//        the zero block)
//
// This function:
//   1. Loads H and converts it to "twisted" form (shifted left by 1 bit in
//      the polynomial representation, with carry propagation using the
//      reduction polynomial)
//   2. Computes H^2 through H^8 by successive polynomial multiplications
//   3. Stores all powers and their Karatsuba pre-processed forms into Htable
//
// The "twisted" representation swaps the two 64-bit halves of each 128-bit
// value and left-shifts by 1 bit. This is done because the GHASH specification
// uses a bit-reversed convention, and the shift+swap normalizes the
// representation for efficient use with ARM's pmull instruction.
// ============================================================================

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(gcm_init_v8)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(gcm_init_v8)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(gcm_init_v8)
        .text
        .balign 4

S2N_BN_SYMBOL(gcm_init_v8):
        CFI_START

        // ------------------------------------------------------------------
        // Step 1: Load H and prepare the "twisted" H value
        // ------------------------------------------------------------------
        // GHASH uses a bit-reflected representation of GF(2^128) elements.
        // The hash key H needs to be left-shifted by 1 bit (as a 128-bit
        // polynomial) with the overflow bit XORed back using the reduction
        // polynomial if needed. This is equivalent to doubling in GF(2^128).

	ld1	{v17.2d},[x1]			// Load the 16-byte hash key H into v17
								// v17 = {H_hi, H_lo} (two 64-bit halves)

	movi	v19.16b,#0xe1		// Set all 16 bytes of v19 to 0xE1
								// This is the start of building the
								// reduction constant

	shl	v19.2d,v19.2d,#57		// Left-shift each 64-bit element by 57
								// 0xE1 << 57 = 0xC200000000000000
								// This is the upper 64 bits of the
								// GF(2^128) reduction polynomial
								// x^128 + x^7 + x^2 + x + 1
								// v19 = {0xC200..00, 0xC200..00}

	ext	v3.16b,v17.16b,v17.16b,#8
								// Swap the two 64-bit halves of H
								// v3 = {H_lo, H_hi}
								// ext with same source and #8 rotates
								// the 128-bit value by 8 bytes

	ushr	v18.2d,v19.2d,#63	// Unsigned shift right by 63 bits
								// v18 = {1, 1} (extract the MSB of
								// each 64-bit lane of v19, which is 1)
								// This creates a mask with just bit 0 set

	dup	v17.4s,v17.s[1]		// Broadcast the 32-bit element at index 1
							// of original H across all 4 lanes of v17
							// Element [1] is bits [63:32] of H,
							// which contains the MSB of H_lo (the bit
							// that determines if we need to XOR the
							// reduction polynomial after left-shift)

	ext	v16.16b,v18.16b,v19.16b,#8
							// Concatenate v18 and v19, extract middle 16 bytes
							// v16 = {v19_lo, v18_hi} = {0xC200..00, 0x00..01}
							// This is the "t0" constant used for conditional
							// reduction: if H's MSB was set, XOR this in

	ushr	v18.2d,v3.2d,#63	// Shift right each 64-bit half of v3 by 63
					// This extracts the MSB (bit 63) of each half
					// v18 = {H_lo >> 63, H_hi >> 63}
					// These are the carry bits from the left shift

	sshr	v17.4s,v17.4s,#31	// Arithmetic shift right by 31 on 32-bit elements
					// This broadcasts bit 31 (the MSB of the original
					// element) across all 32 bits of each lane
					// Creates an all-ones or all-zeros mask based on
					// whether the MSB of H (in the reflected bit order)
					// was 1 or 0. This is the carry bit from H<<1.

	and	v18.16b,v18.16b,v16.16b
					// Mask the carry bits with the reduction constant
					// If H_lo's MSB was 1, keep 0xC200..00 in high lane
					// If H_hi's MSB was 1, keep 0x01 in low lane
					// This prepares the bits to OR into the shifted value

	shl	v3.2d,v3.2d,#1		// Left-shift each 64-bit half of v3 by 1
					// v3 = {H_lo << 1, H_hi << 1}
					// Note: this loses the MSB of each half

	ext	v18.16b,v18.16b,v18.16b,#8
					// Swap halves of v18 to align carry bits with
					// the correct positions:
					// The carry from H_hi's MSB goes into H_lo's LSB
					// The carry from H_lo's MSB (with reduction) goes
					// into H_hi

	and	v16.16b,v16.16b,v17.16b
					// AND the reduction constant with the carry mask
					// If original H's MSB (bit 127 in memory) was set,
					// v16 = {0xC200..00, 0x01}; else v16 = {0, 0}
					// This applies the reduction polynomial conditionally

	orr	v3.16b,v3.16b,v18.16b	// OR in the inter-lane carry bits
					// H_lo gets H_hi's MSB in its LSB
					// H_hi gets H_lo's MSB (potentially with reduction)
					// Now v3 = H <<< 1 (128-bit left rotate/shift by 1)

	eor	v20.16b,v3.16b,v16.16b	// XOR with the conditional reduction polynomial
					// If H's MSB was set, XOR in {0xC2..00, 0x01}
					// This completes the "twisted" H computation:
					// v20 = twisted_H = (H << 1) mod polynomial

	ext	v20.16b, v20.16b, v20.16b, #8
					// Swap halves of twisted H for storage format
					// The "twisted" storage has halves swapped so that
					// subsequent pmull/pmull2 can access both halves
					// efficiently

	st1	{v20.2d},[x0],#16	// Store Htable[0] = twisted H^1
					// Post-increment x0 by 16 bytes

        // ------------------------------------------------------------------
        // Step 2: Calculate H^2 = H * H in GF(2^128)
        // ------------------------------------------------------------------
        // We use Karatsuba multiplication to compute the 128×128-bit
        // polynomial product, followed by reduction modulo the GF(2^128)
        // polynomial.
        //
        // For two 128-bit values A = {a1, a0} and B = {b1, b0}:
        //   Product = a1*b1 * x^128 + (a1*b0 + a0*b1) * x^64 + a0*b0
        //
        // Karatsuba optimization computes the middle term as:
        //   (a1 + a0) * (b1 + b0) - a1*b1 - a0*b0
        // reducing from 4 multiplies to 3.

	ext	v16.16b,v20.16b,v20.16b,#8
					// Swap halves of twisted H for Karatsuba:
					// v16 = {H_lo, H_hi} (untwisted order)

	pmull2	v0.1q,v20.2d,v20.2d	// Polynomial multiply high halves: H_hi * H_hi
					// v0 = high partial product (128-bit result)

	eor	v16.16b,v16.16b,v20.16b	// v16 = H_lo XOR H_hi (Karatsuba pre-processing)
					// This is (a0 + a1) for the Karatsuba middle term

	pmull	v2.1q,v20.1d,v20.1d	// Polynomial multiply low halves: H_lo * H_lo
					// v2 = low partial product (128-bit result)

	pmull	v1.1q,v16.1d,v16.1d	// Polynomial multiply: (H_lo+H_hi) * (H_lo+H_hi)
					// v1 = middle Karatsuba product

        // Karatsuba post-processing: recover the full 256-bit product
        // The 256-bit product is: v0 (bits 255:128) | middle | v2 (bits 127:0)
        // We need to extract the middle 128 bits and combine them properly.

	ext	v17.16b,v0.16b,v2.16b,#8
					// v17 = {v2_hi, v0_lo}
					// Extract bytes 8-23 spanning the boundary
					// between high and low products

	eor	v18.16b,v0.16b,v2.16b	// v18 = v0 XOR v2 (sum of high and low products)

	eor	v1.16b,v1.16b,v17.16b	// Subtract (XOR) the extracted boundary portion
					// from the Karatsuba middle product

	eor	v1.16b,v1.16b,v18.16b	// Subtract (XOR) the sum of high and low products
					// Now v1 contains the true middle 128 bits
					// (the cross terms a0*b1 + a1*b0)
					// Full 256-bit result: v0:high | v1:middle | v2:low
					// But stored as: v2 = bits[127:0], v1 = bits[191:64],
					// v0 = bits[255:128]

        // ------------------------------------------------------------------
        // Modular reduction: reduce 256-bit product modulo x^128 + x^7 + x^2 + x + 1
        // This is done in two phases using the constant 0xC200000000000000
        // ------------------------------------------------------------------
        // The reduction uses the identity: x^128 ≡ x^7 + x^2 + x + 1 (mod p(x))
        // We multiply the high part by the polynomial and fold it back.

        // Phase 1: Multiply low 64 bits of high product by reduction constant
	pmull	v18.1q,v0.1d,v19.1d	// v18 = v0_lo * 0xC200..00 (polynomial multiply)
					// This begins folding the upper 128 bits down

	ins	v2.d[0],v1.d[1]	// v2[0] = v1[1] (move middle-high to low-high position)
					// v2 now = {v1_hi, v2_lo} = adjusted low part

	ins	v1.d[1],v0.d[0]	// v1[1] = v0[0] (move high-low to middle-high position)
					// v1 now = {v0_lo, v1_lo} = adjusted to combine with phase 1

	eor	v0.16b,v1.16b,v18.16b	// v0 = adjusted_middle XOR reduction_phase1
					// Combines the partial reduction with middle bits

        // Phase 2: Complete the reduction
	ext	v18.16b,v0.16b,v0.16b,#8
					// Swap halves of intermediate result
					// v18 = {v0_lo, v0_hi}

	pmull	v0.1q,v0.1d,v19.1d	// v0 = v0_lo * 0xC200..00 (second reduction multiply)

	eor	v18.16b,v18.16b,v2.16b	// XOR swapped intermediate with remaining high bits

	eor	v17.16b,v0.16b,v18.16b	// v17 = final reduced result = H^2
					// Now v17 contains H^2 in GF(2^128)

        // ------------------------------------------------------------------
        // Prepare and store H^2 with Karatsuba pre-processing
        // ------------------------------------------------------------------

	ext	v22.16b,v17.16b,v17.16b,#8
					// v22 = twisted H^2 (halves swapped)
					// This is the form needed for multiplication

	eor	v17.16b,v17.16b,v22.16b
					// v17 = H^2_lo XOR H^2_hi (Karatsuba helper for H^2)

	ext	v21.16b,v16.16b,v17.16b,#8
					// Pack Karatsuba pre-processed values:
					// v21 = {v17_lo, v16_hi}
					// v21_hi = H_lo XOR H_hi (Karatsuba helper for H^1)
					// v21_lo = H^2_lo XOR H^2_hi (Karatsuba helper for H^2)
					// These are packed together for efficient loading

	st1	{v21.2d},[x0],#16	// Store Htable[1] = packed Karatsuba helpers
	st1	{v22.2d},[x0],#16	// Store Htable[2] = twisted H^2

        // ------------------------------------------------------------------
        // Step 3: Calculate H^3 and H^4 simultaneously
        // ------------------------------------------------------------------
        // H^3 = H * H^2 and H^4 = H^2 * H^2
        // Computing both at once improves instruction-level parallelism.

        // H^3 = H^1 * H^2 (using v20=twisted_H, v22=twisted_H^2)
        // H^4 = H^2 * H^2 (using v22=twisted_H^2 with itself)
	pmull2	v0.1q,v20.2d, v22.2d	// H_hi * H^2_hi → high product for H^3
	pmull2	v5.1q,v22.2d,v22.2d	// H^2_hi * H^2_hi → high product for H^4
	pmull	v2.1q,v20.1d, v22.1d	// H_lo * H^2_lo → low product for H^3
	pmull	v7.1q,v22.1d,v22.1d	// H^2_lo * H^2_lo → low product for H^4
	pmull	v1.1q,v16.1d,v17.1d	// (H_lo+H_hi) * (H^2_lo+H^2_hi) → middle for H^3
	pmull	v6.1q,v17.1d,v17.1d	// (H^2_lo+H^2_hi)^2 → middle for H^4

        // Karatsuba post-processing for both H^3 and H^4
	ext	v16.16b,v0.16b,v2.16b,#8	// H^3: extract boundary bytes
	ext	v17.16b,v5.16b,v7.16b,#8	// H^4: extract boundary bytes
	eor	v18.16b,v0.16b,v2.16b		// H^3: XOR high and low products
	eor	v1.16b,v1.16b,v16.16b		// H^3: adjust middle product (step 1)
	eor	v4.16b,v5.16b,v7.16b		// H^4: XOR high and low products
	eor	v6.16b,v6.16b,v17.16b		// H^4: adjust middle product (step 1)
	eor	v1.16b,v1.16b,v18.16b		// H^3: adjust middle product (step 2) → final middle
	pmull	v18.1q,v0.1d,v19.1d		// H^3: 1st phase reduction (high_lo * 0xC2)
	eor	v6.16b,v6.16b,v4.16b		// H^4: adjust middle product (step 2) → final middle
	pmull	v4.1q,v5.1d,v19.1d		// H^4: 1st phase reduction (high_lo * 0xC2)

        // Rearrange for reduction: merge middle bits into high/low
	ins	v2.d[0],v1.d[1]	// H^3: move middle_hi to low result's high lane
	ins	v7.d[0],v6.d[1]	// H^4: move middle_hi to low result's high lane
	ins	v1.d[1],v0.d[0]	// H^3: move high_lo to middle's high lane
	ins	v6.d[1],v5.d[0]	// H^4: move high_lo to middle's high lane
	eor	v0.16b,v1.16b,v18.16b	// H^3: combine with 1st phase reduction
	eor	v5.16b,v6.16b,v4.16b	// H^4: combine with 1st phase reduction

        // 2nd phase of reduction for both H^3 and H^4
	ext	v18.16b,v0.16b,v0.16b,#8	// H^3: swap halves of intermediate
	ext	v4.16b,v5.16b,v5.16b,#8	// H^4: swap halves of intermediate
	pmull	v0.1q,v0.1d,v19.1d		// H^3: 2nd reduction multiply
	pmull	v5.1q,v5.1d,v19.1d		// H^4: 2nd reduction multiply
	eor	v18.16b,v18.16b,v2.16b		// H^3: XOR with remaining bits
	eor	v4.16b,v4.16b,v7.16b		// H^4: XOR with remaining bits

	eor	v16.16b, v0.16b,v18.16b	// v16 = H^3 (final reduced result)
	eor	v17.16b, v5.16b,v4.16b		// v17 = H^4 (final reduced result)

        // Prepare twisted forms and Karatsuba pre-processed values for H^3, H^4
	ext	v23.16b,v16.16b,v16.16b,#8	// v23 = twisted H^3 (halves swapped)
	ext	v25.16b,v17.16b,v17.16b,#8	// v25 = twisted H^4 (halves swapped)
	ext	v18.16b,v22.16b,v22.16b,#8	// v18 = untwisted H^2 (for next computation)
	eor	v16.16b,v16.16b,v23.16b	// v16 = H^3_lo XOR H^3_hi (Karatsuba helper)
	eor	v17.16b,v17.16b,v25.16b	// v17 = H^4_lo XOR H^4_hi (Karatsuba helper)
	eor	v18.16b,v18.16b,v22.16b	// v18 = H^2_lo XOR H^2_hi (recomputed for next use)
	ext	v24.16b,v16.16b,v17.16b,#8	// Pack Karatsuba helpers for H^3 and H^4
					// v24 = {v17_lo, v16_hi} = packed pre-processed values
	st1	{v23.2d,v24.2d,v25.2d},[x0],#48
					// Store Htable[3..5]:
					//   [3] = twisted H^3
					//   [4] = packed Karatsuba helpers for H^3,H^4
					//   [5] = twisted H^4

        // ------------------------------------------------------------------
        // Step 4: Calculate H^5 and H^6
        // ------------------------------------------------------------------
        // H^5 = H^2 * H^3 and H^6 = H^3 * H^3
        // Using v22=twisted_H^2, v23=twisted_H^3

	pmull2	v0.1q,v22.2d, v23.2d	// H^2_hi * H^3_hi → high product for H^5
	pmull2	v5.1q,v23.2d,v23.2d	// H^3_hi * H^3_hi → high product for H^6
	pmull	v2.1q,v22.1d, v23.1d	// H^2_lo * H^3_lo → low product for H^5
	pmull	v7.1q,v23.1d,v23.1d	// H^3_lo * H^3_lo → low product for H^6
	pmull	v1.1q,v16.1d,v18.1d	// (H^3_lo+H^3_hi)*(H^2_lo+H^2_hi) → middle for H^5
	pmull	v6.1q,v16.1d,v16.1d	// (H^3_lo+H^3_hi)^2 → middle for H^6

        // Karatsuba post-processing for both H^5 and H^6
	ext	v16.16b,v0.16b,v2.16b,#8	// H^5: extract boundary
	ext	v17.16b,v5.16b,v7.16b,#8	// H^6: extract boundary
	eor	v18.16b,v0.16b,v2.16b		// H^5: XOR high and low
	eor	v1.16b,v1.16b,v16.16b		// H^5: adjust middle (step 1)
	eor	v4.16b,v5.16b,v7.16b		// H^6: XOR high and low
	eor	v6.16b,v6.16b,v17.16b		// H^6: adjust middle (step 1)
	eor	v1.16b,v1.16b,v18.16b		// H^5: adjust middle (step 2)
	pmull	v18.1q,v0.1d,v19.1d		// H^5: 1st phase reduction
	eor	v6.16b,v6.16b,v4.16b		// H^6: adjust middle (step 2)
	pmull	v4.1q,v5.1d,v19.1d		// H^6: 1st phase reduction

        // Rearrange for reduction
	ins	v2.d[0],v1.d[1]	// H^5: shuffle for reduction
	ins	v7.d[0],v6.d[1]	// H^6: shuffle for reduction
	ins	v1.d[1],v0.d[0]	// H^5: shuffle for reduction
	ins	v6.d[1],v5.d[0]	// H^6: shuffle for reduction
	eor	v0.16b,v1.16b,v18.16b	// H^5: combine with phase 1 result
	eor	v5.16b,v6.16b,v4.16b	// H^6: combine with phase 1 result

        // 2nd phase of reduction
	ext	v18.16b,v0.16b,v0.16b,#8	// H^5: swap halves
	ext	v4.16b,v5.16b,v5.16b,#8	// H^6: swap halves
	pmull	v0.1q,v0.1d,v19.1d		// H^5: 2nd reduction multiply
	pmull	v5.1q,v5.1d,v19.1d		// H^6: 2nd reduction multiply
	eor	v18.16b,v18.16b,v2.16b		// H^5: combine remaining bits
	eor	v4.16b,v4.16b,v7.16b		// H^6: combine remaining bits

	eor	v16.16b,v0.16b,v18.16b		// v16 = H^5 (final)
	eor	v17.16b,v5.16b,v4.16b		// v17 = H^6 (final)

        // Prepare twisted forms and Karatsuba values for H^5, H^6
	ext	v26.16b, v16.16b, v16.16b,#8	// v26 = twisted H^5
	ext	v28.16b, v17.16b, v17.16b,#8	// v28 = twisted H^6
	ext	v18.16b,v22.16b,v22.16b,#8	// v18 = untwisted H^2 (for later)
	eor	v16.16b,v16.16b,v26.16b	// v16 = H^5 Karatsuba helper
	eor	v17.16b,v17.16b,v28.16b	// v17 = H^6 Karatsuba helper
	eor	v18.16b,v18.16b,v22.16b	// v18 = H^2 Karatsuba helper (recomputed)
	ext	v27.16b,v16.16b,v17.16b,#8	// Pack Karatsuba helpers for H^5, H^6
	st1	{v26.2d,v27.2d,v28.2d},[x0],#48
					// Store Htable[6..8]:
					//   [6] = twisted H^5
					//   [7] = packed Karatsuba helpers for H^5,H^6
					//   [8] = twisted H^6

        // ------------------------------------------------------------------
        // Step 5: Calculate H^7 and H^8
        // ------------------------------------------------------------------
        // H^7 = H^2 * H^5 and H^8 = H^2 * H^6
        // Using v22=twisted_H^2, v26=twisted_H^5, v28=twisted_H^6

	pmull2	v0.1q,v22.2d,v26.2d	// H^2_hi * H^5_hi → high product for H^7
	pmull2	v5.1q,v22.2d,v28.2d	// H^2_hi * H^6_hi → high product for H^8
	pmull	v2.1q,v22.1d,v26.1d	// H^2_lo * H^5_lo → low product for H^7
	pmull	v7.1q,v22.1d,v28.1d	// H^2_lo * H^6_lo → low product for H^8
	pmull	v1.1q,v16.1d,v18.1d	// (H^5_lo+H^5_hi)*(H^2_lo+H^2_hi) → middle for H^7
	pmull	v6.1q,v17.1d,v18.1d	// (H^6_lo+H^6_hi)*(H^2_lo+H^2_hi) → middle for H^8

        // Karatsuba post-processing for both H^7 and H^8
	ext	v16.16b,v0.16b,v2.16b,#8	// H^7: extract boundary
	ext	v17.16b,v5.16b,v7.16b,#8	// H^8: extract boundary
	eor	v18.16b,v0.16b,v2.16b		// H^7: XOR high and low
	eor	v1.16b,v1.16b,v16.16b		// H^7: adjust middle (step 1)
	eor	v4.16b,v5.16b,v7.16b		// H^8: XOR high and low
	eor	v6.16b,v6.16b,v17.16b		// H^8: adjust middle (step 1)
	eor	v1.16b,v1.16b,v18.16b		// H^7: adjust middle (step 2)
	pmull	v18.1q,v0.1d,v19.1d		// H^7: 1st phase reduction
	eor	v6.16b,v6.16b,v4.16b		// H^8: adjust middle (step 2)
	pmull	v4.1q,v5.1d,v19.1d		// H^8: 1st phase reduction

        // Rearrange for reduction
	ins	v2.d[0],v1.d[1]	// H^7: shuffle
	ins	v7.d[0],v6.d[1]	// H^8: shuffle
	ins	v1.d[1],v0.d[0]	// H^7: shuffle
	ins	v6.d[1],v5.d[0]	// H^8: shuffle
	eor	v0.16b,v1.16b,v18.16b	// H^7: combine with phase 1
	eor	v5.16b,v6.16b,v4.16b	// H^8: combine with phase 1

        // 2nd phase of reduction
	ext	v18.16b,v0.16b,v0.16b,#8	// H^7: swap halves
	ext	v4.16b,v5.16b,v5.16b,#8	// H^8: swap halves
	pmull	v0.1q,v0.1d,v19.1d		// H^7: 2nd reduction multiply
	pmull	v5.1q,v5.1d,v19.1d		// H^8: 2nd reduction multiply
	eor	v18.16b,v18.16b,v2.16b		// H^7: combine remaining bits
	eor	v4.16b,v4.16b,v7.16b		// H^8: combine remaining bits
	eor	v16.16b,v0.16b,v18.16b		// v16 = H^7 (final)
	eor	v17.16b,v5.16b,v4.16b		// v17 = H^8 (final)

        // Prepare twisted forms and Karatsuba values for H^7, H^8
	ext	v29.16b,v16.16b,v16.16b,#8	// v29 = twisted H^7
	ext	v31.16b,v17.16b,v17.16b,#8	// v31 = twisted H^8
	eor	v16.16b,v16.16b,v29.16b	// v16 = H^7 Karatsuba helper
	eor	v17.16b,v17.16b,v31.16b	// v17 = H^8 Karatsuba helper
	ext	v30.16b,v16.16b,v17.16b,#8	// Pack Karatsuba helpers for H^7, H^8
	st1	{v29.2d,v30.2d,v31.2d},[x0]	// Store Htable[9..11]:
					//   [9]  = twisted H^7
					//   [10] = packed Karatsuba helpers for H^7,H^8
					//   [11] = twisted H^8

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(gcm_init_v8)


// ============================================================================
// gcm_gmult_v8: GHASH single-block multiply - Xi = Xi * H in GF(2^128)
//
// C prototype:
//   void gcm_gmult_v8(uint8_t Xi[16], const uint8_t Htable[192])
//
// Parameters:
//   x0 - pointer to 16-byte Xi (current GHASH accumulator, updated in-place)
//   x1 - pointer to Htable (as initialized by gcm_init_v8)
//
// This function multiplies the current GHASH state Xi by the hash key H
// in GF(2^128) and writes the result back to Xi. It uses:
//   - Karatsuba multiplication (3 pmull operations instead of 4)
//   - Two-phase modular reduction using the 0xC2 constant
//   - Byte reversal for big-endian compatibility (GHASH uses big-endian)
// ============================================================================

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
// gcm_ghash_v8: GHASH multiple blocks
//
// C prototype:
//   void gcm_ghash_v8(uint8_t Xi[16], const uint8_t Htable[192],
//                     const uint8_t *inp, size_t len)
//
// Parameters:
//   x0 - pointer to 16-byte Xi (GHASH accumulator, updated in-place)
//   x1 - pointer to Htable (precomputed H powers from gcm_init_v8)
//   x2 - pointer to input data blocks
//   x3 - length of input data in bytes (must be a multiple of 16)
//
// This function computes:
//   Xi = (Xi ^ inp[0]) * H^n ^ inp[1] * H^(n-1) ^ ... ^ inp[n-1] * H
// where n = len/16 is the number of 16-byte blocks.
//
// For len >= 64, it uses the 4x path (gcm_ghash_v8_4x) which processes
// 4 blocks at a time using H, H^2, H^3, H^4 for maximum throughput.
// For len < 64, it uses a 2x path processing 2 blocks at a time with H, H^2.
//
// The algorithm is "modulo-scheduled" meaning the loop body overlaps
// the multiplication of the current iteration with the reduction of
// the previous iteration for better pipelining.
// ============================================================================

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(gcm_ghash_v8)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(gcm_ghash_v8)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(gcm_ghash_v8)
        .balign 4

S2N_BN_SYMBOL(gcm_ghash_v8):
        CFI_START

	cmp	x3,#64			// Check if we have at least 64 bytes (4 blocks)
						//b.hs	.Lgcm_ghash_v8_4x	// If so, use the optimized 4x path

	// ------------------------------------------------------------------
	// 2x path: Process 2 blocks at a time using H and H^2
	// This path handles 32-63 bytes, or falls through for 16 bytes
	// ------------------------------------------------------------------

	ld1	{v0.2d},[x0]		// Load current Xi (GHASH accumulator)
							// Note: Xi is stored in "rotated" form internally,
							// meaning it would need byte rotation to match the
							// GHASH specification's bit/byte ordering

	subs	x3,x3,#32		// Subtract 32 from length, check if >= 32 bytes
							// Sets condition flags for later branches

	mov	x12,#16				// x12 = 16, used as post-increment for loads
							// In the modulo-scheduled loop, x12 is set to 0
							// just before we would overread past the input,
							// causing the last block(s) to be loaded twice
							// (the duplicate load is harmless as it's not processed)

	ld1	{v20.2d,v21.2d},[x1],#32
							// Load from Htable:
							//   v20 = twisted H^1 (Htable[0])
							//   v21 = packed Karatsuba helpers (Htable[1])

	ext	v20.16b,v20.16b,v20.16b,#8
							// Un-twist H (swap halves to working order)

	movi	v19.16b,#0xe1	// Begin building reduction constant

	ld1	{v22.2d},[x1]		// Load twisted H^2 (Htable[2])

	ext	v22.16b,v22.16b,v22.16b,#8
							// Un-twist H^2

	csel	x12,xzr,x12,eq	// If x3 was exactly 32 (now 0), set x12=0
							// This prevents overreading input on the last iteration

	ext	v0.16b,v0.16b,v0.16b,#8
							// Rotate Xi (swap halves) into internal representation

	ld1	{v16.2d},[x2],#16	// Load first input block I[0], advance pointer by 16

	shl	v19.2d,v19.2d,#57	// Complete reduction constant: 0xC200000000000000

#ifndef __AARCH64EB__
	rev64	v16.16b,v16.16b		// Byte-swap I[0] for little-endian systems
	rev64	v0.16b,v0.16b		// Byte-swap Xi for little-endian systems
#endif

	ext	v3.16b,v16.16b,v16.16b,#8
							// Rotate I[0] (swap halves into working form)

	b.lo	.Lodd_tail_v8	// If original x3 < 32 (only 1 block), jump to tail
							// At this point x3 held the result of x3-32,
							// b.lo means the original length was < 32

        					// We have at least 2 blocks: load I[1] and begin the 2x loop
	ld1	{v17.2d},[x2],x12	// Load I[1], advance pointer by x12 (16 or 0)
#ifndef __AARCH64EB__
	rev64	v17.16b,v17.16b	// Byte-swap I[1] for little-endian
#endif

	ext	v7.16b,v17.16b,v17.16b,#8
							// Rotate I[1] into working form

	eor	v3.16b,v3.16b,v0.16b// XOR I[0] with Xi: v3 = I[0] ^ Xi
							// This is the standard GHASH step: accumulate input

    // Begin multiplication of H * I[1] (to be accumulated with H^2 * (Xi^I[0]))
	pmull	v4.1q,v20.1d,v7.1d	// H_lo * I[1]_lo (low partial product)
	eor	v17.16b,v17.16b,v7.16b	// I[1]_lo XOR I[1]_hi (Karatsuba pre-processing)
	pmull2	v6.1q,v20.2d,v7.2d	// H_hi * I[1]_hi (high partial product)

	b	.Loop_mod2x_v8		// Enter the modulo-scheduled 2x loop

        // ------------------------------------------------------------------
        // Main 2x loop: processes 2 blocks per iteration
        // ------------------------------------------------------------------
        // This loop computes:
        //   result = H^2 * (Xi ^ I[i]) + H * I[i+1]
        // using Karatsuba multiplication for both products simultaneously,
        // then reduces modulo the GF(2^128) polynomial.
        //
        // The loop is "modulo-scheduled": the H*I[i+1] multiplication from
        // the current iteration is started before the loop branches, so
        // that it overlaps with the setup of the next iteration.
        //
        // Register usage in loop:
        //   v3 = rotated (Xi ^ I[i]) — input to H^2 multiplication
        //   v4, v6 = partial products of H * I[i+1] (pre-computed)
        //   v0, v2 = partial products of H^2 * (Xi ^ I[i])
        //   v1 = middle Karatsuba product for H^2
        //   v5 = middle Karatsuba product for H
        //   v19 = reduction constant 0xC200..00

.align	4
.Loop_mod2x_v8:
	ext	v18.16b,v3.16b,v3.16b,#8
					// v18 = rotated v3 (swap halves of Xi^I[i])

	subs	x3,x3,#32		// Decrement remaining length by 32 (2 blocks)

	pmull	v0.1q,v22.1d,v3.1d	// H^2_lo * (Xi^I[i])_lo (low product)

	csel	x12,xzr,x12,lo		// If x3 < 0 (no more data after this), set x12=0
					// Prevents overreading the input buffer

	pmull	v5.1q,v21.1d,v17.1d	// (H_lo+H_hi) * (I[i+1]_lo+I[i+1]_hi)
					// Middle Karatsuba product for H * I[i+1]

	eor	v18.16b,v18.16b,v3.16b	// v18 = (Xi^I[i])_lo XOR (Xi^I[i])_hi
					// Karatsuba pre-processing for H^2 multiplication

	pmull2	v2.1q,v22.2d,v3.2d	// H^2_hi * (Xi^I[i])_hi (high product)

	eor	v0.16b,v0.16b,v4.16b	// Accumulate: add H*I[i+1] low product to H^2 low

	pmull2	v1.1q,v21.2d,v18.2d	// (H^2_lo+H^2_hi) * ((Xi^I[i])_lo+(Xi^I[i])_hi)
					// Middle Karatsuba product for H^2 multiplication
					// Uses v21.d[1] which has H^2's Karatsuba helper

	ld1	{v16.2d},[x2],x12	// Load I[i+2], advance by x12 (16 or 0)

	eor	v2.16b,v2.16b,v6.16b	// Accumulate: add H*I[i+1] high product to H^2 high

	csel	x12,xzr,x12,eq		// If x3 == 0 (last iteration), set x12=0

	eor	v1.16b,v1.16b,v5.16b	// Accumulate: add H*I[i+1] middle to H^2 middle

        // Now v0=accumulated_low, v2=accumulated_high, v1=accumulated_middle
        // Karatsuba post-processing to get the full 256-bit product
	ext	v17.16b,v0.16b,v2.16b,#8
					// Extract boundary bytes between low and high

	eor	v18.16b,v0.16b,v2.16b	// XOR low and high products

	eor	v1.16b,v1.16b,v17.16b	// Adjust middle (step 1)

	ld1	{v17.2d},[x2],x12	// Load I[i+3], advance by x12 (16 or 0)

#ifndef __AARCH64EB__
	rev64	v16.16b,v16.16b		// Byte-swap I[i+2]
#endif

	eor	v1.16b,v1.16b,v18.16b	// Adjust middle (step 2) — final middle term

        // Phase 1 of reduction
	pmull	v18.1q,v0.1d,v19.1d	// low_lo * 0xC200..00

#ifndef __AARCH64EB__
	rev64	v17.16b,v17.16b		// Byte-swap I[i+3]
#endif

	ins	v2.d[0],v1.d[1]	// Rearrange for reduction
	ins	v1.d[1],v0.d[0]	// Rearrange for reduction

	ext	v7.16b,v17.16b,v17.16b,#8
					// Rotate I[i+3] into working form

	ext	v3.16b,v16.16b,v16.16b,#8
					// Rotate I[i+2] into working form

	eor	v0.16b,v1.16b,v18.16b	// Combine with phase 1 reduction result

        // Start H * I[i+3] multiplication for next iteration (pipelining)
	pmull	v4.1q,v20.1d,v7.1d	// H_lo * I[i+3]_lo

	eor	v3.16b,v3.16b,v2.16b	// Accumulate v2 (high part) into v3 early
					// This is part of the modulo-scheduling: we fold
					// the remaining high bits into the next iteration's
					// Xi value early

        // Phase 2 of reduction
	ext	v18.16b,v0.16b,v0.16b,#8
					// Swap halves of intermediate

	pmull	v0.1q,v0.1d,v19.1d	// Second reduction multiply

	eor	v3.16b,v3.16b,v18.16b	// Fold swapped intermediate into next Xi

	eor	v17.16b,v17.16b,v7.16b	// Karatsuba pre-processing for I[i+3]

	eor	v3.16b,v3.16b,v0.16b	// Complete reduction: v3 = new Xi ^ I[i+2]
					// This value feeds into the next iteration

        // Continue H * I[i+3] pre-computation for next iteration
	pmull2	v6.1q,v20.2d,v7.2d	// H_hi * I[i+3]_hi

	b.hs	.Loop_mod2x_v8		// Loop if there are at least 32 more bytes

        // ------------------------------------------------------------------
        // Loop epilogue: clean up after the modulo-scheduled loop
        // ------------------------------------------------------------------
        // When we exit the loop, the last reduction was partially folded
        // into v3 using the early accumulation. We need to reconstruct
        // the proper Xi value.

	eor	v2.16b,v2.16b,v18.16b	// Fix up v2 with the swapped intermediate
	ext	v3.16b,v16.16b,v16.16b,#8
					// Re-construct v3 from I[i+2] (undo early accumulation)

	adds	x3,x3,#32		// Restore x3 to its pre-subtraction value
					// This tells us how many bytes remain

	eor	v0.16b,v0.16b,v2.16b	// Re-construct v0 (the proper reduced Xi)

	b.eq	.Ldone_v8		// If exactly 0 bytes remain, we're done

        // ------------------------------------------------------------------
        // Odd tail: process the last remaining block (when block count is odd)
        // ------------------------------------------------------------------
.Lodd_tail_v8:
	ext	v18.16b,v0.16b,v0.16b,#8
					// Swap halves of current Xi

	eor	v3.16b,v3.16b,v0.16b	// XOR input block with Xi (accumulate)

	eor	v17.16b,v16.16b,v18.16b
					// v17 = rotated input XOR Xi (for Karatsuba)

        // Single block multiplication: H * (Xi ^ input)
	pmull	v0.1q,v20.1d,v3.1d	// H_lo * (Xi^input)_lo
	eor	v17.16b,v17.16b,v3.16b	// Karatsuba pre-processing: (Xi^input)_lo XOR _hi
	pmull2	v2.1q,v20.2d,v3.2d	// H_hi * (Xi^input)_hi
	pmull	v1.1q,v21.1d,v17.1d	// (H_lo+H_hi) * ((Xi^input)_lo+(Xi^input)_hi)

        // Karatsuba post-processing
	ext	v17.16b,v0.16b,v2.16b,#8
	eor	v18.16b,v0.16b,v2.16b
	eor	v1.16b,v1.16b,v17.16b
	eor	v1.16b,v1.16b,v18.16b

        // Phase 1 reduction
	pmull	v18.1q,v0.1d,v19.1d
	ins	v2.d[0],v1.d[1]
	ins	v1.d[1],v0.d[0]
	eor	v0.16b,v1.16b,v18.16b

        // Phase 2 reduction
	ext	v18.16b,v0.16b,v0.16b,#8
	pmull	v0.1q,v0.1d,v19.1d
	eor	v18.16b,v18.16b,v2.16b
	eor	v0.16b,v0.16b,v18.16b	// v0 = final GHASH result

        // ------------------------------------------------------------------
        // Store result and return
        // ------------------------------------------------------------------
.Ldone_v8:
#ifndef __AARCH64EB__
	rev64	v0.16b,v0.16b		// Byte-swap back to big-endian for storage
#endif
	ext	v0.16b,v0.16b,v0.16b,#8
					// Swap halves to complete 128-bit byte reversal

	st1	{v0.2d},[x0]		// Write updated Xi to memory

       CFI_RET

S2N_BN_SIZE_DIRECTIVE(gcm_ghash_v8)

// ============================================================================
// Mark the stack as non-executable (security hardening for Linux ELF binaries)
// ============================================================================
#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
