.arch armv8.2-a+crypto+sha3
        .text

.globl	one_block_aes256_gcm_preloop_tail
.type	one_block_aes256_gcm_preloop_tail,%function
.align	4
one_block_aes256_gcm_preloop_tail:

// ============================================================
// FUNCTION PROLOGUE
// Save callee-saved NEON registers to stack
// ARM calling convention requires preserving d8-d15
// ============================================================

	stp	d8, d9, [sp, #-80]!
	// Save d8, d9 to stack and allocate 80 bytes of stack space

	lsr	x9, x1, #3
	// x9 = bit_length >> 3 = byte_length (convert bits to bytes)
	// This value is returned at the end as the function's return value

	mov	x16, x4
	// x16 = pointer to counter block (save original x4, since x4 gets modified later)

	mov	x11, x5
	// x11 = pointer to AES round keys (save original x5, since x5 gets reused)

	stp	d10, d11, [sp, #16]
	// Save d10, d11 to stack at offset 16

	stp	d12, d13, [sp, #32]
	// Save d12, d13 to stack at offset 32

	stp	d14, d15, [sp, #48]
	// Save d14, d15 to stack at offset 48

	mov	x5, #0xc200000000000000
	// x5 = GCM reduction polynomial constant (x^7 + x^2 + x + 1 shifted to top)

	stp	x5, xzr, [sp, #64]
	// Store polynomial constant and zero to stack at offset 64
	// This creates a 128-bit value [0xC200000000000000 | 0x0000000000000000] in memory
	// Used later by ldr d16 to load the reduction constant

	add	x10, sp, #64
	// x10 = pointer to the polynomial constant on the stack
	// Used later: ldr d16, [x10]

// ============================================================
// LOAD COUNTER BLOCK AND SET UP COUNTER INCREMENT
// The AES-GCM counter is a 16-byte block: [nonce (12 bytes) | counter (4 bytes)]
// The counter is big-endian, but ARM arithmetic is little-endian
// ============================================================

	ld1	{ v0.16b}, [x16]
	// v0 = 16-byte CTR block loaded from memory (nonce || big-endian counter)

	mov	x5, x9
	// x5 = byte_length (copy for later calculations)

	mov	x15, #0x100000000
	// x15 = 1 shifted left by 32 bits
	// This will be placed in a vector to increment the 32-bit counter field

	movi	v31.16b, #0x0
	// v31 = all zeros (clear the register)

	mov	v31.d[1], x15
	// v31 = [0x0000000100000000 | 0x0000000000000000]
	// When used with add v.4s, this adds 1 to the right 32-bit word
	// (the counter position after rev32 byte-swap)

	sub	x5, x5, #1
	// x5 = byte_length - 1

	and	x5, x5, #0xffffffffffffff80
	// x5 = (byte_length - 1) & ~0x7F
	// Round down to multiple of 128 bytes (8 blocks × 16 bytes)
	// This is how many bytes the main loop would process
	// For 1 block (16 bytes): x5 = 0

	add	x5, x5, x0
	// x5 = input_ptr + main_loop_bytes = end of main loop processing
	// For 1 block: x5 = input_ptr + 0 = input_ptr (no main loop iterations)

// ============================================================
// COUNTER BYTE-SWAP AND INCREMENT
// Convert counter from big-endian to little-endian for arithmetic
// ============================================================

	rev32	v30.16b, v0.16b
	// v30 = v0 with bytes reversed within each 32-bit word
	// Converts big-endian counter to little-endian for ARM add instruction

	add	v30.4s, v30.4s, v31.4s
	// Increment counter by 1 (little-endian 32-bit addition)
	// v30 now holds the next counter value (still in little-endian)
	// This prepares the counter for after encryption (will be stored at end)

// ============================================================
// AES-256 ENCRYPTION OF CTR BLOCK 0
// 14 rounds of AES on v0 (the original counter block)
// Each round: SubBytes + ShiftRows (aese) then MixColumns (aesmc)
// Last round (round 13): aese only, no aesmc
// Final XOR with round key 14 happens later via eor3
//
// Round keys loaded in pairs to maximize memory throughput
// ============================================================

	ldp	q26, q27, [x11, #0]
	// q26 = round key 0, q27 = round key 1

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b
	// AES round 0: SubBytes + ShiftRows + XOR rk0, then MixColumns

	ldp	q28, q26, [x11, #32]
	// q28 = round key 2, q26 = round key 3

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b
	// AES round 1: SubBytes + ShiftRows + XOR rk1, then MixColumns

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b
	// AES round 2: SubBytes + ShiftRows + XOR rk2, then MixColumns

	ldp	q27, q28, [x11, #64]
	// q27 = round key 4, q28 = round key 5

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b
	// AES round 3: SubBytes + ShiftRows + XOR rk3, then MixColumns

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b
	// AES round 4: SubBytes + ShiftRows + XOR rk4, then MixColumns

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b
	// AES round 5: SubBytes + ShiftRows + XOR rk5, then MixColumns

	ldp	q26, q27, [x11, #96]
	// q26 = round key 6, q27 = round key 7

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b
	// AES round 6: SubBytes + ShiftRows + XOR rk6, then MixColumns

	ldp	q28, q26, [x11, #128]
	// q28 = round key 8, q26 = round key 9

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b
	// AES round 7: SubBytes + ShiftRows + XOR rk7, then MixColumns

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b
	// AES round 8: SubBytes + ShiftRows + XOR rk8, then MixColumns

// ============================================================
// LOAD CURRENT GHASH TAG AND CONVERT TO PMULL FORMAT
// The tag is stored in GCM byte order in memory
// We need it in ARM PMULL working format for polynomial math
// ============================================================

	ld1	{ v19.16b}, [x3]
	// v19 = current GHASH tag loaded from memory (GCM byte order)

	ext	v19.16b, v19.16b, v19.16b, #8
	// Swap upper and lower 64-bit halves of tag

	rev64	v19.16b, v19.16b
	// Reverse bytes within each 64-bit half
	// v19 is now in PMULL working format for polynomial multiplication

// ============================================================
// CONTINUE AES ROUNDS 9-13
// ============================================================

	ldp	q27, q28, [x11, #160]
	// q27 = round key 10, q28 = round key 11

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b
	// AES round 9: SubBytes + ShiftRows + XOR rk9, then MixColumns

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b
	// AES round 10: SubBytes + ShiftRows + XOR rk10, then MixColumns

	ldp	q26, q27, [x11, #192]
	// q26 = round key 12, q27 = round key 13

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b
	// AES round 11: SubBytes + ShiftRows + XOR rk11, then MixColumns

	ldr	q28, [x11, #224]
	// q28 = round key 14 (the final round key, used later in eor3)

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b
	// AES round 12: SubBytes + ShiftRows + XOR rk12, then MixColumns

	aese	v0.16b, v27.16b
	// AES round 13: SubBytes + ShiftRows + XOR rk13 (NO MixColumns — final aese round)
	// v0 now holds AES output except for final round key XOR (rk14 in v28)

	add	x4, x0, x1, lsr #3
	// x4 = input_ptr + byte_length = end_input_ptr
	// Points to one past the last byte of input

// ============================================================
// SKIP MAIN LOOP AND PREPRETAIL — fall through directly to tail
// For 1 block, x0 >= x5 so we would branch to tail.
// Since this function is specifically for 1 block, we fall straight through.
// The main loop and prepretail labels are empty (dead code was removed).
// ============================================================

.L256_enc_main_loop:

.L256_enc_prepretail:

// ============================================================
// TAIL: ENCRYPT THE SINGLE BLOCK AND SET UP FOR GHASH
// ============================================================

.L256_enc_tail:

	ldr	q8, [x0], #16
	// v8 = load 16 bytes of plaintext from input, then advance input pointer by 16

	ext	v16.16b, v19.16b, v19.16b, #8
	// v16 = v19 with halves swapped
	// Creates a copy of the GHASH tag in XOR-compatible format for feeding into ciphertext
	// v19 itself remains in PMULL format (unchanged)

	mov	v29.16b, v28.16b
	// v29 = round key 14 (copy rk14 for use in eor3)

.inst	0xce007509
	// eor3 v9.16b, v8.16b, v0.16b, v29.16b
	// v9 = plaintext ⊕ AES_output ⊕ rk14
	// This completes AES-CTR encryption:
	//   ciphertext = plaintext XOR AES(counter)
	// The final round key XOR (rk14) is folded into this single operation

// ============================================================
// INITIALIZE GHASH ACCUMULATORS
// For a single block, there are no previous blocks to accumulate
// So HIGH, MID, LOW products start at zero
// Also load the precomputed Hk⊕Lk value for Karatsuba mid term
// ============================================================

	movi	v19.8b, #0
	// v19 = 0 (clear LOW accumulator — will be rebuilt from single block GHASH)

	movi	v17.8b, #0
	// v17 = 0 (clear HIGH accumulator)

	movi	v18.8b, #0
	// v18 = 0 (clear MID accumulator)

	ldr	q21, [x6, #16]
	// v21 = load h2k | h1k from Htable
	// h1k = Hk ⊕ Lk (precomputed XOR of hash key halves for Karatsuba mid term)

// ============================================================
// DEAD CASCADE LABELS
// In the full 8x kernel, these handle 7, 6, 5, ... 2 remaining blocks
// For 1 block, execution falls straight through all of them
// ============================================================

.L256_enc_blocks_more_than_7:

.L256_enc_blocks_more_than_6:

.L256_enc_blocks_more_than_5:

.L256_enc_blocks_more_than_4:

.L256_enc_blocks_more_than_3:

.L256_enc_blocks_more_than_2:

.L256_enc_blocks_more_than_1:

// ============================================================
// HANDLE THE FINAL (AND ONLY) BLOCK
// Build a mask for potentially partial blocks, apply it,
// then perform GHASH and modular reduction
// ============================================================

.L256_enc_blocks_less_than_1:

	and	x1, x1, #127
	// x1 = bit_length mod 128
	// For a full 16-byte block, bit_length = 128, so x1 = 0

	sub	x1, x1, #128
	// x1 = (bit_length mod 128) - 128
	// For a full block: x1 = 0 - 128 = -128

	neg	x1, x1
	// x1 = 128 - (bit_length mod 128)
	// For a full block: x1 = 128
	// This is the number of UNUSED bits that need to be masked off

	mvn	x7, xzr
	// x7 = 0xFFFFFFFFFFFFFFFF (all ones — starting point for mask)

	and	x1, x1, #127
	// x1 = unused_bits mod 128
	// For a full block: 128 mod 128 = 0 (no bits to mask off)

	lsr	x7, x7, x1
	// x7 = 0xFFFFFFFFFFFFFFFF >> unused_bits
	// For a full block (x1=0): x7 = 0xFFFFFFFFFFFFFFFF (all ones — keep everything)
	// For partial blocks: creates a mask with 1s for valid bits, 0s for invalid

	cmp	x1, #64
	// Compare unused bits against 64 to determine which half of the mask to modify

	mvn	x8, xzr
	// x8 = 0xFFFFFFFFFFFFFFFF (all ones — mask for the other half)

	csel	x14, x7, xzr, lt
	// If unused_bits < 64: x14 = x7 (partial mask for upper half)
	// If unused_bits >= 64: x14 = 0 (upper half entirely masked off)

	csel	x13, x8, x7, lt
	// If unused_bits < 64: x13 = 0xFFFFFFFFFFFFFFFF (lower half fully valid)
	// If unused_bits >= 64: x13 = x7 (partial mask for lower half)

	mov	v0.d[0], x13
	// v0 lower 64 bits = mask for lower half of block

	ldr	q20, [x6]
	// v20 = load h1l | h1h from Htable (hash key H for GHASH multiplication)

	ld1	{ v26.16b}, [x2]
	// v26 = load existing bytes at output location
	// Needed for partial blocks: we must preserve bytes outside the valid range

	mov	v0.d[1], x14
	// v0 upper 64 bits = mask for upper half of block
	// v0 is now the complete 128-bit mask
	// For a full block: v0 = all 1s (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)

	and	v9.16b, v9.16b, v0.16b
	// v9 = ciphertext AND mask
	// Zeroes out any invalid bytes in a partial block
	// For a full block: no change (mask is all 1s)

	rev64	v8.16b, v9.16b
	// v8 = ciphertext with bytes reversed within each 64-bit half
	// Converts ciphertext to PMULL format for GHASH multiplication

	rev32	v30.16b, v30.16b
	// Convert counter from little-endian back to big-endian for storage
	// (v30 was in little-endian after the add increment earlier)

	str	q30, [x16]
	// Store the updated (incremented) counter back to memory
	// Next call will use this as the starting counter

	eor	v8.16b, v8.16b, v16.16b
	// v8 = reversed_ciphertext ⊕ partial_tag
	// Feed the previous GHASH state into the current block
	// This is the core GHASH operation: GHASH_new = (GHASH_old ⊕ ciphertext) × H

	st1	{ v9.16b}, [x2]
	// Store the ciphertext (masked) to the output buffer

// ============================================================
// GHASH MULTIPLICATION: (tag ⊕ ciphertext) × H in GF(2^128)
// Using Karatsuba to split 128-bit multiply into three 64-bit multiplies
//
// v8  = [H_input_hi | H_input_lo]  = GHASH input (old_tag ⊕ ciphertext, in PMULL format)
// v20 = [H_key_hi | H_key_low]  = hash key H (high and low halves)
// v21 = [h2k| h1k] = precomputed H_key_hi ⊕ H_key_low (for Karatsuba mid term)
//
// Accumulate into:
//   v17 = HIGH product (H_input_hi × H_key_hi)
//   v18 = MID product  ((H_input_hi ⊕ H_input_lo) × (H_key_hi ⊕ H_key_lo))
//   v19 = LOW product  (H_input_lo × H_key_lo)
// ============================================================

	ins	v16.d[0], v8.d[1]
	// v16.d[0] = H_input_hi (copy high half of GHASH input to low position)
	// Preparation for computing Hi ⊕ Lo for the Karatsuba mid term

	pmull2	v28.1q, v8.2d, v20.2d
	// v28 = H_input_hi × H_key_hi (polynomial multiply of upper halves → 128-bit HIGH product)

	pmull	v26.1q, v8.1d, v20.1d
	// v26 = H_input_lo × H_key_low (polynomial multiply of lower halves → 128-bit LOW product)

	eor	v17.16b, v17.16b, v28.16b
	// v17 = 0 ⊕ (H_input_hi × H_key_hi) = H_input_hi × H_key_hi (accumulate HIGH — was zeroed, so just assignment)

	eor	v19.16b, v19.16b, v26.16b
	// v19 = 0 ⊕ (H_input_lo × H_key_low) = H_input_lo × H_key_low (accumulate LOW — was zeroed, so just assignment)

	eor	v16.8b, v16.8b, v8.8b
	// v16.d[0] = H_input_hi ⊕ H_input_lo (XOR the two halves for Karatsuba mid term)
	// Only operates on lower 8 bytes (.8b) since we only need the lower 64 bits

	pmull	v16.1q, v16.1d, v21.1d
	// v16 = (H_input_hi ⊕ H_input_lo) × (H_input_lo × H_key_low) (Karatsuba mid product → 128-bit result)
	// v21.d[0] = h1k = Hh ⊕ Hl (precomputed)

	eor	v18.16b, v18.16b, v16.16b
	// v18 = 0 ⊕ (H_input_hi ⊕ H_input_lo) × (H_input_lo × H_key_low) (accumulate MID — was zeroed, so just assignment)

// ============================================================
// MODULAR REDUCTION
// Reduce 256-bit product modulo GCM polynomial: x^128 + x^7 + x^2 + x + 1
//
// The 256-bit product is conceptually:
//   [v17 (128 bits HIGH)] [v19 (128 bits LOW)]
// with v18 being the Karatsuba cross-term that overlaps both
//
// Step 1: Karatsuba tidy-up — recover true cross-term
// Step 2: Fold HIGH into MID using polynomial multiplication
// Step 3: Fold MID into LOW using polynomial multiplication
// Result: 128-bit reduced value in v19
// ============================================================

	ldr	d16, [x10]
	// v16 = 0xC200000000000000 (load GCM reduction polynomial from stack)
	// Only lower 64 bits loaded (d16), upper 64 bits are zero
	// Represents x^7 + x^2 + x + 1 (the low part of the GCM polynomial)

	ext	v21.16b, v17.16b, v17.16b, #8
	// v21 = [v17.lo | v17.hi] (swap halves of HIGH product)
	// Need this alignment for folding into mid

.inst	0xce114e52
	// eor3 v18.16b, v18.16b, v17.16b, v19.16b
	// v18 = MID ⊕ HIGH ⊕ LOW
	// KARATSUBA TIDY-UP:
	//   Raw MID = (Hi⊕Lo) × (Hh⊕Hl)
	//   True cross-term = Hi×Hl + Lo×Hh = Raw MID ⊕ HIGH ⊕ LOW
	//   This recovers the actual middle 128 bits of the 256-bit product

	pmull	v29.1q, v17.1d, v16.1d
	// v29 = v17.lo × polynomial_constant
	// Polynomial multiply: lower 64 bits of HIGH × reduction constant
	// This shifts and reduces the high bits toward the middle

.inst	0xce1d5652
	// eor3 v18.16b, v18.16b, v29.16b, v21.16b
	// v18 = v18 ⊕ v29 ⊕ swap(v17)
	// FOLD HIGH INTO MID:
	//   v29 = polynomial reduction of HIGH's lower half
	//   v21 = HIGH with halves swapped (provides the other alignment)
	//   Together they fully fold HIGH into MID
	//   After this, v17 (HIGH) is completely consumed

	pmull	v17.1q, v18.1d, v16.1d
	// v17 = v18.lo × polynomial_constant
	// Polynomial multiply: lower 64 bits of MID × reduction constant
	// This shifts and reduces the mid bits toward the low

	ext	v21.16b, v18.16b, v18.16b, #8
	// v21 = [v18.lo | v18.hi] (swap halves of MID)
	// Need this alignment for folding into low

.inst	0xce115673
	// eor3 v19.16b, v19.16b, v17.16b, v21.16b
	// v19 = LOW ⊕ v17 ⊕ swap(v18)
	// FOLD MID INTO LOW:
	//   v17 = polynomial reduction of MID's lower half
	//   v21 = MID with halves swapped (provides the other alignment)
	//   Together they fully fold MID into LOW
	//   After this, v18 (MID) is completely consumed
	//   v19 now holds the final 128-bit GHASH result in PMULL format

// ============================================================
// CONVERT GHASH RESULT BACK TO GCM MEMORY FORMAT AND STORE
// Reverse the ext #8 + rev64 conversion done when loading the tag
// ============================================================

	ext	v19.16b, v19.16b, v19.16b, #8
	// Swap upper and lower 64-bit halves
	// Begin converting from PMULL format back to GCM byte order

	rev64	v19.16b, v19.16b
	// Reverse bytes within each 64-bit half
	// Complete conversion to GCM byte order

	st1	{ v19.16b }, [x3]
	// Store the updated GHASH tag to memory
	// This tag will be used as input for the next GHASH block (or as the final tag)

	mov	x0, x9
	// Return value = byte_length (number of bytes processed)

// ============================================================
// FUNCTION EPILOGUE
// Restore callee-saved NEON registers from stack
// ============================================================

	ldp	d10, d11, [sp, #16]
	// Restore d10, d11 from stack

	ldp	d12, d13, [sp, #32]
	// Restore d12, d13 from stack

	ldp	d14, d15, [sp, #48]
	// Restore d14, d15 from stack

	ldp	d8, d9, [sp], #80
	// Restore d8, d9 from stack and deallocate 80 bytes of stack space

	ret
	// Return to caller with x0 = byte_length

.size	one_block_aes256_gcm_preloop_tail,.-one_block_aes256_gcm_preloop_tail

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif



//  AES-256-GCM Single Block Encrypt — Pseudocode

//  function one_block_aes256_gcm_preloop_tail(
//      input_ptr,      // pointer to 16 bytes of plaintext
//      bit_length,     // must be 128 for one full block
//      output_ptr,     // pointer to write 16 bytes of ciphertext
//      current_tag,    // pointer to 16-byte GHASH state
//      counter,        // pointer to 16-byte CTR block [nonce(12) || ctr32(4)]
//      round_keys,     // pointer to 15 AES-256 round keys (rk0..rk14)
//      Htable          // pointer to precomputed GHASH H-table
//  ) returns byte_length:

//      // ============================================================
//      // SETUP
//      // ============================================================

//      byte_length = bit_length >> 3                    // convert bits to bytes (= 16)

//      CTR_block = load_128bit(counter)                 // load [nonce || big-endian counter]

//      // ============================================================
//      // INCREMENT COUNTER FOR NEXT USE
//      // ============================================================

//      next_counter = byte_swap_within_32bit_words(CTR_block)  // big-endian → little-endian
//      next_counter = next_counter + 1                          // increment counter (32-bit add)
//      // next_counter stays in little-endian until stored at the end

//      // ============================================================
//      // AES-256 ENCRYPT THE COUNTER BLOCK (14 rounds)
//      // Produces the keystream that will be XORed with plaintext
//      // ============================================================

//      rk0, rk1   = load_round_key_pair(round_keys, offset=0)
//      rk2, rk3   = load_round_key_pair(round_keys, offset=32)
//      rk4, rk5   = load_round_key_pair(round_keys, offset=64)
//      rk6, rk7   = load_round_key_pair(round_keys, offset=96)
//      rk8, rk9   = load_round_key_pair(round_keys, offset=128)
//      rk10, rk11 = load_round_key_pair(round_keys, offset=160)
//      rk12, rk13 = load_round_key_pair(round_keys, offset=192)
//      rk14       = load_round_key(round_keys, offset=224)

//      state = CTR_block

//      // Rounds 0-12: SubBytes + ShiftRows + XOR round key + MixColumns
//      state = AES_round(state, rk0)           // round 0
//      state = AES_round(state, rk1)           // round 1
//      state = AES_round(state, rk2)           // round 2
//      state = AES_round(state, rk3)           // round 3
//      state = AES_round(state, rk4)           // round 4
//      state = AES_round(state, rk5)           // round 5
//      state = AES_round(state, rk6)           // round 6
//      state = AES_round(state, rk7)           // round 7
//      state = AES_round(state, rk8)           // round 8
//      state = AES_round(state, rk9)           // round 9
//      state = AES_round(state, rk10)          // round 10
//      state = AES_round(state, rk11)          // round 11
//      state = AES_round(state, rk12)          // round 12

//      // Round 13: SubBytes + ShiftRows + XOR round key (NO MixColumns)
//      state = AES_final_round(state, rk13)    // round 13

//      keystream = state
//      // Note: rk14 is not applied yet — it gets folded into the XOR below

//      // ============================================================
//      // LOAD AND CONVERT GHASH TAG TO INTERNAL FORMAT
//      // GCM byte order → ARM PMULL working format
//      // ============================================================

//      tag = load_128bit(current_tag)          // load 16-byte GHASH state from memory
//      tag = swap_64bit_halves(tag)            // ext #8: swap upper and lower 64 bits
//      tag = reverse_bytes_within_64bit(tag)   // rev64: reverse bytes in each 64-bit half
//      // tag is now in PMULL-compatible format

//      // ============================================================
//      // ENCRYPT: XOR plaintext with keystream to produce ciphertext
//      // ============================================================

//      plaintext = load_128bit(input_ptr)

//      tag_for_xor = swap_64bit_halves(tag)
//      // Create a half-swapped copy of tag for XOR with ciphertext
//      // Original tag (in PMULL format) is preserved separately

//      ciphertext = plaintext XOR keystream XOR rk14
//      // Three-way XOR in one operation (eor3)
//      // This completes AES-CTR: ciphertext = plaintext ⊕ AES(counter)

//      // ============================================================
//      // BUILD MASK FOR PARTIAL BLOCKS
//      // For a full 16-byte block, mask = all 1s (no masking needed)
//      // For partial blocks, zeroes out unused bytes
//      // ============================================================

//      unused_bits = 128 - (bit_length mod 128)    // = 0 for full block
//      unused_bits = unused_bits mod 128            // = 0 for full block

//      if unused_bits < 64:
//          mask_lower = 0xFFFFFFFFFFFFFFFF                      // lower half fully valid
//          mask_upper = 0xFFFFFFFFFFFFFFFF >> unused_bits        // upper half partially valid
//      else:
//          mask_lower = 0xFFFFFFFFFFFFFFFF >> unused_bits        // lower half partially valid
//          mask_upper = 0                                        // upper half fully masked
//      // For a full block: mask = all 1s

//      // ============================================================
//      // APPLY MASK AND STORE CIPHERTEXT
//      // ============================================================

//      H_key = load_128bit(Htable, offset=0)       // load hash key H (h1l | h1h)

//      ciphertext = ciphertext AND mask            // zero out invalid bytes (no-op for full block)

//      // ============================================================
//      // PREPARE CIPHERTEXT FOR GHASH
//      // Convert ciphertext to PMULL format and feed in previous tag
//      // ============================================================

//      ghash_input = reverse_bytes_within_64bit(ciphertext)   // rev64: convert to PMULL format

//      // Store incremented counter back to memory for next invocation
//      next_counter = byte_swap_within_32bit_words(next_counter)  // little-endian → big-endian
//      store_128bit(counter, next_counter)

//      // Core GHASH XOR: new_input = old_tag ⊕ ciphertext
//      ghash_input = ghash_input XOR tag_for_xor

//      // Store ciphertext to output
//      store_128bit(output_ptr, ciphertext)

//      // ============================================================
//      // GHASH: multiply (tag ⊕ ciphertext) × H in GF(2^128)
//      // Using Karatsuba method: 1 multiply becomes 3 smaller multiplies
//      //
//      // ghash_input = [Hi | Lo]    (high 64 bits, low 64 bits)
//      // H_key       = [Hh | Hl]   (hash key high, hash key low)
//      // H_key_xor   = Hh ⊕ Hl     (precomputed, loaded from Htable)
//      // ============================================================

//      H_key_xor = load_128bit(Htable, offset=16)   // h2k | h1k (precomputed Hh ⊕ Hl)

//      Hi = ghash_input.upper_64bits
//      Lo = ghash_input.lower_64bits
//      Hh = H_key.upper_64bits
//      Hl = H_key.lower_64bits

//      // --- Three Karatsuba multiplies (all in GF(2), i.e., carry-less / polynomial) ---

//      HIGH = polynomial_multiply(Hi, Hh)           // pmull2: upper × upper → 128-bit
//      LOW  = polynomial_multiply(Lo, Hl)           // pmull:  lower × lower → 128-bit
//      MID  = polynomial_multiply(Hi XOR Lo,        // pmull:  (Hi⊕Lo) × (Hh⊕Hl) → 128-bit
//                                 H_key_xor)

//      // ============================================================
//      // MODULAR REDUCTION
//      // Reduce 256-bit product modulo GCM polynomial:
//      //   p(x) = x^128 + x^7 + x^2 + x + 1
//      //
//      // The 256-bit product is:
//      //   bits [255:128] = HIGH
//      //   bits [191:64]  = MID (overlaps both, needs Karatsuba tidy-up)
//      //   bits [127:0]   = LOW
//      //
//      // polynomial_constant = 0xC200000000000000
//      //   represents x^7 + x^2 + x + 1 (the "reducible" part of p(x))
//      // ============================================================

//      polynomial_constant = 0xC200000000000000

//      // Step 1: Karatsuba tidy-up
//      // Raw MID = (Hi⊕Lo) × (Hh⊕Hl), but we need Hi×Hl + Lo×Hh
//      // True cross-term = Raw MID ⊕ HIGH ⊕ LOW

//      MID = MID XOR HIGH XOR LOW

//      // Step 2: Fold HIGH into MID
//      // Multiply lower half of HIGH by polynomial, then XOR with shifted HIGH

//      high_reduced = polynomial_multiply(HIGH.lower_64bits, polynomial_constant)
//      high_swapped = swap_64bit_halves(HIGH)

//      MID = MID XOR high_reduced XOR high_swapped
//      // HIGH is now fully consumed — its contribution is folded into MID

//      // Step 3: Fold MID into LOW
//      // Multiply lower half of MID by polynomial, then XOR with shifted MID

//      mid_reduced = polynomial_multiply(MID.lower_64bits, polynomial_constant)
//      mid_swapped = swap_64bit_halves(MID)

//      result = LOW XOR mid_reduced XOR mid_swapped
//      // MID is now fully consumed — final 128-bit GHASH result is in 'result'

//      // ============================================================
//      // CONVERT RESULT BACK TO GCM FORMAT AND STORE
//      // ============================================================

//      result = swap_64bit_halves(result)           // ext #8
//      result = reverse_bytes_within_64bit(result)  // rev64
//      // result is now in GCM memory byte order

//      store_128bit(current_tag, result)            // store updated GHASH tag

//      return byte_length                           // return 16

//  Helper Functions Reference

//  AES_round(state, round_key):
//      state = SubBytes(state)          // aese includes SubBytes + ShiftRows + XOR
//      state = ShiftRows(state)
//      state = XOR(state, round_key)
//      state = MixColumns(state)        // aesmc
//      return state

//  AES_final_round(state, round_key):
//      state = SubBytes(state)          // aese: SubBytes + ShiftRows + XOR
//      state = ShiftRows(state)
//      state = XOR(state, round_key)
//      // NO MixColumns in final round
//      return state

//  swap_64bit_halves(v):                // ext v, v, v, #8
//      return [v.lower_64 | v.upper_64]

//  reverse_bytes_within_64bit(v):       // rev64 v.16b, v.16b
//      v.upper_64 = reverse_bytes(v.upper_64)
//      v.lower_64 = reverse_bytes(v.lower_64)
//      return v

//  byte_swap_within_32bit_words(v):     // rev32 v.16b, v.16b
//      for each 32-bit word in v:
//          word = reverse_bytes(word)
//      return v

//  polynomial_multiply(a, b):           // pmull or pmull2
//      // Carry-less (XOR-based) multiplication in GF(2)
//      // 64-bit inputs → 128-bit output
//      // No carries propagate — addition is XOR
//      return a ×_GF2 b
