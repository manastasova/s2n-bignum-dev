(* ====================================================================== *)
(* GHASH Specification for AES-GCM                                        *)
(* Based on NIST SP 800-38D, Section 6.3 (Algorithm 1) and 6.4            *)
(* Specifies the ghash function from s2n-bignum/arm/aes-gcm/ghashv8-armx.S*)
(* ====================================================================== *)

(* High-level structure:
   1. Define the reduction polynomial R for GF(2^128)
   2. Define GF(2^128) multiplication via the NIST bit-by-bit algorithm
   3. Define GHASH as a fold of multiply-accumulate over 128-bit blocks
   4. Prove basic correctness properties:
      - Multiplying by zero on either side gives zero
      - GHASH of empty input is zero
      - GHASH of a single block is just gf128_mul
      - GHASH unfolds correctly on CONS *)

(* ---------------------------------------------------------------------- *)
(* The reduction polynomial for GF(2^128):                                *)
(* P(x) = x^128 + x^7 + x^2 + x + 1                                       *)
(* R encodes x^7 + x^2 + x + 1 as a 128-bit word.                         *)
(* NIST bit ordering (MSB first): bits 0,1,2,7 are set.                   *)
(* HOL Light bit ordering (LSB first, bit 0 = LSB): bits 127,126,125,120. *)
(* This equals 0xE1 in the MSB byte, i.e., 0xE1 << 120.                   *)
(* ---------------------------------------------------------------------- *)

let gf128_R = new_definition
  `gf128_R:128 word = word_of_bits {120, 125, 126, 127}`;;

(* ---------------------------------------------------------------------- *)
(* GF(2^128) multiplication (NIST SP 800-38D, Algorithm 1)                *)
(*                                                                        *)
(* gf128_mul_loop x n z v:                                                *)
(*   x = first operand (fixed throughout)                                 *)
(*   n = remaining iterations (counts down from 128 to 0)                 *)
(*   z = accumulator (starts at 0)                                        *)
(*   v = shift register (starts at y, the second operand)                 *)
(*                                                                        *)
(* At each step (from n = 128 down to 1):                                 *)
(*   - Check bit (n-1) of x. In HOL Light, bit (n-1) corresponds to       *)
(*     NIST bit (128-n), so we process from MSB to LSB of x.              *)
(*   - If set, XOR v into z.                                              *)
(*   - Shift v right by 1. If the old LSB was set, XOR with R.            *)
(*                                                                        *)
(* After 128 iterations, return z.                                        *)
(* ---------------------------------------------------------------------- *)

let gf128_mul_loop = define
  `(gf128_mul_loop (x:128 word) 0 (z:128 word) (v:128 word) = z) /\
   (gf128_mul_loop x (SUC n) z v =
      gf128_mul_loop x n
        (if bit n x then word_xor z v else z)
        (if bit 0 v then word_xor (word_ushr v 1) gf128_R
         else word_ushr v 1))`;;

(* Full GF(2^128) multiplication: x * y mod P(x)                          *)

let gf128_mul = new_definition
  `gf128_mul (x:128 word) (y:128 word) : 128 word =
    gf128_mul_loop x 128 (word 0) y`;;

(* ---------------------------------------------------------------------- *)
(* GHASH function (NIST SP 800-38D, Section 6.4, Algorithm 2)             *)
(*                                                                        *)
(* ghash H Y blocks:                                                      *)
(*   H = hash key (128 bits, derived from AES encryption of zero block)   *)
(*   Y = running accumulator                                              *)
(*   blocks = list of 128-bit input blocks                                *)
(*                                                                        *)
(* For each block X_i: Y_{i} = gf128_mul (Y_{i-1} XOR X_i) H              *)
(* ---------------------------------------------------------------------- *)

let ghash = define
  `(ghash (H:128 word) (Y:128 word) [] = Y) /\
   (ghash H Y (CONS (X:128 word) rest) =
      ghash H (gf128_mul (word_xor Y X) H) rest)`;;

(* Top-level GHASH: starts with zero accumulator                          *)

let GHASH = new_definition
  `GHASH (H:128 word) (blocks:(128 word) list) : 128 word =
    ghash H (word 0) blocks`;;

(* ====================================================================== *)
(* Properties of GF(2^128) multiplication                                 *)
(* ====================================================================== *)

(* Left zero: 0 * H = 0 in GF(2^128)                                      *)

let GF128_MUL_LZERO = prove
 (`!H:128 word. gf128_mul (word 0) H = word 0`,
  GEN_TAC THEN REWRITE_TAC[gf128_mul] THEN
  SPEC_TAC (`H:128 word`, `v:128 word`) THEN
  SPEC_TAC (`128`, `n:num`) THEN
  INDUCT_TAC THENL [REWRITE_TAC[gf128_mul_loop]; ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[gf128_mul_loop; BIT_WORD_0] THEN
  ASM_REWRITE_TAC[]);;

(* Right zero: X * 0 = 0 in GF(2^128)                                    *)

let GF128_MUL_RZERO = prove
 (`!X:128 word. gf128_mul X (word 0) = word 0`,
  GEN_TAC THEN REWRITE_TAC[gf128_mul] THEN
  SPEC_TAC (`128`, `n:num`) THEN
  INDUCT_TAC THENL [REWRITE_TAC[gf128_mul_loop]; ALL_TAC] THEN
  REWRITE_TAC[gf128_mul_loop; BIT_WORD_0] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_REFL] THEN
  SUBGOAL_THEN `word_ushr (word 0:128 word) 1 = word 0` SUBST1_TAC THENL
  [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[COND_ID] THEN ASM_REWRITE_TAC[]);;

(* ====================================================================== *)
(* Properties of GHASH                                                    *)
(* ====================================================================== *)

(* GHASH of empty input is zero                                           *)

let GHASH_NIL = prove
 (`!H:128 word. GHASH H [] = word 0`,
  REWRITE_TAC[GHASH; ghash]);;

(* GHASH of a single block                                                *)

let GHASH_SING = prove
 (`!H:128 word X:128 word. GHASH H [X] = gf128_mul X H`,
  REWRITE_TAC[GHASH; ghash; WORD_XOR_0]);;

(* GHASH unfolds on CONS: first block is absorbed then recursion continues *)

let GHASH_CONS = prove
 (`!H:128 word X:128 word Xs:(128 word) list.
    GHASH H (CONS X Xs) = ghash H (gf128_mul X H) Xs`,
  REWRITE_TAC[GHASH; ghash; WORD_XOR_0]);;

  (* ====================================================================== *)
(* Correctness proof for GHASH assembly (gcm_gmult_v8, gcm_ghash_v8)     *)
(* Assembly: s2n-bignum/arm/aes-gcm/ghashv8-armx.S                       *)
(* Spec:     s2n-bignum/arm/proofs/utils/ghash_spec.ml                    *)
(* ====================================================================== *)

(* NOTE: This file is designed to be moved to s2n-bignum/arm/proofs/ghash.ml
   Once there, change the needs/loadt paths accordingly.
   Currently written for standalone testing with the words library. *)

(* ====================================================================== *)
(* Part 1: Mathematical Infrastructure (testable without s2n-bignum)      *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* Reload the GHASH specification definitions                             *)
(* In s2n-bignum: needs "arm/proofs/utils/ghash_spec.ml";;                *)
(* ---------------------------------------------------------------------- *)

let gf128_R = new_definition
  `gf128_R:128 word = word_of_bits {120, 125, 126, 127}`;;

let gf128_mul_loop = define
  `(gf128_mul_loop (x:128 word) 0 (z:128 word) (v:128 word) = z) /\
   (gf128_mul_loop x (SUC n) z v =
      gf128_mul_loop x n
        (if bit n x then word_xor z v else z)
        (if bit 0 v then word_xor (word_ushr v 1) gf128_R
         else word_ushr v 1))`;;

let gf128_mul = new_definition
  `gf128_mul (x:128 word) (y:128 word) : 128 word =
    gf128_mul_loop x 128 (word 0) y`;;

let ghash = define
  `(ghash (H:128 word) (Y:128 word) [] = Y) /\
   (ghash H Y (CONS (X:128 word) rest) =
      ghash H (gf128_mul (word_xor Y X) H) rest)`;;

let GHASH = new_definition
  `GHASH (H:128 word) (blocks:(128 word) list) : 128 word =
    ghash H (word 0) blocks`;;

(* ---------------------------------------------------------------------- *)
(* Carryless (polynomial) multiplication of two 64-bit words              *)
(* This models the ARM PMULL instruction semantics.                       *)
(* Result is a 128-bit word (the full polynomial product, no reduction).  *)
(*                                                                        *)
(* clmul_loop a b n: XOR shifted copies of (zero-extended b) for each    *)
(*   set bit of a, processing bits n-1 down to 0.                        *)
(* ---------------------------------------------------------------------- *)

let clmul_loop = define
  `(clmul_loop (a:64 word) (b:64 word) 0 : 128 word = word 0) /\
   (clmul_loop a b (SUC n) =
      word_xor
        (if bit n a then word_shl (word_zx b : 128 word) n else word 0)
        (clmul_loop a b n))`;;

let clmul = new_definition
  `clmul (a:64 word) (b:64 word) : 128 word = clmul_loop a b 64`;;

(* ---------------------------------------------------------------------- *)
(* Helper: split a 128-bit word into high and low 64-bit halves           *)
(* ---------------------------------------------------------------------- *)

let lo64 = new_definition
  `lo64 (x:128 word) : 64 word = word_subword x (0,64)`;;

let hi64 = new_definition
  `hi64 (x:128 word) : 64 word = word_subword x (64,64)`;;

let join128 = new_definition
  `join128 (hi:64 word) (lo:64 word) : 128 word = word_join hi lo`;;

(* ---------------------------------------------------------------------- *)
(* EXT #8 operation: swap the two 64-bit halves of a 128-bit word         *)
(* This models the ARM EXT v.16b, v.16b, v.16b, #8 instruction           *)
(* ---------------------------------------------------------------------- *)

let swap_halves = new_definition
  `swap_halves (x:128 word) : 128 word = join128 (lo64 x) (hi64 x)`;;

(* ---------------------------------------------------------------------- *)
(* Full 128-bit byte reversal (rev64 + swap halves)                       *)
(* This converts between little-endian ARM memory and NIST byte order.    *)
(* The assembly does: rev64 then ext #8, which together reverse all 16    *)
(* bytes. In HOL Light, this is word_bytereverse (or word_reversefields 8)*)
(* ---------------------------------------------------------------------- *)

(* word_bytereverse is already defined in Library/words.ml *)

(* ---------------------------------------------------------------------- *)
(* Karatsuba decomposition of 128x128 polynomial multiplication           *)
(*                                                                        *)
(* Given X = (Xhi : Xlo) and Y = (Yhi : Ylo), the assembly computes:     *)
(*   v0 = clmul(Ylo, Xlo)           -- low partial product               *)
(*   v2 = clmul(Yhi, Xhi)           -- high partial product              *)
(*   v1 = clmul(Ylo XOR Yhi, Xlo XOR Xhi) -- Karatsuba middle product   *)
(*                                                                        *)
(* The full 256-bit product is then:                                      *)
(*   product[255:128] = v2                                                *)
(*   product[127:0]   = v0                                                *)
(*   cross = v1 XOR v0 XOR v2 (the cross terms a0*b1 + a1*b0)            *)
(*   product[191:64] XOR= cross                                          *)
(*                                                                        *)
(* After Karatsuba combination, the assembly does two-phase reduction     *)
(* using the constant 0xC200000000000000 = 0xE1 << 57.                   *)
(* ---------------------------------------------------------------------- *)

(* The full 256-bit carryless product of two 128-bit values *)
(* Built from four 64x64 partial products using Karatsuba *)
let clmul128_karatsuba = new_definition
  `clmul128_karatsuba (x:128 word) (y:128 word) : 256 word =
    let xlo = lo64 x and xhi = hi64 x
    and ylo = lo64 y and yhi = hi64 y in
    let v0 = clmul xlo ylo in
    let v2 = clmul xhi yhi in
    let v1 = clmul (word_xor xlo xhi) (word_xor ylo yhi) in
    let cross = word_xor (word_xor v1 v0) v2 in
    word_xor
      (word_xor (word_zx v0 : 256 word)
                (word_shl (word_zx cross : 256 word) 64))
      (word_shl (word_zx v2 : 256 word) 128)`;;

(* The same product using 4 direct partial products (schoolbook method) *)
let clmul128_schoolbook = new_definition
  `clmul128_schoolbook (x:128 word) (y:128 word) : 256 word =
    let xlo = lo64 x and xhi = hi64 x
    and ylo = lo64 y and yhi = hi64 y in
    let ll = clmul xlo ylo in
    let lh = clmul xlo yhi in
    let hl = clmul xhi ylo in
    let hh = clmul xhi yhi in
    word_xor
      (word_xor (word_zx ll : 256 word)
                (word_shl (word_zx hh : 256 word) 128))
      (word_shl (word_xor (word_zx lh) (word_zx hl) : 256 word) 64)`;;

(* ---------------------------------------------------------------------- *)
(* Two-phase reduction modulo x^128 + x^7 + x^2 + x + 1                  *)
(*                                                                        *)
(* The reduction constant used by the assembly is:                        *)
(*   0xC200000000000000 = 0xE1 << 57                                      *)
(* stored as: movi v19.16b, #0xe1; shl v19.2d, v19.2d, #57               *)
(*                                                                        *)
(* Phase 1: Fold bits 128-191 down using pmull with reduction constant    *)
(* Phase 2: Fold remaining high bits                                      *)
(* The result is the 128-bit remainder mod the irreducible polynomial.    *)
(* ---------------------------------------------------------------------- *)

let gf128_reduce_constant = new_definition
  `gf128_reduce_constant : 64 word = word 0xC200000000000000`;;

(* ---------------------------------------------------------------------- *)
(* The reduction of a 256-bit polynomial product to 128 bits              *)
(* This matches the two-phase reduction in the assembly:                  *)
(*   Phase 1: pmull(low64, 0xC2<<57), rearrange, XOR                     *)
(*   Phase 2: pmull(result_low64, 0xC2<<57), XOR with remaining          *)
(* ---------------------------------------------------------------------- *)

let gf128_reduce = new_definition
  `gf128_reduce (p:256 word) : 128 word =
    let v0 : 128 word = word_subword p (0,128) in
    let v2 : 128 word = word_subword p (128,128) in
    let phase1_mul = clmul (lo64 v0) gf128_reduce_constant in
    let r1 = word_xor (swap_halves v0) phase1_mul in
    let r1_swapped = swap_halves r1 in
    let phase2_mul = clmul (lo64 r1) gf128_reduce_constant in
    word_xor (word_xor r1_swapped v2) phase2_mul`;;

(* ====================================================================== *)
(* NOTE ON BIT ORDERING AND ASSEMBLY EQUIVALENCE                          *)
(* ====================================================================== *)
(* gf128_mul (NIST Algorithm 1) computes X * Y * x^{-127} mod P          *)
(* where P = x^128 + x^7 + x^2 + x + 1, using NIST bit ordering.        *)
(*                                                                        *)
(* The assembly (clmul + reduce) computes standard polynomial             *)
(* multiplication mod P* (the reflected polynomial):                      *)
(*   P* = x^128 + x^127 + x^126 + x^121 + 1                             *)
(* The reduction constant 0xC200000000000000 = x^63 + x^62 + x^57        *)
(* encodes (P* - x^128 - 1) / x^64 for the two-phase PMULL reduction.    *)
(*                                                                        *)
(* The assembly uses byte reversal (rev64 + ext #8) to convert between    *)
(* memory layout and polynomial representation. The full correctness      *)
(* theorem would relate gf128_mul to the reflected multiplication via     *)
(* bit reversal, accounting for the x^{-127} factor in the NIST spec.    *)
(*                                                                        *)
(* NOTE: gf128_reduce above takes a 256-bit assembled product as input,   *)
(* but the assembly interleaves Karatsuba combination and reduction.      *)
(* A correct model of the assembly reduction would take the three         *)
(* Karatsuba products (v0, v1, v2) directly, not the assembled product.   *)
(* ====================================================================== *)

(* ====================================================================== *)
(* Part 2: Assembly proof infrastructure                                  *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* Machine code for gcm_gmult_v8 (offset 0x260-0x2c7 in ghashv8-armx.o)  *)
(* 26 instructions + ret = 27 instructions, 108 bytes                     *)
(* ---------------------------------------------------------------------- *)

(* NOTE: In s2n-bignum, this would use define_assert_from_elf.
   The hex values below are the raw 32-bit instruction words from
   objdump -d arm/aes-gcm/ghashv8-armx.o *)

(* gcm_gmult_v8 machine code: 27 instructions *)
(* let gcm_gmult_v8_mc = define_assert_from_elf
     "gcm_gmult_v8_mc" "arm/aes-gcm/ghashv8-armx.o"
  [
    0x4c407c11;  (* ld1    {v17.2d}, [x0]                               *)
    0x4f07e433;  (* movi   v19.16b, #0xe1                               *)
    0x4c40ac34;  (* ld1    {v20.2d-v21.2d}, [x1]                        *)
    0x6e144294;  (* ext    v20.16b, v20.16b, v20.16b, #8                *)
    0x4f795673;  (* shl    v19.2d, v19.2d, #57                          *)
    0x6e114223;  (* ext    v3.16b, v17.16b, v17.16b, #8                 *)
    0x0ee3e280;  (* pmull  v0.1q, v20.1d, v3.1d                        *)
    0x6e231e31;  (* eor    v17.16b, v17.16b, v3.16b                     *)
    0x4ee3e282;  (* pmull2 v2.1q, v20.2d, v3.2d                        *)
    0x0ef1e2a1;  (* pmull  v1.1q, v21.1d, v17.1d                       *)
    0x6e024011;  (* ext    v17.16b, v0.16b, v2.16b, #8                  *)
    0x6e221c12;  (* eor    v18.16b, v0.16b, v2.16b                      *)
    0x6e311c21;  (* eor    v1.16b, v1.16b, v17.16b                      *)
    0x6e321c21;  (* eor    v1.16b, v1.16b, v18.16b                      *)
    0x0ef3e012;  (* pmull  v18.1q, v0.1d, v19.1d                       *)
    0x6e084422;  (* ins    v2.d[0], v1.d[1]                             *)
    0x6e180401;  (* ins    v1.d[1], v0.d[0]                             *)
    0x6e321c20;  (* eor    v0.16b, v1.16b, v18.16b                      *)
    0x6e004012;  (* ext    v18.16b, v0.16b, v0.16b, #8                  *)
    0x0ef3e000;  (* pmull  v0.1q, v0.1d, v19.1d                        *)
    0x6e221e52;  (* eor    v18.16b, v18.16b, v2.16b                     *)
    0x6e321c00;  (* eor    v0.16b, v0.16b, v18.16b                      *)
    0x4e200800;  (* rev64  v0.16b, v0.16b                               *)
    0x6e004000;  (* ext    v0.16b, v0.16b, v0.16b, #8                   *)
    0x4c007c00;  (* st1    {v0.2d}, [x0]                                *)
    0xd65f03c0   (* ret                                                  *)
  ];; *)

(* gcm_ghash_v8 machine code: 89 instructions *)
(* let gcm_ghash_v8_mc = define_assert_from_elf
     "gcm_ghash_v8_mc" "arm/aes-gcm/ghashv8-armx.o"
  [
    0xf101007f;  (* cmp    x3, #0x40                                     *)
    0x4c407c00;  (* ld1    {v0.2d}, [x0]                                 *)
    0xf1008063;  (* subs   x3, x3, #0x20                                 *)
    0xd280020c;  (* mov    x12, #0x10                                    *)
    0x4cdfac34;  (* ld1    {v20.2d-v21.2d}, [x1], #32                   *)
    0x6e144294;  (* ext    v20.16b, v20.16b, v20.16b, #8                 *)
    0x4f07e433;  (* movi   v19.16b, #0xe1                                *)
    0x4c407c36;  (* ld1    {v22.2d}, [x1]                                *)
    0x6e1642d6;  (* ext    v22.16b, v22.16b, v22.16b, #8                 *)
    0x9a8c03ec;  (* csel   x12, xzr, x12, eq                            *)
    0x6e004000;  (* ext    v0.16b, v0.16b, v0.16b, #8                    *)
    0x4cdf7c50;  (* ld1    {v16.2d}, [x2], #16                          *)
    0x4f795673;  (* shl    v19.2d, v19.2d, #57                           *)
    0x4e200a10;  (* rev64  v16.16b, v16.16b                              *)
    0x4e200800;  (* rev64  v0.16b, v0.16b                                *)
    0x6e104203;  (* ext    v3.16b, v16.16b, v16.16b, #8                  *)
    0x54000643;  (* b.cc   0x3d0                                         *)
    0x4ccc7c51;  (* ld1    {v17.2d}, [x2], x12                          *)
    0x4e200a31;  (* rev64  v17.16b, v17.16b                              *)
    0x6e114227;  (* ext    v7.16b, v17.16b, v17.16b, #8                  *)
    0x6e201c63;  (* eor    v3.16b, v3.16b, v0.16b                        *)
    0x0ee7e284;  (* pmull  v4.1q, v20.1d, v7.1d                         *)
    0x6e271e31;  (* eor    v17.16b, v17.16b, v7.16b                      *)
    0x4ee7e286;  (* pmull2 v6.1q, v20.2d, v7.2d                         *)
    0x14000002;  (* b      0x330                                         *)
    0xd503201f;  (* nop                                                  *)
    0x6e034072;  (* ext    v18.16b, v3.16b, v3.16b, #8                   *)
    0xf1008063;  (* subs   x3, x3, #0x20                                 *)
    0x0ee3e2c0;  (* pmull  v0.1q, v22.1d, v3.1d                         *)
    0x9a8c33ec;  (* csel   x12, xzr, x12, cc                            *)
    0x0ef1e2a5;  (* pmull  v5.1q, v21.1d, v17.1d                        *)
    0x6e231e52;  (* eor    v18.16b, v18.16b, v3.16b                      *)
    0x4ee3e2c2;  (* pmull2 v2.1q, v22.2d, v3.2d                         *)
    0x6e241c00;  (* eor    v0.16b, v0.16b, v4.16b                        *)
    0x4ef2e2a1;  (* pmull2 v1.1q, v21.2d, v18.2d                        *)
    0x4ccc7c50;  (* ld1    {v16.2d}, [x2], x12                          *)
    0x6e261c42;  (* eor    v2.16b, v2.16b, v6.16b                        *)
    0x9a8c03ec;  (* csel   x12, xzr, x12, eq                            *)
    0x6e251c21;  (* eor    v1.16b, v1.16b, v5.16b                        *)
    0x6e024011;  (* ext    v17.16b, v0.16b, v2.16b, #8                   *)
    0x6e221c12;  (* eor    v18.16b, v0.16b, v2.16b                       *)
    0x6e311c21;  (* eor    v1.16b, v1.16b, v17.16b                       *)
    0x4ccc7c51;  (* ld1    {v17.2d}, [x2], x12                          *)
    0x4e200a10;  (* rev64  v16.16b, v16.16b                              *)
    0x6e321c21;  (* eor    v1.16b, v1.16b, v18.16b                       *)
    0x0ef3e012;  (* pmull  v18.1q, v0.1d, v19.1d                        *)
    0x4e200a31;  (* rev64  v17.16b, v17.16b                              *)
    0x6e084422;  (* ins    v2.d[0], v1.d[1]                              *)
    0x6e180401;  (* ins    v1.d[1], v0.d[0]                              *)
    0x6e114227;  (* ext    v7.16b, v17.16b, v17.16b, #8                  *)
    0x6e104203;  (* ext    v3.16b, v16.16b, v16.16b, #8                  *)
    0x6e321c20;  (* eor    v0.16b, v1.16b, v18.16b                       *)
    0x0ee7e284;  (* pmull  v4.1q, v20.1d, v7.1d                         *)
    0x6e221c63;  (* eor    v3.16b, v3.16b, v2.16b                        *)
    0x6e004012;  (* ext    v18.16b, v0.16b, v0.16b, #8                   *)
    0x0ef3e000;  (* pmull  v0.1q, v0.1d, v19.1d                         *)
    0x6e321c63;  (* eor    v3.16b, v3.16b, v18.16b                       *)
    0x6e271e31;  (* eor    v17.16b, v17.16b, v7.16b                      *)
    0x6e201c63;  (* eor    v3.16b, v3.16b, v0.16b                        *)
    0x4ee7e286;  (* pmull2 v6.1q, v20.2d, v7.2d                         *)
    0x54fffbc2;  (* b.cs   0x330                                         *)
    0x6e321c42;  (* eor    v2.16b, v2.16b, v18.16b                       *)
    0x6e104203;  (* ext    v3.16b, v16.16b, v16.16b, #8                  *)
    0xb1008063;  (* adds   x3, x3, #0x20                                 *)
    0x6e221c00;  (* eor    v0.16b, v0.16b, v2.16b                        *)
    0x54000280;  (* b.eq   0x41c                                         *)
    0x6e004012;  (* ext    v18.16b, v0.16b, v0.16b, #8                   *)
    0x6e201c63;  (* eor    v3.16b, v3.16b, v0.16b                        *)
    0x6e321e11;  (* eor    v17.16b, v16.16b, v18.16b                     *)
    0x0ee3e280;  (* pmull  v0.1q, v20.1d, v3.1d                         *)
    0x6e231e31;  (* eor    v17.16b, v17.16b, v3.16b                      *)
    0x4ee3e282;  (* pmull2 v2.1q, v20.2d, v3.2d                         *)
    0x0ef1e2a1;  (* pmull  v1.1q, v21.1d, v17.1d                        *)
    0x6e024011;  (* ext    v17.16b, v0.16b, v2.16b, #8                   *)
    0x6e221c12;  (* eor    v18.16b, v0.16b, v2.16b                       *)
    0x6e311c21;  (* eor    v1.16b, v1.16b, v17.16b                       *)
    0x6e321c21;  (* eor    v1.16b, v1.16b, v18.16b                       *)
    0x0ef3e012;  (* pmull  v18.1q, v0.1d, v19.1d                        *)
    0x6e084422;  (* ins    v2.d[0], v1.d[1]                              *)
    0x6e180401;  (* ins    v1.d[1], v0.d[0]                              *)
    0x6e321c20;  (* eor    v0.16b, v1.16b, v18.16b                       *)
    0x6e004012;  (* ext    v18.16b, v0.16b, v0.16b, #8                   *)
    0x0ef3e000;  (* pmull  v0.1q, v0.1d, v19.1d                         *)
    0x6e221e52;  (* eor    v18.16b, v18.16b, v2.16b                      *)
    0x6e321c00;  (* eor    v0.16b, v0.16b, v18.16b                       *)
    0x4e200800;  (* rev64  v0.16b, v0.16b                                *)
    0x6e004000;  (* ext    v0.16b, v0.16b, v0.16b, #8                    *)
    0x4c007c00;  (* st1    {v0.2d}, [x0]                                 *)
    0xd65f03c0   (* ret                                                  *)
  ];; *)

(* ====================================================================== *)
(* Part 3: Correctness theorem statements                                 *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* Htable format predicate                                                *)
(* gcm_init_v8 stores H in a specific layout. For gcm_gmult_v8, only the *)
(* first 32 bytes (Htable[0..1]) are used:                                *)
(*   Htable[0]  = H with halves swapped (twisted)                        *)
(*   Htable[1]  = lo64(H) XOR hi64(H) (Karatsuba precomputed helper)     *)
(* ---------------------------------------------------------------------- *)

(* NOTE: valid_htable_for_gmult needs s2n-bignum ARM infrastructure
let valid_htable_for_gmult = new_definition
  `valid_htable_for_gmult (h:128 word) (htable_addr:int64) s <=>
    read (memory :> bytes(htable_addr, 16)) s =
      val (swap_halves h) /\
    read (memory :> bytes(word_add htable_addr (word 16), 16)) s =
      val (join128 (word 0 : 64 word) (word_xor (lo64 h) (hi64 h)))`;;
*)

(* ---------------------------------------------------------------------- *)
(* Correctness of gcm_gmult_v8                                            *)
(*                                                                        *)
(* Precondition:                                                          *)
(*   - Code loaded at pc (offset 0x260 in the object file)                *)
(*   - PC at entry point                                                  *)
(*   - x0 points to Xi (16 bytes), x1 points to Htable                   *)
(*   - Htable was correctly initialized for hash key H                    *)
(*                                                                        *)
(* Postcondition:                                                         *)
(*   - PC advanced past ret                                               *)
(*   - Memory at Xi contains gf128_mul(old_Xi, H)                         *)
(*                                                                        *)
(* NOTE: This theorem requires ARM instruction infrastructure that does   *)
(* not yet exist in s2n-bignum (PMULL, LD1, ST1). Marked with CHEAT_TAC. *)
(* ---------------------------------------------------------------------- *)

(* The correctness statement would be:

let GCM_GMULT_V8_CORRECT = prove
 (`!pc xi_ptr htable_ptr xi_val h_val.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) gcm_gmult_v8_mc /\
            read PC s = word pc /\
            read X0 s = xi_ptr /\
            read X1 s = htable_ptr /\
            read (memory :> bytes128 xi_ptr) s = xi_val /\
            valid_htable_for_gmult h_val htable_ptr s)
       (\s. read PC s = word (pc + 0x64) /\
            read (memory :> bytes128 xi_ptr) s =
              word_bytereverse
                (gf128_mul (word_bytereverse xi_val)
                           (word_bytereverse h_val)))
       (MAYCHANGE [PC; Q0; Q1; Q2; Q3; Q17; Q18; Q19; Q20; Q21] ,,
        MAYCHANGE [memory :> bytes(xi_ptr, 16)])`,
  CHEAT_TAC);;
*)

(* ====================================================================== *)
(* Part 4: Properties of the specification (provable now)                 *)
(* ====================================================================== *)

let GF128_MUL_LZERO = prove
 (`!H:128 word. gf128_mul (word 0) H = word 0`,
  GEN_TAC THEN REWRITE_TAC[gf128_mul] THEN
  SPEC_TAC (`H:128 word`, `v:128 word`) THEN
  SPEC_TAC (`128`, `n:num`) THEN
  INDUCT_TAC THENL [REWRITE_TAC[gf128_mul_loop]; ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[gf128_mul_loop; BIT_WORD_0] THEN
  ASM_REWRITE_TAC[]);;

let GF128_MUL_RZERO = prove
 (`!X:128 word. gf128_mul X (word 0) = word 0`,
  GEN_TAC THEN REWRITE_TAC[gf128_mul] THEN
  SPEC_TAC (`128`, `n:num`) THEN
  INDUCT_TAC THENL [REWRITE_TAC[gf128_mul_loop]; ALL_TAC] THEN
  REWRITE_TAC[gf128_mul_loop; BIT_WORD_0] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_REFL] THEN
  SUBGOAL_THEN `word_ushr (word 0:128 word) 1 = word 0` SUBST1_TAC THENL
  [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[COND_ID] THEN ASM_REWRITE_TAC[]);;

let GF128_MUL_LOOP_LDISTRIB = prove
 (`!n a b za zb v. gf128_mul_loop (word_xor a b) n (word_xor za zb) v =
    word_xor (gf128_mul_loop a n za v) (gf128_mul_loop b n zb v) : 128 word`,
  INDUCT_TAC THENL
  [REWRITE_TAC[gf128_mul_loop; WORD_XOR_REFL];
   REPEAT GEN_TAC THEN REWRITE_TAC[gf128_mul_loop; BIT_WORD_XOR_ALT] THEN
   SUBGOAL_THEN
     `(if ~(bit n (a:128 word) <=> bit n (b:128 word))
       then word_xor (word_xor za zb) v
       else word_xor za zb) : 128 word =
      word_xor (if bit n a then word_xor za v else za)
               (if bit n b then word_xor zb v else zb)`
     SUBST1_TAC THENL
   [BOOL_CASES_TAC `bit n (a:128 word)` THEN
    BOOL_CASES_TAC `bit n (b:128 word)` THEN
    REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    ASM_REWRITE_TAC[]]]);;

let GF128_MUL_LDISTRIB = prove
 (`!a b H:128 word. gf128_mul (word_xor a b) H =
    word_xor (gf128_mul a H) (gf128_mul b H)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gf128_mul] THEN
  MP_TAC(SPECL [`128`; `a:128 word`; `b:128 word`;
                `word 0:128 word`; `word 0:128 word`; `H:128 word`]
    GF128_MUL_LOOP_LDISTRIB) THEN
  REWRITE_TAC[WORD_XOR_REFL]);;

let GF128_MUL_LOOP_RDISTRIB = prove
 (`!n x za zb va vb. gf128_mul_loop x n (word_xor za zb) (word_xor va vb) =
    word_xor (gf128_mul_loop x n za va) (gf128_mul_loop x n zb vb) : 128 word`,
  INDUCT_TAC THENL
  [REWRITE_TAC[gf128_mul_loop; WORD_XOR_REFL];
   REPEAT GEN_TAC THEN REWRITE_TAC[gf128_mul_loop] THEN
   SUBGOAL_THEN
     `(if bit n (x:128 word)
       then word_xor (word_xor za zb) (word_xor va vb)
       else word_xor za zb) : 128 word =
      word_xor (if bit n x then word_xor za va else za)
               (if bit n x then word_xor zb vb else zb)`
     SUBST1_TAC THENL
   [BOOL_CASES_TAC `bit n (x:128 word)` THEN
    REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(if bit 0 (word_xor va vb : 128 word)
       then word_xor (word_ushr (word_xor va vb) 1) gf128_R
       else word_ushr (word_xor va vb) 1) : 128 word =
      word_xor (if bit 0 va then word_xor (word_ushr va 1) gf128_R
                else word_ushr va 1)
               (if bit 0 vb then word_xor (word_ushr vb 1) gf128_R
                else word_ushr vb 1)`
     SUBST1_TAC THENL
   [REWRITE_TAC[BIT_WORD_XOR_ALT; WORD_USHR_XOR] THEN
    BOOL_CASES_TAC `bit 0 (va:128 word)` THEN
    BOOL_CASES_TAC `bit 0 (vb:128 word)` THEN
    REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    ASM_REWRITE_TAC[]]]);;

let GF128_MUL_RDISTRIB = prove
 (`!X H1 H2:128 word. gf128_mul X (word_xor H1 H2) =
    word_xor (gf128_mul X H1) (gf128_mul X H2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gf128_mul] THEN
  MP_TAC(SPECL [`128`; `X:128 word`;
                `word 0:128 word`; `word 0:128 word`;
                `H1:128 word`; `H2:128 word`]
    GF128_MUL_LOOP_RDISTRIB) THEN
  REWRITE_TAC[WORD_XOR_REFL]);;

let GHASH_NIL = prove
 (`!H:128 word. GHASH H [] = word 0`,
  REWRITE_TAC[GHASH; ghash]);;

let GHASH_SING = prove
 (`!H:128 word X:128 word. GHASH H [X] = gf128_mul X H`,
  REWRITE_TAC[GHASH; ghash; WORD_XOR_0]);;

let GHASH_CONS = prove
 (`!H:128 word X:128 word Xs:(128 word) list.
    GHASH H (CONS X Xs) = ghash H (gf128_mul X H) Xs`,
  REWRITE_TAC[GHASH; ghash; WORD_XOR_0]);;

let GHASH_TWO = prove
 (`!H X1 X2:128 word.
    GHASH H [X1; X2] = gf128_mul (word_xor (gf128_mul X1 H) X2) H`,
  REWRITE_TAC[GHASH; ghash; WORD_XOR_0]);;

(* ---------------------------------------------------------------------- *)
(* Properties of clmul (carryless multiplication)                         *)
(* ---------------------------------------------------------------------- *)

let CLMUL_LZERO = prove
 (`!b:64 word. clmul (word 0) b = word 0`,
  GEN_TAC THEN REWRITE_TAC[clmul] THEN
  SPEC_TAC (`64`, `n:num`) THEN
  INDUCT_TAC THENL [REWRITE_TAC[clmul_loop]; ALL_TAC] THEN
  REWRITE_TAC[clmul_loop; BIT_WORD_0; WORD_XOR_0] THEN
  ASM_REWRITE_TAC[]);;

let WORD_SHL_WORD_0 = prove
 (`!n. word_shl (word 0:N word) n = word 0`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD_0; MULT_CLAUSES; MOD_0]);;

let CLMUL_RZERO = prove
 (`!a:64 word. clmul a (word 0) = word 0`,
  GEN_TAC THEN REWRITE_TAC[clmul] THEN
  SPEC_TAC (`64`, `n:num`) THEN
  INDUCT_TAC THENL [REWRITE_TAC[clmul_loop]; ALL_TAC] THEN
  REWRITE_TAC[clmul_loop] THEN
  SUBGOAL_THEN `word_zx (word 0:64 word) : 128 word = word 0` SUBST1_TAC THENL
  [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[WORD_SHL_WORD_0; COND_ID; WORD_XOR_0] THEN
  ASM_REWRITE_TAC[]);;

(* ---------------------------------------------------------------------- *)
(* clmul distributes over XOR (polynomial addition in GF(2))              *)
(* These are key properties for Karatsuba correctness.                    *)
(* ---------------------------------------------------------------------- *)

let CLMUL_LOOP_LDISTRIB = prove
 (`!a b c n. clmul_loop (word_xor a b) c n : 128 word =
    word_xor (clmul_loop a c n) (clmul_loop b c n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[clmul_loop; WORD_XOR_REFL];
   REWRITE_TAC[clmul_loop; BIT_WORD_XOR_ALT] THEN ASM_REWRITE_TAC[] THEN
   BOOL_CASES_TAC `bit n (a:64 word)` THEN
   BOOL_CASES_TAC `bit n (b:64 word)` THEN
   REWRITE_TAC[WORD_XOR_0] THEN
   CONV_TAC WORD_RULE]);;

let CLMUL_LDISTRIB = prove
 (`!a b c:64 word. clmul (word_xor a b) c : 128 word =
    word_xor (clmul a c) (clmul b c)`,
  REWRITE_TAC[clmul; CLMUL_LOOP_LDISTRIB]);;

let CLMUL_LOOP_RDISTRIB = prove
 (`!a b c n. clmul_loop a (word_xor b c) n : 128 word =
    word_xor (clmul_loop a b n) (clmul_loop a c n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[clmul_loop; WORD_XOR_REFL];
   REWRITE_TAC[clmul_loop; WORD_ZX_XOR; WORD_SHL_XOR] THEN
   ASM_REWRITE_TAC[] THEN
   BOOL_CASES_TAC `bit n (a:64 word)` THEN
   REWRITE_TAC[WORD_XOR_0] THEN
   CONV_TAC WORD_RULE]);;

let CLMUL_RDISTRIB = prove
 (`!a b c:64 word. clmul a (word_xor b c) : 128 word =
    word_xor (clmul a b) (clmul a c)`,
  REWRITE_TAC[clmul; CLMUL_LOOP_RDISTRIB]);;

(* ---------------------------------------------------------------------- *)
(* Bit-level properties of clmul (for commutativity proof)                *)
(* ---------------------------------------------------------------------- *)

(* clmul_loop with zero bits in a gives zero *)
let CLMUL_LOOP_ZERO_BITS = prove
 (`!n (a:64 word) b. (!k. k < n ==> ~bit k a)
    ==> clmul_loop a b n = word 0`,
  INDUCT_TAC THENL
  [REWRITE_TAC[clmul_loop];
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[clmul_loop] THEN
   SUBGOAL_THEN `~bit n (a:64 word)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[WORD_XOR_0] THEN
    FIRST_X_ASSUM(fun ih -> MATCH_MP_TAC ih) THEN
    ASM_MESON_TAC[ARITH_RULE `k < n ==> k < SUC n`]]]);;

(* clmul_loop with single-bit first argument equals shift *)
let CLMUL_LOOP_SINGLE_BIT = prove
 (`!n i (b:64 word). i < 64 /\ i <= n ==>
    clmul_loop (word_of_bits {i} : 64 word) b (SUC n) =
    word_shl (word_zx b : 128 word) i`,
  INDUCT_TAC THENL
  [(* Base case: n = 0, so i = 0 *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `i = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[clmul_loop] THEN
   SUBGOAL_THEN `bit 0 (word_of_bits {0} : 64 word) = T` SUBST1_TAC THENL
   [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_64; ARITH];
    REWRITE_TAC[WORD_XOR_0; WORD_SHL_ZERO]];
   (* Step case *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   ONCE_REWRITE_TAC[clmul_loop] THEN
   ASM_CASES_TAC `i = SUC n` THENL
   [(* i = SUC n *)
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `bit (SUC n) (word_of_bits {SUC n} : 64 word) = T` SUBST1_TAC THENL
    [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_64] THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `clmul_loop (word_of_bits {SUC n} : 64 word) b (SUC n) = word 0`
      SUBST1_TAC THENL
    [MATCH_MP_TAC CLMUL_LOOP_ZERO_BITS THEN
     REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_64] THEN
     ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_XOR_0];
    (* i < SUC n, so i <= n *)
    SUBGOAL_THEN `bit (SUC n) (word_of_bits {i} : 64 word) = F` SUBST1_TAC THENL
    [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_64] THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_XOR_0] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* clmul with single-bit first argument *)
let CLMUL_SINGLE_BIT = prove
 (`!i (b:64 word). i < 64 ==>
    clmul (word_of_bits {i} : 64 word) b = word_shl (word_zx b : 128 word) i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[clmul] THEN
  SUBGOAL_THEN `64 = SUC 63` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CLMUL_LOOP_SINGLE_BIT THEN ASM_ARITH_TAC);;

(* Bit-level characterization of clmul_loop with single-bit RIGHT argument *)
let BIT_CLMUL_LOOP_R_SINGLE = prove
 (`!n j k (a:64 word). j < 64 /\ k < 128 ==>
    (bit k (clmul_loop a (word_of_bits{j} : 64 word) n : 128 word) <=>
     j <= k /\ k - j < n /\ bit (k - j) a)`,
  INDUCT_TAC THENL
  [(* Base case *)
   REWRITE_TAC[clmul_loop; BIT_WORD_0; LT];
   (* Step case *)
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   ONCE_REWRITE_TAC[clmul_loop] THEN
   REWRITE_TAC[BIT_WORD_XOR] THEN ASM_REWRITE_TAC[DIMINDEX_128] THEN
   SUBGOAL_THEN
     `bit k (clmul_loop a (word_of_bits{j} : 64 word) n : 128 word) <=>
      j <= k /\ k - j < n /\ bit (k - j) a`
     SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `k:num`; `a:64 word`]) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   COND_CASES_TAC THENL
   [(* bit n a = T *)
    REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD_OF_BITS;
                IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = n + j` THENL
    [SUBGOAL_THEN `n <= k /\ k - n = j /\ j <= k /\ k - j = n /\
                    k - n < 128 /\ k - n < 64 /\ n < SUC n`
       STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[LT_REFL];
     SUBGOAL_THEN `~(n <= k /\ k - n < 128 /\ k - n < 64 /\ k - n = j)`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_ARITH_TAC;
      SUBGOAL_THEN `k - j < n` ASSUME_TAC THENL
      [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]];
    (* ~bit n a *)
    REWRITE_TAC[BIT_WORD_0] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
    [ASM_ARITH_TAC;
     ASM_CASES_TAC `k - j = n` THENL
     [UNDISCH_TAC `bit (k - j) (a:64 word)` THEN ASM_REWRITE_TAC[];
      ASM_ARITH_TAC]]]]);;

(* clmul with single-bit RIGHT argument equals shift *)
let CLMUL_SINGLE_BIT_R = prove
 (`!j (a:64 word). j < 64 ==>
    clmul a (word_of_bits {j} : 64 word) = word_shl (word_zx a : 128 word) j`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_128] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[clmul] THEN
  MP_TAC(SPECL [`64`; `j:num`; `k:num`; `a:64 word`] BIT_CLMUL_LOOP_R_SINGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_128; DIMINDEX_64] THEN
  ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
  [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `k - j < 64` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:64 word`; `k - j:num`] BIT_TRIVIAL) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]]);;

(* XOR cancellation: word_xor (word_xor a b) b = a *)
let WORD_XOR_CANCEL = prove
 (`!a:N word b. word_xor (word_xor a b) b = a`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
  REWRITE_TAC[WORD_XOR_REFL; WORD_XOR_0]);;

(* Helper: commutativity of clmul for words with bounded active bits *)
let CLMUL_COMM_LEMMA = prove
 (`!m (a:64 word) (b:64 word).
    (!k. m <= k ==> ~bit k a) ==> clmul a b = clmul b a`,
  INDUCT_TAC THENL
  [(* Base case: m = 0, so a = word 0 *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `a = word 0 : 64 word` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; DIMINDEX_64] THEN
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[LE_0];
    REWRITE_TAC[CLMUL_LZERO; CLMUL_RZERO]];
   (* Step case: SUC m *)
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `bit m (a:64 word)` THENL
   [(* bit m a = T *)
    SUBGOAL_THEN `m < 64` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
     MP_TAC(ISPECL [`a:64 word`; `m:num`] BIT_TRIVIAL) THEN
     ASM_REWRITE_TAC[DIMINDEX_64];
     ALL_TAC] THEN
    (* Decompose LHS: clmul a b via CLMUL_LDISTRIB *)
    SUBGOAL_THEN
      `clmul a b = word_xor (clmul (word_xor a (word_of_bits{m} : 64 word)) b)
                             (clmul (word_of_bits{m} : 64 word) b) : 128 word`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM CLMUL_LDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     ONCE_REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
     REWRITE_TAC[WORD_XOR_REFL; WORD_XOR_0];
     ALL_TAC] THEN
    (* Decompose RHS: clmul b a via CLMUL_RDISTRIB *)
    SUBGOAL_THEN
      `clmul b a = word_xor (clmul b (word_xor a (word_of_bits{m} : 64 word)))
                             (clmul b (word_of_bits{m} : 64 word)) : 128 word`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM CLMUL_RDISTRIB] THEN AP_TERM_TAC THEN
     ONCE_REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
     REWRITE_TAC[WORD_XOR_REFL; WORD_XOR_0];
     ALL_TAC] THEN
    (* Match both XOR components *)
    MK_COMB_TAC THENL
    [(* clmul a' b = clmul b a' by IH *)
     AP_TERM_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `k < 64` THENL
     [REWRITE_TAC[BIT_WORD_XOR; DIMINDEX_64] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_64] THEN
      ASM_CASES_TAC `k:num = m` THENL
      [ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `!k. SUC m <= k ==> ~bit k (a:64 word)` THEN
       DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
      MP_TAC(ISPECL [`word_xor a (word_of_bits{m} : 64 word)`; `k:num`]
        BIT_TRIVIAL) THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
     (* clmul (word_of_bits{m}) b = clmul b (word_of_bits{m}) *)
     MP_TAC(SPECL [`m:num`; `b:64 word`] CLMUL_SINGLE_BIT) THEN
     MP_TAC(SPECL [`m:num`; `b:64 word`] CLMUL_SINGLE_BIT_R) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    (* ~bit m a: just apply IH *)
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k:num = m` THENL
    [ASM_REWRITE_TAC[];
     UNDISCH_TAC `!k. SUC m <= k ==> ~bit k (a:64 word)` THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;

(* Commutativity of carryless multiplication *)
let CLMUL_COMM = prove
 (`!a b:64 word. clmul a b = clmul b a`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`64`; `a:64 word`; `b:64 word`] CLMUL_COMM_LEMMA) THEN
  ANTS_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`a:64 word`; `k:num`] BIT_TRIVIAL) THEN
   REWRITE_TAC[DIMINDEX_64] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
   SIMP_TAC[]]);;

(* ---------------------------------------------------------------------- *)
(* Properties of join128 / lo64 / hi64 / swap_halves                      *)
(* ---------------------------------------------------------------------- *)

let JOIN128_SPLIT = prove
 (`!x:128 word. join128 (hi64 x) (lo64 x) = x`,
  GEN_TAC THEN REWRITE_TAC[join128; hi64; lo64] THEN BITBLAST_TAC);;

let LO64_JOIN128,HI64_JOIN128 = (CONJ_PAIR o prove)
 (`(!hi lo:64 word. lo64 (join128 hi lo) = lo) /\
   (!hi lo:64 word. hi64 (join128 hi lo) = hi)`,
  REWRITE_TAC[join128; lo64; hi64] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let JOIN128_XOR = prove
 (`!a b c d:64 word. word_xor (join128 a b) (join128 c d) : 128 word =
    join128 (word_xor a c) (word_xor b d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[join128; lo64; hi64] THEN BITBLAST_TAC);;

let LO64_XOR,HI64_XOR = (CONJ_PAIR o prove)
 (`(!x y:128 word. lo64 (word_xor x y) = word_xor (lo64 x) (lo64 y)) /\
   (!x y:128 word. hi64 (word_xor x y) = word_xor (hi64 x) (hi64 y))`,
  REWRITE_TAC[lo64; hi64] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let SWAP_HALVES_INVOLUTION = prove
 (`!x:128 word. swap_halves (swap_halves x) = x`,
  GEN_TAC THEN REWRITE_TAC[swap_halves; join128; lo64; hi64] THEN
  BITBLAST_TAC);;

let SWAP_HALVES_XOR = prove
 (`!x y:128 word. swap_halves (word_xor x y) =
    word_xor (swap_halves x) (swap_halves y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[swap_halves; LO64_XOR; HI64_XOR; JOIN128_XOR]);;

let SWAP_HALVES_0 = prove
 (`swap_halves (word 0 : 128 word) = word 0`,
  REWRITE_TAC[swap_halves; lo64; hi64; join128] THEN BITBLAST_TAC);;

(* ---------------------------------------------------------------------- *)
(* Properties of word_bytereverse (for assembly byte-order conversion)     *)
(* ---------------------------------------------------------------------- *)

let WORD_BYTEREVERSE_XOR = prove
 (`!x y:128 word. word_bytereverse (word_xor x y) =
    word_xor (word_bytereverse x) (word_bytereverse y)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let WORD_BYTEREVERSE_0 = prove
 (`word_bytereverse (word 0 : 128 word) = word 0`,
  BITBLAST_TAC);;

let WORD_BYTEREVERSE_INVOLUTION = prove
 (`!x:128 word. word_bytereverse (word_bytereverse x) = x`,
  GEN_TAC THEN BITBLAST_TAC);;

(* ---------------------------------------------------------------------- *)
(* Karatsuba decomposition is algebraically correct                       *)
(* The 3-multiply Karatsuba method produces the same 256-bit polynomial   *)
(* product as the direct 4-multiply schoolbook method.                    *)
(* ---------------------------------------------------------------------- *)

let KARATSUBA_EQ_SCHOOLBOOK = prove
 (`!x y:128 word. clmul128_karatsuba x y = clmul128_schoolbook x y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clmul128_karatsuba; clmul128_schoolbook;
              LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[CLMUL_LDISTRIB; CLMUL_RDISTRIB] THEN
  REWRITE_TAC[WORD_ZX_XOR; WORD_SHL_XOR] THEN
  CONV_TAC WORD_RULE);;

(* Commutativity of schoolbook 128-bit carryless product *)
let CLMUL128_SCHOOLBOOK_COMM = prove
 (`!x y:128 word. clmul128_schoolbook x y = clmul128_schoolbook y x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clmul128_schoolbook; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
    `clmul (lo64 x) (lo64 y) = clmul (lo64 y) (lo64 x) /\
     clmul (hi64 x) (hi64 y) = clmul (hi64 y) (hi64 x) /\
     clmul (lo64 x) (hi64 y) = clmul (hi64 y) (lo64 x) /\
     clmul (hi64 x) (lo64 y) = clmul (lo64 y) (hi64 x)`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[CLMUL_COMM];
   AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN REFL_TAC]);;

(* Commutativity of Karatsuba 128-bit carryless product *)
let CLMUL128_KARATSUBA_COMM = prove
 (`!x y:128 word. clmul128_karatsuba x y = clmul128_karatsuba y x`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[KARATSUBA_EQ_SCHOOLBOOK] THEN
  MATCH_ACCEPT_TAC CLMUL128_SCHOOLBOOK_COMM);;

(* ---------------------------------------------------------------------- *)
(* Key GHASH streaming property: ghash is associative over APPEND          *)
(* This means GHASH can process data in chunks.                           *)
(* ---------------------------------------------------------------------- *)

let GHASH_ASSOC = prove
 (`!H:128 word xs ys Y:128 word.
    ghash H Y (APPEND xs ys) = ghash H (ghash H Y xs) ys`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
  [REWRITE_TAC[APPEND; ghash];
   ASM_REWRITE_TAC[APPEND; ghash]]);;

let GHASH_APPEND = prove
 (`!H:128 word xs ys.
    GHASH H (APPEND xs ys) = ghash H (GHASH H xs) ys`,
  REWRITE_TAC[GHASH; GHASH_ASSOC]);;

(* ---------------------------------------------------------------------- *)
(* Identity elements for gf128_mul                                        *)
(* word_of_bits {127} is the multiplicative identity (NIST bit ordering)  *)
(* ---------------------------------------------------------------------- *)

let GF128_MUL_LOOP_ZERO_BITS = prove
 (`!n (x:128 word) z v. (!k. k < n ==> ~bit k x)
    ==> gf128_mul_loop x n z v = z`,
  INDUCT_TAC THENL
  [REWRITE_TAC[gf128_mul_loop];
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[gf128_mul_loop] THEN
   SUBGOAL_THEN `~bit n (x:128 word)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun ih -> MATCH_MP_TAC ih) THEN
    ASM_MESON_TAC[ARITH_RULE `k < n ==> k < SUC n`]]]);;

let GF128_MUL_LID = prove
 (`!y:128 word. gf128_mul (word_of_bits {127} : 128 word) y = y`,
  GEN_TAC THEN REWRITE_TAC[gf128_mul] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV)
    [ARITH_RULE `128 = SUC 127`] THEN
  REWRITE_TAC[gf128_mul_loop] THEN
  SUBGOAL_THEN `bit 127 (word_of_bits {127} : 128 word) = T` SUBST1_TAC THENL
  [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY;
               DIMINDEX_128; ARITH];
   REWRITE_TAC[WORD_XOR_0] THEN
   MATCH_MP_TAC GF128_MUL_LOOP_ZERO_BITS THEN
   REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY;
               DIMINDEX_128] THEN ARITH_TAC]);;

(* Helper: word_subword can be extended one bit at a time *)
let WORD_SUBWORD_EXTEND = prove
 (`!x:128 word n. SUC n < 128 ==>
    word_subword x (0,SUC(SUC n)) : 128 word =
    word_xor (if bit (SUC n) x then word_of_bits {SUC n} else word 0 : 128 word)
             (word_subword x (0,SUC n))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR; BIT_WORD_SUBWORD;
              BIT_WORD_OF_BITS; BIT_WORD_0;
              IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128; ADD_CLAUSES] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `MIN (SUC n) 128 = SUC n /\ MIN (SUC(SUC n)) 128 = SUC(SUC n)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i = SUC n` THEN ASM_REWRITE_TAC[] THENL
  [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128;
               LT_REFL] THEN ASM_ARITH_TAC;
   REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `i < SUC n <=> i < SUC(SUC n)` (fun th -> REWRITE_TAC[th]) THEN
   ASM_ARITH_TAC;
   REWRITE_TAC[BIT_WORD_0];
   REWRITE_TAC[BIT_WORD_0] THEN
   SUBGOAL_THEN `i < SUC n <=> i < SUC(SUC n)` (fun th -> REWRITE_TAC[th]) THEN
   ASM_ARITH_TAC]);;

(* Loop characterization: loop with word_of_bits{n} accumulates lower bits *)
let GF128_MUL_LOOP_RID_LEMMA = prove
 (`!n (x:128 word) z. n <= 127 ==>
    gf128_mul_loop x (SUC n) z (word_of_bits {n} : 128 word) =
    word_xor z (word_subword x (0,SUC n) : 128 word)`,
  INDUCT_TAC THENL
  [(* Base case: n = 0 *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[gf128_mul_loop] THEN
   SUBGOAL_THEN `bit 0 (word_of_bits {0} : 128 word) = T` SUBST1_TAC THENL
   [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128; ARITH];
    ALL_TAC] THEN
   SUBGOAL_THEN `!y:128 word. word_subword y (0,1) : 128 word =
     if bit 0 y then word_of_bits {0} else word 0`
     (fun th -> REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_OF_BITS;
                BIT_WORD_0; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> ~(i < 1)`];
    ALL_TAC] THEN
   COND_CASES_TAC THEN CONV_TAC WORD_RULE;
   (* Step case: SUC n *)
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[gf128_mul_loop] THEN
   SUBGOAL_THEN `bit 0 (word_of_bits {SUC n} : 128 word) = F` SUBST1_TAC THENL
   [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
    ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[] THEN
   SUBGOAL_THEN `word_ushr (word_of_bits {SUC n} : 128 word) 1 =
                 word_of_bits {n} : 128 word` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_OF_BITS;
                IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `n <= 127` (fun h ->
     FIRST_X_ASSUM (fun ih -> REWRITE_TAC[MATCH_MP ih h])) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `SUC n < 128` (fun h ->
     REWRITE_TAC[MATCH_MP WORD_SUBWORD_EXTEND h]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THEN CONV_TAC WORD_RULE]);;

(* Right identity: gf128_mul x (word_of_bits{127}) = x *)
let GF128_MUL_RID = prove
 (`!x:128 word. gf128_mul x (word_of_bits {127} : 128 word) = x`,
  GEN_TAC THEN REWRITE_TAC[gf128_mul] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV)
    [ARITH_RULE `128 = SUC 127`] THEN
  MP_TAC (SPECL [`127`; `x:128 word`; `word 0:128 word`]
    GF128_MUL_LOOP_RID_LEMMA) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; DIMINDEX_128; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

(* ---------------------------------------------------------------------- *)
(* gf128_shift: the right-shift-with-reduction operation                  *)
(* This is x -> x*x mod P in GF(2^128) polynomial terms.                *)
(* ---------------------------------------------------------------------- *)

let gf128_shift = new_definition
  `gf128_shift (v:128 word) : 128 word =
    if bit 0 v then word_xor (word_ushr v 1) gf128_R
    else word_ushr v 1`;;

let gf128_shift_iter = define
  `(gf128_shift_iter 0 (y:128 word) = y) /\
   (gf128_shift_iter (SUC n) y = gf128_shift (gf128_shift_iter n y))`;;

(* gf128_shift is GF(2)-linear *)
let GF128_SHIFT_LINEAR = prove
 (`!a b:128 word. gf128_shift (word_xor a b) =
    word_xor (gf128_shift a) (gf128_shift b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gf128_shift; BIT_WORD_XOR_ALT; WORD_USHR_XOR] THEN
  BOOL_CASES_TAC `bit 0 (a:128 word)` THEN
  BOOL_CASES_TAC `bit 0 (b:128 word)` THEN
  REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

(* Iteration commutes with shift *)
let GF128_SHIFT_ITER_STEP = prove
 (`!n (v:128 word). gf128_shift_iter n (gf128_shift v) =
    gf128_shift_iter (SUC n) v`,
  INDUCT_TAC THENL
  [REWRITE_TAC[gf128_shift_iter];
   GEN_TAC THEN ONCE_REWRITE_TAC[gf128_shift_iter] THEN
   AP_TERM_TAC THEN ASM_REWRITE_TAC[]]);;

(* Additive iteration *)
let GF128_SHIFT_ITER_ADD = prove
 (`!m n (v:128 word). gf128_shift_iter (m + n) v =
    gf128_shift_iter m (gf128_shift_iter n v)`,
  INDUCT_TAC THENL
  [REWRITE_TAC[ADD; gf128_shift_iter];
   ASM_REWRITE_TAC[ADD; gf128_shift_iter]]);;

(* gf128_shift on word_of_bits{m} for m > 0 just decrements *)
let GF128_SHIFT_SINGLE_BIT = prove
 (`!m. 0 < m /\ m < 128 ==>
    gf128_shift (word_of_bits{m} : 128 word) = word_of_bits{m - 1}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[gf128_shift] THEN
  SUBGOAL_THEN `bit 0 (word_of_bits{m} : 128 word) = F` SUBST1_TAC THENL
  [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
   ASM_ARITH_TAC;
   REWRITE_TAC[] THEN
   REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_OF_BITS;
               IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_ARITH_TAC]);;

(* gf128_shift of word_of_bits{0} = gf128_R *)
let GF128_SHIFT_BIT0 = prove
 (`gf128_shift (word_of_bits{0} : 128 word) = gf128_R`,
  REWRITE_TAC[gf128_shift] THEN
  SUBGOAL_THEN `bit 0 (word_of_bits{0} : 128 word) = T` SUBST1_TAC THENL
  [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128; ARITH];
   REWRITE_TAC[] THEN
   SUBGOAL_THEN `word_ushr (word_of_bits{0} : 128 word) 1 = word 0` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_OF_BITS; BIT_WORD_0;
                IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ARITH_TAC;
    REWRITE_TAC[WORD_XOR_0]]]);;

(* Iterated shift of single bit: k steps from bit m goes to bit m-k *)
let GF128_SHIFT_ITER_SINGLE = prove
 (`!k m. k <= m /\ m < 128 ==>
    gf128_shift_iter k (word_of_bits{m} : 128 word) = word_of_bits{m - k}`,
  INDUCT_TAC THENL
  [REWRITE_TAC[gf128_shift_iter; SUB_0];
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[gf128_shift_iter] THEN
   SUBGOAL_THEN `0 < m - k /\ m - k < 128` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_SIMP_TAC[GF128_SHIFT_SINGLE_BIT] THEN
   SUBGOAL_THEN `m - k - 1 = m - SUC k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REFL_TAC]]);;

(* gf128_mul_loop with word_of_bits{m}: only bit m contributes *)
let GF128_MUL_LOOP_SINGLE_BIT = prove
 (`!n m (z:128 word) (v:128 word).
    m < n /\ m < 128 ==>
    gf128_mul_loop (word_of_bits{m} : 128 word) n z v =
    word_xor z (gf128_shift_iter (n - 1 - m) v)`,
  INDUCT_TAC THENL
  [ARITH_TAC;
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC[gf128_mul_loop] THEN
   REWRITE_TAC[GSYM gf128_shift] THEN
   ASM_CASES_TAC `m = n:num` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `bit n (word_of_bits{n} : 128 word) = T` SUBST1_TAC THENL
    [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `SUC n - 1 - n = 0` SUBST1_TAC THENL
    [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[gf128_shift_iter] THEN
    MATCH_MP_TAC GF128_MUL_LOOP_ZERO_BITS THEN
    REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `m < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `bit n (word_of_bits{m} : 128 word) = F` SUBST1_TAC THENL
    [REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `z:128 word`;
                                    `gf128_shift (v:128 word)`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[GF128_SHIFT_ITER_STEP] THEN
    SUBGOAL_THEN `SUC (n - 1 - m) = SUC n - 1 - m` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC]]);;

(* gf128_mul (word_of_bits{m}) y = gf128_shift_iter (127-m) y *)
let GF128_MUL_SINGLE_BIT_L = prove
 (`!m (y:128 word). m < 128 ==>
    gf128_mul (word_of_bits{m} : 128 word) y = gf128_shift_iter (127 - m) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gf128_mul] THEN
  MP_TAC(SPECL [`128`; `m:num`; `word 0:128 word`; `y:128 word`]
    GF128_MUL_LOOP_SINGLE_BIT) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_XOR_0] THEN
  SUBGOAL_THEN `128 - 1 - m = 127 - m` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* Single-bit x single-bit commutativity *)
let GF128_MUL_SINGLE_BIT_COMM = prove
 (`!m j. m < 128 /\ j < 128 ==>
    gf128_mul (word_of_bits{m} : 128 word) (word_of_bits{j} : 128 word) =
    gf128_mul (word_of_bits{j} : 128 word) (word_of_bits{m} : 128 word)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GF128_MUL_SINGLE_BIT_L] THEN
  ASM_CASES_TAC `127 <= m + j` THENL
  [(* Case m + j >= 127: both sides are word_of_bits{m+j-127} *)
   SUBGOAL_THEN `127 - m <= j /\ j < 128` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `127 - j <= m /\ m < 128` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[GF128_SHIFT_ITER_SINGLE] THEN
   SUBGOAL_THEN `j - (127 - m) = m - (127 - j)` (fun th -> REWRITE_TAC[th]) THEN
   ASM_ARITH_TAC;
   (* Case m + j < 127: both = gf128_shift_iter(126-m-j)(gf128_R) *)
   SUBGOAL_THEN `127 - m = (126 - m - j) + SUC j` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   ONCE_REWRITE_TAC[GF128_SHIFT_ITER_ADD] THEN
   REWRITE_TAC[gf128_shift_iter] THEN
   SUBGOAL_THEN `j <= j /\ j < 128`
     (fun h -> REWRITE_TAC[MATCH_MP GF128_SHIFT_ITER_SINGLE h]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[SUB_REFL; GF128_SHIFT_BIT0] THEN
   SUBGOAL_THEN `127 - j = (126 - m - j) + SUC m` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   ONCE_REWRITE_TAC[GF128_SHIFT_ITER_ADD] THEN
   REWRITE_TAC[gf128_shift_iter] THEN
   SUBGOAL_THEN `m <= m /\ m < 128`
     (fun h -> REWRITE_TAC[MATCH_MP GF128_SHIFT_ITER_SINGLE h]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[SUB_REFL; GF128_SHIFT_BIT0]]);;

(* Single-bit commutativity for bounded-bits y *)
let GF128_MUL_SINGLE_BIT_COMM_GEN = prove
 (`!n m (y:128 word). m < 128 /\ (!k. n <= k ==> ~bit k y) ==>
    gf128_mul (word_of_bits{m} : 128 word) y = gf128_mul y (word_of_bits{m})`,
  INDUCT_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `y = word 0 : 128 word` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; DIMINDEX_128] THEN
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[LE_0];
    REWRITE_TAC[GF128_MUL_LZERO; GF128_MUL_RZERO]];
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `bit n (y:128 word)` THENL
   [SUBGOAL_THEN `n < 128` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
     MP_TAC(ISPECL [`y:128 word`; `n:num`] BIT_TRIVIAL) THEN
     ASM_REWRITE_TAC[DIMINDEX_128]; ALL_TAC] THEN
    SUBGOAL_THEN
      `gf128_mul (word_of_bits{m} : 128 word) y =
       word_xor (gf128_mul (word_of_bits{m} : 128 word)
                            (word_xor y (word_of_bits{n} : 128 word)))
                (gf128_mul (word_of_bits{m} : 128 word) (word_of_bits{n}))`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM GF128_MUL_RDISTRIB] THEN AP_TERM_TAC THEN
     ONCE_REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
     REWRITE_TAC[WORD_XOR_REFL; WORD_XOR_0]; ALL_TAC] THEN
    SUBGOAL_THEN
      `gf128_mul y (word_of_bits{m} : 128 word) =
       word_xor (gf128_mul (word_xor y (word_of_bits{n} : 128 word))
                            (word_of_bits{m} : 128 word))
                (gf128_mul (word_of_bits{n} : 128 word) (word_of_bits{m}))`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM GF128_MUL_LDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     ONCE_REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
     REWRITE_TAC[WORD_XOR_REFL; WORD_XOR_0]; ALL_TAC] THEN
    MK_COMB_TAC THENL
    [AP_TERM_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`;
       `word_xor y (word_of_bits{n} : 128 word)`]) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `k < 128` THENL
      [REWRITE_TAC[BIT_WORD_XOR; DIMINDEX_128] THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
       ASM_CASES_TAC `k:num = n` THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `!k. SUC n <= k ==> ~bit k (y:128 word)` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
       MP_TAC(ISPECL [`word_xor y (word_of_bits{n} : 128 word)`; `k:num`]
         BIT_TRIVIAL) THEN
       REWRITE_TAC[DIMINDEX_128] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
      SIMP_TAC[]];
     MATCH_MP_TAC GF128_MUL_SINGLE_BIT_COMM THEN ASM_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `y:128 word`]) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `k:num = n` THENL
     [ASM_REWRITE_TAC[];
      UNDISCH_TAC `!k. SUC n <= k ==> ~bit k (y:128 word)` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
     SIMP_TAC[]]]]);;

(* Single-bit commutativity for all y *)
let GF128_MUL_SINGLE_BIT_COMM_ALL = prove
 (`!m (y:128 word). m < 128 ==>
    gf128_mul (word_of_bits{m} : 128 word) y = gf128_mul y (word_of_bits{m})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`128`; `m:num`; `y:128 word`] GF128_MUL_SINGLE_BIT_COMM_GEN) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`y:128 word`; `k:num`] BIT_TRIVIAL) THEN
   REWRITE_TAC[DIMINDEX_128] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
   SIMP_TAC[]]);;

(* Bounded-bits commutativity of gf128_mul *)
let GF128_MUL_COMM_LEMMA = prove
 (`!m (x:128 word) (y:128 word).
    (!k. m <= k ==> ~bit k x) ==> gf128_mul x y = gf128_mul y x`,
  INDUCT_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `x = word 0 : 128 word` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; DIMINDEX_128] THEN
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[LE_0];
    REWRITE_TAC[GF128_MUL_LZERO; GF128_MUL_RZERO]];
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `bit m (x:128 word)` THENL
   [SUBGOAL_THEN `m < 128` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
     MP_TAC(ISPECL [`x:128 word`; `m:num`] BIT_TRIVIAL) THEN
     ASM_REWRITE_TAC[DIMINDEX_128]; ALL_TAC] THEN
    SUBGOAL_THEN
      `gf128_mul x y = word_xor
        (gf128_mul (word_xor x (word_of_bits{m} : 128 word)) y)
        (gf128_mul (word_of_bits{m} : 128 word) y) : 128 word`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM GF128_MUL_LDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     ONCE_REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
     REWRITE_TAC[WORD_XOR_REFL; WORD_XOR_0]; ALL_TAC] THEN
    SUBGOAL_THEN
      `gf128_mul y x = word_xor
        (gf128_mul y (word_xor x (word_of_bits{m} : 128 word)))
        (gf128_mul y (word_of_bits{m} : 128 word)) : 128 word`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM GF128_MUL_RDISTRIB] THEN AP_TERM_TAC THEN
     ONCE_REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
     REWRITE_TAC[WORD_XOR_REFL; WORD_XOR_0]; ALL_TAC] THEN
    MK_COMB_TAC THENL
    [AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `k < 128` THENL
     [REWRITE_TAC[BIT_WORD_XOR; DIMINDEX_128] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
      ASM_CASES_TAC `k:num = m` THENL
      [ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `!k. SUC m <= k ==> ~bit k (x:128 word)` THEN
       DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
      MP_TAC(ISPECL [`word_xor x (word_of_bits{m} : 128 word)`; `k:num`]
        BIT_TRIVIAL) THEN
      REWRITE_TAC[DIMINDEX_128] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
     MP_TAC(SPECL [`m:num`; `y:128 word`] GF128_MUL_SINGLE_BIT_COMM_ALL) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k:num = m` THENL
    [ASM_REWRITE_TAC[];
     UNDISCH_TAC `!k. SUC m <= k ==> ~bit k (x:128 word)` THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;

(* Commutativity of gf128_mul *)
let GF128_MUL_COMM = prove
 (`!x y:128 word. gf128_mul x y = gf128_mul y x`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`128`; `x:128 word`; `y:128 word`] GF128_MUL_COMM_LEMMA) THEN
  ANTS_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`x:128 word`; `k:num`] BIT_TRIVIAL) THEN
   REWRITE_TAC[DIMINDEX_128] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
   SIMP_TAC[]]);;

(* ---------------------------------------------------------------------- *)
(* gf128_shift commutes with gf128_mul: key to associativity             *)
(* ---------------------------------------------------------------------- *)

let GF128_SHIFT_0 = prove
 (`gf128_shift (word 0 : 128 word) = word 0`,
  REWRITE_TAC[gf128_shift; BIT_WORD_0] THEN CONV_TAC WORD_REDUCE_CONV);;

let GF128_MUL_LOOP_SHIFT = prove
 (`!n (x:128 word) (z:128 word) (v:128 word).
   gf128_mul_loop x n (gf128_shift z) (gf128_shift v) =
   gf128_shift (gf128_mul_loop x n z v)`,
  INDUCT_TAC THENL
  [REWRITE_TAC[gf128_mul_loop];
   REPEAT GEN_TAC THEN REWRITE_TAC[gf128_mul_loop] THEN
   REWRITE_TAC[GSYM gf128_shift] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[GSYM GF128_SHIFT_LINEAR] THEN
   ASM_REWRITE_TAC[]]);;

let GF128_MUL_SHIFT_R = prove
 (`!x (y:128 word). gf128_mul x (gf128_shift y) =
   gf128_shift (gf128_mul x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gf128_mul] THEN
  MP_TAC(SPECL [`128`; `x:128 word`; `word 0:128 word`; `y:128 word`]
    GF128_MUL_LOOP_SHIFT) THEN
  SUBGOAL_THEN `gf128_shift (word 0:128 word) = word 0`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[gf128_shift; BIT_WORD_0] THEN CONV_TAC WORD_REDUCE_CONV);;

let GF128_MUL_SHIFT_L = prove
 (`!x (y:128 word). gf128_mul (gf128_shift x) y =
   gf128_shift (gf128_mul x y)`,
  ONCE_REWRITE_TAC[GF128_MUL_COMM] THEN REWRITE_TAC[GF128_MUL_SHIFT_R]);;

let GF128_MUL_SHIFT_ITER_R = prove
 (`!n x (y:128 word). gf128_mul x (gf128_shift_iter n y) =
   gf128_shift_iter n (gf128_mul x y)`,
  INDUCT_TAC THENL
  [REWRITE_TAC[gf128_shift_iter];
   ASM_REWRITE_TAC[gf128_shift_iter; GF128_MUL_SHIFT_R]]);;

let GF128_SHIFT_ITER_LINEAR = prove
 (`!n (a:128 word) (b:128 word).
   gf128_shift_iter n (word_xor a b) =
   word_xor (gf128_shift_iter n a) (gf128_shift_iter n b)`,
  INDUCT_TAC THENL
  [REWRITE_TAC[gf128_shift_iter];
   ASM_REWRITE_TAC[gf128_shift_iter; GF128_SHIFT_LINEAR]]);;

let GF128_SHIFT_ITER_0 = prove
 (`!n. gf128_shift_iter n (word 0 : 128 word) = word 0`,
  INDUCT_TAC THENL
  [REWRITE_TAC[gf128_shift_iter];
   REWRITE_TAC[gf128_shift_iter] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[gf128_shift; BIT_WORD_0] THEN CONV_TAC WORD_REDUCE_CONV]);;

(* ---------------------------------------------------------------------- *)
(* Associativity of gf128_mul                                             *)
(* ---------------------------------------------------------------------- *)

(* Single-bit associativity: gf128_mul x (gf128_mul (word_of_bits{m}) z)  *)
(* = gf128_mul (gf128_mul x (word_of_bits{m})) z                         *)
let GF128_MUL_ASSOC_SINGLE_BIT = prove
 (`!m x (z:128 word). m < 128 ==>
   gf128_mul x (gf128_mul (word_of_bits{m}) z) =
   gf128_mul (gf128_mul x (word_of_bits{m})) z`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GF128_MUL_SINGLE_BIT_L; GF128_MUL_SHIFT_ITER_R] THEN
  SUBGOAL_THEN `gf128_mul x (word_of_bits{m} : 128 word) =
    gf128_shift_iter (127 - m) x` SUBST1_TAC THENL
  [ONCE_REWRITE_TAC[GF128_MUL_COMM] THEN ASM_SIMP_TAC[GF128_MUL_SINGLE_BIT_L];
   ONCE_REWRITE_TAC[GF128_MUL_COMM] THEN
   REWRITE_TAC[GF128_MUL_SHIFT_ITER_R]]);;

(* Bounded-bits associativity helper *)
let GF128_MUL_ASSOC_LEMMA = prove
 (`!n x (y:128 word) z. (!k. n <= k ==> ~bit k y) ==>
   gf128_mul x (gf128_mul y z) = gf128_mul (gf128_mul x y) z`,
  INDUCT_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `y = word 0 : 128 word` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; DIMINDEX_128] THEN
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[LE_0];
    REWRITE_TAC[GF128_MUL_LZERO; GF128_MUL_RZERO; GF128_MUL_LZERO]];
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `bit n (y:128 word)` THENL
   [SUBGOAL_THEN `n < 128` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
     MP_TAC(ISPECL [`y:128 word`; `n:num`] BIT_TRIVIAL) THEN
     ASM_REWRITE_TAC[DIMINDEX_128]; ALL_TAC] THEN
    SUBGOAL_THEN
      `gf128_mul x (gf128_mul y z) =
       word_xor (gf128_mul x (gf128_mul (word_xor y (word_of_bits{n} : 128 word)) z))
                (gf128_mul x (gf128_mul (word_of_bits{n} : 128 word) z)) : 128 word`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM GF128_MUL_LDISTRIB; GSYM GF128_MUL_RDISTRIB] THEN
     AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     ONCE_REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
     REWRITE_TAC[WORD_XOR_REFL; WORD_XOR_0]; ALL_TAC] THEN
    SUBGOAL_THEN
      `gf128_mul (gf128_mul x y) z =
       word_xor (gf128_mul (gf128_mul x (word_xor y (word_of_bits{n} : 128 word))) z)
                (gf128_mul (gf128_mul x (word_of_bits{n} : 128 word)) z) : 128 word`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM GF128_MUL_RDISTRIB; GSYM GF128_MUL_LDISTRIB] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     ONCE_REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
     REWRITE_TAC[WORD_XOR_REFL; WORD_XOR_0]; ALL_TAC] THEN
    MK_COMB_TAC THENL
    [AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     ASM_CASES_TAC `k < 128` THENL
     [REWRITE_TAC[BIT_WORD_XOR; DIMINDEX_128] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; NOT_IN_EMPTY; DIMINDEX_128] THEN
      ASM_CASES_TAC `k:num = n` THENL
      [ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `!k. SUC n <= k ==> ~bit k (y:128 word)` THEN
       DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
      MP_TAC(ISPECL [`word_xor y (word_of_bits{n} : 128 word)`; `k:num`]
        BIT_TRIVIAL) THEN
      REWRITE_TAC[DIMINDEX_128] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
     MP_TAC(SPECL [`n:num`; `x:128 word`; `z:128 word`] GF128_MUL_ASSOC_SINGLE_BIT) THEN
     ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k:num = n` THENL
    [ASM_REWRITE_TAC[];
     UNDISCH_TAC `!k. SUC n <= k ==> ~bit k (y:128 word)` THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;

(* Full associativity of gf128_mul *)
let GF128_MUL_ASSOC = prove
 (`!x y z:128 word. gf128_mul x (gf128_mul y z) = gf128_mul (gf128_mul x y) z`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`128`; `x:128 word`; `y:128 word`; `z:128 word`]
    GF128_MUL_ASSOC_LEMMA) THEN
  ANTS_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`y:128 word`; `k:num`] BIT_TRIVIAL) THEN
   REWRITE_TAC[DIMINDEX_128] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
   SIMP_TAC[]]);;

(* ---------------------------------------------------------------------- *)
(* word_subword distributes over XOR (polymorphic)                        *)
(* ---------------------------------------------------------------------- *)

let WORD_SUBWORD_XOR = prove
 (`!(p:N word) (q:N word) pos len. word_subword (word_xor p q) (pos,len) : M word =
    word_xor (word_subword p (pos,len)) (word_subword q (pos,len))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR; BIT_WORD_SUBWORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < MIN len (dimindex(:M))` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `pos + i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dimindex(:N) <= pos + i` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~bit (pos + i) (p:N word)` ASSUME_TAC THENL
  [ASM_MESON_TAC[BIT_TRIVIAL; NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `~bit (pos + i) (q:N word)` ASSUME_TAC THENL
  [ASM_MESON_TAC[BIT_TRIVIAL; NOT_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* join128 with XOR in high half and zero in low half *)
let JOIN128_XOR_ZERO = prove
 (`!a b:64 word. join128 (word_xor a b) (word 0 : 64 word) =
    word_xor (join128 a (word 0)) (join128 b (word 0))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:64 word`; `word 0:64 word`;
                  `b:64 word`; `word 0:64 word`] (GSYM JOIN128_XOR)) THEN
  REWRITE_TAC[WORD_XOR_REFL]);;

(* ---------------------------------------------------------------------- *)
(* gf128_reduce is GF(2)-linear (distributes over XOR)                    *)
(* ---------------------------------------------------------------------- *)

let GF128_REDUCE_LINEAR = prove
 (`!p q:256 word. gf128_reduce (word_xor p q) =
    word_xor (gf128_reduce p) (gf128_reduce q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gf128_reduce; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR; LO64_XOR; HI64_XOR; CLMUL_LDISTRIB;
              SWAP_HALVES_XOR] THEN
  CONV_TAC WORD_RULE);;

let GF128_REDUCE_0 = prove
 (`gf128_reduce (word 0 : 256 word) = (word 0 : 128 word)`,
  MP_TAC(ISPECL [`word 0:256 word`; `word 0:256 word`] GF128_REDUCE_LINEAR) THEN
  REWRITE_TAC[WORD_XOR_REFL]);;

(* ---------------------------------------------------------------------- *)
(* Bit reversal properties (word_reversefields 1 = full bit reversal)     *)
(* ---------------------------------------------------------------------- *)

let WORD_REVERSEFIELDS_1_XOR = prove
 (`!x y:128 word. word_reversefields 1 (word_xor x y) : 128 word =
    word_xor (word_reversefields 1 x) (word_reversefields 1 y)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let WORD_REVERSEFIELDS_1_ZERO = prove
 (`word_reversefields 1 (word 0 : 128 word) : 128 word = word 0`,
  BITBLAST_TAC);;

let WORD_REVERSEFIELDS_1_INVOLUTION = prove
 (`!x:128 word. word_reversefields 1 (word_reversefields 1 x) = x`,
  GEN_TAC THEN BITBLAST_TAC);;

(* ====================================================================== *)
(* WARNING: gf128_reduce above does NOT correctly compute polynomial      *)
(* reduction mod P*. The assembly's two-phase PMULL reduction is          *)
(* interleaved with the Karatsuba decomposition and cannot be separated   *)
(* into a standalone function on a contiguous 256-bit word. The theorems  *)
(* GF128_REDUCE_LINEAR and GF128_REDUCE_0 are valid but only describe    *)
(* structural properties of the (incorrect) definition. For the correct   *)
(* standard-representation multiplication, use gf128_mul_std below.       *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* gf128_mul_std: GF(2^128) multiplication in standard polynomial         *)
(* representation, defined via gf128_mul and bit reversal.                 *)
(*                                                                        *)
(* In the standard representation, bit i of a word represents x^i.        *)
(* In the NIST representation (used by gf128_mul), bit i represents       *)
(* x^{127-i} (MSB-first). Bit reversal (word_reversefields 1) converts   *)
(* between the two.                                                       *)
(* ---------------------------------------------------------------------- *)

let gf128_mul_std = new_definition
  `gf128_mul_std (x:128 word) (y:128 word) : 128 word =
    word_reversefields 1
      (gf128_mul (word_reversefields 1 x) (word_reversefields 1 y))`;;

(* ---------------------------------------------------------------------- *)
(* Bridge theorem: connecting gf128_mul to gf128_mul_std                   *)
(* ---------------------------------------------------------------------- *)

let GF128_MUL_BRIDGE = prove
 (`!x y:128 word. gf128_mul x y =
    word_reversefields 1
      (gf128_mul_std (word_reversefields 1 x) (word_reversefields 1 y))`,
  REWRITE_TAC[gf128_mul_std; WORD_REVERSEFIELDS_1_INVOLUTION]);;

(* ---------------------------------------------------------------------- *)
(* Identity element for gf128_mul                                          *)
(* In NIST representation, the identity is word_of_bits{127} (MSB set).   *)
(* ---------------------------------------------------------------------- *)

let GF128_MUL_1 = prove
 (`!y:128 word. gf128_mul (word_of_bits {127} : 128 word) y = y`,
  GEN_TAC THEN
  REWRITE_TAC[GF128_MUL_SINGLE_BIT_L] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[gf128_shift_iter]);;

(* ---------------------------------------------------------------------- *)
(* Algebraic properties of gf128_mul_std                                   *)
(* ---------------------------------------------------------------------- *)

let GF128_MUL_STD_COMM = prove
 (`!x y:128 word. gf128_mul_std x y = gf128_mul_std y x`,
  REWRITE_TAC[gf128_mul_std; GF128_MUL_COMM]);;

let GF128_MUL_STD_ASSOC = prove
 (`!x y z:128 word.
    gf128_mul_std x (gf128_mul_std y z) =
    gf128_mul_std (gf128_mul_std x y) z`,
  REWRITE_TAC[gf128_mul_std; WORD_REVERSEFIELDS_1_INVOLUTION;
              GF128_MUL_ASSOC]);;

let GF128_MUL_STD_LDISTRIB = prove
 (`!a b c:128 word. gf128_mul_std (word_xor a b) c =
    word_xor (gf128_mul_std a c) (gf128_mul_std b c)`,
  REWRITE_TAC[gf128_mul_std; WORD_REVERSEFIELDS_1_XOR; GF128_MUL_LDISTRIB]);;

let GF128_MUL_STD_RDISTRIB = prove
 (`!a b c:128 word. gf128_mul_std a (word_xor b c) =
    word_xor (gf128_mul_std a b) (gf128_mul_std a c)`,
  REWRITE_TAC[gf128_mul_std; WORD_REVERSEFIELDS_1_XOR; GF128_MUL_RDISTRIB]);;

let GF128_MUL_STD_LZERO = prove
 (`!y:128 word. gf128_mul_std (word 0) y = word 0`,
  REWRITE_TAC[gf128_mul_std; WORD_REVERSEFIELDS_1_ZERO; GF128_MUL_LZERO]);;

let GF128_MUL_STD_RZERO = prove
 (`!x:128 word. gf128_mul_std x (word 0) = word 0`,
  REWRITE_TAC[gf128_mul_std; WORD_REVERSEFIELDS_1_ZERO; GF128_MUL_RZERO]);;

let GF128_MUL_STD_1 = prove
 (`!y:128 word. gf128_mul_std (word_of_bits {0} : 128 word) y = y`,
  GEN_TAC THEN REWRITE_TAC[gf128_mul_std] THEN
  SUBGOAL_THEN `word_reversefields 1 (word_of_bits {0} : 128 word) =
                (word_of_bits {127} : 128 word)` SUBST1_TAC THENL
  [BITBLAST_TAC; ALL_TAC] THEN
  REWRITE_TAC[GF128_MUL_1; WORD_REVERSEFIELDS_1_INVOLUTION]);;

(* ---------------------------------------------------------------------- *)
(* Bilinearity of clmul128_schoolbook                                      *)
(* ---------------------------------------------------------------------- *)

let CLMUL128_SCHOOLBOOK_LDISTRIB = prove
 (`!a b c:128 word. clmul128_schoolbook (word_xor a b) c =
    word_xor (clmul128_schoolbook a c) (clmul128_schoolbook b c)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clmul128_schoolbook; LET_DEF; LET_END_DEF;
              LO64_XOR; HI64_XOR; CLMUL_LDISTRIB; CLMUL_RDISTRIB;
              WORD_ZX_XOR; WORD_SHL_XOR] THEN
  CONV_TAC WORD_RULE);;

let CLMUL128_SCHOOLBOOK_RDISTRIB = prove
 (`!a b c:128 word. clmul128_schoolbook a (word_xor b c) =
    word_xor (clmul128_schoolbook a b) (clmul128_schoolbook a c)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clmul128_schoolbook; LET_DEF; LET_END_DEF;
              LO64_XOR; HI64_XOR; CLMUL_LDISTRIB; CLMUL_RDISTRIB;
              WORD_ZX_XOR; WORD_SHL_XOR] THEN
  CONV_TAC WORD_RULE);;

let CLMUL128_SCHOOLBOOK_LZERO = prove
 (`!y:128 word. clmul128_schoolbook (word 0) y = word 0`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`word 0:128 word`; `word 0:128 word`; `y:128 word`]
    CLMUL128_SCHOOLBOOK_LDISTRIB) THEN
  REWRITE_TAC[WORD_XOR_REFL]);;

let CLMUL128_SCHOOLBOOK_RZERO = prove
 (`!x:128 word. clmul128_schoolbook x (word 0) = word 0`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`x:128 word`; `word 0:128 word`; `word 0:128 word`]
    CLMUL128_SCHOOLBOOK_RDISTRIB) THEN
  REWRITE_TAC[WORD_XOR_REFL]);;

(* ====================================================================== *)
(* INFRASTRUCTURE NEEDED (documented for future work)                     *)
(* ====================================================================== *)
(*
To complete the proof, the following must be added to s2n-bignum:

1. PMULL instruction semantics (instruction.ml):
   arm_PMULL Rd Rn Rm =
     Rd := clmul (lo64 (read Rn s)) (lo64 (read Rm s))

   arm_PMULL2 Rd Rn Rm =
     Rd := clmul (hi64 (read Rn s)) (hi64 (read Rm s))

2. LD1 vector load semantics (instruction.ml):
   arm_LD1_single Rt Rn =
     Rt := read (memory :> bytes128 (read Rn s)) s

   arm_LD1_pair Rt Rt2 Rn =
     Rt := read (memory :> bytes128 (read Rn s)) s ,,
     Rt2 := read (memory :> bytes128 (word_add (read Rn s) (word 16))) s

   arm_LD1_post Rt Rn imm =
     arm_LD1_single Rt Rn ,, Rn := word_add (read Rn s) (word imm)

3. ST1 vector store semantics (instruction.ml):
   arm_ST1_single Rt Rn =
     memory :> bytes128 (read Rn s) := read Rt s

4. Instruction decoding for PMULL/LD1/ST1 (decode.ml):
   Add bit patterns for these instruction encodings.

5. Once these are added, the proof follows the standard pattern:
   - ARM_MK_EXEC_RULE on the machine code
   - ENSURES_SEQUENCE_TAC to chain instruction blocks
   - ARM_STEPS_TAC to simulate each instruction
   - KARATSUBA_REDUCE_EQ_GF128_MUL to connect to spec
*)
