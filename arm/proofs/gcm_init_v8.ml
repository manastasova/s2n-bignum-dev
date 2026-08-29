(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* GCM_INIT_V8: expand the GHASH hash key H into the PMULL/v8 power table.    *)
(* Correctness against the POLYVAL/GHASH algebraic spec in                    *)
(* common/polyval_ghash.ml.  X0 = Htable (192 bytes written), X1 = H.         *)
(*                                                                            *)
(* Layout: the routine is branch-free, so the proof is four straight-line      *)
(* blocks tiling PC 0x0..0x208, composed by ARM_BIGSTEP_TAC into              *)
(* GCM_INIT_V8_CORRECT:                                                       *)
(*                                                                            *)
(*   0x0   -> 0x80   the fused twist + H^2                    (32 steps)       *)
(*   0x80  -> 0x104  H^3, H^4 and the Htable[0..1] store      (33 steps)       *)
(*   0x104 -> 0x1e0  H^5, H^6, H^7, H^8 + Htable[2..5]        (55 steps)       *)
(*   0x1e0 -> 0x208  the closing packs and Htable[6..11]      (10 steps)       *)
(*                                                                            *)
(* The .S is emitted in ASAP order over its RAW dependence graph with the SIMD *)
(* registers allocated by linear scan over that order (see the .S header), so  *)
(* the four power chains INTERLEAVE and the block boundaries are the three PCs *)
(* at which every live value is a named power or byteswap.  That is the only   *)
(* thing the tiling depends on -- the algebra is unchanged, so ALL of it still *)
(* lives once in the two toolkit sections below and each block's script is     *)
(* still just steps + SPEC_UNFOLD_TAC + one PRODUCT_TAC/SQUARE_TAC per product *)
(* + LANE_CLOSE_TAC.                                                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/polyval_ghash.ml";;
needs "common/karatsuba_pmul.ml";;      (* PMUL_SCHOOLBOOK; ~0.5s on top of the above *)

(**** print_literal_from_elf "arm/gcm/gcm_init_v8.o";;
 ****)

let gcm_init_v8_mc = define_assert_from_elf
 "gcm_init_v8_mc" "arm/gcm/gcm_init_v8.o"
[
  0x4c407c20;       (* arm_LDR Q0 X1 No_Offset *)
  0xf9400423;       (* arm_LDR X3 X1 (Immediate_Offset (word 8)) *)
  0x4f07e421;       (* arm_MOVI Q1 (word 16276538888567251425) *)
  0x4f07e7e2;       (* arm_MOVI Q2 (word 18446744073709551615) *)
  0x4f00e403;       (* arm_MOVI Q3 (word 0) *)
  0x4f795424;       (* arm_SHL_VEC Q4 Q1 57 64 128 *)
  0x6f410441;       (* arm_USHR_VEC Q1 Q2 63 64 128 *)
  0xd37ff863;       (* arm_LSL X3 X3 1 *)
  0x6e044022;       (* arm_EXT Q2 Q1 Q4 64 *)
  0x9e670061;       (* arm_FMOV_ItoF Q1 X3 0 *)
  0x6f410405;       (* arm_USHR_VEC Q5 Q0 63 64 128 *)
  0x4f410406;       (* arm_SSHR_VEC Q6 Q0 63 64 128 *)
  0x4f415407;       (* arm_SHL_VEC Q7 Q0 1 64 128 *)
  0x0ee1e020;       (* arm_PMULL_VEC Q0 Q1 Q1 64 *)
  0x4ec628c1;       (* arm_TRN1 Q1 Q6 Q6 64 128 *)
  0x0ee7e0e6;       (* arm_PMULL_VEC Q6 Q7 Q7 64 *)
  0x4ee5e0b0;       (* arm_PMULL2_VEC Q16 Q5 Q5 64 *)
  0x6e0540b1;       (* arm_EXT Q17 Q5 Q5 64 *)
  0x4ee4e005;       (* arm_PMULL2_VEC Q5 Q0 Q4 64 *)
  0x0ee4e012;       (* arm_PMULL_VEC Q18 Q0 Q4 64 *)
  0x4e211c53;       (* arm_AND_VEC Q19 Q2 Q1 128 *)
  0x6e301cc1;       (* arm_EOR_VEC Q1 Q6 Q16 128 *)
  0x4eb11ce2;       (* arm_ORR_VEC Q2 Q7 Q17 128 *)
  0x6e124246;       (* arm_EXT Q6 Q18 Q18 64 *)
  0x0ee4e247;       (* arm_PMULL_VEC Q7 Q18 Q4 64 *)
  0x6e251c10;       (* arm_EOR_VEC Q16 Q0 Q5 128 *)
  0x6e331c20;       (* arm_EOR_VEC Q0 Q1 Q19 128 *)
  0x6e034261;       (* arm_EXT Q1 Q19 Q3 64 *)
  0x6e271cc3;       (* arm_EOR_VEC Q3 Q6 Q7 128 *)
  0x6e201e05;       (* arm_EOR_VEC Q5 Q16 Q0 128 *)
  0x6e211c40;       (* arm_EOR_VEC Q0 Q2 Q1 128 *)
  0x6e231ca1;       (* arm_EOR_VEC Q1 Q5 Q3 128 *)
  0x6e004002;       (* arm_EXT Q2 Q0 Q0 64 *)
  0x0ee1e023;       (* arm_PMULL_VEC Q3 Q1 Q1 64 *)
  0x4ee1e005;       (* arm_PMULL2_VEC Q5 Q0 Q1 64 *)
  0x0ee1e006;       (* arm_PMULL_VEC Q6 Q0 Q1 64 *)
  0x4ee1e027;       (* arm_PMULL2_VEC Q7 Q1 Q1 64 *)
  0x6e014030;       (* arm_EXT Q16 Q1 Q1 64 *)
  0x4ec12811;       (* arm_TRN1 Q17 Q0 Q1 64 128 *)
  0x4ec16812;       (* arm_TRN2 Q18 Q0 Q1 64 128 *)
  0x0ee1e053;       (* arm_PMULL_VEC Q19 Q2 Q1 64 *)
  0x4ee1e054;       (* arm_PMULL2_VEC Q20 Q2 Q1 64 *)
  0x0ee4e062;       (* arm_PMULL_VEC Q2 Q3 Q4 64 *)
  0x6e261cb5;       (* arm_EOR_VEC Q21 Q5 Q6 128 *)
  0x6e271c65;       (* arm_EOR_VEC Q5 Q3 Q7 128 *)
  0x4ee4e066;       (* arm_PMULL2_VEC Q6 Q3 Q4 64 *)
  0x6e321e23;       (* arm_EOR_VEC Q3 Q17 Q18 128 *)
  0x6e134267;       (* arm_EXT Q7 Q19 Q19 64 *)
  0x0ee4e271;       (* arm_PMULL_VEC Q17 Q19 Q4 64 *)
  0x6e024052;       (* arm_EXT Q18 Q2 Q2 64 *)
  0x0ee4e053;       (* arm_PMULL_VEC Q19 Q2 Q4 64 *)
  0x6e1542a2;       (* arm_EXT Q2 Q21 Q21 64 *)
  0x0ee4e2b6;       (* arm_PMULL_VEC Q22 Q21 Q4 64 *)
  0x6e261cb5;       (* arm_EOR_VEC Q21 Q5 Q6 128 *)
  0xad000c00;       (* arm_STP Q0 Q3 X0 (Immediate_Offset (iword (&0))) *)
  0x6e311ce0;       (* arm_EOR_VEC Q0 Q7 Q17 128 *)
  0x6e331e43;       (* arm_EOR_VEC Q3 Q18 Q19 128 *)
  0x6e221ec5;       (* arm_EOR_VEC Q5 Q22 Q2 128 *)
  0x6e004002;       (* arm_EXT Q2 Q0 Q0 64 *)
  0x0ee4e006;       (* arm_PMULL_VEC Q6 Q0 Q4 64 *)
  0x6e231ea0;       (* arm_EOR_VEC Q0 Q21 Q3 128 *)
  0x6e341ca3;       (* arm_EOR_VEC Q3 Q5 Q20 128 *)
  0x6e261c45;       (* arm_EOR_VEC Q5 Q2 Q6 128 *)
  0x6e004002;       (* arm_EXT Q2 Q0 Q0 64 *)
  0x6e231cb1;       (* arm_EOR_VEC Q17 Q5 Q3 128 *)
  0x0ee0e006;       (* arm_PMULL_VEC Q6 Q0 Q0 64 *)
  0x4ee0e007;       (* arm_PMULL2_VEC Q7 Q0 Q0 64 *)
  0x0ee4e0c3;       (* arm_PMULL_VEC Q3 Q6 Q4 64 *)
  0x6e271cc5;       (* arm_EOR_VEC Q5 Q6 Q7 128 *)
  0x4ee4e0c7;       (* arm_PMULL2_VEC Q7 Q6 Q4 64 *)
  0x0ef1e006;       (* arm_PMULL_VEC Q6 Q0 Q17 64 *)
  0x4ef1e052;       (* arm_PMULL2_VEC Q18 Q2 Q17 64 *)
  0x0ef1e053;       (* arm_PMULL_VEC Q19 Q2 Q17 64 *)
  0x0ef1e034;       (* arm_PMULL_VEC Q20 Q1 Q17 64 *)
  0x4ef1e215;       (* arm_PMULL2_VEC Q21 Q16 Q17 64 *)
  0x0ef1e216;       (* arm_PMULL_VEC Q22 Q16 Q17 64 *)
  0x0ef1e237;       (* arm_PMULL_VEC Q23 Q17 Q17 64 *)
  0x4ef1e238;       (* arm_PMULL2_VEC Q24 Q17 Q17 64 *)
  0x4ef1e019;       (* arm_PMULL2_VEC Q25 Q0 Q17 64 *)
  0x4ef1e03a;       (* arm_PMULL2_VEC Q26 Q1 Q17 64 *)
  0x4ec02a21;       (* arm_TRN1 Q1 Q17 Q0 64 128 *)
  0x4ec06a3b;       (* arm_TRN2 Q27 Q17 Q0 64 128 *)
  0x6e114220;       (* arm_EXT Q0 Q17 Q17 64 *)
  0x6e034071;       (* arm_EXT Q17 Q3 Q3 64 *)
  0x0ee4e07c;       (* arm_PMULL_VEC Q28 Q3 Q4 64 *)
  0x6e271ca3;       (* arm_EOR_VEC Q3 Q5 Q7 128 *)
  0x6e331e45;       (* arm_EOR_VEC Q5 Q18 Q19 128 *)
  0x0ee4e0c7;       (* arm_PMULL_VEC Q7 Q6 Q4 64 *)
  0x6e361eb2;       (* arm_EOR_VEC Q18 Q21 Q22 128 *)
  0x0ee4e293;       (* arm_PMULL_VEC Q19 Q20 Q4 64 *)
  0x6e0640d5;       (* arm_EXT Q21 Q6 Q6 64 *)
  0x6e144286;       (* arm_EXT Q6 Q20 Q20 64 *)
  0x0ee4e2f4;       (* arm_PMULL_VEC Q20 Q23 Q4 64 *)
  0x6e381ef6;       (* arm_EOR_VEC Q22 Q23 Q24 128 *)
  0x4ee4e2f8;       (* arm_PMULL2_VEC Q24 Q23 Q4 64 *)
  0x6e3b1c37;       (* arm_EOR_VEC Q23 Q1 Q27 128 *)
  0xad010010;       (* arm_STP Q16 Q0 X0 (Immediate_Offset (iword (&32))) *)
  0x6e3c1e20;       (* arm_EOR_VEC Q0 Q17 Q28 128 *)
  0x6e271ca1;       (* arm_EOR_VEC Q1 Q5 Q7 128 *)
  0x6e331e45;       (* arm_EOR_VEC Q5 Q18 Q19 128 *)
  0x6e144287;       (* arm_EXT Q7 Q20 Q20 64 *)
  0x0ee4e290;       (* arm_PMULL_VEC Q16 Q20 Q4 64 *)
  0x6e381ed1;       (* arm_EOR_VEC Q17 Q22 Q24 128 *)
  0xad020817;       (* arm_STP Q23 Q2 X0 (Immediate_Offset (iword (&64))) *)
  0x6e201c62;       (* arm_EOR_VEC Q2 Q3 Q0 128 *)
  0x6e351c20;       (* arm_EOR_VEC Q0 Q1 Q21 128 *)
  0x6e261ca1;       (* arm_EOR_VEC Q1 Q5 Q6 128 *)
  0x6e301ce3;       (* arm_EOR_VEC Q3 Q7 Q16 128 *)
  0x6e024045;       (* arm_EXT Q5 Q2 Q2 64 *)
  0x6e004006;       (* arm_EXT Q6 Q0 Q0 64 *)
  0x6e014027;       (* arm_EXT Q7 Q1 Q1 64 *)
  0x0ee4e010;       (* arm_PMULL_VEC Q16 Q0 Q4 64 *)
  0x0ee4e020;       (* arm_PMULL_VEC Q0 Q1 Q4 64 *)
  0x6e231e21;       (* arm_EOR_VEC Q1 Q17 Q3 128 *)
  0x6e251c43;       (* arm_EOR_VEC Q3 Q2 Q5 128 *)
  0x6e391cc2;       (* arm_EOR_VEC Q2 Q6 Q25 128 *)
  0x6e3a1ce4;       (* arm_EOR_VEC Q4 Q7 Q26 128 *)
  0x6e014026;       (* arm_EXT Q6 Q1 Q1 64 *)
  0x6e221e07;       (* arm_EOR_VEC Q7 Q16 Q2 128 *)
  0x6e241c02;       (* arm_EOR_VEC Q2 Q0 Q4 128 *)
  0x6e0740e0;       (* arm_EXT Q0 Q7 Q7 64 *)
  0x4ec12844;       (* arm_TRN1 Q4 Q2 Q1 64 128 *)
  0x4ec16850;       (* arm_TRN2 Q16 Q2 Q1 64 128 *)
  0x6e024041;       (* arm_EXT Q1 Q2 Q2 64 *)
  0x6e201ce2;       (* arm_EOR_VEC Q2 Q7 Q0 128 *)
  0x6e301c87;       (* arm_EOR_VEC Q7 Q4 Q16 128 *)
  0x6e034044;       (* arm_EXT Q4 Q2 Q3 64 *)
  0xad031c01;       (* arm_STP Q1 Q7 X0 (Immediate_Offset (iword (&96))) *)
  0xad040006;       (* arm_STP Q6 Q0 X0 (Immediate_Offset (iword (&128))) *)
  0xad051404;       (* arm_STP Q4 Q5 X0 (Immediate_Offset (iword (&160))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let GCM_INIT_V8_EXEC = ARM_MK_EXEC_RULE gcm_init_v8_mc;;

(* ========================================================================= *)
(* MACHINE CHECK for the human-approved htable_mem mid-slot orientation fix.  *)
(*                                                                            *)
(* The four packed-mid slots of `htable_mem` (common/polyval_ghash.ml) were   *)
(* corrected 2026-08-26 to store the LOWER power's karatsuba_mid in the LOW    *)
(* 64 bits and the HIGHER power's in the HIGH 64 bits, matching REF_MID        *)
(* (tests/ref_gcm_init.c:177-178, verified byte-for-byte vs. real assembly     *)
(* over 2000 inputs).  This lemma makes that orientation an explicit,          *)
(* machine-checked claim about each slot's LOW/HIGH lanes rather than an       *)
(* implicit reading of HOL's `word_join` argument order.                       *)
(* ========================================================================= *)

let HTABLE_MEM_MID_LANES = prove
 (`!h:int128. !ptr:int64. !s:armstate.
    htable_mem h ptr s
    ==> word_subword
          (read (memory :> bytes128 (word_add ptr (word 16))) s) (0,64):64 word =
          karatsuba_mid(h_power h 0) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 16))) s) (64,64):64 word =
          karatsuba_mid(h_power h 1) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 64))) s) (0,64):64 word =
          karatsuba_mid(h_power h 2) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 64))) s) (64,64):64 word =
          karatsuba_mid(h_power h 3) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 112))) s) (0,64):64 word =
          karatsuba_mid(h_power h 4) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 112))) s) (64,64):64 word =
          karatsuba_mid(h_power h 5) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 160))) s) (0,64):64 word =
          karatsuba_mid(h_power h 6) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 160))) s) (64,64):64 word =
          karatsuba_mid(h_power h 7)`,
  REWRITE_TAC[htable_mem] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST);;

(* Concrete-byte KAT (the check that would have caught the original error):   *)
(* at the fixed "ByteSwap" hash key H_mem = 0x0807..0102..08 (from            *)
(* tests/ref_gcm_init.c gcm_init_v8_kats[5], whose expected Htable bytes were  *)
(* produced by the verbatim AWS-LC C reference and verified vs. real assembly  *)
(* over 2000 inputs), the spec's first three slot expressions evaluate to      *)
(* exactly the C reference numerals.  The internal key is                      *)
(* ghash_twist(byteswap128 H_mem) (the half-swap convention).  This covers     *)
(* BOTH layout patterns: byteswap128 (slots 0,2) and the fixed packed-mid      *)
(* orientation word_join(kmid higher)(kmid lower) (slot 1), so a lower/higher  *)
(* swap in either would fail this proof.  Numerals below decompose as          *)
(* out[2i+1]*2^64 + out[2i], out[] = ref_gcm_init_v8(H_mem):                    *)
(*   slot0 = byteswap128(H^1),  slot1 = pack(kmid H^2, kmid H^1),  slot2 = bsw(H^2). *)
let HTABLE_MEM_KAT_FIRST3 = prove
 (`byteswap128
     (h_power
       (ghash_twist(byteswap128 (word 0x08070605040302010102030405060708:int128))) 0) =
     word 21340584272258163075941918885976739344 /\
   word_join
     (karatsuba_mid
       (h_power
         (ghash_twist(byteswap128 (word 0x08070605040302010102030405060708:int128))) 1)
       :64 word)
     (karatsuba_mid
       (h_power
         (ghash_twist(byteswap128 (word 0x08070605040302010102030405060708:int128))) 0)
       :64 word):128 word =
     word 180621838512046301753057854212163635730 /\
   byteswap128
     (h_power
       (ghash_twist(byteswap128 (word 0x08070605040302010102030405060708:int128))) 1) =
     word 181047608966400424755469230121728647223`,
  CONV_TAC(REWRITE_CONV[num_CONV `1`; h_power] THENC
    REWRITE_CONV[polyval_dot; polyval_reduce_prop3; byteswap128; karatsuba_mid;
                 ghash_twist; POLYVAL_TWIST_CONST] THENC
    TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV WORD_RED_CONV THENC WORD_REDUCE_CONV));;

(* ========================================================================= *)
(* SPEC-SIDE ALGEBRA: nested `polyval_dot` operands  <->  `h_power`.          *)
(*                                                                            *)
(* The routine builds its powers by an addition chain of `polyval_dot`s; the  *)
(* spec (`htable_mem`, common/polyval_ghash.ml) names them `h_power h k`.     *)
(* These four lemmas bridge the two, so every block below is STATED in the    *)
(* spec's own `h_power` vocabulary and only unfolds to operand form inside    *)
(* its own proof.                                                            *)
(*                                                                            *)
(*   POLYVAL_DOT_SYM   : dot is commutative (word equality, via WORD_PMUL_SYM)*)
(*   DOT_TO_PROD_L     : poly(dot(dot a b) c) * x^256 == (poly a * poly b)*   *)
(*                       poly c  (mod Q)  -- the double-reduction congruence  *)
(*   POLYVAL_DOT_ASSOC : dot is associative (word equality; both sides cancel *)
(*                       x^256 to the same poly a*b*c mod the irreducible Q)  *)
(*   HPOWER_OPERANDS   : h_power h 0..7 as the exact operand nests the blocks *)
(*                       compute (the DEPTH-3 addition chain: H^7 = H^3.H^4,  *)
(*                       H^8 = H^4.H^4, so the last two blocks are            *)
(*                       independent).  Since every factor is the same h, any *)
(*                       parenthesization right-normalizes to the identical   *)
(*                       right-comb under POLYVAL_DOT_ASSOC, so no            *)
(*                       commutativity is needed for these eight identities.  *)
(* ========================================================================= *)

let POLYVAL_DOT_SYM = prove
 (`!a b:128 word. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC WORD_PMUL_SYM);;

(* poly(dot(dot a b) c) * x^256 == (poly a * poly b) * poly c   (mod Q) *)
let DOT_TO_PROD_L = prove
 (`!a b c:128 word.
    (ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot a b) c))
       (ring_pow bool_poly (poly_var bool_ring one) 256) ==
     ring_mul bool_poly (ring_mul bool_poly (poly_of_word a) (poly_of_word b))
       (poly_of_word c)) mod_polyval`,
  REPEAT GEN_TAC THEN SUBST1_TAC(ARITH_RULE `256 = 128 + 128`) THEN
  SIMP_TAC[RING_POW_ADD; POLY_VAR_BOOL_POLY] THEN
  SIMP_TAC[RING_MUL_ASSOC; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC `ring_mul bool_poly (ring_mul bool_poly (poly_of_word (polyval_dot a b)) (poly_of_word (c:128 word))) (ring_pow bool_poly (poly_var bool_ring one) 128)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOD_POLYVAL_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[POLYVAL_DOT_CORRECT]; SIMP_TAC[MOD_POLYVAL_REFL; POLY_VARPOW_BOOL_POLY]];
    MP_TAC(ISPECL[`poly_of_word (polyval_dot a b)`; `poly_of_word (c:128 word)`; `ring_pow bool_poly (poly_var bool_ring one) 128`] BOOL_POLY_MUL_COMM23) THEN
    ANTS_TAC THENL [SIMP_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC MOD_POLYVAL_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[POLYVAL_DOT_CORRECT]; SIMP_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD]]]);;

let POLYVAL_DOT_ASSOC = prove
 (`!a b c:128 word. polyval_dot (polyval_dot a b) c = polyval_dot a (polyval_dot b c)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(ISPECL[`a:128 word`;`polyval_dot b c:128 word`] POLYVAL_DOT_SYM) THEN
  MATCH_MP_TAC(ISPEC `256` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC `ring_mul bool_poly (ring_mul bool_poly (poly_of_word (a:128 word)) (poly_of_word (b:128 word))) (poly_of_word (c:128 word))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DOT_TO_PROD_L];
    ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
    MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC `ring_mul bool_poly (ring_mul bool_poly (poly_of_word (b:128 word)) (poly_of_word (c:128 word))) (poly_of_word (a:128 word))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[DOT_TO_PROD_L];
      MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN CONJ_TAC THENL
       [SIMP_TAC[RING_MUL; BOOL_POLY_OF_WORD];
        MESON_TAC[RING_MUL_SYM; RING_MUL_ASSOC; RING_MUL; BOOL_POLY_OF_WORD]]]]);;

let HPOWER_OPERANDS = prove
 (`!h:128 word.
    h_power h 0 = h /\
    h_power h 1 = polyval_dot h h /\
    h_power h 2 = polyval_dot h (polyval_dot h h) /\
    h_power h 3 = polyval_dot (polyval_dot h h) (polyval_dot h h) /\
    h_power h 4 = polyval_dot (polyval_dot h h) (polyval_dot h (polyval_dot h h)) /\
    h_power h 5 = polyval_dot (polyval_dot h (polyval_dot h h)) (polyval_dot h (polyval_dot h h)) /\
    h_power h 6 = polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) (polyval_dot h (polyval_dot h h)) /\
    h_power h 7 = polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) (polyval_dot (polyval_dot h h) (polyval_dot h h))`,
  GEN_TAC THEN
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power] THEN
  REWRITE_TAC[POLYVAL_DOT_ASSOC]);;

(* ========================================================================= *)
(* WORD-LEVEL TOOLKIT shared by the four power blocks (Phases 4-6).           *)
(*                                                                            *)
(* Each power block computes two powers by two interleaved carryless products, *)
(* each followed by the same two-phase Gueron reduction, and stores three      *)
(* 128-bit words.  Every register and store value in its postcondition is an   *)
(* XOR / lane rearrangement of the SAME opaque 64x64 base products, so ONE set *)
(* of rules discharges all four blocks -- genuine-mid and square products      *)
(* alike.  This is why nothing below is specialised to a power.                *)
(*                                                                            *)
(* PROOF STRATEGY (algebraic, NOT a brute bit-blast -- a symbolic word_pmul is *)
(* opaque to WORD_BLAST):                                                     *)
(*   1. symbolic-step the block and read off the raw register/store values;    *)
(*   2. unfold the spec (polyval_dot / prop3 / karatsuba_mid / byteswap128),   *)
(*      rewrite each wide product with PMUL_SB, kill a square's middle with     *)
(*      SQ_CROSS_0, normalize every lane with LANE_CONV and                     *)
(*      abbreviate the base products + the two pmul-by-w results, so the goal  *)
(*      becomes PMUL-FREE over opaque atoms;                                   *)
(*   3. close each 128-bit equality per 64-bit lane (LANE_CLOSE_TAC).          *)
(* ========================================================================= *)

(* SCHOOLBOOK decomposition of a wide (128x128 -> 256) carryless product.      *)
(* PMUL_SCHOOLBOOK states it under a chain of `let`s, which hides the equation  *)
(* from the rewriter; unfolding them exposes it as a rewrite usable at EVERY    *)
(* occurrence, so no per-operand-pair instance is needed.  Its right-hand side  *)
(* contains only 64x64 products, so it cannot re-match itself and terminates.   *)
(*                                                                            *)
(* WHY SCHOOLBOOK AND NOT KARATSUBA: the routine now forms the middle 128 bits *)
(* as the two CROSS products a_lo.b_hi (+) a_hi.b_lo rather than as Karatsuba's *)
(* (a_lo+a_hi).(b_lo+b_hi) (+) p_lo (+) p_hi.  That is one extra `pmull` but it *)
(* removes the Karatsuba "fold" from the multiply's dependency path: the cross  *)
(* products read the byteswapped operand (which the table already holds) and    *)
(* the algebraic one, so ALL FOUR products issue the cycle the previous power   *)
(* lands, and the reconstruction is one XOR instead of three.                   *)
let PMUL_SB =
  GEN_ALL(CONV_RULE(TOP_DEPTH_CONV let_CONV)(SPEC_ALL PMUL_SCHOOLBOOK));;

(* Frobenius, schoolbook form: for a SQUARE the two cross products are equal    *)
(* (word_pmul is commutative), so the whole middle 128 bits VANISH.  This is    *)
(* what lets a square skip its mid `pmull` entirely and take the product's low  *)
(* half to be p_lo and its high half to be p_hi verbatim.                       *)
let SQ_CROSS_0 = prove
 (`!(a:64 word) (b:64 word).
     word_xor (word_pmul a b:128 word) (word_pmul b a) = word 0`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(RAND_CONV(REWR_CONV WORD_PMUL_SYM))) THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* Frobenius, ADDITIVE form: a carryless SQUARE is additive, because every      *)
(* cross term appears twice (word_pmul is commutative) and so cancels.  Each     *)
(* lane of the twisted key is an XOR of 2-3 DISJOINT summands, so this is what   *)
(* lets H^2's two products be taken off the RAW key in parallel with the twist    *)
(* instead of after it (Phase 3) -- the single biggest remaining latency win.    *)
let PMUL_SQ_XOR2 = prove
 (`!(a:64 word) (b:64 word).
     word_pmul (word_xor a b) (word_xor a b):128 word =
     word_xor (word_pmul a a) (word_pmul b b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [WORD_PMUL_SYM] THEN
  CONV_TAC WORD_BITWISE_RULE);;

let PMUL_SQ_XOR3 = prove
 (`!(a:64 word) b c.
     word_pmul (word_xor (word_xor a b) c) (word_xor (word_xor a b) c):128 word =
     word_xor (word_xor (word_pmul a a) (word_pmul b b)) (word_pmul c c)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PMUL_SQ_XOR2] THEN CONV_TAC WORD_BITWISE_RULE);;

(* subword lanes of a byteswapped operand, and the mid of a byteswapped key   *)
let SUBWORD_BS_LEMMAS = prove
 (`(!h:int128. word_subword (byteswap128 h) (0,64):64 word = word_subword h (64,64)) /\
   (!h:int128. word_subword (byteswap128 h) (64,64):64 word = word_subword h (0,64)) /\
   (!h:int128. word_subword (word_join (byteswap128 h) (byteswap128 h):256 word) (64,128):128 word = h) /\
   (!h:int128. word_subword (word_xor (byteswap128 h) h) (0,64):64 word =
               word_xor (word_subword h (0,64)) (word_subword h (64,64)))`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* two 128-bit words are equal iff their two 64-bit lanes agree.              *)
let WORD_EQ_128_LANES = prove
 (`!x y:128 word.
     (word_subword x (0,64):64 word = word_subword y (0,64)) /\
     (word_subword x (64,64):64 word = word_subword y (64,64))
     ==> x = y`,
  CONV_TAC WORD_BLAST);;

(* Lane normalization: push word_subword through join / zx / shl / insert /   *)
(* xor until only the opaque atoms remain, and drop the `word 0` lanes that    *)
(* exposes -- including the ones a SQUARE's vanishing middle contributes.      *)
(* One TOP_DEPTH_CONV over the whole rule set reaches the joint fixpoint.      *)
(*                                                                            *)
(* It ALSO fully distributes every pmul-by-w over its argument's xor chain     *)
(* (WORD_PMUL_XOR, already in common/ghash.ml).  That is what makes the split  *)
(* reductions provable.  The routine exploits that `\x. word_pmul x w` is      *)
(* GF(2)-LINEAR to take Gueron's reduction apart (see the Phase 5 header):     *)
(* where the spec folds a whole xor chain through ONE pmul-by-w, the           *)
(* hardware multiplies the summands SEPARATELY and xors afterwards -- and for  *)
(* the middle term, vice versa.  So the two sides' pmul-by-w terms are no      *)
(* longer even permutations of each other and the old sort-based              *)
(* canonicalization could not equate them.  Distributing instead pushes BOTH   *)
(* sides down to the same multiset of `word_pmul <atomic lane> w`, which       *)
(* WORD_BITWISE_RULE then closes as opaque atoms -- no new abbreviations and   *)
(* no per-shape rewrite.                                                      *)
let LANE_CONV =
  let shl_lanes = map WORD_BLAST
   [`(word_subword (word_shl (word_zx (x:128 word):256 word) 64) (0,64):64 word) = (word 0:64 word)`;
    `(word_subword (word_shl (word_zx (x:128 word):256 word) 64) (64,64):64 word) = word_subword x (0,64)`;
    `(word_subword (word_shl (word_zx (x:128 word):256 word) 64) (128,64):64 word) = word_subword x (64,64)`;
    `(word_subword (word_shl (word_zx (x:128 word):256 word) 64) (192,64):64 word) = (word 0:64 word)`;
    `(word_subword (word_shl (word_zx (x:128 word):256 word) 128) (0,64):64 word) = (word 0:64 word)`;
    `(word_subword (word_shl (word_zx (x:128 word):256 word) 128) (64,64):64 word) = (word 0:64 word)`;
    `(word_subword (word_shl (word_zx (x:128 word):256 word) 128) (128,64):64 word) = word_subword x (0,64)`;
    `(word_subword (word_shl (word_zx (x:128 word):256 word) 128) (192,64):64 word) = word_subword x (64,64)`]
  and zero_lanes = map WORD_BLAST
   [`(word_subword (word 0:128 word) (0,64):64 word) = (word 0:64 word)`;
    `(word_subword (word 0:128 word) (64,64):64 word) = (word 0:64 word)`]
  and ins_lanes = map WORD_BLAST
   [`(word_insert (x:128 word) (0,64) (v:128 word) :128 word) =
     (word_join (word_subword x (64,64):64 word) (word_subword v (0,64):64 word) :128 word)`;
    `(word_insert (x:128 word) (64,64) (v:128 word) :128 word) =
     (word_join (word_subword v (0,64):64 word) (word_subword x (0,64):64 word) :128 word)`]
  and xor_0 = CONJUNCTS(WORD_BLAST
   `(!x:64 word. word_xor x (word 0) = x) /\
    (!x:64 word. word_xor (word 0) x = x)`)
  (* TRN1/TRN2 .2d (the packed-mid builders) are `word_interleave_lo/hi`, which  *)
  (* is definitionally a `word_join` of one lane from each operand -- so once    *)
  (* unfolded the existing join/subword machinery handles them with no new       *)
  (* lane reasoning at all.                                                     *)
  and trn_lanes = CONJUNCTS(prove
   (`(!x y:128 word. word_interleave_lo x y =
        word_join (word_subword y (0,64):64 word) (word_subword x (0,64):64 word)) /\
     (!x y:128 word. word_interleave_hi x y =
        word_join (word_subword y (64,64):64 word) (word_subword x (64,64):64 word))`,
    REWRITE_TAC[word_interleave_lo; word_interleave_hi] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[])) in
  TOP_DEPTH_CONV
   (FIRST_CONV (map REWR_CONV
                  (shl_lanes @ zero_lanes @ ins_lanes @ xor_0 @ trn_lanes @
                   [CONJUNCT1 WORD_PMUL_XOR] @ CONJUNCTS WORD_PMUL_0) @
                [WORD_SIMPLE_SUBWORD_CONV; REWR_CONV WORD_SUBWORD_XOR]));;

(* ------------------------------------------------------------------------- *)
(* The four tactics every block is built from.                               *)
(* ------------------------------------------------------------------------- *)

(* Set up a straight-line block goal and run its `n` instructions: expand the *)
(* ABI MAYCHANGE frame, split the nonoverlapping hypotheses into assumptions, *)
(* symbolically execute to the block's exit PC, then substitute the resulting *)
(* hardware values into the postcondition.                                    *)
let GCM_BLOCK_STEPS_TAC n =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst GCM_INIT_V8_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SOME_FLAGS; MODIFIABLE_SIMD_REGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[];;

(* Unfold the spec side down to opaque 64x64 products: polyval_dot -> the      *)
(* schoolbook reconstruction (with a square's middle killed by SQ_CROSS_0) +    *)
(* the Gueron reduction, then normalize all lanes.                             *)
let SPEC_UNFOLD_TAC =
  REWRITE_TAC[SUBWORD_BS_LEMMAS] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid; byteswap128; PMUL_SB] THEN
  REWRITE_TAC[SQ_CROSS_0] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC LANE_CONV;;

(* Close a conjunction of 128-bit equalities that are XOR rearrangements of   *)
(* the same opaque atoms, one 64-bit lane at a time.  This is bit-count-      *)
(* INDEPENDENT: WORD_BLAST on the combined ~640-bit identity times out (BDD   *)
(* blow-up superlinear in width) whereas the per-lane word-level close does   *)
(* not care about the width.                                                  *)
let LANE_CLOSE_TAC =
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC WORD_EQ_128_LANES THEN CONJ_TAC THEN
  CONV_TAC LANE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE;;

(* Name the opaque atoms of ONE of a block's two carryless products.  For       *)
(* product `k` of operands a,b:                                                 *)
(*   PL<k>, PH<k>  the two "straight" 64x64 half-products a_lo.b_lo, a_hi.b_hi,  *)
(*   C1<k>, C2<k>  the two CROSS products a_lo.b_hi, a_hi.b_lo -- present only   *)
(*                 when the operands DIFFER, since for a square SQ_CROSS_0 has   *)
(*                 already killed the whole middle,                             *)
(*   QA<k>         the first-phase Gueron pmul-by-w result.                      *)
(* Only the FIRST-phase pmul-by-w gets an atom.  Everything downstream of it is  *)
(* handled by LANE_CONV's distribution step, which pushes both the hardware's    *)
(* and the spec's pmul-by-w terms down to the same multiset of                   *)
(* `word_pmul <atomic lane> w` -- so the two sides agree on those without any    *)
(* naming, even though the routine's split reduction and the spec's nested one   *)
(* group them completely differently.  Once every product of a block has been    *)
(* through this the goal is PMUL-FREE over these atoms and LANE_CLOSE_TAC        *)
(* finishes.  Everything power-specific about a block lives in its calls to      *)
(* PRODUCT_TAC / SQUARE_TAC below.                                               *)
let GUERON_ATOMS_TAC =
  let p_lo_tm = `word_pmul (word_subword (a:int128) (0,64):64 word)
                           (word_subword (b:int128) (0,64):64 word):128 word`
  and p_hi_tm = `word_pmul (word_subword (a:int128) (64,64):64 word)
                           (word_subword (b:int128) (64,64):64 word):128 word`
  and c1_tm = `word_pmul (word_subword (a:int128) (0,64):64 word)
                         (word_subword (b:int128) (64,64):64 word):128 word`
  and c2_tm = `word_pmul (word_subword (a:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word):128 word`
  and q_a_tm = `word_pmul (word_subword (PL:128 word) (0,64):64 word)
                          ((word 13979173243358019584):64 word):128 word`
  and atom s k = mk_var(s ^ string_of_int k,`:128 word`) in
  let abbrev v tm = ABBREV_TAC(mk_eq(v,tm)) in
  fun k square a b ->
    let pl = atom "PL" k in
    let opnds = [a,`a:int128`; b,`b:int128`] in
    MAP_EVERY (uncurry abbrev)
     ([pl, subst opnds p_lo_tm; atom "PH" k, subst opnds p_hi_tm] @
      (if square then [] else [atom "C1" k, subst opnds c1_tm;
                               atom "C2" k, subst opnds c2_tm]) @
      [atom "QA" k, subst [pl,`PL:128 word`] q_a_tm]) THEN
    CONV_TAC LANE_CONV;;

let PRODUCT_TAC k a b = GUERON_ATOMS_TAC k false a b;;   (* operands differ *)
let SQUARE_TAC k a = GUERON_ATOMS_TAC k true a a;;       (* a . a *)

(* ------------------------------------------------------------------------- *)
(* Extra machinery for the fused twist+H^2 block (Phase 3).                   *)
(*                                                                            *)
(* The routine no longer forms the twisted key's two carryless products at     *)
(* all.  Both the twist `T` and the Gueron reduce `L` are GF(2)-LINEAR and a   *)
(* carryless SQUARE is additive, so `L o square o T` distributes over the      *)
(* twist's DISJOINT summands and H^2 is assembled straight off the RAW key:    *)
(*                                                                            *)
(*   H^2 = L(S.d[1]^2) ^ S.d[0]^2 ^ u.d[1] ^ (carry ? Q : 0)                   *)
(*                                                                            *)
(* with S = H<<1 per lane, u = H>>63 per lane, carry = bit 63 of H's low lane, *)
(* and Q = 0xc2000000_00000000_00000000_00000001 -- the POLYVAL modulus, which *)
(* is exactly L(1) ^ w^2 (w = 0xc2000000_00000000).  The three pieces below    *)
(* are what let the spec's `p_lo`/`p_hi` be rewritten into that form.          *)
(* ------------------------------------------------------------------------- *)

(* The `and` that selects the conditional constant, split into its two lanes.  *)
let FMASK = prove
 (`!m:int64. word_and (word_join m m:int128)
                      (word 0xc2000000000000000000000000000001) =
             word_join (word_and (word 0xc200000000000000) m)
                       (word_and (word 1) m)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ghash_twist's two 64-bit lanes as XORs of DISJOINT summands.  Lane 0 needs   *)
(* only the shift and the other lane's top bit; lane 1 additionally carries the *)
(* conditional 0xc2.0, masked by the very bit ghash_twist tests.  Left in the   *)
(* `if`-free masked form so the SAME carry bit governs both sides downstream.   *)
let TWIST_LANES = prove
 (`!k:int128.
     word_subword (ghash_twist k) (0,64):int64 =
       word_xor (word_shl (word_subword k (0,64)) 1)
                (word_ushr (word_subword k (64,64)) 63) /\
     word_subword (ghash_twist k) (64,64):int64 =
       word_xor (word_xor (word_shl (word_subword k (64,64)) 1)
                          (word_ushr (word_subword k (0,64)) 63))
                (word_and (word 0xc200000000000000)
                          (word_ishr (word_subword k (64,64)) 63))`,
  GEN_TAC THEN REWRITE_TAC[ghash_twist; POLYVAL_TWIST_CONST] THEN BITBLAST_TAC);;

(* Every carryless product whose operand depends ONLY on the carry bit is a    *)
(* masked CONSTANT, and here they are, in the exact shapes the reduce produces: *)
(* the carry squared, the carry times w, and (twice over) w times w.  Each is   *)
(* stated as a `word_join` of its two lanes so that lane normalization needs no *)
(* rule for pushing `word_subword` through `word_and`.  Proved by the only case *)
(* split in the file -- on the carry bit -- after which WORD_PMUL_CONV just     *)
(* evaluates the constants (1.1 = 1, 1.w = w, w.w = 0x5004..<<64, all carryless). *)
let CARRY_PMULS = prove
 (`(!x:int64. word_pmul (word_ushr x 63) (word_ushr x 63):int128 =
              word_join (word 0:int64) (word_and (word 1) (word_ishr x 63))) /\
   (!x:int64. word_pmul (word_ushr x 63) (word 0xc200000000000000:int64):int128 =
              word_join (word 0:int64)
                        (word_and (word 0xc200000000000000) (word_ishr x 63))) /\
   (!x:int64. word_pmul (word_and (word 1) (word_ishr x 63))
                        (word 0xc200000000000000:int64):int128 =
              word_join (word 0:int64)
                        (word_and (word 0xc200000000000000) (word_ishr x 63))) /\
   (!x:int64. word_pmul (word_and (word 0xc200000000000000) (word_ishr x 63))
                        (word 0xc200000000000000:int64):int128 =
              word_join (word_and (word 0x5004000000000000) (word_ishr x 63))
                        (word 0:int64)) /\
   (!x:int64. word_pmul (word_and (word 0xc200000000000000) (word_ishr x 63))
                        (word_and (word 0xc200000000000000) (word_ishr x 63)):int128 =
              word_join (word_and (word 0x5004000000000000) (word_ishr x 63))
                        (word 0:int64))`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  SUBGOAL_THEN
   `word_ushr (x:int64) 63 = (if bit 63 x then word 1 else word 0) /\
    word_ishr (x:int64) 63 =
      (if bit 63 x then word 18446744073709551615 else word 0)`
   (CONJUNCTS_THEN SUBST1_TAC) THENL [BITBLAST_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[WORD_PMUL_0] THEN
  CONV_TAC(DEPTH_CONV(WORD_PMUL_CONV ORELSEC WORD_RED_CONV)) THEN
  CONV_TAC WORD_BLAST);;

(* The routine reads the key's high 64 bits through the GP pipe (`ldr x3,[x1,#8]` *)
(* + `lsl` + `fmov`, which lands its square two cycles before a vector `shl`      *)
(* could), so the stepper needs the input as two `bytes64` reads as well as the   *)
(* `bytes128` one the (frozen) precondition supplies.  Add them, keeping both.    *)
let SPLIT_INPUT_TAC =
  STRIP_ASSUME_TAC(GEN_REWRITE_RULE I
    [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)]
    (ASSUME `read (memory :> bytes128 H_ptr) s0 = H`));;

(* Fold the twisted key's raw bit expression into the spec atom the moment the  *)
(* routine finishes computing it, so the rest of the block (its byteswap, the   *)
(* packed-mid `trn1`/`trn2` and the store) sees an OPAQUE operand -- exactly as  *)
(* the later power blocks do, which is what keeps their `word_or`-free algebra   *)
(* usable here.  The raw term is read off the assumption for register `rname`     *)
(* rather than transcribed, so a reschedule -- or a reallocation -- of the twist  *)
(* does not invalidate this.                                                      *)
let ATOMIZE_TWIST_TAC rname sname atom : tactic =
  fun (asl,w) ->
    let is_reg th = match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),_) ->
          string_of_term c = rname && string_of_term st = sname
      | _ -> false in
    let th = snd(find (fun (_,t) -> is_reg t) asl) in
    let raw = rand(concl th) in
    (SUBGOAL_THEN (mk_eq(raw,atom)) SUBST_ALL_TAC THENL
      [REWRITE_TAC[byteswap128; ghash_twist; POLYVAL_TWIST_CONST] THEN BITBLAST_TAC;
       ALL_TAC]) (asl,w);;

(* LANE_CLOSE_TAC plus the carry-constant collapse.  The two must ALTERNATE:     *)
(* LANE_CONV's distribution of pmul-by-w is what exposes the next carry-only     *)
(* product, and CARRY_PMULS' `word_join` results are what LANE_CONV then splits  *)
(* into lanes.  Three rounds reach the fixpoint (the reduce is two deep).        *)
let CARRY_CLOSE_TAC =
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC WORD_EQ_128_LANES THEN CONJ_TAC THEN
  CONV_TAC LANE_CONV THEN
  REWRITE_TAC[CARRY_PMULS] THEN CONV_TAC LANE_CONV THEN
  REWRITE_TAC[CARRY_PMULS] THEN CONV_TAC LANE_CONV THEN
  REWRITE_TAC[CARRY_PMULS] THEN CONV_TAC LANE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE;;

(* ========================================================================= *)
(* Phase 3: the FUSED twist + H^2 block (PC 0x0 -> 0x80, 32 steps).           *)
(*                                                                            *)
(* The routine never forms the twisted key's two carryless products.  Both the *)
(* twist `T` and the Gueron reduce `L` are GF(2)-LINEAR and a carryless SQUARE  *)
(* is additive, so `L o square o T` distributes over the twist's DISJOINT       *)
(* summands and H^2 is assembled straight off the RAW key:                     *)
(*                                                                            *)
(*   H^2 = L(S.d[1]^2) ^ S.d[0]^2 ^ u.d[1] ^ (carry ? Q : 0)                   *)
(*                                                                            *)
(* This block now stops the moment H^2 exists.  Everything the old version of   *)
(* it also did -- the algebraic-lane copy of the key, H^2's byteswap, the       *)
(* Karatsuba pack and the Htable[0..1] store -- has been scheduled INTO the     *)
(* next block by the ASAP ordering, so all this one owns is the twist and H^2,   *)
(* and its interface is just three registers.                                  *)
(*                                                                            *)
(* The twisted key lands in Q0 (it is Q0 that ATOMIZE_TWIST_TAC folds), the      *)
(* reduction constant w in Q4 and H^2 in Q1.                                   *)
(* ========================================================================= *)

let GCM_INIT_V8_TWIST_H2 = prove
 (`!Htable H_ptr H h1 pc.
    h1 = ghash_twist(byteswap128 H) /\
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192) /\
    nonoverlapping (Htable, 192) (H_ptr, 16)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [Htable; H_ptr] s /\
              read (memory :> bytes128 H_ptr) s = H)
         (\s. read PC s = word (pc + 0x80) /\
              read X0 s = Htable /\
              read Q4 s = word 0xc200000000000000c200000000000000 /\
              read Q0 s = byteswap128 h1 /\
              read Q1 s = h_power h1 1)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC
    [`Htable:int64`; `H_ptr:int64`; `H:int128`; `h1:int128`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst GCM_INIT_V8_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SOME_FLAGS; MODIFIABLE_SIMD_REGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  SPLIT_INPUT_TAC THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--31) THEN
  ATOMIZE_TWIST_TAC "Q0" "s31" `byteswap128(ghash_twist(byteswap128 H))` THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (32--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FMASK] THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  SPEC_UNFOLD_TAC THEN
  REWRITE_TAC[TWIST_LANES] THEN
  REWRITE_TAC[PMUL_SQ_XOR2; PMUL_SQ_XOR3] THEN
  CARRY_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 5: the H^3 & H^4 block, PC 0x80 -> 0x104 (33 steps).                  *)
(*                                                                            *)
(*   H^3 = h_power h1 2 = polyval_dot h1 H^2   (genuine product)               *)
(*   H^4 = h_power h1 3 = polyval_dot H^2 H^2  (a SQUARE)                      *)
(*                                                                            *)
(* Also finishes the FIRST block's table work, which the ASAP schedule moved    *)
(* down here because it has slack and H^3's four products do not: the           *)
(* algebraic-lane copy of the key (`ext` of Q0), byteswap128 H^2, the           *)
(* trn1/trn2 Karatsuba pack and `stp q0,q3,[x0]`.                              *)
(*                                                                            *)
(* H^3's cross products read the byteswapped key straight out of Q0, which is    *)
(* the very value Htable[0] stores; H^4 is a square, so SQ_CROSS_0 kills its    *)
(* whole middle.  Live out: w (Q4), H^2 (Q1) and its byteswap (Q16), H^3 (Q17),  *)
(* H^4 (Q0) and its byteswap (Q2) -- the last two feed all four of the next     *)
(* block's powers.                                                            *)
(* ========================================================================= *)

let GCM_INIT_V8_H34 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x80) /\
              read X0 s = Htable /\
              read Q4 s = word 0xc200000000000000c200000000000000 /\
              read Q0 s = byteswap128 h1 /\
              read Q1 s = h_power h1 1)
         (\s. read PC s = word (pc + 0x104) /\
              read X0 s = Htable /\
              read Q4 s = word 0xc200000000000000c200000000000000 /\
              read Q1 s = h_power h1 1 /\
              read Q16 s = byteswap128 (h_power h1 1) /\
              read Q17 s = h_power h1 2 /\
              read Q0 s = h_power h1 3 /\
              read Q2 s = byteswap128 (h_power h1 3) /\
              read (memory :> bytes128 Htable) s = byteswap128 h1 /\
              read (memory :> bytes128 (word_add Htable (word 16))) s =
                word_join (karatsuba_mid (h_power h1 1)) (karatsuba_mid h1))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `h1:int128`; `pc:num`] THEN
  GCM_BLOCK_STEPS_TAC 33 THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  ABBREV_TAC `h2 = polyval_dot h1 h1` THEN
  SPEC_UNFOLD_TAC THEN
  PRODUCT_TAC 3 `h1:int128` `h2:int128` THEN
  SQUARE_TAC 4 `h2:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 6: the H^5, H^6, H^7 and H^8 block, PC 0x104 -> 0x1e0 (55 steps).     *)
(*                                                                            *)
(*   H^8 = h_power h1 7 = polyval_dot H^4 H^4  (a SQUARE)                      *)
(*   H^5 = h_power h1 4 = polyval_dot H^2 H^3  (genuine)                       *)
(*   H^6 = h_power h1 5 = polyval_dot H^3 H^3  (a SQUARE)                      *)
(*   H^7 = h_power h1 6 = polyval_dot H^4 H^3  (genuine)                       *)
(*                                                                            *)
(* ALL FOUR remaining powers, in one block.  That is forced by the schedule     *)
(* rather than chosen: every one of them depends only on H^3/H^4, so the ASAP    *)
(* order issues their twelve products together and interleaves the four         *)
(* reduction chains -- there is no PC between them at which only named powers    *)
(* are live.  Nothing about the ALGEBRA changes; the block simply runs           *)
(* GUERON_ATOMS_TAC four times instead of two or three.                         *)
(*                                                                            *)
(* H^7 is stated as H^4 . H^3 (not H^3 . H^4) because the cross products read    *)
(* the OTHER operand's byteswapped copy and only H^4's is in the table; the      *)
(* same holds for H^5 = H^2 . H^3.                                             *)
(*                                                                            *)
(* Stores Htable[2..5] (`stp q16,q0,[x0,#32]` and `stp q23,q2,[x0,#64]`).  Live  *)
(* out: H^5 (Q2), H^6 (Q1) and its byteswap (Q6), H^7 (Q7), byteswap128 H^8      *)
(* (Q5) and H^8's Karatsuba fold (Q3) -- w is dead from here, the last block     *)
(* has no products.                                                            *)
(* ========================================================================= *)

let GCM_INIT_V8_H5678 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x104) /\
              read X0 s = Htable /\
              read Q4 s = word 0xc200000000000000c200000000000000 /\
              read Q1 s = h_power h1 1 /\
              read Q16 s = byteswap128 (h_power h1 1) /\
              read Q17 s = h_power h1 2 /\
              read Q0 s = h_power h1 3 /\
              read Q2 s = byteswap128 (h_power h1 3) /\
              read (memory :> bytes128 Htable) s = byteswap128 h1 /\
              read (memory :> bytes128 (word_add Htable (word 16))) s =
                word_join (karatsuba_mid (h_power h1 1)) (karatsuba_mid h1))
         (\s. read PC s = word (pc + 0x1e0) /\
              read X0 s = Htable /\
              read Q2 s = h_power h1 4 /\
              read Q1 s = h_power h1 5 /\
              read Q6 s = byteswap128 (h_power h1 5) /\
              read Q7 s = h_power h1 6 /\
              read Q5 s = byteswap128 (h_power h1 7) /\
              read Q3 s = word_join (karatsuba_mid (h_power h1 7))
                                    (karatsuba_mid (h_power h1 7)) /\
              read (memory :> bytes128 Htable) s = byteswap128 h1 /\
              read (memory :> bytes128 (word_add Htable (word 16))) s =
                word_join (karatsuba_mid (h_power h1 1)) (karatsuba_mid h1) /\
              read (memory :> bytes128 (word_add Htable (word 32))) s =
                byteswap128 (h_power h1 1) /\
              read (memory :> bytes128 (word_add Htable (word 48))) s =
                byteswap128 (h_power h1 2) /\
              read (memory :> bytes128 (word_add Htable (word 64))) s =
                word_join (karatsuba_mid (h_power h1 3)) (karatsuba_mid (h_power h1 2)) /\
              read (memory :> bytes128 (word_add Htable (word 80))) s =
                byteswap128 (h_power h1 3))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `h1:int128`; `pc:num`] THEN
  GCM_BLOCK_STEPS_TAC 55 THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  MAP_EVERY ABBREV_TAC
   [`h2 = polyval_dot h1 h1`; `h3 = polyval_dot h1 h2`;
    `h4 = polyval_dot h2 h2`] THEN
  SPEC_UNFOLD_TAC THEN
  SQUARE_TAC 8 `h4:int128` THEN
  PRODUCT_TAC 5 `h2:int128` `h3:int128` THEN
  SQUARE_TAC 6 `h3:int128` THEN
  PRODUCT_TAC 7 `h4:int128` `h3:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 6b: the closing block, PC 0x1e0 -> 0x208 (10 steps, ends at the ret). *)
(*                                                                            *)
(* No products at all: byteswap128 of H^5 and H^7, the two remaining Karatsuba  *)
(* packs ({mid H^5, mid H^6} by trn1/trn2 and {mid H^7, mid H^8} by one `ext`   *)
(* of the two broadcast folds) and the last three `stp`s, Htable[6..11].        *)
(* Every operand is an opaque power out of the precondition, so the whole block *)
(* closes on lane identities alone -- no PMUL reasoning, hence no              *)
(* SPEC_UNFOLD_TAC and no atoms.                                              *)
(*                                                                            *)
(* The postcondition carries ALL TWELVE slots, so Phase 7 reads the full        *)
(* htable_mem table straight off this block's post.                            *)
(* ========================================================================= *)

let GCM_INIT_V8_TAIL = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x1e0) /\
              read X0 s = Htable /\
              read Q2 s = h_power h1 4 /\
              read Q1 s = h_power h1 5 /\
              read Q6 s = byteswap128 (h_power h1 5) /\
              read Q7 s = h_power h1 6 /\
              read Q5 s = byteswap128 (h_power h1 7) /\
              read Q3 s = word_join (karatsuba_mid (h_power h1 7))
                                    (karatsuba_mid (h_power h1 7)) /\
              read (memory :> bytes128 Htable) s = byteswap128 h1 /\
              read (memory :> bytes128 (word_add Htable (word 16))) s =
                word_join (karatsuba_mid (h_power h1 1)) (karatsuba_mid h1) /\
              read (memory :> bytes128 (word_add Htable (word 32))) s =
                byteswap128 (h_power h1 1) /\
              read (memory :> bytes128 (word_add Htable (word 48))) s =
                byteswap128 (h_power h1 2) /\
              read (memory :> bytes128 (word_add Htable (word 64))) s =
                word_join (karatsuba_mid (h_power h1 3)) (karatsuba_mid (h_power h1 2)) /\
              read (memory :> bytes128 (word_add Htable (word 80))) s =
                byteswap128 (h_power h1 3))
         (\s. read PC s = word (pc + 0x208) /\
              read X0 s = Htable /\
              read (memory :> bytes128 Htable) s = byteswap128 h1 /\
              read (memory :> bytes128 (word_add Htable (word 16))) s =
                word_join (karatsuba_mid (h_power h1 1)) (karatsuba_mid h1) /\
              read (memory :> bytes128 (word_add Htable (word 32))) s =
                byteswap128 (h_power h1 1) /\
              read (memory :> bytes128 (word_add Htable (word 48))) s =
                byteswap128 (h_power h1 2) /\
              read (memory :> bytes128 (word_add Htable (word 64))) s =
                word_join (karatsuba_mid (h_power h1 3)) (karatsuba_mid (h_power h1 2)) /\
              read (memory :> bytes128 (word_add Htable (word 80))) s =
                byteswap128 (h_power h1 3) /\
              read (memory :> bytes128 (word_add Htable (word 96))) s =
                byteswap128 (h_power h1 4) /\
              read (memory :> bytes128 (word_add Htable (word 112))) s =
                word_join (karatsuba_mid (h_power h1 5)) (karatsuba_mid (h_power h1 4)) /\
              read (memory :> bytes128 (word_add Htable (word 128))) s =
                byteswap128 (h_power h1 5) /\
              read (memory :> bytes128 (word_add Htable (word 144))) s =
                byteswap128 (h_power h1 6) /\
              read (memory :> bytes128 (word_add Htable (word 160))) s =
                word_join (karatsuba_mid (h_power h1 7)) (karatsuba_mid (h_power h1 6)) /\
              read (memory :> bytes128 (word_add Htable (word 176))) s =
                byteswap128 (h_power h1 7))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `h1:int128`; `pc:num`] THEN
  GCM_BLOCK_STEPS_TAC 10 THEN
  SPEC_UNFOLD_TAC THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 7: the core correctness theorem, GCM_INIT_V8_CORRECT.                *)
(*                                                                            *)
(* Compose the four blocks into one `ensures` from function entry (PC 0x0) to *)
(* the `ret` (PC 0x208), establishing the full 12-slot htable_mem             *)
(* postcondition for the half-swapped algebraic key h1 = ghash_twist(         *)
(* byteswap128 H).  Each block is applied as a single atomic transition with  *)
(* ARM_BIGSTEP_TAC, so the raw pmull expansions never re-appear -- they were  *)
(* discharged inside the per-block proofs.  The blocks tile the routine:      *)
(* post_i => pre_{i+1} syntactically (every power block is instantiated at    *)
(* the same h1, and the powers are named in htable_mem's own h_power form),   *)
(* so ASM_REWRITE_TAC[] discharges each block's precondition, and             *)
(* htable_mem's twelve slots then match the assumptions directly.            *)
(*                                                                            *)
(* NONSELFMODIFYING NOTE (the one subtlety): ARM_BIGSTEP_TAC must show the     *)
(* frame write  memory :> bytes(Htable,192)  is disjoint from the code region *)
(* memory :> bytelist(word pc,524).  Its ORTHOGONAL_COMPONENTS_TAC scans the  *)
(* assumptions for a RAW `nonoverlapping (word pc,524) (Htable,192)` driver    *)
(* and needs the length CONCRETE (524).  Hence: reduce LENGTH gcm_init_v8_mc   *)
(* to 524 via `fst GCM_INIT_V8_EXEC` in the setup rewrite, and do NOT rewrite  *)
(* NONOVERLAPPING_CLAUSES on the initial assumptions (keep the driver form).   *)
(* ========================================================================= *)

(* the MAYCHANGE/length normalization every block instance needs, and one     *)
(* bigstep through a power block at the internal key of the enclosing proof.  *)
let MAYCHANGE_EXPAND_TAC =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS; SOME_FLAGS;
              fst GCM_INIT_V8_EXEC];;

let GCM_BLOCK_STEP_TAC sname blockth =
  MP_TAC(SPECL[`Htable:int64`; `ghash_twist(byteswap128 H):int128`; `pc:num`]
              blockth) THEN
  MAYCHANGE_EXPAND_TAC THEN ASM_REWRITE_TAC[] THEN
  ARM_BIGSTEP_TAC GCM_INIT_V8_EXEC sname;;

let GCM_INIT_V8_CORRECT = prove
 (`!Htable H_ptr H pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192) /\
    nonoverlapping (Htable, 192) (H_ptr, 16)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [Htable; H_ptr] s /\
              read (memory :> bytes128 H_ptr) s = H)
         (\s. read PC s = word (pc + 0x208) /\
              htable_mem (ghash_twist(byteswap128 H)) Htable s)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `H_ptr:int64`; `H:int128`; `pc:num`] THEN
  MAYCHANGE_EXPAND_TAC THEN
  STRIP_TAC THEN
  MP_TAC(SPECL[`Htable:int64`;`H_ptr:int64`;`H:int128`;
               `ghash_twist(byteswap128 H)`;`pc:num`]
              GCM_INIT_V8_TWIST_H2) THEN
  REWRITE_TAC[] THEN
  MAYCHANGE_EXPAND_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC(!simulation_precanon_thms) THEN
                       ENSURES_INIT_TAC "s0" THEN MP_TAC th) THEN
  ARM_BIGSTEP_TAC GCM_INIT_V8_EXEC "s1" THEN
  GCM_BLOCK_STEP_TAC "s2" GCM_INIT_V8_H34 THEN
  GCM_BLOCK_STEP_TAC "s3" GCM_INIT_V8_H5678 THEN
  GCM_BLOCK_STEP_TAC "s4" GCM_INIT_V8_TAIL THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[htable_mem; CONJUNCT1 h_power]);;

(* ========================================================================= *)
(* Phase 8: the standard-ABI subroutine wrapper (leaf, no stack frame).       *)
(*                                                                            *)
(* Wrap the core with the return via X30.  Two mechanical points:             *)
(*  - Reduce LENGTH gcm_init_v8_mc to 524 (`fst GCM_INIT_V8_EXEC`) in the goal *)
(*    and in the core theorem so ARM_ADD_RETURN_NOSTACK_TAC's internal         *)
(*    nonselfmodifying / NONOVERLAPPING checks see a concrete-length driver.   *)
(*  - htable_mem is an opaque folded predicate that does NOT propagate through *)
(*    the trailing `ret` (only `read (memory :> ...) s = v` facts do), so feed *)
(*    the wrapper a core with htable_mem UNFOLDED — its 12 memory reads then   *)
(*    propagate to the return state — and re-fold htable_mem to close.         *)
(* ========================================================================= *)

let GCM_INIT_V8_SUBROUTINE_CORRECT = prove
 (`!Htable H_ptr H pc returnaddress.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192) /\
    nonoverlapping (Htable, 192) (H_ptr, 16)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word pc /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [Htable; H_ptr] s /\
              read (memory :> bytes128 H_ptr) s = H)
         (\s. read PC s = returnaddress /\
              htable_mem (ghash_twist(byteswap128 H)) Htable s)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  REWRITE_TAC[fst GCM_INIT_V8_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC GCM_INIT_V8_EXEC
    (REWRITE_RULE[htable_mem; fst GCM_INIT_V8_EXEC] GCM_INIT_V8_CORRECT) THEN
  REWRITE_TAC[htable_mem] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9: constant-time and memory-safety.                                  *)
(*                                                                            *)
(* The routine is branch-free with fully data-independent addressing, so it   *)
(* is constant-time: the event trace f_events depends only on the PUBLIC args *)
(* (H_ptr, Htable, pc, returnaddress) and NOT on the secret key value H.  All *)
(* memory accesses stay in bounds: reads confined to [H_ptr,16], writes to    *)
(* [Htable,192].  The full spec is generated mechanically from the registered *)
(* signature and the correctness theorem, then discharged by the generic      *)
(* safety tactic.                                                            *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "gcm_init_v8" subroutine_signatures)
    GCM_INIT_V8_SUBROUTINE_CORRECT
    GCM_INIT_V8_EXEC;;

let GCM_INIT_V8_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e Htable H_ptr pc returnaddress.
        nonoverlapping (word pc,LENGTH gcm_init_v8_mc) (Htable,192) /\
        nonoverlapping (Htable,192) (H_ptr,16)
        ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
                 read PC s = word pc /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [Htable; H_ptr] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events H_ptr Htable pc returnaddress /\
                      memaccess_inbounds e2 [H_ptr,16; Htable,192] [Htable,192]))
            (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars GCM_INIT_V8_EXEC);;
