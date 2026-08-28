(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* GCM_INIT_V8: expand the GHASH hash key H into the PMULL/v8 power table.    *)
(* Correctness against the POLYVAL/GHASH algebraic spec in                    *)
(* common/polyval_ghash.ml.  X0 = Htable (192 bytes written), X1 = H.         *)
(*                                                                            *)
(* Layout: the routine is branch-free, so the proof is five straight-line     *)
(* blocks tiling PC 0x0..0x254 -- the twist, then four power blocks computing  *)
(* two of H^2..H^8 each -- composed by ARM_BIGSTEP_TAC into                    *)
(* GCM_INIT_V8_CORRECT.  The four power blocks differ only in which Q         *)
(* registers and which powers they touch, so ALL their algebra lives once in   *)
(* the two toolkit sections below and each block's script is the same six      *)
(* steps.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/polyval_ghash.ml";;
needs "common/karatsuba_pmul.ml";;      (* PMUL_KARATSUBA; ~0.5s on top of the above *)

(**** print_literal_from_elf "arm/gcm/gcm_init_v8.o";;
 ****)

let gcm_init_v8_mc = define_assert_from_elf
 "gcm_init_v8_mc" "arm/gcm/gcm_init_v8.o"
[
  0x4c407c31;       (* arm_LDR Q17 X1 No_Offset *)
  0x4f07e433;       (* arm_MOVI Q19 (word 16276538888567251425) *)
  0x4f795673;       (* arm_SHL_VEC Q19 Q19 57 64 128 *)
  0x6e114223;       (* arm_EXT Q3 Q17 Q17 64 *)
  0x6f410672;       (* arm_USHR_VEC Q18 Q19 63 64 128 *)
  0x4e0c0631;       (* arm_DUP_ELEM Q17 Q17 32 128 1 *)
  0x6e134250;       (* arm_EXT Q16 Q18 Q19 64 *)
  0x6f410472;       (* arm_USHR_VEC Q18 Q3 63 64 128 *)
  0x4f210631;       (* arm_SSHR_VEC Q17 Q17 31 32 128 *)
  0x4e301e52;       (* arm_AND_VEC Q18 Q18 Q16 128 *)
  0x4f415463;       (* arm_SHL_VEC Q3 Q3 1 64 128 *)
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0x4e311e10;       (* arm_AND_VEC Q16 Q16 Q17 128 *)
  0x4eb21c63;       (* arm_ORR_VEC Q3 Q3 Q18 128 *)
  0x6e301c74;       (* arm_EOR_VEC Q20 Q3 Q16 128 *)
  0x6e144294;       (* arm_EXT Q20 Q20 Q20 64 *)
  0x4c9f7c14;       (* arm_STR Q20 X0 (Postimmediate_Offset (word 16)) *)
  0x6e144290;       (* arm_EXT Q16 Q20 Q20 64 *)
  0x4ef4e280;       (* arm_PMULL2_VEC Q0 Q20 Q20 64 *)
  0x6e341e10;       (* arm_EOR_VEC Q16 Q16 Q20 128 *)
  0x0ef4e282;       (* arm_PMULL_VEC Q2 Q20 Q20 64 *)
  0x0ef0e201;       (* arm_PMULL_VEC Q1 Q16 Q16 64 *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c11;       (* arm_EOR_VEC Q17 Q0 Q18 128 *)
  0x6e114236;       (* arm_EXT Q22 Q17 Q17 64 *)
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e114215;       (* arm_EXT Q21 Q16 Q17 64 *)
  0x4c9f7c15;       (* arm_STR Q21 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f7c16;       (* arm_STR Q22 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef6e280;       (* arm_PMULL2_VEC Q0 Q20 Q22 64 *)
  0x4ef6e2c5;       (* arm_PMULL2_VEC Q5 Q22 Q22 64 *)
  0x0ef6e282;       (* arm_PMULL_VEC Q2 Q20 Q22 64 *)
  0x0ef6e2c7;       (* arm_PMULL_VEC Q7 Q22 Q22 64 *)
  0x0ef1e201;       (* arm_PMULL_VEC Q1 Q16 Q17 64 *)
  0x0ef1e226;       (* arm_PMULL_VEC Q6 Q17 Q17 64 *)
  0x6e024010;       (* arm_EXT Q16 Q0 Q2 64 *)
  0x6e0740b1;       (* arm_EXT Q17 Q5 Q7 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e271ca4;       (* arm_EOR_VEC Q4 Q5 Q7 128 *)
  0x6e311cc6;       (* arm_EOR_VEC Q6 Q6 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e241cc6;       (* arm_EOR_VEC Q6 Q6 Q4 128 *)
  0x0ef3e0a4;       (* arm_PMULL_VEC Q4 Q5 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e0844c7;       (* arm_INS Q7 Q6 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e1804a6;       (* arm_INS Q6 Q5 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e241cc5;       (* arm_EOR_VEC Q5 Q6 Q4 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x6e0540a4;       (* arm_EXT Q4 Q5 Q5 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x0ef3e0a5;       (* arm_PMULL_VEC Q5 Q5 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 128 *)
  0x6e321c10;       (* arm_EOR_VEC Q16 Q0 Q18 128 *)
  0x6e241cb1;       (* arm_EOR_VEC Q17 Q5 Q4 128 *)
  0x6e104217;       (* arm_EXT Q23 Q16 Q16 64 *)
  0x6e114239;       (* arm_EXT Q25 Q17 Q17 64 *)
  0x6e1642d2;       (* arm_EXT Q18 Q22 Q22 64 *)
  0x6e371e03;       (* arm_EOR_VEC Q3 Q16 Q23 128 *)
  0x6e391e35;       (* arm_EOR_VEC Q21 Q17 Q25 128 *)
  0x6e361e52;       (* arm_EOR_VEC Q18 Q18 Q22 128 *)
  0x6e154078;       (* arm_EXT Q24 Q3 Q21 64 *)
  0x4c9f6c17;       (* arm_STP3 Q23 Q24 Q25 X0 (Postimmediate_Offset (word 48)) *)
  0x4ef7e2c0;       (* arm_PMULL2_VEC Q0 Q22 Q23 64 *)
  0x4ef7e2e5;       (* arm_PMULL2_VEC Q5 Q23 Q23 64 *)
  0x0ef7e2c2;       (* arm_PMULL_VEC Q2 Q22 Q23 64 *)
  0x0ef7e2e7;       (* arm_PMULL_VEC Q7 Q23 Q23 64 *)
  0x0ef2e061;       (* arm_PMULL_VEC Q1 Q3 Q18 64 *)
  0x0ee3e066;       (* arm_PMULL_VEC Q6 Q3 Q3 64 *)
  0x6e024010;       (* arm_EXT Q16 Q0 Q2 64 *)
  0x6e0740b1;       (* arm_EXT Q17 Q5 Q7 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e271ca4;       (* arm_EOR_VEC Q4 Q5 Q7 128 *)
  0x6e311cc6;       (* arm_EOR_VEC Q6 Q6 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e241cc6;       (* arm_EOR_VEC Q6 Q6 Q4 128 *)
  0x0ef3e0a4;       (* arm_PMULL_VEC Q4 Q5 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e0844c7;       (* arm_INS Q7 Q6 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e1804a6;       (* arm_INS Q6 Q5 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e241cc5;       (* arm_EOR_VEC Q5 Q6 Q4 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x6e0540a4;       (* arm_EXT Q4 Q5 Q5 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x0ef3e0a5;       (* arm_PMULL_VEC Q5 Q5 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 128 *)
  0x6e321c10;       (* arm_EOR_VEC Q16 Q0 Q18 128 *)
  0x6e241cb1;       (* arm_EOR_VEC Q17 Q5 Q4 128 *)
  0x6e10421a;       (* arm_EXT Q26 Q16 Q16 64 *)
  0x6e11423c;       (* arm_EXT Q28 Q17 Q17 64 *)
  0x6e3a1e10;       (* arm_EOR_VEC Q16 Q16 Q26 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e11421b;       (* arm_EXT Q27 Q16 Q17 64 *)
  0x4c9f6c1a;       (* arm_STP3 Q26 Q27 Q28 X0 (Postimmediate_Offset (word 48)) *)
  0x4ef9e2e0;       (* arm_PMULL2_VEC Q0 Q23 Q25 64 *)
  0x4ef9e325;       (* arm_PMULL2_VEC Q5 Q25 Q25 64 *)
  0x0ef9e2e2;       (* arm_PMULL_VEC Q2 Q23 Q25 64 *)
  0x0ef9e327;       (* arm_PMULL_VEC Q7 Q25 Q25 64 *)
  0x0ef5e061;       (* arm_PMULL_VEC Q1 Q3 Q21 64 *)
  0x0ef5e2a6;       (* arm_PMULL_VEC Q6 Q21 Q21 64 *)
  0x6e024010;       (* arm_EXT Q16 Q0 Q2 64 *)
  0x6e0740b1;       (* arm_EXT Q17 Q5 Q7 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e271ca4;       (* arm_EOR_VEC Q4 Q5 Q7 128 *)
  0x6e311cc6;       (* arm_EOR_VEC Q6 Q6 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e241cc6;       (* arm_EOR_VEC Q6 Q6 Q4 128 *)
  0x0ef3e0a4;       (* arm_PMULL_VEC Q4 Q5 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e0844c7;       (* arm_INS Q7 Q6 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e1804a6;       (* arm_INS Q6 Q5 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e241cc5;       (* arm_EOR_VEC Q5 Q6 Q4 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x6e0540a4;       (* arm_EXT Q4 Q5 Q5 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x0ef3e0a5;       (* arm_PMULL_VEC Q5 Q5 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 128 *)
  0x6e321c10;       (* arm_EOR_VEC Q16 Q0 Q18 128 *)
  0x6e241cb1;       (* arm_EOR_VEC Q17 Q5 Q4 128 *)
  0x6e10421d;       (* arm_EXT Q29 Q16 Q16 64 *)
  0x6e11423f;       (* arm_EXT Q31 Q17 Q17 64 *)
  0x6e3d1e10;       (* arm_EOR_VEC Q16 Q16 Q29 128 *)
  0x6e3f1e31;       (* arm_EOR_VEC Q17 Q17 Q31 128 *)
  0x6e11421e;       (* arm_EXT Q30 Q16 Q17 64 *)
  0x4c006c1d;       (* arm_STP3 Q29 Q30 Q31 X0 No_Offset *)
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
    h_power h 6 = polyval_dot (polyval_dot h (polyval_dot h h)) (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
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
(*      rewrite each wide product with PMUL_KARA, collapse a square's          *)
(*      Karatsuba middle with FROB64, normalize every lane with LANE_CONV and  *)
(*      abbreviate the base products + the two pmul-by-w results, so the goal  *)
(*      becomes PMUL-FREE over opaque atoms;                                   *)
(*   3. close each 128-bit equality per 64-bit lane (LANE_CLOSE_TAC).          *)
(* ========================================================================= *)

(* Karatsuba decomposition of a wide (128x128 -> 256) carryless product.      *)
(* PMUL_KARATSUBA states it under a chain of `let`s, which hides the equation *)
(* from the rewriter; unfolding them exposes it as a rewrite usable at EVERY   *)
(* occurrence, so no per-operand-pair instance is needed.  Its right-hand side *)
(* contains only 64x64 products, so it cannot re-match itself and terminates.  *)
let PMUL_KARA =
  GEN_ALL(CONV_RULE(TOP_DEPTH_CONV let_CONV)(SPEC_ALL PMUL_KARATSUBA));;

(* Frobenius: for a SQUARE the Karatsuba middle collapses to p_lo XOR p_hi.   *)
let FROB64 = prove
 (`!a b:64 word. word_pmul (word_xor a b) (word_xor a b) : 128 word =
                 word_xor (word_pmul a a : 128 word) (word_pmul b b : 128 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [WORD_PMUL_SYM] THEN
  CONV_TAC WORD_BITWISE_RULE);;

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

(* The hardware's and the spec's SECOND-phase Gueron pmul-by-w argument are    *)
(* the same XOR of five 64-bit lanes written two different ways; unifying them *)
(* is what lets both sides' second pmul-by-w abbreviate to one opaque atom.    *)
(* `l`,`L` are the low product's two lanes, `h` the high product's low lane,   *)
(* `m` the Karatsuba middle's low lane, `q` the first-phase result's low lane. *)
(* For a SQUARE the middle has already collapsed to `word_xor l h` (FROB64),   *)
(* so a square block is literally the same instance as a genuine-mid one --     *)
(* which is why one lemma serves all eight powers.                            *)
let VEQ = prove
 (`!l L h m q:64 word.
     word_xor (word_xor L (word_xor (word_xor m l) h)) q =
     word_xor q (word_xor (word_xor h l) (word_xor L m))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* Lane normalization: push word_subword through join / zx / shl / insert /   *)
(* xor until only the opaque atoms remain, and drop the `word 0` lanes that    *)
(* exposes.  One TOP_DEPTH_CONV over the whole rule set reaches the joint      *)
(* fixpoint.                                                                  *)
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
  and ins_lanes = map WORD_BLAST
   [`(word_insert (x:128 word) (0,64) (v:128 word) :128 word) =
     (word_join (word_subword x (64,64):64 word) (word_subword v (0,64):64 word) :128 word)`;
    `(word_insert (x:128 word) (64,64) (v:128 word) :128 word) =
     (word_join (word_subword v (0,64):64 word) (word_subword x (0,64):64 word) :128 word)`]
  and xor_0 = CONJUNCTS(WORD_BLAST
   `(!x:64 word. word_xor x (word 0) = x) /\
    (!x:64 word. word_xor (word 0) x = x)`) in
  TOP_DEPTH_CONV
   (FIRST_CONV (map REWR_CONV (shl_lanes @ ins_lanes @ xor_0) @
                [WORD_SIMPLE_SUBWORD_CONV; REWR_CONV WORD_SUBWORD_XOR]));;

(* `MID_SWAP a b` normalizes a hardware Karatsuba middle -- which the assembly *)
(* forms with the HIGHER power's fold first (pmull v16/v17, v18) -- to the     *)
(* operand order PMUL_KARA produces.  It has to be a DIRECTED instance: the    *)
(* general fact is permutative and HOL Light's rewriter has no ordered         *)
(* rewriting, so rewriting with it would loop.                                *)
let MID_SWAP =
  let fold h = subst [h,`h:int128`]
    `word_xor (word_subword (h:int128) (0,64):64 word)
              (word_subword h (64,64)):64 word` in
  fun a b -> ISPECL [fold b; fold a] WORD_PMUL_SYM;;

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

(* Unfold the spec side down to opaque 64x64 products: polyval_dot -> the     *)
(* Karatsuba reconstruction + the Gueron reduction, then normalize all lanes. *)
let SPEC_UNFOLD_TAC =
  REWRITE_TAC[SUBWORD_BS_LEMMAS] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid; byteswap128; PMUL_KARA] THEN
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
  CONV_TAC LANE_CONV THEN CONV_TAC WORD_BITWISE_RULE;;

(* Name the five opaque atoms of ONE of a block's two carryless products, and  *)
(* normalize the lanes over them.  For product `k` of operands a,b:            *)
(*   PL<k>, PH<k>  the two 64x64 half-products,                                *)
(*   PM<k>         the Karatsuba middle -- present only when the operands       *)
(*                 DIFFER, since for a square FROB64 has already collapsed the  *)
(*                 middle to PL<k> (+) PH<k>,                                   *)
(*   QA<k>, QV<k>  the first- and second-phase Gueron pmul-by-w results, the    *)
(*                 second in VEQ-normalized form so that the hardware's and the *)
(*                 spec's shape of its argument become the same atom.           *)
(* Once both products have been through this the goal is PMUL-FREE and          *)
(* LANE_CLOSE_TAC finishes.  Everything power-specific about a block lives in   *)
(* the two calls to PRODUCT_TAC / SQUARE_TAC below.                             *)
let GUERON_ATOMS_TAC =
  let p_lo_tm = `word_pmul (word_subword (a:int128) (0,64):64 word)
                           (word_subword (b:int128) (0,64):64 word):128 word`
  and p_hi_tm = `word_pmul (word_subword (a:int128) (64,64):64 word)
                           (word_subword (b:int128) (64,64):64 word):128 word`
  and p_mid_tm = `word_pmul (word_xor (word_subword (a:int128) (0,64):64 word)
                                      (word_subword a (64,64)))
                            (word_xor (word_subword (b:int128) (0,64):64 word)
                                      (word_subword b (64,64))):128 word`
  and q_a_tm = `word_pmul (word_subword (PL:128 word) (0,64):64 word)
                          ((word 13979173243358019584):64 word):128 word`
  and q_v_tm = `word_pmul
                 (word_xor (word_subword (QA:128 word) (0,64):64 word)
                   (word_xor (word_xor (word_subword (PH:128 word) (0,64))
                                       (word_subword (PL:128 word) (0,64)))
                             (word_xor (word_subword PL (64,64)) (m:64 word))))
                 ((word 13979173243358019584):64 word):128 word`
  and sq_mid_tm = `word_xor (word_subword (PL:128 word) (0,64):64 word)
                            (word_subword (PH:128 word) (0,64))`
  and gen_mid_tm = `word_subword (PM:128 word) (0,64):64 word`
  and atom s k = mk_var(s ^ string_of_int k,`:128 word`) in
  let abbrev v tm = ABBREV_TAC(mk_eq(v,tm)) in
  fun k square a b ->
    let pl = atom "PL" k and ph = atom "PH" k and qa = atom "QA" k in
    let opnds = [a,`a:int128`; b,`b:int128`]
    and atoms = [pl,`PL:128 word`; ph,`PH:128 word`; qa,`QA:128 word`] in
    MAP_EVERY (uncurry abbrev)
     ([pl, subst opnds p_lo_tm; ph, subst opnds p_hi_tm] @
      (if square then [] else [atom "PM" k, subst opnds p_mid_tm]) @
      [qa, subst atoms q_a_tm]) THEN
    CONV_TAC LANE_CONV THEN REWRITE_TAC[VEQ] THEN
    abbrev (atom "QV" k)
      (subst ((subst (if square then atoms
                      else [atom "PM" k,`PM:128 word`])
                     (if square then sq_mid_tm else gen_mid_tm),
               `m:64 word`) :: atoms)
             q_v_tm);;

let PRODUCT_TAC k a b = GUERON_ATOMS_TAC k false a b;;   (* operands differ *)
let SQUARE_TAC k a = GUERON_ATOMS_TAC k true a a;;       (* a . a *)

(* ========================================================================= *)
(* Phase 3: the twist (PC 0x0 -> 0x44).                                       *)
(*                                                                            *)
(* The first 17 instructions load the raw 128-bit hash key H from [X1],       *)
(* compute the x-twist in the internal (half-swapped) representation, and     *)
(* store the result as Htable[0] via `st1 {v20.2d},[x0],#16`.                 *)
(*                                                                            *)
(* HALF-SWAP BYTE-ORDER CONVENTION (the linchpin of the whole proof):         *)
(*                                                                            *)
(*   Let  H  = read (memory :> bytes128 H_ptr) s   be the raw little-endian   *)
(*   128-bit value in memory.  `byteswap128` swaps the two 64-bit halves      *)
(*   (word0 <-> word1); it is the HOL image of the `ext v,v,#8` the routine   *)
(*   applies immediately after the load.  Then                                *)
(*                                                                            *)
(*        Htable[0]  =  byteswap128 (ghash_twist (byteswap128 H)).            *)
(*                                                                            *)
(*   Equivalently: the algebraic ("polynomial-basis") GHASH key that the      *)
(*   spec calls H is  byteswap128 H_mem, i.e. the memory value with its two   *)
(*   64-bit halves swapped.  All the internal PMULL math (Phases 4-7) runs    *)
(*   on that half-swapped representation, and every stored entry is the       *)
(*   byteswap128 of the corresponding internal power (see `htable_mem`,       *)
(*   whose first slot is `byteswap128 (h_power h 0) = byteswap128 h`).         *)
(*                                                                            *)
(*   The carry bit that `ghash_twist` tests as `bit 127` is, in the internal  *)
(*   representation, the top bit of `byteswap128 H` = `bit 63 H`; the routine *)
(*   broadcasts exactly that bit via `dup v17.4s,v17.s[1]` + `sshr ...,#31`.   *)
(*                                                                            *)
(* The whole equality is a fixed-width bit identity, closed by `BITBLAST_TAC` *)
(* (the conditional in `ghash_twist` is left in place so the SAME carry bit   *)
(* governs both sides; do NOT `COND_CASES_TAC` first, or the bit-blaster      *)
(* loses the shared assumption and the two branches no longer line up).       *)
(* ========================================================================= *)

let GCM_INIT_V8_TWIST = prove
 (`!Htable H_ptr H pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192) /\
    nonoverlapping (Htable, 192) (H_ptr, 16)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [Htable; H_ptr] s /\
              read (memory :> bytes128 H_ptr) s = H)
         (\s. read PC s = word (pc + 0x44) /\
              read X0 s = word_add Htable (word 16) /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q20 s = byteswap128(ghash_twist(byteswap128 H)) /\
              read (memory :> bytes128 Htable) s =
                byteswap128(ghash_twist(byteswap128 H)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `H_ptr:int64`; `H:int128`; `pc:num`] THEN
  GCM_BLOCK_STEPS_TAC 17 THEN
  REWRITE_TAC[byteswap128; ghash_twist; POLYVAL_TWIST_CONST] THEN
  BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 4: the H^2 block, PC 0x44 -> 0x9c.                                   *)
(*                                                                            *)
(*   H^2 = h_power h1 1 = polyval_dot h1 h1   (a SQUARE: mid via FROB64)       *)
(*                                                                            *)
(* Stores the H^1/H^2 Karatsuba-mid pack at Htable+16 and byteswap128(H^2) at *)
(* Htable+32.  Q19 holds Gueron's reduction constant w = 0xC2000000_00000000; *)
(* h1 is the internal (half-swapped) algebraic key of Phase 3.                *)
(*                                                                            *)
(* The postcondition also pins the two Karatsuba "folds" the block leaves     *)
(* live for the next block: Q16 = h1 (+) byteswap128 h1 and Q17 = H^2 (+)      *)
(* byteswap128 H^2 (each lane = the corresponding karatsuba_mid).  Those are   *)
(* the true hardware values at 0x9c, machine-checked by the same 22-step run,  *)
(* so the H^3/H^4 block need not re-derive them.                               *)
(*                                                                            *)
(* NOTE ON THE PACKED-MID ORDER: the routine writes                            *)
(*   word_join (karatsuba_mid H^2) (karatsuba_mid H^1),                        *)
(* i.e. the LOWER power's mid in the LOW 64 bits.  `htable_mem`'s packed-mid   *)
(* slots were corrected to that orientation on 2026-08-26; see                 *)
(* HTABLE_MEM_MID_LANES / HTABLE_MEM_KAT_FIRST3 above, which machine-check it. *)
(* ========================================================================= *)

let GCM_INIT_V8_H2 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x44) /\
              read X0 s = word_add Htable (word 16) /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q20 s = byteswap128 h1 /\
              read (memory :> bytes128 Htable) s = byteswap128 h1)
         (\s. read PC s = word (pc + 0x9c) /\
              read X0 s = word_add Htable (word 48) /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q20 s = byteswap128 h1 /\
              read Q22 s = byteswap128 (h_power h1 1) /\
              read Q16 s = word_xor h1 (byteswap128 h1) /\
              read Q17 s = word_xor (h_power h1 1) (byteswap128 (h_power h1 1)) /\
              read (memory :> bytes128 Htable) s = byteswap128 h1 /\
              read (memory :> bytes128 (word_add Htable (word 16))) s =
                word_join (karatsuba_mid (h_power h1 1)) (karatsuba_mid h1) /\
              read (memory :> bytes128 (word_add Htable (word 32))) s =
                byteswap128 (h_power h1 1))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `h1:int128`; `pc:num`] THEN
  GCM_BLOCK_STEPS_TAC 22 THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  SPEC_UNFOLD_TAC THEN
  REWRITE_TAC[FROB64] THEN
  SQUARE_TAC 2 `h1:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 5: the H^3 & H^4 block, PC 0x9c -> 0x134.                            *)
(*                                                                            *)
(*   H^3 = h_power h1 2 = polyval_dot h1 H^2   (Q20 . Q22: genuine mid)        *)
(*   H^4 = h_power h1 3 = polyval_dot H^2 H^2  (Q22 . Q22: a SQUARE)           *)
(*                                                                            *)
(* Stores byteswap128 H^3, the packed pair, and byteswap128 H^4 at Htable+48/  *)
(* +64/+80 via a single 3-register st1 (arm_STP3 at 0x130 -- the first proof   *)
(* use of the newly-modelled instruction).  The H^3 mid is pmull v16,v17 =     *)
(* fold h1 . fold H^2, already in PMUL_KARA's operand order, so no MID_SWAP.   *)
(*                                                                            *)
(* The postcondition exposes every register the H^5/H^6 block reads at 0x134   *)
(* plus the accumulated slots, so the blocks compose with no re-derivation.    *)
(* ========================================================================= *)

let GCM_INIT_V8_H34 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x9c) /\
              read X0 s = word_add Htable (word 48) /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q20 s = byteswap128 h1 /\
              read Q22 s = byteswap128 (h_power h1 1) /\
              read Q16 s = word_xor h1 (byteswap128 h1) /\
              read Q17 s = word_xor (h_power h1 1) (byteswap128 (h_power h1 1)) /\
              read (memory :> bytes128 Htable) s = byteswap128 h1 /\
              read (memory :> bytes128 (word_add Htable (word 16))) s =
                word_join (karatsuba_mid (h_power h1 1)) (karatsuba_mid h1) /\
              read (memory :> bytes128 (word_add Htable (word 32))) s =
                byteswap128 (h_power h1 1))
         (\s. read PC s = word (pc + 0x134) /\
              read X0 s = word_add Htable (word 96) /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q22 s = byteswap128 (h_power h1 1) /\
              read Q23 s = byteswap128 (h_power h1 2) /\
              read Q25 s = byteswap128 (h_power h1 3) /\
              read Q18 s = word_xor (h_power h1 1) (byteswap128 (h_power h1 1)) /\
              read Q3 s = word_xor (h_power h1 2) (byteswap128 (h_power h1 2)) /\
              read Q21 s = word_xor (h_power h1 3) (byteswap128 (h_power h1 3)) /\
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
  GCM_BLOCK_STEPS_TAC 38 THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  ABBREV_TAC `h2 = polyval_dot h1 h1` THEN
  SPEC_UNFOLD_TAC THEN
  REWRITE_TAC[FROB64] THEN
  PRODUCT_TAC 3 `h1:int128` `h2:int128` THEN
  SQUARE_TAC 4 `h2:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 6a: the H^5 & H^6 block, PC 0x134 -> 0x1c4.                          *)
(*                                                                            *)
(*   H^5 = h_power h1 4 = polyval_dot H^2 H^3  (Q22 . Q23: genuine mid)        *)
(*   H^6 = h_power h1 5 = polyval_dot H^3 H^3  (Q23 . Q23: a SQUARE)           *)
(*                                                                            *)
(* Stores the three words at Htable+96/+112/+128 via one 3-register st1        *)
(* (arm_STP3 at 0x1c0).  0x134..0x1c0 never writes below +96, so the six lower *)
(* slots thread through for free and are carried in the pre/postcondition.     *)
(*                                                                            *)
(* The H^3 and H^4 multiplicands (Q23/Q25) and their Karatsuba folds (Q3/Q21)  *)
(* are UNTOUCHED here and are carried through the pre/postcondition: with the  *)
(* depth-3 chain the NEXT block (H^7 = H^3.H^4, H^8 = H^4.H^4) consumes them   *)
(* rather than this block's outputs, which is exactly what lets the two blocks *)
(* overlap in the machine's out-of-order window.                               *)
(*                                                                            *)
(* ONE wrinkle over Phase 5: the hardware forms the H^5 middle as              *)
(* pmull v3,v18 = (fold H^3).(fold H^2), the OPPOSITE operand order to         *)
(* PMUL_KARA's decomposition of H^2 . H^3, so it needs a MID_SWAP.             *)
(* ========================================================================= *)

let GCM_INIT_V8_H56 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x134) /\
              read X0 s = word_add Htable (word 96) /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q22 s = byteswap128 (h_power h1 1) /\
              read Q23 s = byteswap128 (h_power h1 2) /\
              read Q25 s = byteswap128 (h_power h1 3) /\
              read Q18 s = word_xor (h_power h1 1) (byteswap128 (h_power h1 1)) /\
              read Q3 s = word_xor (h_power h1 2) (byteswap128 (h_power h1 2)) /\
              read Q21 s = word_xor (h_power h1 3) (byteswap128 (h_power h1 3)) /\
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
         (\s. read PC s = word (pc + 0x1c4) /\
              read X0 s = word_add Htable (word 144) /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q23 s = byteswap128 (h_power h1 2) /\
              read Q25 s = byteswap128 (h_power h1 3) /\
              read Q3 s = word_xor (h_power h1 2) (byteswap128 (h_power h1 2)) /\
              read Q21 s = word_xor (h_power h1 3) (byteswap128 (h_power h1 3)) /\
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
                byteswap128 (h_power h1 5))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `h1:int128`; `pc:num`] THEN
  GCM_BLOCK_STEPS_TAC 36 THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  MAP_EVERY ABBREV_TAC
   [`h2 = polyval_dot h1 h1`; `h3 = polyval_dot h1 h2`] THEN
  SPEC_UNFOLD_TAC THEN
  REWRITE_TAC[FROB64] THEN
  REWRITE_TAC[MID_SWAP `h2:int128` `h3:int128`] THEN
  PRODUCT_TAC 5 `h2:int128` `h3:int128` THEN
  SQUARE_TAC 6 `h3:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 6b: the H^7 & H^8 block, PC 0x1c4 -> 0x254 (ends at the ret).        *)
(*                                                                            *)
(*   H^7 = h_power h1 6 = polyval_dot H^3 H^4  (Q23 . Q25: genuine mid)       *)
(*   H^8 = h_power h1 7 = polyval_dot H^4 H^4  (Q25 . Q25: a SQUARE)          *)
(*                                                                            *)
(* This is the DEPTH-3 form of the addition chain: both powers are built from  *)
(* H^3/H^4 (produced by Phase 5) rather than from H^5/H^6 (Phase 6a), so this  *)
(* block does not depend on Phase 6a at all and the two overlap on the         *)
(* machine.  Structurally it is now the SAME shape as Phase 5 -- one genuine-  *)
(* mid product plus one square -- so it needs FROB64 for H^8 and no MID_SWAP   *)
(* at all: the hardware mid pmull is (fold H^3).(fold H^4), already PMUL_KARA's *)
(* operand order for H^3 . H^4.  Stores the three words at                     *)
(* Htable+144/+160/+176 via the final 3-register st1 (arm_STP3 at 0x250, NO    *)
(* post-index -- X0 stays Htable+144).  Symbolic execution ends at the ret     *)
(* (0x254); the ret is handled by the Phase 8 subroutine wrapper.              *)
(*                                                                            *)
(* The postcondition carries ALL TWELVE slots, so Phase 7 reads the full       *)
(* htable_mem table straight off this block's post.                            *)
(* ========================================================================= *)

let GCM_INIT_V8_H78 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x1c4) /\
              read X0 s = word_add Htable (word 144) /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q23 s = byteswap128 (h_power h1 2) /\
              read Q25 s = byteswap128 (h_power h1 3) /\
              read Q3 s = word_xor (h_power h1 2) (byteswap128 (h_power h1 2)) /\
              read Q21 s = word_xor (h_power h1 3) (byteswap128 (h_power h1 3)) /\
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
                byteswap128 (h_power h1 5))
         (\s. read PC s = word (pc + 0x254) /\
              read X0 s = word_add Htable (word 144) /\
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
  GCM_BLOCK_STEPS_TAC 36 THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  MAP_EVERY ABBREV_TAC
   [`h2 = polyval_dot h1 h1`; `h3 = polyval_dot h1 h2`;
    `h4 = polyval_dot h2 h2`] THEN
  SPEC_UNFOLD_TAC THEN
  REWRITE_TAC[FROB64] THEN
  PRODUCT_TAC 7 `h3:int128` `h4:int128` THEN
  SQUARE_TAC 8 `h4:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 7: the core correctness theorem, GCM_INIT_V8_CORRECT.                *)
(*                                                                            *)
(* Compose the five blocks into one `ensures` from function entry (PC 0x0) to *)
(* the `ret` (PC 0x254), establishing the full 12-slot htable_mem             *)
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
(* memory :> bytelist(word pc,600).  Its ORTHOGONAL_COMPONENTS_TAC scans the  *)
(* assumptions for a RAW `nonoverlapping (word pc,600) (Htable,192)` driver    *)
(* and needs the length CONCRETE (600).  Hence: reduce LENGTH gcm_init_v8_mc   *)
(* to 600 via `fst GCM_INIT_V8_EXEC` in the setup rewrite, and do NOT rewrite  *)
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
         (\s. read PC s = word (pc + 0x254) /\
              htable_mem (ghash_twist(byteswap128 H)) Htable s)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `H_ptr:int64`; `H:int128`; `pc:num`] THEN
  MAYCHANGE_EXPAND_TAC THEN
  STRIP_TAC THEN
  MP_TAC(SPECL[`Htable:int64`;`H_ptr:int64`;`H:int128`;`pc:num`]
              GCM_INIT_V8_TWIST) THEN
  MAYCHANGE_EXPAND_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC(!simulation_precanon_thms) THEN
                       ENSURES_INIT_TAC "s0" THEN MP_TAC th) THEN
  ARM_BIGSTEP_TAC GCM_INIT_V8_EXEC "s1" THEN
  GCM_BLOCK_STEP_TAC "s2" GCM_INIT_V8_H2 THEN
  GCM_BLOCK_STEP_TAC "s3" GCM_INIT_V8_H34 THEN
  GCM_BLOCK_STEP_TAC "s4" GCM_INIT_V8_H56 THEN
  GCM_BLOCK_STEP_TAC "s5" GCM_INIT_V8_H78 THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[htable_mem; CONJUNCT1 h_power]);;

(* ========================================================================= *)
(* Phase 8: the standard-ABI subroutine wrapper (leaf, no stack frame).       *)
(*                                                                            *)
(* Wrap the core with the return via X30.  Two mechanical points:             *)
(*  - Reduce LENGTH gcm_init_v8_mc to 600 (`fst GCM_INIT_V8_EXEC`) in the goal *)
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
