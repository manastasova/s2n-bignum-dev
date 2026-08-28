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
(* blocks tiling PC 0x0..0x1c4 -- the twist, then four power blocks computing  *)
(* two of H^2..H^8 each -- composed by ARM_BIGSTEP_TAC into                    *)
(* GCM_INIT_V8_CORRECT.  The four power blocks differ only in which Q         *)
(* registers and which powers they touch, so ALL their algebra lives once in   *)
(* the two toolkit sections below and each block's script is the same six      *)
(* steps.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/polyval_ghash.ml";;
needs "common/karatsuba_pmul.ml";;      (* PMUL_SCHOOLBOOK; ~0.5s on top of the above *)

(**** print_literal_from_elf "arm/gcm/gcm_init_v8.o";;
 ****)

let gcm_init_v8_mc = define_assert_from_elf
 "gcm_init_v8_mc" "arm/gcm/gcm_init_v8.o"
[
  0x4c407c31;       (* arm_LDR Q17 X1 No_Offset *)
  0x4f07e433;       (* arm_MOVI Q19 (word 16276538888567251425) *)
  0x4f00e402;       (* arm_MOVI Q2 (word 0) *)
  0x4f795673;       (* arm_SHL_VEC Q19 Q19 57 64 128 *)
  0x6f410632;       (* arm_USHR_VEC Q18 Q17 63 64 128 *)
  0x4f410623;       (* arm_SSHR_VEC Q3 Q17 63 64 128 *)
  0x6e024270;       (* arm_EXT Q16 Q19 Q2 64 *)
  0x4f415634;       (* arm_SHL_VEC Q20 Q17 1 64 128 *)
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0x4e231e10;       (* arm_AND_VEC Q16 Q16 Q3 128 *)
  0x4eb21e94;       (* arm_ORR_VEC Q20 Q20 Q18 128 *)
  0x6e301e94;       (* arm_EOR_VEC Q20 Q20 Q16 128 *)
  0x6e144283;       (* arm_EXT Q3 Q20 Q20 64 *)
  0x4ef4e280;       (* arm_PMULL2_VEC Q0 Q20 Q20 64 *)
  0x6e341c70;       (* arm_EOR_VEC Q16 Q3 Q20 128 *)
  0x0ef4e282;       (* arm_PMULL_VEC Q2 Q20 Q20 64 *)
  0x6e004001;       (* arm_EXT Q1 Q0 Q0 64 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c11;       (* arm_EOR_VEC Q17 Q0 Q18 128 *)
  0x6e114236;       (* arm_EXT Q22 Q17 Q17 64 *)
  0x6e361e21;       (* arm_EOR_VEC Q1 Q17 Q22 128 *)
  0x6e014215;       (* arm_EXT Q21 Q16 Q1 64 *)
  0xad005414;       (* arm_STP Q20 Q21 X0 (Immediate_Offset (iword (&0))) *)
  0x0ef1e060;       (* arm_PMULL_VEC Q0 Q3 Q17 64 *)
  0x4ef1e062;       (* arm_PMULL2_VEC Q2 Q3 Q17 64 *)
  0x4ef1e281;       (* arm_PMULL2_VEC Q1 Q20 Q17 64 *)
  0x0ef1e290;       (* arm_PMULL_VEC Q16 Q20 Q17 64 *)
  0x0ef1e225;       (* arm_PMULL_VEC Q5 Q17 Q17 64 *)
  0x4ef1e227;       (* arm_PMULL2_VEC Q7 Q17 Q17 64 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e004010;       (* arm_EXT Q16 Q0 Q0 64 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e014032;       (* arm_EXT Q18 Q1 Q1 64 *)
  0x0ef3e021;       (* arm_PMULL_VEC Q1 Q1 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c35;       (* arm_EOR_VEC Q21 Q1 Q18 128 *)
  0x6e0540a6;       (* arm_EXT Q6 Q5 Q5 64 *)
  0x0ef3e0a4;       (* arm_PMULL_VEC Q4 Q5 Q19 64 *)
  0x6e241cc5;       (* arm_EOR_VEC Q5 Q6 Q4 128 *)
  0x6e0540a4;       (* arm_EXT Q4 Q5 Q5 64 *)
  0x0ef3e0a5;       (* arm_PMULL_VEC Q5 Q5 Q19 64 *)
  0x6e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 128 *)
  0x6e241cb4;       (* arm_EOR_VEC Q20 Q5 Q4 128 *)
  0x6e1542b7;       (* arm_EXT Q23 Q21 Q21 64 *)
  0x6e144299;       (* arm_EXT Q25 Q20 Q20 64 *)
  0x6e371eb0;       (* arm_EOR_VEC Q16 Q21 Q23 128 *)
  0x6e391e92;       (* arm_EOR_VEC Q18 Q20 Q25 128 *)
  0x6e124218;       (* arm_EXT Q24 Q16 Q18 64 *)
  0xad015c16;       (* arm_STP Q22 Q23 X0 (Immediate_Offset (iword (&32))) *)
  0xad026418;       (* arm_STP Q24 Q25 X0 (Immediate_Offset (iword (&64))) *)
  0x0ef5e220;       (* arm_PMULL_VEC Q0 Q17 Q21 64 *)
  0x4ef5e222;       (* arm_PMULL2_VEC Q2 Q17 Q21 64 *)
  0x4ef5e2c1;       (* arm_PMULL2_VEC Q1 Q22 Q21 64 *)
  0x0ef5e2d0;       (* arm_PMULL_VEC Q16 Q22 Q21 64 *)
  0x0ef5e2a5;       (* arm_PMULL_VEC Q5 Q21 Q21 64 *)
  0x4ef5e2a7;       (* arm_PMULL2_VEC Q7 Q21 Q21 64 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e004010;       (* arm_EXT Q16 Q0 Q0 64 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e014032;       (* arm_EXT Q18 Q1 Q1 64 *)
  0x0ef3e021;       (* arm_PMULL_VEC Q1 Q1 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c30;       (* arm_EOR_VEC Q16 Q1 Q18 128 *)
  0x6e0540a6;       (* arm_EXT Q6 Q5 Q5 64 *)
  0x0ef3e0a4;       (* arm_PMULL_VEC Q4 Q5 Q19 64 *)
  0x6e241cc5;       (* arm_EOR_VEC Q5 Q6 Q4 128 *)
  0x6e0540a4;       (* arm_EXT Q4 Q5 Q5 64 *)
  0x0ef3e0a5;       (* arm_PMULL_VEC Q5 Q5 Q19 64 *)
  0x6e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 128 *)
  0x6e241cb1;       (* arm_EOR_VEC Q17 Q5 Q4 128 *)
  0x6e10421a;       (* arm_EXT Q26 Q16 Q16 64 *)
  0x6e11423c;       (* arm_EXT Q28 Q17 Q17 64 *)
  0x6e3a1e10;       (* arm_EOR_VEC Q16 Q16 Q26 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e11421b;       (* arm_EXT Q27 Q16 Q17 64 *)
  0xad036c1a;       (* arm_STP Q26 Q27 X0 (Immediate_Offset (iword (&96))) *)
  0x0ef5e280;       (* arm_PMULL_VEC Q0 Q20 Q21 64 *)
  0x4ef5e282;       (* arm_PMULL2_VEC Q2 Q20 Q21 64 *)
  0x4ef5e321;       (* arm_PMULL2_VEC Q1 Q25 Q21 64 *)
  0x0ef5e330;       (* arm_PMULL_VEC Q16 Q25 Q21 64 *)
  0x0ef4e285;       (* arm_PMULL_VEC Q5 Q20 Q20 64 *)
  0x4ef4e287;       (* arm_PMULL2_VEC Q7 Q20 Q20 64 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e004010;       (* arm_EXT Q16 Q0 Q0 64 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e014032;       (* arm_EXT Q18 Q1 Q1 64 *)
  0x0ef3e021;       (* arm_PMULL_VEC Q1 Q1 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c30;       (* arm_EOR_VEC Q16 Q1 Q18 128 *)
  0x6e0540a6;       (* arm_EXT Q6 Q5 Q5 64 *)
  0x0ef3e0a4;       (* arm_PMULL_VEC Q4 Q5 Q19 64 *)
  0x6e241cc5;       (* arm_EOR_VEC Q5 Q6 Q4 128 *)
  0x6e0540a4;       (* arm_EXT Q4 Q5 Q5 64 *)
  0x0ef3e0a5;       (* arm_PMULL_VEC Q5 Q5 Q19 64 *)
  0x6e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 128 *)
  0x6e241cb1;       (* arm_EOR_VEC Q17 Q5 Q4 128 *)
  0x6e10421d;       (* arm_EXT Q29 Q16 Q16 64 *)
  0x6e11423f;       (* arm_EXT Q31 Q17 Q17 64 *)
  0x6e3d1e10;       (* arm_EOR_VEC Q16 Q16 Q29 128 *)
  0x6e3f1e31;       (* arm_EOR_VEC Q17 Q17 Q31 128 *)
  0x6e11421e;       (* arm_EXT Q30 Q16 Q17 64 *)
  0xad04741c;       (* arm_STP Q28 Q29 X0 (Immediate_Offset (iword (&128))) *)
  0xad057c1e;       (* arm_STP Q30 Q31 X0 (Immediate_Offset (iword (&160))) *)
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
    (!x:64 word. word_xor (word 0) x = x)`) in
  TOP_DEPTH_CONV
   (FIRST_CONV (map REWR_CONV (shl_lanes @ zero_lanes @ ins_lanes @ xor_0) @
                [WORD_SIMPLE_SUBWORD_CONV; REWR_CONV WORD_SUBWORD_XOR]));;

(* Both sides' Gueron pmul-by-w arguments are the SAME XOR of 64-bit lanes      *)
(* written in different orders and associations (the hardware's order is the one *)
(* the instruction schedule happens to produce, the spec's is the one            *)
(* polyval_reduce_prop3 produces).  Rather than a directed rewrite per shape,    *)
(* CANONICALIZE every `word_pmul <64-bit xor chain> w`: flatten the chain, sort  *)
(* it, rebuild it, and justify the step with WORD_BITWISE_RULE.  After this the  *)
(* two sides' pmul-by-w terms are LITERALLY EQUAL, so they are automatically the *)
(* same opaque atom for the per-lane close and no atom has to be abbreviated for *)
(* them at all.  It fails when already canonical, so it terminates under         *)
(* ONCE_DEPTH_CONV.                                                             *)
let PMUL_W_CANON_CONV =
  let wtm = `(word 13979173243358019584):64 word`
  and xor64 = `word_xor:(64)word->(64)word->(64)word`
  and ty64 = `:(64)word` in
  let rec flat tm =
    match tm with
      Comb(Comb(op,l),r) when op = xor64 -> flat l @ flat r
    | _ -> [tm] in
  let build l = end_itlist (fun a b -> mk_comb(mk_comb(xor64,a),b)) l in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_pmul",_),a),b) when b = wtm && type_of a = ty64 ->
        let a' = build (sort (<) (flat a)) in
        if a' = a then failwith "PMUL_W_CANON_CONV: already canonical"
        else AP_THM (AP_TERM (rator (rator tm))
                             (WORD_BITWISE_RULE (mk_eq(a,a')))) b
    | _ -> failwith "PMUL_W_CANON_CONV";;

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
  CONV_TAC(ONCE_DEPTH_CONV PMUL_W_CANON_CONV) THEN
  CONV_TAC WORD_BITWISE_RULE;;

(* Name the opaque atoms of ONE of a block's two carryless products.  For       *)
(* product `k` of operands a,b:                                                 *)
(*   PL<k>, PH<k>  the two "straight" 64x64 half-products a_lo.b_lo, a_hi.b_hi,  *)
(*   C1<k>, C2<k>  the two CROSS products a_lo.b_hi, a_hi.b_lo -- present only   *)
(*                 when the operands DIFFER, since for a square SQ_CROSS_0 has   *)
(*                 already killed the whole middle,                             *)
(*   QA<k>         the first-phase Gueron pmul-by-w result.                      *)
(* The SECOND-phase pmul-by-w needs no atom: PMUL_W_CANON_CONV makes the         *)
(* hardware's and the spec's copies of it literally the same term.  Once both    *)
(* products have been through this the goal is PMUL-FREE over these atoms and    *)
(* LANE_CLOSE_TAC finishes.  Everything power-specific about a block lives in    *)
(* the two calls to PRODUCT_TAC / SQUARE_TAC below.                              *)
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

(* ========================================================================= *)
(* Phase 3: the twist (PC 0x0 -> 0x30).                                       *)
(*                                                                            *)
(* The first 12 instructions load the raw 128-bit hash key H from [X1] and    *)
(* compute the x-twist DIRECTLY IN STORE-LANE ORDER.  (The AWS-LC original    *)
(* did the shift in algebraic lane order and paid an `ext` at each end; both   *)
(* are gone -- the reduction constant is simply built with its two lanes       *)
(* swapped, `ext v16,v19,v1,#8` instead of `ext v16,v1,v19,#8`.)  Nothing is   *)
(* stored yet: Htable[0] goes out with Htable[1] in one `stp` at the end of    *)
(* Phase 4, and X0 is never modified (all stores use immediate offsets).      *)
(*                                                                            *)
(* HALF-SWAP BYTE-ORDER CONVENTION (the linchpin of the whole proof):         *)
(*                                                                            *)
(*   Let  H  = read (memory :> bytes128 H_ptr) s   be the raw little-endian   *)
(*   128-bit value in memory.  `byteswap128` swaps the two 64-bit halves      *)
(*   (word0 <-> word1).  Then                                                 *)
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
(*   broadcasts exactly that bit via `dup v3.4s,v17.s[1]` + `sshr ...,#31`.    *)
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
         (\s. read PC s = word (pc + 0x30) /\
              read X0 s = Htable /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q20 s = byteswap128(ghash_twist(byteswap128 H)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `H_ptr:int64`; `H:int128`; `pc:num`] THEN
  GCM_BLOCK_STEPS_TAC 12 THEN
  REWRITE_TAC[byteswap128; ghash_twist; POLYVAL_TWIST_CONST] THEN
  BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 4: the H^2 block, PC 0x30 -> 0x6c.                                   *)
(*                                                                            *)
(*   H^2 = h_power h1 1 = polyval_dot h1 h1   (a SQUARE)                       *)
(*                                                                            *)
(* SQUARING IS FROBENIUS, so this block has NO middle product at all.  In       *)
(* GF(2)[x] the two schoolbook cross products of a . a are equal, so their XOR  *)
(* -- the whole middle 128 bits -- is ZERO (SQ_CROSS_0) and the 256-bit square  *)
(* is exactly p_lo + p_hi*x^128.  The routine therefore takes the product's low *)
(* half to be p_lo (its word-swap is a single `ext v1,v0,v0,#8`) and its high    *)
(* half to be p_hi untouched, and emits only the two `pmull`s by w (Gueron's    *)
(* two reduction phases).                                                      *)
(*                                                                            *)
(* Stores Htable[0..1] with one `stp q20,q21,[x0]`; X0 is not modified.  Q19    *)
(* holds Gueron's reduction constant w = 0xC2000000_00000000; h1 is the         *)
(* internal (half-swapped) algebraic key of Phase 3.                           *)
(*                                                                            *)
(* THE TWO REPRESENTATIONS.  From here on every power is kept in BOTH forms:    *)
(* the ALGEBRAIC one (Q3 = h1, Q17 = H^2, ...), which is what the reduction     *)
(* naturally produces and what the next multiply's `pmull`/`pmull2` read, and   *)
(* the BYTESWAPPED one (Q20, Q22, ...), which is what the table stores and what *)
(* the next multiply's CROSS products read.  Keeping both is what removes the   *)
(* `ext`+`eor` Karatsuba fold from the multiply's dependency path.              *)
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
              read PC s = word (pc + 0x30) /\
              read X0 s = Htable /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q20 s = byteswap128 h1)
         (\s. read PC s = word (pc + 0x6c) /\
              read X0 s = Htable /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q3 s = h1 /\
              read Q17 s = h_power h1 1 /\
              read Q20 s = byteswap128 h1 /\
              read Q22 s = byteswap128 (h_power h1 1) /\
              read (memory :> bytes128 Htable) s = byteswap128 h1 /\
              read (memory :> bytes128 (word_add Htable (word 16))) s =
                word_join (karatsuba_mid (h_power h1 1)) (karatsuba_mid h1))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `h1:int128`; `pc:num`] THEN
  GCM_BLOCK_STEPS_TAC 15 THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  SPEC_UNFOLD_TAC THEN
  SQUARE_TAC 2 `h1:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 5: the H^3 & H^4 block, PC 0x6c -> 0xe0.                             *)
(*                                                                            *)
(*   H^3 = h_power h1 2 = polyval_dot h1 H^2   (genuine: 4 schoolbook products) *)
(*   H^4 = h_power h1 3 = polyval_dot H^2 H^2  (a SQUARE: middle vanishes)      *)
(*                                                                            *)
(* All six `pmull`s issue off values that are live BEFORE the block: the two    *)
(* straight products from the algebraic Q3/Q17, the two cross products from the *)
(* byteswapped Q20 and the algebraic Q17 (`pmull2 Q20.2d,Q17.2d` is a_lo.b_hi   *)
(* because byteswapping swaps the lanes), and the square's two from Q17.  No    *)
(* Karatsuba fold is on the multiply path at all, which is the whole point of   *)
(* the schoolbook form; the folds are still computed, but only to build the      *)
(* packed-mid table word, which is off the critical path.                       *)
(*                                                                            *)
(* Stores Htable[2..5] with two `stp`s at immediate offsets +32 and +64 (X0 is  *)
(* never modified).  H^3 lands in Q21 and H^4 in Q20 -- Q20's byteswapped H^1   *)
(* is dead once this block's cross products have read it, and Q21's Htable[1]   *)
(* pack word is dead once Phase 4 stored it -- so both powers stay live in the  *)
(* algebraic form the next two blocks need, with byteswap128 H^4 in Q25.        *)
(* ========================================================================= *)

let GCM_INIT_V8_H34 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x6c) /\
              read X0 s = Htable /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q3 s = h1 /\
              read Q17 s = h_power h1 1 /\
              read Q20 s = byteswap128 h1 /\
              read Q22 s = byteswap128 (h_power h1 1) /\
              read (memory :> bytes128 Htable) s = byteswap128 h1 /\
              read (memory :> bytes128 (word_add Htable (word 16))) s =
                word_join (karatsuba_mid (h_power h1 1)) (karatsuba_mid h1))
         (\s. read PC s = word (pc + 0xe0) /\
              read X0 s = Htable /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q17 s = h_power h1 1 /\
              read Q21 s = h_power h1 2 /\
              read Q20 s = h_power h1 3 /\
              read Q22 s = byteswap128 (h_power h1 1) /\
              read Q25 s = byteswap128 (h_power h1 3) /\
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
  GCM_BLOCK_STEPS_TAC 29 THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  ABBREV_TAC `h2 = polyval_dot h1 h1` THEN
  SPEC_UNFOLD_TAC THEN
  PRODUCT_TAC 3 `h1:int128` `h2:int128` THEN
  SQUARE_TAC 4 `h2:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 6a: the H^5 & H^6 block, PC 0xe0 -> 0x150.                           *)
(*                                                                            *)
(*   H^5 = h_power h1 4 = polyval_dot H^2 H^3  (genuine)                       *)
(*   H^6 = h_power h1 5 = polyval_dot H^3 H^3  (a SQUARE)                      *)
(*                                                                            *)
(* Stores Htable[6..7] (`stp q26,q27,[x0,#96]`); byteswap128 H^6 stays in Q28   *)
(* and is written by the NEXT block's `stp q28,q29,[x0,#128]`, so Q28 is        *)
(* carried in the postcondition.  0xe0..0x150 never writes below +96, so the    *)
(* six lower slots thread through for free.                                    *)
(*                                                                            *)
(* H^5 and H^6 are never multiplied by anything, so they may live in this       *)
(* block's scratch registers; what MUST survive it are H^3 (Q21) and H^4        *)
(* (Q20/Q25), because the depth-3 chain has the NEXT block build H^7 and H^8    *)
(* out of those rather than out of this block's outputs -- which is exactly     *)
(* what lets the two blocks overlap in the machine's out-of-order window.      *)
(* ========================================================================= *)

let GCM_INIT_V8_H56 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0xe0) /\
              read X0 s = Htable /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q17 s = h_power h1 1 /\
              read Q21 s = h_power h1 2 /\
              read Q20 s = h_power h1 3 /\
              read Q22 s = byteswap128 (h_power h1 1) /\
              read Q25 s = byteswap128 (h_power h1 3) /\
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
         (\s. read PC s = word (pc + 0x150) /\
              read X0 s = Htable /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q21 s = h_power h1 2 /\
              read Q20 s = h_power h1 3 /\
              read Q25 s = byteswap128 (h_power h1 3) /\
              read Q28 s = byteswap128 (h_power h1 5) /\
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
                word_join (karatsuba_mid (h_power h1 5)) (karatsuba_mid (h_power h1 4)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `h1:int128`; `pc:num`] THEN
  GCM_BLOCK_STEPS_TAC 28 THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  MAP_EVERY ABBREV_TAC
   [`h2 = polyval_dot h1 h1`; `h3 = polyval_dot h1 h2`] THEN
  SPEC_UNFOLD_TAC THEN
  PRODUCT_TAC 5 `h2:int128` `h3:int128` THEN
  SQUARE_TAC 6 `h3:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 6b: the H^7 & H^8 block, PC 0x150 -> 0x1c4 (ends at the ret).        *)
(*                                                                            *)
(*   H^7 = h_power h1 6 = polyval_dot H^4 H^3  (genuine)                      *)
(*   H^8 = h_power h1 7 = polyval_dot H^4 H^4  (a SQUARE)                     *)
(*                                                                            *)
(* This is the DEPTH-3 form of the addition chain: both powers are built from   *)
(* H^3/H^4 (Phase 5) rather than from H^5/H^6 (Phase 6a), so this block does    *)
(* not depend on Phase 6a at all and the two overlap on the machine.  H^7 is    *)
(* stated as H^4 . H^3 (not H^3 . H^4) because the FRESHER operand has to be    *)
(* the one supplying the algebraic lanes: the cross products read the OTHER     *)
(* operand's byteswapped copy, and only H^4's (Q25) is in the table.            *)
(* Stores Htable[8..11] with the last two `stp`s (+128, +160).  Symbolic        *)
(* execution ends at the ret (0x1c4); the ret is handled by the Phase 8         *)
(* subroutine wrapper.                                                        *)
(*                                                                            *)
(* The postcondition carries ALL TWELVE slots, so Phase 7 reads the full        *)
(* htable_mem table straight off this block's post.                            *)
(* ========================================================================= *)

let GCM_INIT_V8_H78 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x150) /\
              read X0 s = Htable /\
              read Q19 s = word 0xc200000000000000c200000000000000 /\
              read Q21 s = h_power h1 2 /\
              read Q20 s = h_power h1 3 /\
              read Q25 s = byteswap128 (h_power h1 3) /\
              read Q28 s = byteswap128 (h_power h1 5) /\
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
                word_join (karatsuba_mid (h_power h1 5)) (karatsuba_mid (h_power h1 4)))
         (\s. read PC s = word (pc + 0x1c4) /\
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
  GCM_BLOCK_STEPS_TAC 29 THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  MAP_EVERY ABBREV_TAC
   [`h2 = polyval_dot h1 h1`; `h3 = polyval_dot h1 h2`;
    `h4 = polyval_dot h2 h2`] THEN
  SPEC_UNFOLD_TAC THEN
  PRODUCT_TAC 7 `h4:int128` `h3:int128` THEN
  SQUARE_TAC 8 `h4:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 7: the core correctness theorem, GCM_INIT_V8_CORRECT.                *)
(*                                                                            *)
(* Compose the five blocks into one `ensures` from function entry (PC 0x0) to *)
(* the `ret` (PC 0x1c4), establishing the full 12-slot htable_mem             *)
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
(* memory :> bytelist(word pc,456).  Its ORTHOGONAL_COMPONENTS_TAC scans the  *)
(* assumptions for a RAW `nonoverlapping (word pc,456) (Htable,192)` driver    *)
(* and needs the length CONCRETE (456).  Hence: reduce LENGTH gcm_init_v8_mc   *)
(* to 456 via `fst GCM_INIT_V8_EXEC` in the setup rewrite, and do NOT rewrite  *)
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
         (\s. read PC s = word (pc + 0x1c4) /\
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
(*  - Reduce LENGTH gcm_init_v8_mc to 456 (`fst GCM_INIT_V8_EXEC`) in the goal *)
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
