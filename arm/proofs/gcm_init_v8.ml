(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* GCM_INIT_V8: expand the GHASH hash key H into the PMULL/v8 power table.    *)
(* Correctness against the POLYVAL/GHASH algebraic spec in                    *)
(* common/polyval_ghash.ml.  X0 = Htable (192 bytes written), X1 = H.         *)
(*                                                                            *)
(* Layout: the routine is branch-free, so the proof is three straight-line     *)
(* blocks tiling PC 0x0..0x1ec, composed by ARM_BIGSTEP_TAC into              *)
(* GCM_INIT_V8_CORRECT:                                                       *)
(*                                                                            *)
(*   0x0   -> 0x64   the fused twist + H^2                    (25 steps)       *)
(*   0x64  -> 0x1c4  H^3..H^8 + Htable[0..5]                  (88 steps)       *)
(*   0x1c4 -> 0x1ec  the closing packs and Htable[6..11]      (10 steps)       *)
(*                                                                            *)
(* The .S's instruction ORDER is a hardware-scored search over topological     *)
(* orders of its whole RAW dependence graph, with the SIMD registers allocated *)
(* by linear scan over that order (see the .S header), so all six power chains *)
(* INTERLEAVE and the block boundaries are the only two interior PCs at which  *)
(* every live value is a named power, byteswap or fold.  That is the only      *)
(* thing the tiling depends on -- the algebra is unchanged, so ALL of it still *)
(* lives once in the two toolkit sections below and each block's script is     *)
(* still just steps + SPEC_UNFOLD_TAC + one PRODUCT_TAC/SQUARE_TAC per product *)
(* + LANE_CLOSE_TAC.  Six powers land in ONE block because the search's order  *)
(* leaves no cut between them; see the Phase 2 header.                        *)
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
  0x4f795422;       (* arm_SHL_VEC Q2 Q1 57 64 128 *)
  0x6f410401;       (* arm_USHR_VEC Q1 Q0 63 64 128 *)
  0xd37ff864;       (* arm_LSL X4 X3 1 *)
  0x9e670083;       (* arm_FMOV_ItoF Q3 X4 0 *)
  0x4f415404;       (* arm_SHL_VEC Q4 Q0 1 64 128 *)
  0x0ee3e060;       (* arm_PMULL_VEC Q0 Q3 Q3 64 *)
  0x0ee4e083;       (* arm_PMULL_VEC Q3 Q4 Q4 64 *)
  0x6e014025;       (* arm_EXT Q5 Q1 Q1 64 *)
  0x4ee2e006;       (* arm_PMULL2_VEC Q6 Q0 Q2 64 *)
  0x0ee2e007;       (* arm_PMULL_VEC Q7 Q0 Q2 64 *)
  0x4ea51c90;       (* arm_ORR_VEC Q16 Q4 Q5 128 *)
  0x6e0740e4;       (* arm_EXT Q4 Q7 Q7 64 *)
  0x0ee2e0f1;       (* arm_PMULL_VEC Q17 Q7 Q2 64 *)
  0x0ee2e027;       (* arm_PMULL_VEC Q7 Q1 Q2 64 *)
  0x6e251c32;       (* arm_EOR_VEC Q18 Q1 Q5 128 *)
  0x6e231c01;       (* arm_EOR_VEC Q1 Q0 Q3 128 *)
  0x6e271e00;       (* arm_EOR_VEC Q0 Q16 Q7 128 *)
  0x4ec72a43;       (* arm_TRN1 Q3 Q18 Q7 64 128 *)
  0x6e211cc5;       (* arm_EOR_VEC Q5 Q6 Q1 128 *)
  0x6e311c81;       (* arm_EOR_VEC Q1 Q4 Q17 128 *)
  0x6e251c64;       (* arm_EOR_VEC Q4 Q3 Q5 128 *)
  0x6e241c23;       (* arm_EOR_VEC Q3 Q1 Q4 128 *)
  0x6e004001;       (* arm_EXT Q1 Q0 Q0 64 *)
  0x0ee3e064;       (* arm_PMULL_VEC Q4 Q3 Q3 64 *)
  0x0ee3e005;       (* arm_PMULL_VEC Q5 Q0 Q3 64 *)
  0x4ee3e006;       (* arm_PMULL2_VEC Q6 Q0 Q3 64 *)
  0x4ee3e067;       (* arm_PMULL2_VEC Q7 Q3 Q3 64 *)
  0x6e034070;       (* arm_EXT Q16 Q3 Q3 64 *)
  0x4ee3e031;       (* arm_PMULL2_VEC Q17 Q1 Q3 64 *)
  0x0ee3e032;       (* arm_PMULL_VEC Q18 Q1 Q3 64 *)
  0x0ee2e093;       (* arm_PMULL_VEC Q19 Q4 Q2 64 *)
  0x6e251cd4;       (* arm_EOR_VEC Q20 Q6 Q5 128 *)
  0x0ee2e265;       (* arm_PMULL_VEC Q5 Q19 Q2 64 *)
  0x4ee2e086;       (* arm_PMULL2_VEC Q6 Q4 Q2 64 *)
  0x6e271c95;       (* arm_EOR_VEC Q21 Q4 Q7 128 *)
  0x6e124244;       (* arm_EXT Q4 Q18 Q18 64 *)
  0x0ee2e247;       (* arm_PMULL_VEC Q7 Q18 Q2 64 *)
  0x6e134272;       (* arm_EXT Q18 Q19 Q19 64 *)
  0x6e144293;       (* arm_EXT Q19 Q20 Q20 64 *)
  0x0ee2e296;       (* arm_PMULL_VEC Q22 Q20 Q2 64 *)
  0x6e261eb4;       (* arm_EOR_VEC Q20 Q21 Q6 128 *)
  0x4ec32806;       (* arm_TRN1 Q6 Q0 Q3 64 128 *)
  0x4ec36815;       (* arm_TRN2 Q21 Q0 Q3 64 128 *)
  0x6e351cc3;       (* arm_EOR_VEC Q3 Q6 Q21 128 *)
  0x6e271c86;       (* arm_EOR_VEC Q6 Q4 Q7 128 *)
  0x6e251e44;       (* arm_EOR_VEC Q4 Q18 Q5 128 *)
  0x6e331ec5;       (* arm_EOR_VEC Q5 Q22 Q19 128 *)
  0xad000c00;       (* arm_STP Q0 Q3 X0 (Immediate_Offset (iword (&0))) *)
  0x6e0640c3;       (* arm_EXT Q3 Q6 Q6 64 *)
  0x0ee2e0c7;       (* arm_PMULL_VEC Q7 Q6 Q2 64 *)
  0x6e241e86;       (* arm_EOR_VEC Q6 Q20 Q4 128 *)
  0x6e311ca4;       (* arm_EOR_VEC Q4 Q5 Q17 128 *)
  0x6e271c65;       (* arm_EOR_VEC Q5 Q3 Q7 128 *)
  0x6e0640c3;       (* arm_EXT Q3 Q6 Q6 64 *)
  0x0ee6e007;       (* arm_PMULL_VEC Q7 Q0 Q6 64 *)
  0x4ee6e011;       (* arm_PMULL2_VEC Q17 Q0 Q6 64 *)
  0x0ee6e020;       (* arm_PMULL_VEC Q0 Q1 Q6 64 *)
  0x0ee6e0d2;       (* arm_PMULL_VEC Q18 Q6 Q6 64 *)
  0x4ee6e0d3;       (* arm_PMULL2_VEC Q19 Q6 Q6 64 *)
  0x4ee6e034;       (* arm_PMULL2_VEC Q20 Q1 Q6 64 *)
  0x6e241ca1;       (* arm_EOR_VEC Q1 Q5 Q4 128 *)
  0x6e271e24;       (* arm_EOR_VEC Q4 Q17 Q7 128 *)
  0x0ee2e005;       (* arm_PMULL_VEC Q5 Q0 Q2 64 *)
  0x6e004007;       (* arm_EXT Q7 Q0 Q0 64 *)
  0x0ee2e240;       (* arm_PMULL_VEC Q0 Q18 Q2 64 *)
  0x6e331e51;       (* arm_EOR_VEC Q17 Q18 Q19 128 *)
  0x4ee2e253;       (* arm_PMULL2_VEC Q19 Q18 Q2 64 *)
  0x0ee1e0d2;       (* arm_PMULL_VEC Q18 Q6 Q1 64 *)
  0x4ee1e075;       (* arm_PMULL2_VEC Q21 Q3 Q1 64 *)
  0x0ee1e076;       (* arm_PMULL_VEC Q22 Q3 Q1 64 *)
  0x0ee1e037;       (* arm_PMULL_VEC Q23 Q1 Q1 64 *)
  0x4ee1e038;       (* arm_PMULL2_VEC Q24 Q1 Q1 64 *)
  0x4ee1e0d9;       (* arm_PMULL2_VEC Q25 Q6 Q1 64 *)
  0x6e251c9a;       (* arm_EOR_VEC Q26 Q4 Q5 128 *)
  0x6e004004;       (* arm_EXT Q4 Q0 Q0 64 *)
  0x0ee2e005;       (* arm_PMULL_VEC Q5 Q0 Q2 64 *)
  0x6e014020;       (* arm_EXT Q0 Q1 Q1 64 *)
  0x6e331e3b;       (* arm_EOR_VEC Q27 Q17 Q19 128 *)
  0x6e124251;       (* arm_EXT Q17 Q18 Q18 64 *)
  0x0ee2e253;       (* arm_PMULL_VEC Q19 Q18 Q2 64 *)
  0x0ee2e2f2;       (* arm_PMULL_VEC Q18 Q23 Q2 64 *)
  0x6e381efc;       (* arm_EOR_VEC Q28 Q23 Q24 128 *)
  0x4ee2e2f8;       (* arm_PMULL2_VEC Q24 Q23 Q2 64 *)
  0xad010010;       (* arm_STP Q16 Q0 X0 (Immediate_Offset (iword (&32))) *)
  0x6e271f40;       (* arm_EOR_VEC Q0 Q26 Q7 128 *)
  0x6e251c87;       (* arm_EOR_VEC Q7 Q4 Q5 128 *)
  0x6e124244;       (* arm_EXT Q4 Q18 Q18 64 *)
  0x0ee2e245;       (* arm_PMULL_VEC Q5 Q18 Q2 64 *)
  0x6e381f90;       (* arm_EOR_VEC Q16 Q28 Q24 128 *)
  0x4ec62832;       (* arm_TRN1 Q18 Q1 Q6 64 128 *)
  0x4ec66837;       (* arm_TRN2 Q23 Q1 Q6 64 128 *)
  0x6e371e41;       (* arm_EOR_VEC Q1 Q18 Q23 128 *)
  0x6e004006;       (* arm_EXT Q6 Q0 Q0 64 *)
  0x0ee2e012;       (* arm_PMULL_VEC Q18 Q0 Q2 64 *)
  0x6e271f60;       (* arm_EOR_VEC Q0 Q27 Q7 128 *)
  0x6e361ea7;       (* arm_EOR_VEC Q7 Q21 Q22 128 *)
  0x6e331e35;       (* arm_EOR_VEC Q21 Q17 Q19 128 *)
  0x6e351cf1;       (* arm_EOR_VEC Q17 Q7 Q21 128 *)
  0x6e251c87;       (* arm_EOR_VEC Q7 Q4 Q5 128 *)
  0xad020c01;       (* arm_STP Q1 Q3 X0 (Immediate_Offset (iword (&64))) *)
  0x6e341cc1;       (* arm_EOR_VEC Q1 Q6 Q20 128 *)
  0x6e004003;       (* arm_EXT Q3 Q0 Q0 64 *)
  0x6e271e04;       (* arm_EOR_VEC Q4 Q16 Q7 128 *)
  0x6e114225;       (* arm_EXT Q5 Q17 Q17 64 *)
  0x0ee2e226;       (* arm_PMULL_VEC Q6 Q17 Q2 64 *)
  0x6e211e42;       (* arm_EOR_VEC Q2 Q18 Q1 128 *)
  0x6e391ca1;       (* arm_EOR_VEC Q1 Q5 Q25 128 *)
  0x6e044085;       (* arm_EXT Q5 Q4 Q4 64 *)
  0x6e024047;       (* arm_EXT Q7 Q2 Q2 64 *)
  0x6e211cd0;       (* arm_EOR_VEC Q16 Q6 Q1 128 *)
  0x6e104201;       (* arm_EXT Q1 Q16 Q16 64 *)
  0x4ec42846;       (* arm_TRN1 Q6 Q2 Q4 64 128 *)
  0x4ec46851;       (* arm_TRN2 Q17 Q2 Q4 64 128 *)
  0x6e311cc2;       (* arm_EOR_VEC Q2 Q6 Q17 128 *)
  0xad040405;       (* arm_STP Q5 Q1 X0 (Immediate_Offset (iword (&128))) *)
  0x4ec02a01;       (* arm_TRN1 Q1 Q16 Q0 64 128 *)
  0x4ec06a04;       (* arm_TRN2 Q4 Q16 Q0 64 128 *)
  0x6e241c20;       (* arm_EOR_VEC Q0 Q1 Q4 128 *)
  0xad030807;       (* arm_STP Q7 Q2 X0 (Immediate_Offset (iword (&96))) *)
  0xad050c00;       (* arm_STP Q0 Q3 X0 (Immediate_Offset (iword (&160))) *)
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
(*                                                                            *)
(* The evaluation is STAGED, and the staging is the whole cost of the lemma:   *)
(* the twisted key and H^2 are each reduced to a NUMERAL before byteswap128 /   *)
(* karatsuba_mid / polyval_reduce_prop3 are unfolded.  Unfolding first and      *)
(* reducing afterwards (the obvious one-pass `TOP_DEPTH_CONV let_CONV THENC     *)
(* WORD_REDUCE_CONV`) flattens prop3's 13-`let` DAG into a tree, and            *)
(* DEPTH_CONV does not memoise, so WORD_PMUL_CONV recomputes the 128x128        *)
(* carry-less product (1.3s each) once per duplicated occurrence -- ~20 times.  *)
(* CBV_LET_CONV keeps that sharing INSIDE prop3 by reducing each binding to a   *)
(* numeral before substituting it, so `word_pmul a w` is done once, not four    *)
(* times.  Identical statement, identical numerals; load 52s -> 1.8s.           *)
let HTABLE_MEM_KAT_FIRST3 =
  let CBV_LET_CONV =
    REPEATC(CHANGED_CONV(WORD_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV)) THENC
    WORD_REDUCE_CONV in
  let HKEY =
    (REWRITE_CONV[ghash_twist; POLYVAL_TWIST_CONST; byteswap128] THENC
     WORD_REDUCE_CONV)
    `ghash_twist(byteswap128 (word 0x08070605040302010102030405060708:int128))` in
  let HSQ =
    (REWRITE_CONV[num_CONV `1`; h_power; polyval_dot] THENC WORD_REDUCE_CONV THENC
     REWR_CONV polyval_reduce_prop3 THENC CBV_LET_CONV)
    (list_mk_comb(`h_power`,[rand(concl HKEY); `1`])) in
  prove
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
  CONV_TAC(REWRITE_CONV[HKEY] THENC REWRITE_CONV[HSQ; h_power] THENC
           REWRITE_CONV[byteswap128; karatsuba_mid] THENC WORD_REDUCE_CONV));;

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
    h_power h 4 = polyval_dot h (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
    h_power h 5 = polyval_dot (polyval_dot h (polyval_dot h h)) (polyval_dot h (polyval_dot h h)) /\
    h_power h 6 = polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) (polyval_dot h (polyval_dot h h)) /\
    h_power h 7 = polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) (polyval_dot (polyval_dot h h) (polyval_dot h h))`,
  GEN_TAC THEN
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power] THEN
  REWRITE_TAC[POLYVAL_DOT_ASSOC]);;

(* ========================================================================= *)
(* WORD-LEVEL TOOLKIT shared by the power blocks (Phases 1-2).                *)
(*                                                                            *)
(* Each power is computed by a carryless product (or square) followed by the   *)
(* same two-phase Gueron reduction; the searched instruction order interleaves *)
(* all seven of those chains, so Phase 2 alone holds six of them.  Every       *)
(* register and store value in a block's postcondition is an XOR / lane        *)
(* rearrangement of the SAME opaque 64x64 base products, so ONE set of rules   *)
(* discharges every block -- genuine-mid and square products alike.  This is   *)
(* why nothing below is specialised to a power.                               *)
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
(* instead of after it (Phase 1) -- the single biggest remaining latency win.    *)
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
(* GF(2)-LINEAR to take Gueron's reduction apart (see the Phase 2 header):     *)
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
(* Extra machinery for the fused twist+H^2 block (Phase 1).                   *)
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

(* (There used to be an FMASK lemma here, splitting the `and` that selected the  *)
(* conditional constant into its two lanes.  The routine no longer HAS that       *)
(* `and`: the masked modulus is `trn1(u ^ ext(u,u,8), pmull(u.d[0],w))`, so the    *)
(* only fact the low lane needs is CARRY_BIT_USHR above.)                         *)

(* The carry bit in the two forms the two sides produce: the spec's masked      *)
(* `word_and (word 1) (word_ishr x 63)` (what TWIST_LANES / CARRY_PMULS leave)   *)
(* is literally the hardware's `word_ushr x 63` -- the routine now reads the      *)
(* carry straight out of `u = H >>u 63` instead of masking a broadcast `sshr`.    *)
let CARRY_BIT_USHR = prove
 (`!x:int64. word_and (word 1) (word_ishr x 63) = word_ushr x 63`,
  GEN_TAC THEN BITBLAST_TAC);;

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
(* does not invalidate this.  The twisted key's raw expression now contains a      *)
(* `word_pmul` (the one-instruction conditional modulus), and BITBLAST cannot see   *)
(* inside `word_pmul`, so the obligation is first normalized by LANE_CONV -- which  *)
(* reduces the `word_subword`s around the carry lane -- and then collapsed by       *)
(* CARRY_PMULS; only then is it a pure bit identity.                               *)
let ATOMIZE_TWIST_TAC rname sname atom : tactic =
  fun (asl,w) ->
    let is_reg th = match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),_) ->
          string_of_term c = rname && string_of_term st = sname
      | _ -> false in
    let th = snd(find (fun (_,t) -> is_reg t) asl) in
    let raw = rand(concl th) in
    (SUBGOAL_THEN (mk_eq(raw,atom)) SUBST_ALL_TAC THENL
      [CONV_TAC LANE_CONV THEN REWRITE_TAC[CARRY_PMULS] THEN
       REWRITE_TAC[byteswap128; ghash_twist; POLYVAL_TWIST_CONST] THEN BITBLAST_TAC;
       ALL_TAC]) (asl,w);;

(* Same idea for a POWER computed mid-block.  Once six powers share one block the  *)
(* later products read the EARLIER powers' raw register expressions, not opaque    *)
(* operands, and the closing WORD_BITWISE_RULE then sees `word_pmul` applied to a   *)
(* whole reduce chain and fails.  So the moment H^4 (and then H^3) is complete,     *)
(* fold its raw expression into the spec term, proving that one 128-bit equation    *)
(* on its own -- which is cheap, because in isolation it needs only ITS OWN two     *)
(* products' atoms.  Everything downstream then sees an opaque power, exactly as    *)
(* it did when each power had its own block.  Like ATOMIZE_TWIST_TAC, the raw term  *)
(* is READ OFF the assumption for register `rname` in state `sname` rather than     *)
(* transcribed, so a reschedule or a reallocation does not invalidate the call.     *)
let ATOMIZE_POWER_TAC rname sname atom tac : tactic =
  fun (asl,w) ->
    let is_reg th = match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),_) ->
          string_of_term c = rname && string_of_term st = sname
      | _ -> false in
    let th = snd(find (fun (_,t) -> is_reg t) asl) in
    let raw = rand(concl th) in
    (SUBGOAL_THEN (mk_eq(raw,atom)) SUBST_ALL_TAC THENL [tac; ALL_TAC]) (asl,w);;

(* (Historical note, for the next reschedule: when a block interface has to carry  *)
(* not just a power but a raw 64x64 PRODUCT of one -- which happened in 018, where  *)
(* the ASAP order issued H^8's halves five instructions after H^4 existed -- those  *)
(* conjuncts cannot be closed by LANE_CLOSE_TAC, because WORD_BITWISE_RULE cannot   *)
(* see inside `word_pmul`.  The fix was to prove the POWER's own conjunct first and  *)
(* SUBST_ALL_TAC it, after which the product conjuncts close by reflexivity.  The    *)
(* current tiling needs no such interface, so the tactic itself is gone.)            *)

(* LANE_CLOSE_TAC plus the carry-constant collapse.  The two must ALTERNATE:     *)
(* LANE_CONV's distribution of pmul-by-w is what exposes the next carry-only     *)
(* product, and CARRY_PMULS' `word_join` results are what LANE_CONV then splits  *)
(* into lanes.  Three rounds reach the fixpoint (the reduce is two deep).        *)
(* CARRY_BIT_USHR rides along in every round: CARRY_PMULS states its results in   *)
(* the masked `word_and (word 1) (word_ishr x 63)` form, while the routine now     *)
(* reads the carry straight out of `u = H >>u 63`, so without normalizing the two  *)
(* spellings the last lane does not close.                                        *)
let CARRY_CLOSE_TAC =
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC WORD_EQ_128_LANES THEN CONJ_TAC THEN
  CONV_TAC LANE_CONV THEN
  REWRITE_TAC[CARRY_PMULS; CARRY_BIT_USHR] THEN CONV_TAC LANE_CONV THEN
  REWRITE_TAC[CARRY_PMULS; CARRY_BIT_USHR] THEN CONV_TAC LANE_CONV THEN
  REWRITE_TAC[CARRY_PMULS; CARRY_BIT_USHR] THEN CONV_TAC LANE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE;;

(* ========================================================================= *)
(* Phase 1: the FUSED twist + H^2 block (PC 0x0 -> 0x64, 25 steps).           *)
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
(* reduction constant w in Q2 and H^2 in Q3.                                   *)
(*                                                                            *)
(* The conditional constant is no longer BUILT.  `u = H >>u 63` (per lane)     *)
(* already holds the carry as the INTEGER 0/1 in lane 0, so pmull(u.d[0], w)   *)
(* IS {carry ? 0xc2..00 : 0, 0} bit for bit -- which is literally clause 2 of  *)
(* CARRY_PMULS below -- and trn1(u ^ ext(u,u,8), that) is the masked POLYVAL   *)
(* modulus with u.d[1] already xored into its low lane.  So the 0xff and 0x0   *)
(* `movi`s, the {1,1}, the `ext` that assembled Q, the `sshr` mask, its `trn1` *)
(* broadcast, the `and` and one `eor` are all gone -- and FMASK with them; the *)
(* only new fact needed is CARRY_BIT_USHR for the low lane.                                   *)
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
         (\s. read PC s = word (pc + 0x64) /\
              read X0 s = Htable /\
              read Q2 s = word 0xc200000000000000c200000000000000 /\
              read Q0 s = byteswap128 h1 /\
              read Q3 s = h_power h1 1)
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
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--20) THEN
  ATOMIZE_TWIST_TAC "Q0" "s20" `byteswap128(ghash_twist(byteswap128 H))` THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (21--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  SPEC_UNFOLD_TAC THEN
  REWRITE_TAC[TWIST_LANES] THEN
  REWRITE_TAC[PMUL_SQ_XOR2; PMUL_SQ_XOR3] THEN
  CARRY_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 2: ALL SIX remaining powers in one block, PC 0x64 -> 0x1c4 (88 steps).*)
(*                                                                            *)
(*   H^3 = h_power h1 2 = polyval_dot h1 H^2   (genuine)                       *)
(*   H^4 = h_power h1 3 = polyval_dot H^2 H^2  (a SQUARE)                      *)
(*   H^5 = h_power h1 4 = polyval_dot h1 H^4   (genuine)                       *)
(*   H^6 = h_power h1 5 = polyval_dot H^3 H^3  (a SQUARE)                      *)
(*   H^7 = h_power h1 6 = polyval_dot H^4 H^3  (genuine)                       *)
(*   H^8 = h_power h1 7 = polyval_dot H^4 H^4  (a SQUARE)                      *)
(*                                                                            *)
(* One block for six powers is FORCED by the schedule, not chosen.  The stream  *)
(* is the best topological order of the whole dependence graph that a hardware- *)
(* scored search found, so the six reduction chains are completely interleaved   *)
(* and PC 0x1c4 is the first place in 0x64..0x1ec where every live value is a     *)
(* named quantity; the other clean cuts (0x1c8, 0x1d4, 0x1d8, 0x1e4, 0x1e8) are   *)
(* all inside the tail.  Nothing about the ALGEBRA changes: the block             *)
(* just runs GUERON_ATOMS_TAC six times instead of two.                          *)
(*                                                                            *)
(* H^5 is stated as h1 . H^4 and H^7 as H^4 . H^3 because the cross products     *)
(* read the OTHER operand's byteswapped copy, and of each pair only the second   *)
(* operand's byteswap is live (h1's is Q0 itself -- the value Htable[0] stores   *)
(* -- and H^4's is the one the table needs at Htable[5]).                        *)
(*                                                                            *)
(* Also finishes the first block's table work, which the schedule moved down     *)
(* here because it has slack and H^3's four products do not: the algebraic-lane  *)
(* copy of the key, byteswap128 H^2, the folds of H and H^2 and their pack.      *)
(* Stores Htable[0..5].  Live out: H^5 (Q2), H^6 (Q4), H^7 (Q16), H^8 (Q0),     *)
(* byteswap128 H^5 (Q7), H^6 (Q5) and H^8 (Q3) -- w dies here, the last block    *)
(* has no products.  H^8 ITSELF (not its fold) is in the interface now, because  *)
(* the packed mids are built by trn1/trn2 straight off the two RAW powers        *)
(* instead of from their folds: trn1(A,B) ^ trn2(A,B) = {mid A, mid B} is the    *)
(* same three instructions but two cycles shallower, and LANE_CONV already knows *)
(* TRN1/TRN2 (they unfold to a word_join of one lane from each operand).         *)
(* ========================================================================= *)

let GCM_INIT_V8_H345678 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x64) /\
              read X0 s = Htable /\
              read Q2 s = word 0xc200000000000000c200000000000000 /\
              read Q0 s = byteswap128 h1 /\
              read Q3 s = h_power h1 1)
         (\s. read PC s = word (pc + 0x1c4) /\
              read X0 s = Htable /\
              read Q2 s = h_power h1 4 /\
              read Q4 s = h_power h1 5 /\
              read Q16 s = h_power h1 6 /\
              read Q0 s = h_power h1 7 /\
              read Q7 s = byteswap128 (h_power h1 4) /\
              read Q5 s = byteswap128 (h_power h1 5) /\
              read Q3 s = byteswap128 (h_power h1 7) /\
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
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst GCM_INIT_V8_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SOME_FLAGS; MODIFIABLE_SIMD_REGS] THEN
  REWRITE_TAC[HPOWER_OPERANDS] THEN
  MAP_EVERY ABBREV_TAC
   [`h2 = polyval_dot h1 h1`; `h3 = polyval_dot h1 h2`;
    `h4 = polyval_dot h2 h2`] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--29) THEN
  ATOMIZE_POWER_TAC "Q6" "s29" `h4:int128`
   (EXPAND_TAC "h4" THEN SPEC_UNFOLD_TAC THEN
    SQUARE_TAC 4 `h2:int128` THEN LANE_CLOSE_TAC) THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (30--39) THEN
  ATOMIZE_POWER_TAC "Q1" "s39" `h3:int128`
   (EXPAND_TAC "h3" THEN SPEC_UNFOLD_TAC THEN
    PRODUCT_TAC 3 `h1:int128` `h2:int128` THEN LANE_CLOSE_TAC) THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (40--88) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SPEC_UNFOLD_TAC THEN
  PRODUCT_TAC 5 `h1:int128` `h4:int128` THEN
  SQUARE_TAC 6 `h3:int128` THEN
  PRODUCT_TAC 7 `h4:int128` `h3:int128` THEN
  SQUARE_TAC 8 `h4:int128` THEN
  LANE_CLOSE_TAC);;

(* ========================================================================= *)
(* Phase 3: the closing block, PC 0x1c4 -> 0x1ec (10 steps, ends at the ret).  *)
(*                                                                            *)
(* No products at all: byteswap128 H^7, the two remaining Karatsuba packs (each *)
(* a trn1/trn2 pair off the two RAW powers plus an `eor`) and the                *)
(* last three `stp`s, Htable[6..11].  Every operand is an opaque power out of    *)
(* the precondition, so the whole block closes on lane identities alone -- no    *)
(* PMUL reasoning and no atoms, though SPEC_UNFOLD_TAC is still what turns the   *)
(* spec's karatsuba_mid / byteswap128 into lanes.                               *)
(*                                                                            *)
(* The postcondition carries ALL TWELVE slots, so Phase 4 reads the full        *)
(* htable_mem table straight off this block's post.                            *)
(* ========================================================================= *)

let GCM_INIT_V8_TAIL = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x1c4) /\
              read X0 s = Htable /\
              read Q2 s = h_power h1 4 /\
              read Q4 s = h_power h1 5 /\
              read Q16 s = h_power h1 6 /\
              read Q0 s = h_power h1 7 /\
              read Q7 s = byteswap128 (h_power h1 4) /\
              read Q5 s = byteswap128 (h_power h1 5) /\
              read Q3 s = byteswap128 (h_power h1 7) /\
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
         (\s. read PC s = word (pc + 0x1ec) /\
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
(* Phase 4: the core correctness theorem, GCM_INIT_V8_CORRECT.                *)
(*                                                                            *)
(* Compose the three blocks into one `ensures` from function entry (PC 0x0) to *)
(* the `ret` (PC 0x1ec), establishing the full 12-slot htable_mem             *)
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
(* memory :> bytelist(word pc,496).  Its ORTHOGONAL_COMPONENTS_TAC scans the  *)
(* assumptions for a RAW `nonoverlapping (word pc,496) (Htable,192)` driver    *)
(* and needs the length CONCRETE (496).  Hence: reduce LENGTH gcm_init_v8_mc   *)
(* to 496 via `fst GCM_INIT_V8_EXEC` in the setup rewrite, and do NOT rewrite  *)
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
         (\s. read PC s = word (pc + 0x1ec) /\
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
  GCM_BLOCK_STEP_TAC "s2" GCM_INIT_V8_H345678 THEN
  GCM_BLOCK_STEP_TAC "s3" GCM_INIT_V8_TAIL THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[htable_mem; CONJUNCT1 h_power]);;

(* ========================================================================= *)
(* Phase 5: the standard-ABI subroutine wrapper (leaf, no stack frame).       *)
(*                                                                            *)
(* Wrap the core with the return via X30.  Two mechanical points:             *)
(*  - Reduce LENGTH gcm_init_v8_mc to 496 (`fst GCM_INIT_V8_EXEC`) in the goal *)
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
(* Phase 6: constant-time and memory-safety.                                  *)
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
