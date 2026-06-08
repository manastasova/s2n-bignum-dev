(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* aes256_gcm_one_block.ml                                                 *)
(*                                                                         *)
(* The 1-block AES-256-GCM separate-blocks encrypt proof — the N=1         *)
(* instance of the generic N-block framework, handling a final block of    *)
(* ANY length from 1 to 16 bytes (a possibly-partial block).  Shared        *)
(* lemmas and the framework live in arm/proofs/utils/gcm_aesgcm_helpers.ml  *)
(* and arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml.                       *)
(*                                                                         *)
(* The routine masks the ciphertext to the low 8*byte_len bits, inserts the *)
(* untouched original output bytes above the message end (the `bif`), and   *)
(* feeds the masked block into GHASH.  The proof models this with a         *)
(* data-dependent mask word (2^(8*byte_len) - 1) built from the variable    *)
(* shift / conditional-select sequence (see ONE_BLOCK_MASK_REG).            *)
(*                                                                         *)
(* PER-N CONTENT (only piece in this file):                                *)
(*   - aes256_gcm_one_block_mc (the machine code blob) and EXEC            *)
(*   - ONE_BLOCK_MASK_REG etc.: the partial-block mask-construction lemmas  *)
(*   - GCM_GHASH_STEP_MASKED_TAC: the GHASH closure over the masked block,  *)
(*     via ghash_1block_karatsuba and its bridge to polyval_dot             *)
(*   - GCM_CT_STEP_TAC: the single-block ciphertext closure                *)
(*   - The main theorem ONE_BLOCK_PRELOOP_TAIL_CORRECT                     *)
(* ========================================================================= *)

(* All dependencies (base/AES/ghash_spec/aesgcm helpers) are pulled in       *)
(* transitively by the N-block framework file below.                          *)
needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;

(* ========================================================================= *)
(*  PER-N MACHINE CODE                                                       *)
(* ========================================================================= *)

let aes256_gcm_one_block_mc = define_assert_from_elf
  "aes256_gcm_one_block_mc"
  "arm/aes-gcm/aes256_gcm_one_block.o"
[
  0x6dbb27e8;       (* arm_STP D8 D9 SP (Preimmediate_Offset (iword (-- &80))) *)
  0xd343fc29;       (* arm_LSR X9 X1 3 *)
  0xaa0403f0;       (* arm_MOV X16 X4 *)
  0xaa0503eb;       (* arm_MOV X11 X5 *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0xd2f84005;       (* arm_MOVZ X5 (word 49664) 48 *)
  0xa9047fe5;       (* arm_STP X5 XZR SP (Immediate_Offset (iword (&64))) *)
  0x910103ea;       (* arm_ADD X10 SP (rvalue (word 64)) *)
  0x4c407200;       (* arm_LDR Q0 X16 No_Offset *)
  0xaa0903e5;       (* arm_MOV X5 X9 *)
  0xd2c0002f;       (* arm_MOVZ X15 (word 1) 32 *)
  0x4f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x4e181dff;       (* arm_INS_GEN Q31 X15 64 64 *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0x9279e0a5;       (* arm_AND X5 X5 (rvalue (word 18446744073709551488)) *)
  0x8b0000a5;       (* arm_ADD X5 X5 X0 *)
  0x6e20081e;       (* arm_REV32_VEC Q30 Q0 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x92401821;       (* arm_AND X1 X1 (rvalue (word 127)) *)
  0xd1020021;       (* arm_SUB X1 X1 (rvalue (word 128)) *)
  0xcb0103e1;       (* arm_NEG X1 X1 *)
  0xaa3f03e7;       (* arm_MVN X7 XZR *)
  0x92401821;       (* arm_AND X1 X1 (rvalue (word 127)) *)
  0x9ac124e7;       (* arm_LSRV X7 X7 X1 *)
  0xf101003f;       (* arm_CMP X1 (rvalue (word 64)) *)
  0xaa3f03e8;       (* arm_MVN X8 XZR *)
  0x9a9fb0ee;       (* arm_CSEL X14 X7 XZR Condition_LT *)
  0x9a87b10d;       (* arm_CSEL X13 X8 X7 Condition_LT *)
  0x4e081da0;       (* arm_INS_GEN Q0 X13 0 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4c40705a;       (* arm_LDR Q26 X2 No_Offset *)
  0x4e181dc0;       (* arm_INS_GEN Q0 X14 64 64 *)
  0x4e201d29;       (* arm_AND_VEC Q9 Q9 Q0 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 128 *)
  0x6ee01f49;       (* arm_BIF Q9 Q26 Q0 128 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2 Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL Q16 Q16 Q21 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x0ef0e23d;       (* arm_PMULL Q29 Q17 Q16 64 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x0ef0e251;       (* arm_PMULL Q17 Q18 Q16 64 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0xce115673;       (* arm_EOR3 Q19 Q19 Q17 Q21 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x6cc527e8;       (* arm_LDP D8 D9 SP (Postimmediate_Offset (iword (&80))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let ONE_BLOCK_PRELOOP_TAIL_EXEC =
  ARM_MK_EXEC_RULE aes256_gcm_one_block_mc;;

(* ========================================================================= *)
(* PARTIAL-BLOCK MASK CONSTRUCTION                                            *)
(*                                                                           *)
(* For an input of byte_len bytes (1 <= byte_len <= 16), the routine builds a *)
(* 128-bit mask register in Q0 from byte_len via the sequence                 *)
(*   and x1,#127 ; sub #128 ; neg ; and #127 ; lsrv (all-ones >> n) ;         *)
(*   cmp #64 ; csel ; csel ; ins d0/d1.                                       *)
(* The lemma below shows that this register, in the exact ival/flag form the  *)
(* symbolic simulator produces, equals word (2^(8*byte_len) - 1): a mask with *)
(* the low 8*byte_len bits set.  The proof peels byte_len into its 16 values  *)
(* (a single 16-way ARITH_RULE disjunction is intractable) and reduces each   *)
(* concrete case by word/num/int arithmetic.                                  *)
(* ========================================================================= *)

let mask_red_tac =
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV ORELSEC INT_RED_CONV) THENC
           WORD_REDUCE_CONV THENC NUM_REDUCE_CONV);;

(* Peel `lo <= b /\ b <= 16` one value at a time; each rule is cheap, whereas
   a single 16-way ARITH_RULE disjunction does not terminate in reasonable time. *)
let one_block_cases16 lo =
  if lo = 16 then
    ARITH_RULE(Printf.sprintf "%d <= b /\\ b <= 16 ==> b = 16" lo |> parse_term)
  else
    ARITH_RULE(Printf.sprintf
      "%d <= b /\\ b <= 16 <=> b = %d \\/ (%d <= b /\\ b <= 16)" lo lo (lo+1)
      |> parse_term);;

let rec MASK_PEEL_TAC lo =
  if lo = 16 then
    DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP (one_block_cases16 16) th)) THEN
    mask_red_tac
  else
    REWRITE_TAC[one_block_cases16 lo] THEN
    DISCH_THEN(DISJ_CASES_THEN (fun th ->
      (SUBST1_TAC th THEN mask_red_tac)
      ORELSE (MP_TAC th THEN MASK_PEEL_TAC (lo+1))));;

(* Inserting both 64-bit lanes of a 128-bit register discards the original base. *)
let WORD_INSERT_BOTH_LANES = prove
 (`!(b0:int128) (a:int64) (c:int64).
     word_insert ((word_insert b0 (0,64) a):int128) (64,64) c : int128 =
     word_join c a`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* The mask register the routine builds in Q0 (base b0 = the AES ciphertext that
   previously occupied Q0; both its lanes are overwritten by the two csel results)
   equals word (2^(8*byte_len) - 1). *)
let ONE_BLOCK_MASK_REG = prove
 (`!byte_len (b0:int128). 1 <= byte_len /\ byte_len <= 16 ==>
    (word_insert
     ((word_insert (b0:int128)
        (0,64)
        (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
              ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
                ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
         then word 18446744073709551615:int64
         else word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)))):int128)
     (64,64)
     (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
           ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
             ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
        then word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127))
        else word 0:int64)
    : int128)
    = word (2 EXP (8 * byte_len) - 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_INSERT_BOTH_LANES] THEN
  SPEC_TAC(`byte_len:num`,`byte_len:num`) THEN GEN_TAC THEN
  MASK_PEEL_TAC 1);;

(* The returned byte length: x9 = (8*byte_len) >> 3 = byte_len for byte_len <= 16. *)
let ONE_BLOCK_USHR_BYTELEN = prove
 (`!byte_len. byte_len <= 16
     ==> word_ushr (word (8 * byte_len):int64) 3 = word byte_len`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `val (word (8 * byte_len):int64) = 8 * byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXP; ARITH] THEN ARITH_TAC);;

(* The masked ciphertext written by the bif store: masking the already-masked
   block again with the same mask is idempotent. *)
let ONE_BLOCK_MASK_IDEM = prove
 (`!(ct:int128) (mask:int128).
     word_and (word_and mask ct) mask = word_and ct mask`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* GHASH STEP TACTIC (N=1)                                                    *)
(*                                                                           *)
(* Closes the GHASH conjunct by rewriting the single-block ghash_polyval_acc *)
(* via the ghash_1block_karatsuba spec and its bridge to polyval_dot         *)
(* (GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT), then the byte-level subword/      *)
(* halfswap normalization, atom/pmul ABBREVs and a final WORD_RULE closure.  *)
(* ========================================================================= *)

let GCM_GHASH_STEP_TAC =
  REWRITE_TAC[ghash_polyval_acc; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT th)]) THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN
    `word_xor xi (word_xor pt
       (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                         rk8 rk9 rk10 rk11 rk12 rk13 rk14)) =
     word_xor xi ct:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ct" THEN EXPAND_TAC "s13" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC];
    ALL_TAC
  ] THEN
  ASM_REWRITE_TAC[] THEN
  (* Invert the rev64 + halfswap byte-level expansion via final_xi.          *)
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word`
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO;
              REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[WORD_XOR_ASSOC; KAR_MID_BRIDGE; WORD_SUBWORD_0;
              WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_ASSOC; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[KAR_MID_BRIDGE; WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Common-pattern atomic abbreviations (4 = 2N + 2 for N=1) *)
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[karatsuba_mid] THEN
  ABBREV_TAC `(uA0:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ct)) (0,64)` THEN
  ABBREV_TAC `(uA1:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ct)) (64,64)` THEN
  ABBREV_TAC `(uD0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(uD1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  (* 3 inner pmuls (3 = 3N for N=1) *)
  ABBREV_TAC `(p1:(128)word) = word_pmul (uA0:(64)word) (uD0:(64)word)` THEN
  ABBREV_TAC `(p2:(128)word) = word_pmul (uA1:(64)word) (uD1:(64)word)` THEN
  ABBREV_TAC `(p3:(128)word) =
    word_pmul (word_xor (uA0:(64)word) (uA1:(64)word))
              (word_xor (uD0:(64)word) (uD1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  (* 7 z-vars (= 6N+1 for N=1) *)
  ABBREV_TAC `(z1:(64)word) = word_subword (p1:(128)word) (0,64)` THEN
  ABBREV_TAC `(z2:(64)word) = word_subword (p1:(128)word) (64,64)` THEN
  ABBREV_TAC `(z3:(64)word) = word_subword (p2:(128)word) (0,64)` THEN
  ABBREV_TAC `(z4:(64)word) = word_subword (p2:(128)word) (64,64)` THEN
  ABBREV_TAC `(z5:(64)word) = word_subword (p3:(128)word) (0,64)` THEN
  ABBREV_TAC `(z6:(64)word) = word_subword (p3:(128)word) (64,64)` THEN
  ABBREV_TAC `(zD:(64)word) =
    word_subword (word_pmul (z1:(64)word) (word 13979173243358019584:(64)word):(128)word)
                 (0,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize the BIG pmul args (XOR-AC) *)
  SUBGOAL_THEN
    `word_pmul (word_xor (z2:(64)word)
                (word_xor z5
                (word_xor z3
                (word_xor z1 zD))))
               (word 13979173243358019584:(64)word):(128)word =
     word_pmul (word_xor (z5:(64)word)
                (word_xor z1
                (word_xor z3
                (word_xor zD z2))))
               (word 13979173243358019584:(64)word):(128)word`
    ASSUME_TAC THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* ABBREV the outer pmul terms and their subword extractions *)
  ABBREV_TAC
    `qBigP = word_pmul
       (word_xor (z5:(64)word) (word_xor z1 (word_xor z3 (word_xor zD z2))))
       (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC
    `qSmallP = word_pmul (z1:(64)word)
                        (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC `qBigPL = word_subword (qBigP:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qBigPH = word_subword (qBigP:(128)word) (64,64):(64)word` THEN
  ABBREV_TAC `qSmallPH = word_subword (qSmallP:(128)word) (64,64):(64)word` THEN
  (* Final closure *)
  BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE];;

(* ========================================================================= *)
(* CIPHERTEXT CLOSURE: 1-block instance (shared with GCM_NBLOCK_CT_STEP_TAC). *)
(* For 1-block: ivec_1 = ivec (no gcm_ctr_inc), so no LANE/CTR chain.        *)
(* ========================================================================= *)

let GCM_CT_STEP_TAC = GCM_NBLOCK_CT1_STEP_TAC 1;;

(* ========================================================================= *)
(* GHASH STEP TACTIC (N=1, partial block)                                     *)
(*                                                                           *)
(* As GCM_GHASH_STEP_TAC, but the GHASH input is the MASKED block            *)
(* ctm = word_and ct mask (mask = word (2^(8*byte_len) - 1)).  The symbolic   *)
(* state carries the block as word_and mask ct; the spec uses word_and ct    *)
(* mask, so the opening SUBGOAL bridges the two via commutativity, and the    *)
(* atomic abbreviations are taken over ctm.                                   *)
(* ========================================================================= *)

let GCM_GHASH_STEP_MASKED_TAC =
  REWRITE_TAC[ghash_polyval_acc; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT th)]) THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm = word_and (ct:(128)word) mask` THEN
  (* Fold the spec-side AES expression to the abbreviated ciphertext `ct`, so
     the postcondition's masked block word_and (word_xor pt aes) mask matches
     ctm = word_and ct mask. *)
  SUBGOAL_THEN
    `word_xor pt (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                   rk8 rk9 rk10 rk11 rk12 rk13 rk14) = ct`
    (fun th -> REWRITE_TAC[th]) THENL [
    MAP_EVERY EXPAND_TAC ["ct"; "s13"] THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC];
    ALL_TAC
  ] THEN
  (* The symbolic GHASH input is word_and mask ct; the spec uses word_and ct
     mask = ctm.  Bridge the two via commutativity of word_and. *)
  SUBGOAL_THEN `word_and (mask:(128)word) (ct:(128)word) = ctm`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm" THEN CONV_TAC WORD_BITWISE_RULE;
    ALL_TAC
  ] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word`
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO;
              REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[WORD_XOR_ASSOC; KAR_MID_BRIDGE; WORD_SUBWORD_0;
              WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_ASSOC; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[KAR_MID_BRIDGE; WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[karatsuba_mid] THEN
  ABBREV_TAC `(uA0:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ctm)) (0,64)` THEN
  ABBREV_TAC `(uA1:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ctm)) (64,64)` THEN
  ABBREV_TAC `(uD0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(uD1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(p1:(128)word) = word_pmul (uA0:(64)word) (uD0:(64)word)` THEN
  ABBREV_TAC `(p2:(128)word) = word_pmul (uA1:(64)word) (uD1:(64)word)` THEN
  ABBREV_TAC `(p3:(128)word) =
    word_pmul (word_xor (uA0:(64)word) (uA1:(64)word))
              (word_xor (uD0:(64)word) (uD1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  ABBREV_TAC `(z1:(64)word) = word_subword (p1:(128)word) (0,64)` THEN
  ABBREV_TAC `(z2:(64)word) = word_subword (p1:(128)word) (64,64)` THEN
  ABBREV_TAC `(z3:(64)word) = word_subword (p2:(128)word) (0,64)` THEN
  ABBREV_TAC `(z4:(64)word) = word_subword (p2:(128)word) (64,64)` THEN
  ABBREV_TAC `(z5:(64)word) = word_subword (p3:(128)word) (0,64)` THEN
  ABBREV_TAC `(z6:(64)word) = word_subword (p3:(128)word) (64,64)` THEN
  ABBREV_TAC `(zD:(64)word) =
    word_subword (word_pmul (z1:(64)word) (word 13979173243358019584:(64)word):(128)word)
                 (0,64)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (z2:(64)word)
                (word_xor z5
                (word_xor z3
                (word_xor z1 zD))))
               (word 13979173243358019584:(64)word):(128)word =
     word_pmul (word_xor (z5:(64)word)
                (word_xor z1
                (word_xor z3
                (word_xor zD z2))))
               (word 13979173243358019584:(64)word):(128)word`
    ASSUME_TAC THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
    `qBigP = word_pmul
       (word_xor (z5:(64)word) (word_xor z1 (word_xor z3 (word_xor zD z2))))
       (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC
    `qSmallP = word_pmul (z1:(64)word)
                        (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC `qBigPL = word_subword (qBigP:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qBigPH = word_subword (qBigP:(128)word) (64,64):(64)word` THEN
  ABBREV_TAC `qSmallPH = word_subword (qSmallP:(128)word) (64,64):(64)word` THEN
  BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE];;

(* ========================================================================= *)
(*                         THE PROOF                                         *)
(* ========================================================================= *)

let ONE_BLOCK_PRELOOP_TAIL_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,452) (in_ptr:int64,16) /\
    nonoverlapping (word pc,452) (out_ptr:int64,16) /\
    nonoverlapping (word pc,452) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,452) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,452) (key_ptr:int64,240) /\
    nonoverlapping (word pc,452) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,452) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,16) (out_ptr,16) /\
    nonoverlapping (in_ptr,16) (xi_ptr,16) /\
    nonoverlapping (in_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,16) (xi_ptr,16) /\
    nonoverlapping (out_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,16) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,16) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,16) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,16) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,452) /\
    nonoverlapping (xi_ptr,16) (word pc,452) /\
    nonoverlapping (out_ptr,16) (word pc,452)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_one_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt /\
           read (memory :> bytes128 out_ptr) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = byteswap128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h)
      (\s. let ct = word_xor pt (aes256_block_enc ivec rk0 rk1 rk2 rk3
                     rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm = word_and ct mask in
           read PC s = word(pc + 448) /\
           read X0 s = word byte_len /\
           read (memory :> bytes128 out_ptr) s =
             word_or ctm (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ctm]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,16);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,

  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst ONE_BLOCK_PRELOOP_TAIL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue (shared across all N). *)
  ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-84: AES rounds for the single block. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--84) THEN

  (* Abbreviate the AES output (`ct` = full-block ciphertext, `s13` = round-13
     intermediate) so the shared CT/GHASH closure tactics can fold them back. *)
  ABBREV_TAC `ct = word_xor (word_xor pt (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese ivec rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13)) rk14:(128)word` THEN
  ABBREV_TAC `s13 = aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese ivec rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13:(128)word` THEN

  (* Collapse the data-dependent partial-block mask register (Q0/Q8/Q9) to
     word (2^(8*byte_len) - 1) via the mask-construction lemma. *)
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP ONE_BLOCK_MASK_REG th])) THEN
  DISCARD_OLDSTATE_TAC "s84" THEN

  (* Steps 85-104: bif (partial store fixup), counter store, masked-block
     store, GHASH Karatsuba up to the final EOR3 in Q19. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (85--104) THEN

  (* Post-simulation normalization, lifted into a named tactic. *)
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN

  (* ABBREV Q19 as `final_xi` BEFORE the EXT/REV64 byte-level explosion. *)
  ABBREV_FINAL_XI_TAC THEN

  (* Steps 105-112: EXT, REV64, ST1, MOV, LDP*4 — Q19 now opaque.  Stop just
     before the RET (#113); the postcondition PC is the RET's address (pc+448). *)
  ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC (105--112) THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[ONE_BLOCK_USHR_BYTELEN; ONE_BLOCK_MASK_IDEM] THEN
  CONJ_TAC THENL [
    GCM_CT_STEP_TAC;
    GCM_GHASH_STEP_MASKED_TAC
  ]);;
