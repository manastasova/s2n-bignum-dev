(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC
 *)

(* ========================================================================= *)
(* Tripling modulo p_sm2, the field characteristic for the CC SM2 curve.     *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/sm2/bignum_triple_sm2.o";;
 ****)

let bignum_triple_sm2_mc = define_assert_from_elf "bignum_triple_sm2_mc" "arm/sm2/bignum_triple_sm2.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411825;       (* arm_LDP X5 X6 X1 (Immediate_Offset (iword (&16))) *)
  0xd37ff862;       (* arm_LSL X2 X3 1 *)
  0xab030042;       (* arm_ADDS X2 X2 X3 *)
  0x93c3fc83;       (* arm_EXTR X3 X4 X3 63 *)
  0xba040063;       (* arm_ADCS X3 X3 X4 *)
  0x93c4fca4;       (* arm_EXTR X4 X5 X4 63 *)
  0xba050084;       (* arm_ADCS X4 X4 X5 *)
  0x93c5fcc5;       (* arm_EXTR X5 X6 X5 63 *)
  0xba0600a5;       (* arm_ADCS X5 X5 X6 *)
  0xd37ffcc6;       (* arm_LSR X6 X6 63 *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0x910004c6;       (* arm_ADD X6 X6 (rvalue (word 1)) *)
  0xd3607cc7;       (* arm_LSL X7 X6 32 *)
  0xcb0600e8;       (* arm_SUB X8 X7 X6 *)
  0xab060042;       (* arm_ADDS X2 X2 X6 *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0xda9f23e6;       (* arm_CSETM X6 Condition_CC *)
  0xab060042;       (* arm_ADDS X2 X2 X6 *)
  0x92607cc8;       (* arm_AND X8 X6 (rvalue (word 18446744069414584320)) *)
  0xba080063;       (* arm_ADCS X3 X3 X8 *)
  0xba060084;       (* arm_ADCS X4 X4 X6 *)
  0x925ff8c7;       (* arm_AND X7 X6 (rvalue (word 18446744069414584319)) *)
  0x9a0700a5;       (* arm_ADC X5 X5 X7 *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_TRIPLE_SM2_EXEC = ARM_MK_EXEC_RULE bignum_triple_sm2_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let sm2genshortredlemma = prove
 (`!n. n < 3 * 2 EXP 256
       ==> let q = (n DIV 2 EXP 256) + 1 in
           q <= 3 /\
           q * p_sm2 <= n + p_sm2 /\
           n < q * p_sm2 + p_sm2`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_sm2] THEN ARITH_TAC);;

let BIGNUM_TRIPLE_SM2_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x74) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_triple_sm2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = word (pc + 0x70) /\
                  bignum_from_memory (z,4) s = (3 * n) MOD p_sm2)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  (*** Input load and initial multiplication by 3 ***)

  ARM_ACCSTEPS_TAC BIGNUM_TRIPLE_SM2_EXEC (1--12) (1--12) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s4; sum_s6; sum_s8; sum_s10; sum_s12] =
    3 * n`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN EXPAND_TAC "mullo_s11" THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_0; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 = 1 + 63`; EXP_ADD; MOD_MULT2] THEN
    REWRITE_TAC[ADD_SUB; DIV_0; REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
    REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`read (rvalue y) s = x`; `word_subword a b = c`; `word_shl a b = c`] THEN
    DISCARD_FLAGS_TAC] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = (3 * n) DIV 2 EXP 256` THEN
  SUBGOAL_THEN `h < 3` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 4)` THEN EXPAND_TAC "h" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s12:int64 = word h` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `3 * n` sm2genshortredlemma) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 4)` THEN ARITH_TAC;
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of 3 * n - (h + 1) * p_sm2 ***)

  ARM_ACCSTEPS_TAC BIGNUM_TRIPLE_SM2_EXEC (16--19) (13--20) THEN
  MP_TAC(SPECL
   [`word_neg(word(bitval(~carry_s19))):int64`;
    `&(bignum_of_wordlist[sum_s16; sum_s17; sum_s18; sum_s19]):real`;
    `256`; `3 * n`; `(h + 1) * p_sm2`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_NOT_MASK; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_sm2 <= 3 * n + p_sm2`;
        `3 * n < (h + 1) * p_sm2 + p_sm2`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist[sum_s4; sum_s6; sum_s8; sum_s10; word h] =
      3 * n`)) THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 3` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REWRITE_TAC[REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
    REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    REWRITE_TAC[WORD_ARITH `word_neg x = word_neg y <=> val x = val y`] THEN
    REWRITE_TAC[VAL_WORD_BITVAL; EQ_BITVAL] THEN
    REWRITE_TAC[TAUT `(~p <=> q) <=> (p <=> ~q)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP]) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  ARM_ACCSTEPS_TAC BIGNUM_TRIPLE_SM2_EXEC [21;23;24;26] (21--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> 3 * n < (h + 1) * p_sm2` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &(3 * n) - y + z ==> &(3 * n) = x + y - z`)) THEN
  REWRITE_TAC[p_sm2] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_sm2; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_TRIPLE_SM2_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
        nonoverlapping (word pc,0x74) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_triple_sm2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,4) s = (3 * n) MOD p_sm2)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_TRIPLE_SM2_EXEC
    BIGNUM_TRIPLE_SM2_CORRECT);;
