(* === 4-block-branch helpers (param 48+byte_len, C-arg 384+8*byte_len) === *)
let GCM_CT2_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 4 2;;
let GCM_CT3_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 4 3;;

let GCM_CBZ_LEMMA4 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(384+8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(384+8*byte_len):int64) = 384+8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let GCM_WSUB4 = prove
 (`byte_len <= 16 ==> word_sub (word (48+byte_len):int64) (word 1) = word (47 + byte_len)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `47 + byte_len = (48 + byte_len) - 1` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_SUB] THEN
  COND_CASES_TAC THENL [REFL_TAC; POP_ASSUM MP_TAC THEN ARITH_TAC]);;

let GCM_X5_LEMMA4 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (384+8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (384+8*byte_len):int64) 3 = word (48+byte_len)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[FOURBLOCK_USHR]; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB4] THEN
  SUBGOAL_THEN `word_and (word (47+byte_len):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let GCM_X5TAIL_LEMMA4 = prove
 (`byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (384+8*byte_len):int64) 3)) in_ptr = word (48+byte_len)`,
  STRIP_TAC THEN ASM_SIMP_TAC[FOURBLOCK_USHR] THEN CONV_TAC WORD_RULE);;

let GCM_CASC4_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 64 <= t /\ t <= 112 ==>
    ((~(val (word_sub (word (48+byte_len):int64) (word t)) = 0) /\
      (ival (word_sub (word (48+byte_len):int64) (word t)) < &0 <=>
       ~(ival (word (48+byte_len):int64) - &t = ival (word_sub (word (48+byte_len):int64) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (48+byte_len):int64) = &(48+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (48+byte_len):int64) (word t) = iword(&(48+byte_len) - &t)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(48+byte_len) - &t):int64) = &(48+byte_len) - &t` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 63 = 9223372036854775808`] THEN
    SUBGOAL_THEN `&(48+byte_len):int <= &64 /\ &64:int <= &t /\ &t:int <= &112` MP_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  SUBGOAL_THEN `&(48+byte_len):int <= &64 /\ &64:int <= &t` MP_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASC4_TRUE = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word (48+byte_len):int64) (word 48)) = 0) /\
      (ival (word_sub (word (48+byte_len):int64) (word 48)) < &0 <=>
       ~(ival (word (48+byte_len):int64) - &48 = ival (word_sub (word (48+byte_len):int64) (word 48)))))
     <=> T)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (48+byte_len):int64) = &(48+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (48+byte_len):int64) (word 48) = iword(&(48+byte_len) - &48)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(48+byte_len) - &48):int64) = &(48+byte_len) - &48` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 63 = 9223372036854775808`] THEN
    SUBGOAL_THEN `&(48+byte_len):int <= &64` MP_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&1:int <= &byte_len` MP_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASCADE4_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE(
        (map (fun t -> MATCH_MP GCM_CASC4_FALSE (CONJ bl16
                (CONJ (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `64 <= t`))
                      (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `t <= 112`)))))
             [64;80;96;112]) @
        [MATCH_MP GCM_CASC4_TRUE (CONJ bl1 bl16); COND_CLAUSES])) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;
