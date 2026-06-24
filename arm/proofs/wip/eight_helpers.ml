let GCM_CBZ_LEMMA8 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(896+8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(896+8*byte_len):int64) = 896+8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let GCM_WSUB8 = prove
 (`byte_len <= 16 ==> word_sub (word (112+byte_len):int64) (word 1) = word (111 + byte_len)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `111 + byte_len = (112 + byte_len) - 1` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_SUB] THEN
  COND_CASES_TAC THENL [REFL_TAC; POP_ASSUM MP_TAC THEN ARITH_TAC]);;

let GCM_X8_LEMMA8 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (896+8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (896+8*byte_len):int64) 3 = word (112+byte_len)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[EIGHTBLOCK_USHR]; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB8] THEN
  SUBGOAL_THEN `word_and (word (111+byte_len):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let GCM_X8TAIL_LEMMA8 = prove
 (`byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (896+8*byte_len):int64) 3)) in_ptr = word (112+byte_len)`,
  STRIP_TAC THEN ASM_SIMP_TAC[EIGHTBLOCK_USHR] THEN CONV_TAC WORD_RULE);;


(* Cascade for more_than_7: total lanes = 112+byte_len (113..128).  The b.gt #112
   is taken directly (total >= 113) into .more_than_7.  No FALSE thresholds;
   TRUE threshold = 112.  (more_than_7 is the highest/last dispatch branch.) *)
let GCM_CASC8_TRUE = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word (112+byte_len):int64) (word 112)) = 0) /\
      (ival (word_sub (word (112+byte_len):int64) (word 112)) < &0 <=>
       ~(ival (word (112+byte_len):int64) - &112 = ival (word_sub (word (112+byte_len):int64) (word 112)))))
     <=> T)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (112+byte_len):int64) = &(112+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (112+byte_len):int64) (word 112) = iword(&(112+byte_len) - &112)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(112+byte_len) - &112):int64) = &(112+byte_len) - &112` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 63 = 9223372036854775808`] THEN
    SUBGOAL_THEN `&(112+byte_len):int <= &128` MP_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&1:int <= &byte_len` MP_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASCADE8_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP GCM_CASC8_TRUE (CONJ bl1 bl16); COND_CLAUSES]) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;
