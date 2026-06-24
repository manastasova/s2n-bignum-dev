(* ===== helper lemmas for the GHASH final closure ===== *)
let XI_HS_LO = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (0,64):(64)word =
   word_subword (word_reversefields 8 xi) (0,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;
let XI_HS_HI = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (64,64):(64)word =
   word_subword (word_reversefields 8 xi) (64,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

let GCM_CT1_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 4 1;;

let MASK_COLLAPSE_TAC =
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= byte_len /\ byte_len <= 16` then
    REWRITE_TAC[GEN `b0:int128` (MP (SPEC_ALL FOURBLOCK_MASK_REG) bth)] else NO_TAC);;

let DROP_CT_STORES =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       (rand(concl th)=`ct1:(128)word` || rand(concl th)=`ct2:(128)word` || rand(concl th)=`ct3:(128)word`) &&
       can(term_match[]`read (memory :> bytes128 p) (s:armstate)`)(lhs(concl th))
    then ALL_TAC else NO_TAC));;

let CLOSE_C1BYTE =
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th)=`ct1:(128)word` &&
      can(term_match[]`read (memory :> bytes128 out_ptr) (s:armstate)`)(lhs(concl th))
     then REWRITE_TAC[th] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th)=`ct1:(128)word` &&
      aconv (lhs(concl th)) `word_xor pt1 (word_xor s13_1 rk14):(128)word`
     then REWRITE_TAC[th] else NO_TAC);;

(* leaf closer for each XOR-sum half *)
let GHASH_LEAF_CLOSE =
  REWRITE_TAC[XI_HS_LO; XI_HS_HI] THEN
  (SUBGOAL_THEN `word_and mask ct4 = ctm4:(128)word` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th)=`ctm4:(128)word` &&
       aconv(lhs(concl th))`word_and ct4 mask:(128)word` then
       (GEN_REWRITE_TAC RAND_CONV [SYM th] THEN CONV_TAC WORD_BITWISE_RULE) else NO_TAC); ALL_TAC]
   ORELSE ALL_TAC) THEN
  (SUBGOAL_THEN `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo))) (word_xor (hg0:(64)word) hg1):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC]
   ORELSE ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;;
