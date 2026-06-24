let AES256_GCM_ENCRYPT_LT_4BLOCK_CORRECT = prove
 (gcm_4b_goal,
  GCM_INIT_TAC GCM_CBZ_LEMMA4 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  FIRST_ASSUM(fun th -> if can(term_match[]`read Q0 (s:armstate)=(x:int128)`)(concl th)
    then ABBREV_TAC(mk_eq(mk_var("s13_1",`:(128)word`),rand(concl th))) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can(term_match[]`read Q1 (s:armstate)=(x:int128)`)(concl th)
    then ABBREV_TAC(mk_eq(mk_var("s13_2",`:(128)word`),rand(concl th))) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can(term_match[]`read Q2 (s:armstate)=(x:int128)`)(concl th)
    then ABBREV_TAC(mk_eq(mk_var("s13_3",`:(128)word`),rand(concl th))) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can(term_match[]`read Q3 (s:armstate)=(x:int128)`)(concl th)
    then ABBREV_TAC(mk_eq(mk_var("s13_4",`:(128)word`),rand(concl th))) else NO_TAC) THEN
  GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA4 THEN GCM_RUN 267 272 THEN GCM_BND16 GCM_X5TAIL_LEMMA4 THEN
  GCM_RUN_THEN GCM_CASCADE4_TAC 273 321 THEN
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN
  GCM_RUN 322 335 THEN ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN
  GCM_RUN 336 348 THEN ABBREV_TAC `ct3 = word_xor (word_xor pt3 s13_3) rk14:(128)word` THEN
  GCM_RUN 349 366 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FOURBLOCK_MASK_REG th])) THEN
  GCM_RUN 367 379 THEN GCM_RUN 380 394 THEN ARM_STEPS_TAC AES256_GCM_EXEC (395--395) THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (396--403) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FOURBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[FOURBLOCK_USHR] THEN
  CONJ_TAC THENL [GCM_CT1_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [
    SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FOURBLOCK_MASK_REG th]) THEN
    REWRITE_TAC[NBLOCK_MASK_IDEM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `s13_4:(128)word` &&
        not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE; CTR_WORD_INSERT] THEN
    REWRITE_TAC[gcm_ctr_inc] THEN
    ABBREV_TAC `ctr3b:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
    ABBREV_TAC `br3b:(32)word = word_bytereverse (ctr3b:(32)word)` THEN
    ABBREV_TAC `step1_3b:(32)word = word_bytereverse (word_add (br3b:(32)word) (word 1:(32)word))` THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "step1_3b" THEN
    REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
    CONV_TAC WORD_RULE; ALL_TAC] THEN
  MASK_COLLAPSE_TAC THEN
  ABBREV_TAC `ct4 = word_xor (word_xor pt4 s13_4) rk14:(128)word` THEN
  SUBGOAL_THEN `word_xor pt4 (word_xor s13_4 rk14) = ct4:(128)word` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th)=`ct4:(128)word` &&
        aconv (lhs(concl th)) `word_xor (word_xor pt4 s13_4) rk14:(128)word`
       then REWRITE_TAC[SYM th] else NO_TAC) THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  FOLD_AND_BRIDGE THEN GHASH_TAIL3a THEN MASK_COLLAPSE_TAC THEN DROP_CT_STORES THEN
  SUBGOAL_THEN `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th)=`ct1:(128)word` &&
        aconv (lhs(concl th)) `word_xor pt1 (word_xor s13_1 rk14):(128)word`
       then REWRITE_TAC[SYM th] else NO_TAC) THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  TAIL_P1 THEN TAIL_P2c THEN BINOP_TAC THEN LEAF2);;
