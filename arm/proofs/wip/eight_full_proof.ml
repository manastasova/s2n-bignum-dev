(* Full assembled AES256_GCM_ENCRYPT_LT_8BLOCK_CORRECT proof (more_than_7).
   Mirrors the 7-block (more_than_6) recipe.  The more_than_7 path is the
   highest dispatch branch (b.gt #112 taken directly to the 8-wide GHASH at
   0xf98), which reads scratch register Q18 via an INS (mov v18.d[0]) before
   fully writing it; the precondition pins read Q18 = q18i (its high lane is
   dead, overwritten by the pmull that uses only the low lane). *)

let AES256_GCM_ENCRYPT_LT_8BLOCK_CORRECT = prove
 (gcm_8b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA8 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X8_LEMMA8 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X8TAIL_LEMMA8 THEN
  GCM_RUN_THEN GCM_CASCADE8_TAC 273 276 THEN
  GCM_RUN 277 300 THEN
  abbrev_ct8 0 1 THEN abbrev_ct8 16 2 THEN
  GCM_RUN 301 340 THEN
  abbrev_ct8 32 3 THEN abbrev_ct8 48 4 THEN abbrev_ct8 64 5 THEN
  GCM_RUN 341 370 THEN
  abbrev_ct8 80 6 THEN abbrev_ct8 96 7 THEN
  GCM_RUN 371 417 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP EIGHTBLOCK_MASK_REG th])) THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (418--425) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP EIGHTBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[EIGHTBLOCK_USHR] THEN
  (* ---- nine conjuncts: ct1..ct7, masked-ct8, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_8 1; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT5_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT6_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT7_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_8B_MASKED_CT8_CLOSE; ALL_TAC] THEN
  (* ---- ct8 abbreviation (spec form) so the closer's ctm8 works ---- *)
  ABBREV_TAC `ct8 = word_xor pt8
    (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))))))
                      rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_8B_GHASH_CLOSE);;
