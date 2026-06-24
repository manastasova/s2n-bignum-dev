(* Full assembled AES256_GCM_ENCRYPT_LT_7BLOCK_CORRECT proof (more_than_6).
   Depends on (already loaded in session):
   gcm_seven_block_closers.ml, GCM_ANDMASK0, five_abbrev_ct.ml, seven_helpers.ml,
   sevengoal.ml (WITH h7k), seven_abbrev_ct7.ml (abbrev_ct7/CT_CLOSE_7/
   GCM_7B_MASKED_CT7_CLOSE), seven_ghash_closer.ml (GCM_7B_GHASH_CLOSE etc). *)

let AES256_GCM_ENCRYPT_LT_7BLOCK_CORRECT = prove
 (gcm_7b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA7 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X7_LEMMA7 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X7TAIL_LEMMA7 THEN
  GCM_RUN_THEN GCM_CASCADE7_TAC 273 321 THEN
  abbrev_ct7 0 1 THEN abbrev_ct7 16 2 THEN abbrev_ct7 32 3 THEN
  GCM_RUN 322 348 THEN abbrev_ct7 48 4 THEN
  GCM_RUN 349 362 THEN abbrev_ct7 64 5 THEN
  GCM_RUN 363 376 THEN abbrev_ct7 80 6 THEN
  GCM_RUN 377 417 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SEVENBLOCK_MASK_REG th])) THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (418--425) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP SEVENBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[SEVENBLOCK_USHR] THEN
  (* ---- eight conjuncts: ct1..ct6, masked-ct7, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_7 1; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT5_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT6_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_7B_MASKED_CT7_CLOSE; ALL_TAC] THEN
  (* ---- ct7 abbreviation (spec form) so the closer's ctm7 works ---- *)
  ABBREV_TAC `ct7 = word_xor pt7
    (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))))
                      rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_7B_GHASH_CLOSE);;
