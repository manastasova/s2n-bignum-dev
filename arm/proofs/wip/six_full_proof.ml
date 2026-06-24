(* Full assembled AES256_GCM_ENCRYPT_LT_6BLOCK_CORRECT proof (more_than_5).    *)
(* Depends on: gcm_six_block_closers.ml, wip/sixgoal.ml, wip/six_helpers.ml,   *)
(* wip/five_abbrev_ct.ml, wip/six_ghash_closer.ml.                             *)

(* ct1 closer (counter = ivec, no inc). *)
let CT_CLOSE_6 nidx =
  let s13n = "s13_"^string_of_int nidx and ctn = "ct"^string_of_int nidx in
  EXPAND_TAC ctn THEN EXPAND_TAC s13n THEN
  REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];;

(* masked-ct6 store conjunct closer: collapse the mask reg, peel word_or/
   word_and/word_xor to the counter identity (machine +5 form vs spec
   gcm_ctr_inc^5), discharge with the nested-insert collapse. *)
let GCM_6B_MASKED_CT6_CLOSE : tactic =
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add5 = WORD_RULE `word_add (word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 5)` in
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP SIXBLOCK_MASK_REG th]) THEN
  REWRITE_TAC[NBLOCK_MASK_IDEM] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_or (word_and x m) r = word_or (word_and y m) r:(128)word`) THEN
  AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
              CTR_WORD_INSERT] THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
  REWRITE_TAC[add5; BYTEREVERSE_JOIN_FOLD] THEN
  AP_TERM_TAC THEN REWRITE_TAC[bri] THEN REWRITE_TAC[add5];;

let AES256_GCM_ENCRYPT_LT_6BLOCK_CORRECT = prove
 (gcm_6b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA6 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X6_LEMMA6 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X6TAIL_LEMMA6 THEN
  GCM_RUN_THEN GCM_CASCADE6_TAC 273 321 THEN
  abbrev_ct_from_store 0 1 THEN abbrev_ct_from_store 16 2 THEN
  GCM_RUN 322 335 THEN abbrev_ct_from_store 32 3 THEN
  GCM_RUN 336 362 THEN abbrev_ct_from_store 48 4 THEN
  GCM_RUN 363 376 THEN abbrev_ct_from_store 64 5 THEN
  GCM_RUN 377 411 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SIXBLOCK_MASK_REG th])) THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (412--419) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP SIXBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[SIXBLOCK_USHR] THEN
  (* ---- seven conjuncts: ct1..ct5, masked-ct6, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_6 1; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT5_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_6B_MASKED_CT6_CLOSE; ALL_TAC] THEN
  (* ---- ct6 abbreviation (spec form) so the closer's ctm6 works ---- *)
  ABBREV_TAC `ct6 = word_xor pt6
    (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))))
                      rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_6B_GHASH_CLOSE);;
