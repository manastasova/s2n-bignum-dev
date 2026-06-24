let FOLD_AND_BRIDGE =
  REWRITE_TAC[GHASH_POLYVAL_ACC_4; POLYVAL_DOT_H4_EQ_LOCAL;
              GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  (* Fold xi⊕pt1⊕aes = xi⊕ct1 *)
  SUBGOAL_THEN
    `word_xor xi (word_xor pt1
       (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                         rk8 rk9 rk10 rk11 rk12 rk13 rk14)) =
     word_xor xi ct1:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ct1" THEN EXPAND_TAC "s13_1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC
  ] THEN
  (* Fold pt2⊕aes = ct2 *)
  SUBGOAL_THEN
    `word_xor pt2
       (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4 rk5 rk6
                         rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) =
     ct2:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `ct2:(128)word` &&
         aconv (lhs(concl th))
               `word_xor pt2 (word_xor s13_2 rk14):(128)word`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[aes256_block_enc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `s13_2:(128)word` &&
         not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read"
             with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN;
                LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT; gcm_ctr_inc] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD];
    ALL_TAC
  ] THEN
  (* Fold pt3⊕aes(gcm_ctr_inc²) = ct3 *)
  SUBGOAL_THEN
    `word_xor pt3
       (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc ivec))
                         rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11
                         rk12 rk13 rk14) =
     ct3:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `ct3:(128)word` &&
         aconv (lhs(concl th))
               `word_xor pt3 (word_xor s13_3 rk14):(128)word`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[aes256_block_enc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `s13_3:(128)word` &&
         not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read"
             with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN;
                LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT] THEN
    REWRITE_TAC[gcm_ctr_inc] THEN
    ABBREV_TAC `ctr2b:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
    ABBREV_TAC `br2b:(32)word = word_bytereverse (ctr2b:(32)word)` THEN
    ABBREV_TAC `step1_2b:(32)word = word_bytereverse (word_add (br2b:(32)word) (word 1:(32)word))` THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "step1_2b" THEN
    REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC
  ] THEN
  (* Fold pt4⊕aes(gcm_ctr_inc³) = ct4 *)
  SUBGOAL_THEN
    `word_xor pt4
       (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))
                         rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11
                         rk12 rk13 rk14) =
     ct4:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `ct4:(128)word` &&
         aconv (lhs(concl th))
               `word_xor pt4 (word_xor s13_4 rk14):(128)word`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[aes256_block_enc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `s13_4:(128)word` &&
         not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read"
             with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN;
                LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT] THEN
    REWRITE_TAC[gcm_ctr_inc] THEN
    ABBREV_TAC `ctr3b:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
    ABBREV_TAC `br3b:(32)word = word_bytereverse (ctr3b:(32)word)` THEN
    ABBREV_TAC `step1_3b:(32)word = word_bytereverse (word_add (br3b:(32)word) (word 1:(32)word))` THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "step1_3b" THEN
    REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC
  ] THEN
  (* Partial last block: abbreviate the mask and the masked block ctm4, and
     bridge the simulator's word_and mask ct4 to ctm4 = word_and ct4 mask. *)
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm4 = word_and (ct4:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct4:(128)word) = ctm4`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm4" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  (* Normalize h^3 from left-assoc (polyval_dot (polyval_dot h h) h) to the
     symmetric form (polyval_dot h (polyval_dot h h)) used by the bridge. *)
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h =
     polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  (* Apply bridge lemma *)
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`;
     `word_reversefields 8 ct3:int128`;
     `word_reversefields 8 ctm4:int128`;
     `h:int128`; `h1k:int128`;
     `word_join (word 0:(64)word)
        (word_subword (h1k:(128)word) (64,64):(64)word)
      :(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word)
        (word_subword (h3k:(128)word) (64,64):(64)word)
      :(128)word`]
    GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword
       (word_join (word 0:(64)word)
                  (word_subword (h1k:(128)word) (64,64):(64)word)
        :(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword
         (word_join (word 0:(64)word)
                    (word_subword (h1k:(128)word) (64,64):(64)word)
          :(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL
      [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]];
    ALL_TAC
  ] THEN
  SUBGOAL_THEN
    `word_subword
       (word_join (word 0:(64)word)
                  (word_subword (h3k:(128)word) (64,64):(64)word)
        :(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword
         (word_join (word 0:(64)word)
                    (word_subword (h3k:(128)word) (64,64):(64)word)
          :(128)word) (0,64):(64)word =
       word_subword (h3k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL
      [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]];
    ALL_TAC
  ] THEN
  ASM_REWRITE_TAC[] THEN
  ALL_TAC;;
