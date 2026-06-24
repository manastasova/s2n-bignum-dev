let GHASH_TAIL3a =
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_4block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word)
                             (karatsuba_mid (polyval_dot h h):(64)word)
                   :(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word)
                             (karatsuba_mid (polyval_dot (polyval_dot h h)
                                                          (polyval_dot h h)):(64)word)
                   :(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try (let l = lhs(concl th) in
             is_comb l &&
             (let r = rator l in
              not(is_comb r &&
                  (try fst(dest_const(rator r)) = "read" with _ -> false))))
        with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
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
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* GHASH closure in 5/6-block style: 18 atomic + 12 pmul + 24 z-var ABBREVs,
     qS/qB Barrett pmuls, bubble_sort_conv XOR-AC closure. The two byte-form
     folds below are 4-block-specific (ct1 is not opaque in the mid term). *)
  ALL_TAC;;
