(* ========================================================================= *)
(* Self-contained 8-block GHASH conjunct closer for the single-binary        *)
(* aes256_gcm.ml more_than_7 (8-block) branch.  Reaches "No subgoals" from    *)
(* the final GHASH equality (machine word_join = spec word_reversefields).    *)
(* Mirrors the 7-block recipe (GCM_7B_GHASH_CLOSE); adds the ks8 +7-counter   *)
(* bridge and the in-asm b0-general mask-register collapse that the 8-block   *)
(* sim leaves baked into final_xi.                                            *)
(* ========================================================================= *)

let XI_HS_LO_8 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (0,64):(64)word =
   word_subword (word_reversefields 8 xi) (0,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

let XI_HS_HI_8 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (64,64):(64)word =
   word_subword (word_reversefields 8 xi) (64,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

let GCM_8B_TAIL_NOFINAL : tactic =
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm8 = word_and (ct8:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct8:(128)word) = ctm8`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm8" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h =
     polyval_dot (polyval_dot h h) (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[POLYVAL_DOT_H4_EQ_LOCAL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`;
     `word_reversefields 8 ct3:int128`;
     `word_reversefields 8 ct4:int128`;
     `word_reversefields 8 ct5:int128`;
     `word_reversefields 8 ct6:int128`;
     `word_reversefields 8 ct7:int128`;
     `word_reversefields 8 ctm8:int128`;
     `h:int128`;
     `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word`;
     `h5k:int128`;
     `word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word`;
     `h7k:int128`;
     `word_join (word 0:(64)word) (word_subword (h7k:(128)word) (64,64):(64)word):(128)word`]
    GHASH_8BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h3k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h5k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h7k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h7k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h7k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_8block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot h h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try (let l = lhs(concl th) in is_comb l &&
             (let r = rator l in not(is_comb r && (try fst(dest_const(rator r)) = "read" with _ -> false))))
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
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* c-atom ABBREVs *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c4lo:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c4hi:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c5lo:(64)word) = word_subword (word_reversefields 8 (ct5:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c5hi:(64)word) = word_subword (word_reversefields 8 (ct5:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c6lo:(64)word) = word_subword (word_reversefields 8 (ct6:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c6hi:(64)word) = word_subword (word_reversefields 8 (ct6:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c7lo:(64)word) = word_subword (word_reversefields 8 (ct7:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c7hi:(64)word) = word_subword (word_reversefields 8 (ct7:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c8lo:(64)word) = word_subword (word_reversefields 8 (ctm8:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c8hi:(64)word) = word_subword (word_reversefields 8 (ctm8:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hf0:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hf1:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hg0:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hg1:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hh0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hh1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hj0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hj1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hm0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hm1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hn0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hn1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* inner pmul ABBREVs *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hn0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hn1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hn0:(64)word) (hn1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hm0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hm1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hm0:(64)word) (hm1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (hj0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (hj1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (hj0:(64)word) (hj1:(64)word))` THEN
  ABBREV_TAC `(w4lo:(128)word) = word_pmul (c4lo:(64)word) (hh0:(64)word)` THEN
  ABBREV_TAC `(w4hi:(128)word) = word_pmul (c4hi:(64)word) (hh1:(64)word)` THEN
  ABBREV_TAC `(w4md:(128)word) = word_pmul (word_xor (c4hi:(64)word) (c4lo:(64)word)) (word_xor (hh0:(64)word) (hh1:(64)word))` THEN
  ABBREV_TAC `(w5lo:(128)word) = word_pmul (c5lo:(64)word) (hg0:(64)word)` THEN
  ABBREV_TAC `(w5hi:(128)word) = word_pmul (c5hi:(64)word) (hg1:(64)word)` THEN
  ABBREV_TAC `(w5md:(128)word) = word_pmul (word_xor (c5hi:(64)word) (c5lo:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word))` THEN
  ABBREV_TAC `(w6lo:(128)word) = word_pmul (c6lo:(64)word) (hf0:(64)word)` THEN
  ABBREV_TAC `(w6hi:(128)word) = word_pmul (c6hi:(64)word) (hf1:(64)word)` THEN
  ABBREV_TAC `(w6md:(128)word) = word_pmul (word_xor (c6hi:(64)word) (c6lo:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w7lo:(128)word) = word_pmul (c7lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w7hi:(128)word) = word_pmul (c7hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w7md:(128)word) = word_pmul (word_xor (c7hi:(64)word) (c7lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w8lo:(128)word) = word_pmul (c8lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w8hi:(128)word) = word_pmul (c8hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w8md:(128)word) = word_pmul (word_xor (c8hi:(64)word) (c8lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hn0:(64)word) (hn1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* z-vars *)
  ABBREV_TAC `(w1lo_l:(64)word) = word_subword (w1lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1lo_h:(64)word) = word_subword (w1lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1hi_l:(64)word) = word_subword (w1hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1hi_h:(64)word) = word_subword (w1hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1md_l:(64)word) = word_subword (w1md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1md_h:(64)word) = word_subword (w1md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2lo_l:(64)word) = word_subword (w2lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2lo_h:(64)word) = word_subword (w2lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2hi_l:(64)word) = word_subword (w2hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2hi_h:(64)word) = word_subword (w2hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2md_l:(64)word) = word_subword (w2md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2md_h:(64)word) = word_subword (w2md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3lo_l:(64)word) = word_subword (w3lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3lo_h:(64)word) = word_subword (w3lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3hi_l:(64)word) = word_subword (w3hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3hi_h:(64)word) = word_subword (w3hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3md_l:(64)word) = word_subword (w3md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3md_h:(64)word) = word_subword (w3md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4lo_l:(64)word) = word_subword (w4lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4lo_h:(64)word) = word_subword (w4lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4hi_l:(64)word) = word_subword (w4hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4hi_h:(64)word) = word_subword (w4hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4md_l:(64)word) = word_subword (w4md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4md_h:(64)word) = word_subword (w4md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5lo_l:(64)word) = word_subword (w5lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5lo_h:(64)word) = word_subword (w5lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5hi_l:(64)word) = word_subword (w5hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5hi_h:(64)word) = word_subword (w5hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5md_l:(64)word) = word_subword (w5md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5md_h:(64)word) = word_subword (w5md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6lo_l:(64)word) = word_subword (w6lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6lo_h:(64)word) = word_subword (w6lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6hi_l:(64)word) = word_subword (w6hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6hi_h:(64)word) = word_subword (w6hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6md_l:(64)word) = word_subword (w6md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6md_h:(64)word) = word_subword (w6md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w7lo_l:(64)word) = word_subword (w7lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w7lo_h:(64)word) = word_subword (w7lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w7hi_l:(64)word) = word_subword (w7hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w7hi_h:(64)word) = word_subword (w7hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w7md_l:(64)word) = word_subword (w7md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w7md_h:(64)word) = word_subword (w7md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w8lo_l:(64)word) = word_subword (w8lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w8lo_h:(64)word) = word_subword (w8lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w8hi_l:(64)word) = word_subword (w8hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w8hi_h:(64)word) = word_subword (w8hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w8md_l:(64)word) = word_subword (w8md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w8md_h:(64)word) = word_subword (w8md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Normalize LHS mid-pmuls to abbreviated w?md (swapped xor arg order). *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hm0:(64)word) (hm1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (hj0:(64)word) (hj1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c4lo:(64)word) (c4hi:(64)word)) (word_xor (hh0:(64)word) (hh1:(64)word)):(128)word = w4md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w4md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c5lo:(64)word) (c5hi:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w5md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w5md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c6lo:(64)word) (c6hi:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w6md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w6md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c7lo:(64)word) (c7hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w7md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w7md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c8lo:(64)word) (c8hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w8md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w8md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hn0:(64)word) (hn1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w8lo_l:(64)word) (word_xor w7lo_l (word_xor w6lo_l (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (w1lo_l)))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l (word_xor w6lo_l (word_xor w7lo_l (w8lo_l)))))))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w8md_l:(64)word) (word_xor w7md_l (word_xor w6md_l (word_xor w5md_l (word_xor w4md_l (word_xor w3md_l (word_xor w2md_l (word_xor w1md_l (word_xor w8lo_l (word_xor w7lo_l (word_xor w6lo_l (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w8hi_l (word_xor w7hi_l (word_xor w6hi_l (word_xor w5hi_l (word_xor w4hi_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w8lo_h (word_xor w7lo_h (word_xor w6lo_h (word_xor w5lo_h (word_xor w4lo_h (word_xor w3lo_h (word_xor w2lo_h (w1lo_h))))))))))))))))))))))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w4lo_h (word_xor w5lo_h (word_xor w6lo_h (word_xor w7lo_h (word_xor w8lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w4md_l (word_xor w5md_l (word_xor w6md_l (word_xor w7md_l (word_xor w8md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w4hi_l (word_xor w5hi_l (word_xor w6hi_l (word_xor w7hi_l (word_xor w8hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l (word_xor w6lo_l (word_xor w7lo_l (word_xor w8lo_l ((word_subword (qS:(128)word) (0,64))))))))))))))))))))))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* Step 4: b0-general mask-register collapse, applied to ALL assumptions. *)
let GCM_8B_MASK_COLLAPSE_ASMS : tactic =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[GEN `b0:int128` (MP (SPEC_ALL EIGHTBLOCK_MASK_REG) bth)]) else NO_TAC);;

(* Step 5: bridge the machine block-8 keystream (collapsed +7 counter, baked
   into final_xi) to the spec ct8. *)
let GCM_8B_KS8_FOLD : tactic = fun (asl,w) ->
  let substr sub s =
    let ls=String.length s and lb=String.length sub in
    let rec go i = if i+lb>ls then false
                   else if String.sub s i lb = sub then true else go(i+1) in go 0 in
  let fxidef = snd(find (fun (_,th) ->
    is_eq(concl th) && (try rand(concl th)=`final_xi:(128)word` with _->false)) asl) in
  let body = lhs(concl fxidef) in
  let best = ref body in
  let rec walk t =
    (try let s=string_of_term t in
      if substr "pt8" s && substr "aese" s &&
         (try fst(dest_const(repeat rator t))="word_xor" with _->false) &&
         String.length s < String.length(string_of_term !best) then best := t
     with _->());
    (match t with Comb(a,b)->walk a; walk b | Abs(_,b)->walk b | _->()) in
  walk body;
  let ks8 = !best in
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add7 = WORD_RULE `word_add (word_add (word_add (word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 7)` in
  (SUBGOAL_THEN (mk_eq(ks8, `ct8:(128)word`)) ASSUME_TAC THENL
    [EXPAND_TAC "ct8" THEN
     REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
     REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                 CTR_WORD_INSERT] THEN
     REWRITE_TAC[gcm_ctr_inc] THEN
     CONV_TAC SYM_CONV THEN
     REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
     REWRITE_TAC[add7; BYTEREVERSE_JOIN_FOLD] THEN
     AP_TERM_TAC THEN REWRITE_TAC[bri] THEN REWRITE_TAC[add7];
     ALL_TAC] THEN
   FIRST_ASSUM(fun th ->
     if is_eq(concl th) && rand(concl th)=`ct8:(128)word` &&
        (try fst(dest_const(repeat rator (lhs(concl th))))="word_xor" with _->false) &&
        String.length(string_of_term(lhs(concl th))) > 1000
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC))
  (asl,w);;

let GCM_8B_QB_FOLD : tactic = fun (asl,w) ->
  let found = ref [] in
  let rec walk t =
    (try if is_comb t && is_comb(rator t) &&
            fst(dest_const(rator(rator t)))="word_pmul" then found := t :: !found
     with _->());
    (match t with Comb(a,b)->walk a; walk b | Abs(_,b)->walk b | _->()) in
  walk (rhs w);
  match List.sort_uniq compare !found with
    [] -> ALL_TAC (asl,w)
  | qbcopy :: _ ->
    (SUBGOAL_THEN (mk_eq(qbcopy, `qB:(128)word`)) (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC])
    (asl,w);;

(* The full GHASH closer: applied at the final GHASH conjunct. *)
let GCM_8B_GHASH_CLOSE : tactic =
  GCM_8B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_8; POLYVAL_DOT_H8_EQ; POLYVAL_DOT_H7_EQ; POLYVAL_DOT_H6_EQ; POLYVAL_DOT_H5_EQ; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_8B_MASK_COLLAPSE_ASMS THEN
  GCM_8B_KS8_FOLD THEN
  GCM_8B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_8; XI_HS_HI_8] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  SUBGOAL_THEN
   `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
              (word_xor (hn0:(64)word) hn1):(128)word = w1md`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  GCM_8B_QB_FOLD THEN
  ASM_REWRITE_TAC[] THEN
  BINOP_TAC THENL
   [CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;
    CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC];;
