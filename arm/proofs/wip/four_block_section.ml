
(* ========================================================================= *)
(* The L256_enc_blocks_more_than_3 branch (4-block: three full blocks +       *)
(* partial block 4, total 49..64 bytes) of the single binary, proved as a     *)
(* standalone theorem and applied exactly as the XTS length-band lemmas are.   *)
(* Reuses the four-block masked closers from gcm_four_block_closers.ml.        *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_four_block_closers.ml";;

(* --- 4-block-branch length/cascade helpers (thresholds over 48+byte_len) --- *)

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

(* --- 4-block GHASH final-closure helper lemmas/tactics --- *)


(* GHASH-closure helper lemmas (xi half-swap normalization). *)
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

(* b0-general mask-register collapse; drop ct-store hyps before byte-folds. *)
let GCM_4B_MASK_COLLAPSE_TAC =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    REWRITE_TAC[GEN `b0:int128` (MP (SPEC_ALL FOURBLOCK_MASK_REG) bth)] else NO_TAC);;
let GCM_4B_DROP_CT_STORES =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       (rand(concl th)=`ct1:(128)word` || rand(concl th)=`ct2:(128)word` || rand(concl th)=`ct3:(128)word`) &&
       can(term_match[]`read (memory :> bytes128 p) (s:armstate)`)(lhs(concl th))
    then ALL_TAC else NO_TAC));;
let gcm_4b_w1md_target = `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo))) (word_xor (hg0:(64)word) hg1):(128)word`;;
let GCM_4B_CTM4_FOLD : tactic = fun (asl,w) ->
  if can (find_term (fun t -> t = `word_and mask (ct4:(128)word):(128)word`)) w then
   (SUBGOAL_THEN `word_and mask ct4 = ctm4:(128)word` (fun th -> REWRITE_TAC[th]) THENL
    [FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th)=`ctm4:(128)word` &&
        aconv(lhs(concl th))`word_and ct4 mask:(128)word` then
        (GEN_REWRITE_TAC RAND_CONV [SYM th] THEN CONV_TAC WORD_BITWISE_RULE) else NO_TAC); ALL_TAC]) (asl,w)
  else ALL_TAC (asl,w);;
let GCM_4B_W1MD_FOLD : tactic = fun (asl,w) ->
  if can (find_term (fun t -> t = gcm_4b_w1md_target)) w then
   (SUBGOAL_THEN `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo))) (word_xor (hg0:(64)word) hg1):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC]) (asl,w)
  else ALL_TAC (asl,w);;
let GCM_4B_LEAF_CLOSE =
  REWRITE_TAC[XI_HS_LO; XI_HS_HI] THEN GCM_4B_CTM4_FOLD THEN ASM_REWRITE_TAC[] THEN
  GCM_4B_W1MD_FOLD THEN ASM_REWRITE_TAC[] THEN CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;;

(* GHASH closer slices (from GCM_4BLOCK_GHASH_STEP_MASKED_TAC). *)
let GCM_4B_FOLD_AND_BRIDGE =
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

let GCM_4B_TAIL3A =
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
  ALL_TAC;;

let GCM_4B_TAIL_P1 =
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c4lo:(64)word) = word_subword (word_reversefields 8 (ctm4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c4hi:(64)word) = word_subword (word_reversefields 8 (ctm4:(128)word)) (64,64)` THEN
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
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Byte-form fold: ct1's definition (pt1 xor s13_1 xor rk14) leaks the
     (rev8 _)_lo/_hi byte forms into the (xi xor ct1) Karatsuba term; re-fold
     them to the c1lo/c1hi atoms (4-block-specific; ct1 is not opaque here). *)
  SUBGOAL_THEN
    `(word_xor (word_subword (word_reversefields 8 (pt1:(128)word)) (0,64))
               (word_xor (word_subword (word_reversefields 8 (s13_1:(128)word)) (0,64))
                         (word_subword (word_reversefields 8 (rk14:(128)word)) (0,64))) :(64)word
      = c1lo) /\
     (word_xor (word_subword (word_reversefields 8 (pt1:(128)word)) (64,64))
               (word_xor (word_subword (word_reversefields 8 (s13_1:(128)word)) (64,64))
                         (word_subword (word_reversefields 8 (rk14:(128)word)) (64,64))) :(64)word
      = c1hi)`
    (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THENL
       [EXPAND_TAC "c1lo" THEN EXPAND_TAC "ct1" THEN
        REWRITE_TAC[GSYM WORD_REVERSEFIELDS_XOR_8_128; GSYM WORD_SUBWORD_XOR];
        EXPAND_TAC "c1hi" THEN EXPAND_TAC "ct1" THEN
        REWRITE_TAC[GSYM WORD_REVERSEFIELDS_XOR_8_128; GSYM WORD_SUBWORD_XOR]];
     ALL_TAC];;

let GCM_4B_TAIL_P2C =
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hg0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hg1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hg0:(64)word) (hg1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hf0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hf1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w4lo:(128)word) = word_pmul (c4lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w4hi:(128)word) = word_pmul (c4hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w4md:(128)word) = word_pmul (word_xor (c4hi:(64)word) (c4lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
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
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c4lo:(64)word) (c4hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w4md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w4md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w4lo_l:(64)word) (word_xor w3lo_l (word_xor w2lo_l w1lo_l))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (word_xor w3lo_l w4lo_l))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w4md_l:(64)word) (word_xor w3md_l (word_xor w2md_l (word_xor w1md_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w4hi_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w4lo_h (word_xor w3lo_h (word_xor w2lo_h w1lo_h)))))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w4lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w4md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w4hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_subword (qS:(128)word) (0,64)))))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC] THEN
  ALL_TAC;;

(* The 4-block branch goal (three full + one partial block). *)
let gcm_4b_goal = `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (pt4:(128)word)
    (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,64) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,64) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,64) (out_ptr,64) /\
    nonoverlapping (in_ptr,64) (xi_ptr,16) /\
    nonoverlapping (in_ptr,64) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,64) (xi_ptr,16) /\
    nonoverlapping (out_ptr,64) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,64) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,64) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,64) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,64) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,64) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (384 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add in_ptr (word 48))) s = pt4 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = byteswap128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
             byteswap128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s =
             byteswap128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s =
             byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)))
      (\s. let ct1 =
             word_xor pt1
               (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct2 =
             word_xor pt2
               (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4
                                 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12
                                 rk13 rk14) in
           let ct3 =
             word_xor pt3
               (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc ivec))
                                 rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8
                                 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct4 =
             word_xor pt4
               (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))
                                 rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8
                                 rk9 rk10 rk11 rk12 rk13 rk14) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm4 = word_and ct4 mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word (48 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = ct3 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s =
             word_or ctm4 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ct3;
                                     word_reversefields 8 ctm4]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,64);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`;;

let GCM_4BLOCK_CT1_FILE_TAC = GCM_NBLOCK_CT_STEP_TAC 4 1;;

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
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FOURBLOCK_MASK_REG th])) THEN
  GCM_RUN 367 379 THEN GCM_RUN 380 394 THEN ARM_STEPS_TAC AES256_GCM_EXEC (395--395) THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (396--403) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FOURBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[FOURBLOCK_USHR] THEN
  CONJ_TAC THENL [GCM_4BLOCK_CT1_FILE_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_4BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_4BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [
    SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
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
  GCM_4B_MASK_COLLAPSE_TAC THEN
  ABBREV_TAC `ct4 = word_xor (word_xor pt4 s13_4) rk14:(128)word` THEN
  SUBGOAL_THEN `word_xor pt4 (word_xor s13_4 rk14) = ct4:(128)word` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th)=`ct4:(128)word` &&
        aconv (lhs(concl th)) `word_xor (word_xor pt4 s13_4) rk14:(128)word`
       then REWRITE_TAC[SYM th] else NO_TAC) THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  GCM_4B_FOLD_AND_BRIDGE THEN GCM_4B_TAIL3A THEN GCM_4B_MASK_COLLAPSE_TAC THEN GCM_4B_DROP_CT_STORES THEN
  SUBGOAL_THEN `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th)=`ct1:(128)word` &&
        aconv (lhs(concl th)) `word_xor pt1 (word_xor s13_1 rk14):(128)word`
       then REWRITE_TAC[SYM th] else NO_TAC) THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  GCM_4B_TAIL_P1 THEN GCM_4B_TAIL_P2C THEN BINOP_TAC THEN GCM_4B_LEAF_CLOSE);;
