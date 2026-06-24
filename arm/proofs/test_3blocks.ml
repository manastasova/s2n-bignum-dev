(* xi half-swap normalizers (same as XI_HS_LO/HI). *)
let XI_HS_LO_4 = XI_HS_LO;;
let XI_HS_HI_4 = XI_HS_HI;;

(* ct1 closer (counter = ivec, no inc) — mirror CT_CLOSE_5. *)
let CT_CLOSE_4 nidx =
  let s13n = "s13_"^string_of_int nidx and ctn = "ct"^string_of_int nidx in
  EXPAND_TAC ctn THEN EXPAND_TAC s13n THEN
  REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];;

(* Step 1+2: establish the three full-block spec-form ct folds F1..F3 and fold
   them into the RHS ghash list — mirror GCM_5B_FOLD_SPEC_CTS (which folds 4). *)
let GCM_4B_FOLD_SPEC_CTS : tactic =
  (* F1 *)
  SUBGOAL_THEN
   `word_xor pt1 (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9
                  rk10 rk11 rk12 rk13 rk14) = ct1`
   ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* F2 *)
  SUBGOAL_THEN
   `word_xor pt2 (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4 rk5
                  rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) = ct2`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_4BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  (* F3 *)
  SUBGOAL_THEN
   `word_xor pt3 (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc ivec)) rk0 rk1 rk2
                  rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) = ct3`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_4BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  (* fold the three full blocks into the RHS ghash list only. *)
  (fun (asl,w) ->
     let getf n = snd(find (fun (_,th) ->
       is_eq(concl th) && rand(concl th)=mk_var("ct"^string_of_int n,`:(128)word`) &&
       (let l=lhand(concl th) in
        (try fst(dest_const(rator(rator l)))="word_xor" with _->false) &&
        (try fst(dest_const(repeat rator (rand l)))="aes256_block_enc" with _->false))) asl) in
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [getf 1; getf 2; getf 3] (asl,w));;

(* Step 3: b0-general mask-register collapse over the assumptions. *)
let GCM_4B_MASK_COLLAPSE_ASMS : tactic =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[GEN `b0:int128` (MP (SPEC_ALL FOURBLOCK_MASK_REG) bth)]) else NO_TAC);;

(* Step 5: bridge the machine block-4 keystream (collapsed +3 counter, baked
   into final_xi) to the spec ct4 — mirror GCM_5B_KS5_FOLD (+4). *)
let GCM_4B_KS4_FOLD : tactic = fun (asl,w) ->
  let substr sub s =
    let ls=String.length s and lb=String.length sub in
    let rec go i = if i+lb>ls then false
                   else if String.sub s i lb = sub then true else go(i+1) in go 0 in
  let fxidef = snd(find (fun (_,th) ->
    is_eq(concl th) && (try rand(concl th)=`final_xi:(128)word` with _->false)) asl) in
  let body = lhs(concl fxidef) in
  let best = ref None in
  let rec walk t =
    (try let s=string_of_term t in
      if substr "pt4" s && substr "aese" s && substr "rk14" s &&
         (try fst(dest_const(repeat rator t))="word_xor" with _->false) &&
         (match !best with None->true | Some b -> String.length s < String.length(string_of_term b))
      then best := Some t
     with _->());
    (match t with Comb(a,b)->walk a; walk b | Abs(_,b)->walk b | _->()) in
  walk body;
  let ks4 = (match !best with Some t->t | None->failwith "KS4_FOLD: ks4 not found") in
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add3 = WORD_RULE `word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1) = word_add x (word 3)` in
  (SUBGOAL_THEN (mk_eq(ks4, `ct4:(128)word`)) ASSUME_TAC THENL
    [CONV_TAC SYM_CONV THEN EXPAND_TAC "ct4" THEN
     REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[WORD_XOR_ASSOC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
     REWRITE_TAC[gcm_ctr_inc] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
     REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
     REWRITE_TAC[bri] THEN REWRITE_TAC[add3] THEN
     REWRITE_TAC[CTR_WORD_INSERT];
     ALL_TAC] THEN
   FIRST_ASSUM(fun th ->
     if is_eq(concl th) && rand(concl th)=`ct4:(128)word` &&
        (try fst(dest_const(repeat rator (lhs(concl th))))="word_xor" with _->false) &&
        String.length(string_of_term(lhs(concl th))) > 1000
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC))
  (asl,w);;

(* Closer tail (ctm4 abbrev + h^3 norm + bridge + atomic ABBREVs + qS/qB),
   minus the final BINOP — mirror GCM_5B_TAIL_NOFINAL for N=4. *)
let GCM_4B_TAIL_NOFINAL : tactic =
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm4 = word_and (ct4:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct4:(128)word) = ctm4`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm4" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  (* Normalize h^3 left-assoc -> symmetric (to match the 4-block bridge). *)
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  (* Apply 4-block bridge. *)
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`; `word_reversefields 8 ct3:int128`;
     `word_reversefields 8 ctm4:int128`;
     `h:int128`; `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word`]
    GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
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
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_4block_karatsuba; LET_DEF; LET_END_DEF] THEN
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
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* 18 atomic ABBREVs (c1lo..c4hi, xi, hd..hg). *)
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
  ASM_REWRITE_TAC[] THEN
  (* 12 inner pmul ABBREVs (w1..w4). *)
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
  (* 24 z-vars. *)
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
  ASM_REWRITE_TAC[] THEN
  (* Normalize LHS mid-pmuls to the abbreviated w?md (swapped xor arg order). *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c4lo:(64)word) (c4hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w4md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w4md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul; fold both XOR orderings. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w4lo_l:(64)word) (word_xor w3lo_l (word_xor w2lo_l w1lo_l))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (word_xor w3lo_l w4lo_l))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold the LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w4md_l:(64)word) (word_xor w3md_l (word_xor w2md_l (word_xor w1md_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w4hi_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w4lo_h (word_xor w3lo_h (word_xor w2lo_h w1lo_h)))))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w4lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w4md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w4hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_subword (qS:(128)word) (0,64)))))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* per-half XOR-AC closer — mirror GCM_5B_HALF_CLOSE (4 mids, qS 4, qB 17). *)
let GCM_4B_FOLD_MIDS_TAC : tactic =
  fun (asl,gg) ->
    let rec finds hd t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = hd ->
          a :: (finds hd a (finds hd x acc))
      | Comb(l,r) -> finds hd l (finds hd r acc)
      | Abs(_,b) -> finds hd b acc | _ -> acc in
    let hgw = `word_xor (hg0:(64)word) hg1`
    and hfw = `word_xor (hf0:(64)word) hf1`
    and hew = `word_xor (he0:(64)word) he1`
    and hdw = `word_xor (hd0:(64)word) hd1` in
    let mk tgt hd arg =
      SUBGOAL_THEN
        (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[arg;hd]),tgt))
        (fun th -> REWRITE_TAC[th]) THENL
       [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC WORD_RULE; ALL_TAC] in
    (EVERY ((map (mk `w1md:(128)word` hgw) (setify(finds hgw gg [])))
          @ (map (mk `w2md:(128)word` hfw) (setify(finds hfw gg [])))
          @ (map (mk `w3md:(128)word` hew) (setify(finds hew gg [])))
          @ (map (mk `w4md:(128)word` hdw) (setify(finds hdw gg []))))) (asl,gg);;

let GCM_4B_FOLD_TO tgt natoms : tactic =
  let w64 = `word 13979173243358019584:(64)word` in
  fun (asl,gg) ->
    let rec finds t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = w64 ->
          a :: (finds a (finds x acc))
      | Comb(l,r) -> finds l (finds r acc) | Abs(_,b) -> finds b acc | _ -> acc in
    let rec at t = match t with
      | Comb(Comb(Const("word_xor",_),x),y) -> at x @ at y | _ -> [t] in
    let args = List.filter (fun a -> List.length(at a) = natoms) (setify(finds gg [])) in
    (EVERY (map (fun a ->
       FIRST [SUBGOAL_THEN
                (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[a;w64]),tgt))
                (fun th -> REWRITE_TAC[th]) THENL
               [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
                CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC; ALL_TAC];
              ALL_TAC]) args)) (asl,gg);;

let GCM_4B_HALF_CLOSE : tactic =
  GCM_4B_FOLD_MIDS_TAC THEN ASM_REWRITE_TAC[] THEN
  GCM_4B_FOLD_TO `qS:(128)word` 4 THEN ASM_REWRITE_TAC[] THEN
  GCM_4B_FOLD_TO `qB:(128)word` 17 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

(* The full GHASH closer — mirror GCM_5B_GHASH_CLOSE. *)
let GCM_4B_GHASH_CLOSE : tactic =
  GCM_4B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_4; POLYVAL_DOT_H4_EQ_LOCAL; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_4B_MASK_COLLAPSE_ASMS THEN
  GCM_4B_KS4_FOLD THEN
  GCM_4B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_4; XI_HS_HI_4] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
              (word_xor (hg0:(64)word) hg1):(128)word = w1md`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_4B_HALF_CLOSE; GCM_4B_HALF_CLOSE];;

(* masked-ct4 store conjunct closer — mirror GCM_5B_MASKED_CT5_CLOSE (+3). *)
let GCM_4B_MASKED_CT4_CLOSE : tactic =
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add3 = WORD_RULE `word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1) = word_add x (word 3)` in
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FOURBLOCK_MASK_REG th]) THEN
  REWRITE_TAC[NBLOCK_MASK_IDEM] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_or (word_and x m) r = word_or (word_and y m) r:(128)word`) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
  REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
  REWRITE_TAC[bri] THEN REWRITE_TAC[add3] THEN
  REWRITE_TAC[CTR_WORD_INSERT];;


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

let AES256_GCM_ENCRYPT_LT_4BLOCK_CONCRETE = prove
 (gcm_4b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA4 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA4 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X5TAIL_LEMMA4 THEN
  GCM_RUN_THEN GCM_CASCADE4_TAC 273 321 THEN
  abbrev_ct_from_store 0 1 THEN
  GCM_RUN 322 335 THEN abbrev_ct_from_store 16 2 THEN
  GCM_RUN 336 348 THEN abbrev_ct_from_store 32 3 THEN
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
  (* ---- five conjuncts: ct1..ct3, masked-ct4, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_4 1; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_4BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_4BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_4B_MASKED_CT4_CLOSE; ALL_TAC] THEN
  (* ---- ct4 abbreviation (spec form) so the closer's ctm4 works ---- *)
  ABBREV_TAC `ct4 = word_xor pt4
    (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))
                      rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_4B_GHASH_CLOSE);;
