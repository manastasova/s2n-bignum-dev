(* ========================================================================= *)
(* 7-block branch: CORRECTED store-based ct abbreviation (strict address +    *)
(* plaintext matcher). The prior abbrev_ct_from_store off=0 pattern           *)
(* `read (memory :> bytes128 out_ptr) s` term-matched word_add out_ptr        *)
(* (word N) because out_ptr is a free var, causing the ct1=s13_2 "collision"  *)
(* that all prior 7-block sessions mis-attributed to a fundamental issue.     *)
(* This strict version pins the exact address AND the plaintext ptN.          *)
(* ========================================================================= *)

let abbrev_ct7 off nidx : tactic = fun (asl,w) ->
  let addr = if off=0 then `out_ptr:int64`
    else vsubst[mk_small_numeral off,`Z:num`] `word_add out_ptr (word Z):int64` in
  let ptn = mk_var("pt"^string_of_int nidx,`:(128)word`) in
  let store = tryfind (fun (_,th) -> let t=concl th in
    if is_eq t &&
       (try fst(dest_const(rator(rator(lhs t))))="read" with _->false) &&
       (try aconv (rand(rand(rand(rator(lhs t))))) addr with _->false) &&
       (try fst(dest_const(repeat rator (rand t)))="word_xor" with _->false) &&
       (try aconv (lhand(lhand(rand t))) ptn with _->false)
    then t else fail()) asl in
  let ks0 = rand(lhand(rand store)) in
  let ks =
    if (try fst(dest_const(rator(rator ks0)))="read" with _->false)
    then (try tryfind (fun (_,th) -> let t=concl th in if is_eq t && lhs t = ks0 then rand t else fail()) asl with _ -> ks0)
    else ks0 in
  let s13n = mk_var("s13_"^string_of_int nidx,`:(128)word`) in
  let ctn = mk_var("ct"^string_of_int nidx,`:(128)word`) in
  (ABBREV_TAC(mk_eq(s13n,ks)) THEN
   ABBREV_TAC(mk_eq(ctn,
     list_mk_comb(`word_xor:(128)word->(128)word->(128)word`,
       [list_mk_comb(`word_xor:(128)word->(128)word->(128)word`,[ptn;s13n]); `rk14:(128)word`]))))
  (asl,w);;

(* ct1 closer (counter = ivec). *)
let CT_CLOSE_7 nidx =
  let s13n = "s13_"^string_of_int nidx and ctn = "ct"^string_of_int nidx in
  EXPAND_TAC ctn THEN EXPAND_TAC s13n THEN
  REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];;

(* masked-ct7 store conjunct closer: block-7 = gcm_ctr_inc^6 -> "+6". *)
let GCM_7B_MASKED_CT7_CLOSE : tactic =
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add6 = WORD_RULE `word_add (word_add (word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 6)` in
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
  REWRITE_TAC[add6; BYTEREVERSE_JOIN_FOLD] THEN
  AP_TERM_TAC THEN REWRITE_TAC[bri] THEN REWRITE_TAC[add6];;

(* GHASH ct-fold (mirror GCM_6B_FOLD_SPEC_CTS, 6 full-block cts). *)
let GCM_7B_FOLD_SPEC_CTS : tactic =
  SUBGOAL_THEN
   `word_xor pt1 (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9
                  rk10 rk11 rk12 rk13 rk14) = ct1`
   ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt2 (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4 rk5
                  rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) = ct2`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt3 (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc ivec)) rk0 rk1 rk2
                  rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) = ct3`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt4 (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))
                  rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13
                  rk14) = ct4`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt5 (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))
                  rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13
                  rk14) = ct5`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT5_STEP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt6 (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))))
                  rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13
                  rk14) = ct6`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT6_STEP_TAC; ALL_TAC] THEN
  (fun (asl,w) ->
     let getf n = snd(find (fun (_,th) ->
       is_eq(concl th) && rand(concl th)=mk_var("ct"^string_of_int n,`:(128)word`) &&
       (let l=lhand(concl th) in
        (try fst(dest_const(rator(rator l)))="word_xor" with _->false) &&
        (try fst(dest_const(repeat rator (rand l)))="aes256_block_enc" with _->false))) asl) in
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [getf 1; getf 2; getf 3; getf 4; getf 5; getf 6] (asl,w));;

(* The GHASH conjunct closes via GCM_7B_GHASH_CLOSE (mirror of the 6-block    *)
(* GCM_6B_GHASH_CLOSE) defined in seven_ghash_closer.ml — its bridge MP_TAC   *)
(* uses the genuine htable h7k now present in the goal.                       *)
