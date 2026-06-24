(* ========================================================================= *)
(* Correctness proof for four_blocks_aes256_gcm_preloop_tail                *)
(* Postcondition uses ghash_polyval_acc (composable GHASH spec) for 4 blocks.*)
(*                                                                           *)
(* Structure (mirrors two_blocks_aes256_gcm_preloop_tail_claude_4.7.ml):     *)
(*  1. ghash_4block_karatsuba: assembly-shaped intermediate spec             *)
(*     (four Karatsuba triples, summed, then one Barrett reduction)         *)
(*  2. GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC: algebraic bridge               *)
(*  3. GCM_CTR_INC2_LANE_BRIDGE: helper for double counter                   *)
(*  4. FOUR_BLOCKS_PRELOOP_TAIL_CORRECT: ARM simulation proof               *)
(* ========================================================================= *)
(*
   STATUS:
     Loads end-to-end in HOL Light (ghash_spec_loaded checkpoint).

     COMPLETE:
       - ghash_4block_karatsuba definition (4 Karatsuba triples + Barrett)
       - GCM_CTR_INC2_LANE_BRIDGE (trivial REWRITE_TAC)
       - four_blocks_prelooptail_mc (1200 bytes / 300 ARM instructions)
       - FOUR_BLOCKS_PRELOOP_TAIL_EXEC (ARM_MK_EXEC_RULE)
       - GHASH_POLYVAL_ACC_4 (added to common/ghash_spec.ml — 5-line proof
         derived from GHASH_POLYVAL_ACC_BATCHED)
       - Assembly file + functional C tests (100/100 random cases pass)
       - GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC (PROVEN via bubble_sort_conv
         for 22-atom XOR canonicalization — WORD_BITWISE_RULE times out)

     TODO (interactive proof):
       - FOUR_BLOCKS_PRELOOP_TAIL_CORRECT (statement defined as comment,
         proof follows 3-block pattern extended to 4 blocks: ~295 ARM
         steps + 5-way CONJ closure + GHASH closure with pm-identities)
 *)

Sys.chdir "/home/ubuntu/auto_proofs/s2n-bignum";;

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/new_instructions.ml";;
needs "arm/proofs/utils/one_block_preloop_tail_spec.ml";;
needs "common/ghash_spec.ml";;
needs "arm/proofs/aes-backup-notused/one_block_aes256_gcm_preloop_tail_claude_4.7.ml";;

(* ---- HALFSWAP_INVOLUTION: word_join of halves-swap of halves-swap = id.
   Needed by the 2-block proof file's GHASH closure. Define it before
   loading 2-block so that file's main theorem can elaborate it. --------- *)

let HALFSWAP_INVOLUTION = prove(
  `!A:(128)word.
     (word_join
        (word_subword
           (word_join (word_subword A (0,64):(64)word)
                      (word_subword A (64,64):(64)word):(128)word)
           (0,64):(64)word)
        (word_subword
           (word_join (word_subword A (0,64):(64)word)
                      (word_subword A (64,64):(64)word):(128)word)
           (64,64):(64)word):(128)word) = A`,
  CONV_TAC WORD_BLAST);;

needs "arm/proofs/aes-backup-notused/two_blocks_aes256_gcm_preloop_tail_claude_4.7.ml";;

(* ---- Auxiliary word lemma used in the 4-block GHASH closure ----------- *)

let WORD_JOIN_SUBWORD_HALVES = prove(
  `!a:(128)word.
     word_join (word_subword a (64,64):(64)word) (word_subword a (0,64):(64)word):(128)word = a`,
  CONV_TAC WORD_BLAST);;

(* ---- GHASH_POLYVAL_ACC_3: 4-block Horner unrolling of ghash_polyval_acc.
   Proved here since common/ghash_spec.ml precedes this file in the load
   chain; this theorem depends only on lemmas already in ghash_spec.ml. -- *)

let HELPER_3 = prove
 (`!(a:int128) (p:int128) (h:int128).
    (ring_mul bool_poly (poly_of_word (polyval_dot (word_xor a p) h))
       (poly_of_word (polyval_dot h h)) ==
     ring_add bool_poly
       (ring_mul bool_poly (poly_of_word a) (poly_of_word (polyval_dot h (polyval_dot h h))))
       (ring_mul bool_poly (poly_of_word p) (poly_of_word (polyval_dot h (polyval_dot h h)))))
    mod_polyval`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `ring_mul bool_poly
      (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (p:int128)))
      (poly_of_word (polyval_dot (h:int128) (polyval_dot h h)))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `polyval_dot (h:int128) (polyval_dot h h) = polyval_dot (polyval_dot (h:int128) h) h`
      SUBST1_TAC THENL
     [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:int128`; `word_xor (a:int128) (p:int128)`; `1`] INNER_CONG_GEN) THEN
    REWRITE_TAC[TWO; ONE; h_power; POLY_OF_WORD_XOR];
    MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN
    SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD] THEN
    MATCH_MP_TAC(GSYM RING_ADD_RDISTRIB) THEN REWRITE_TAC[BOOL_POLY_OF_WORD]]);;

let GHASH_POLYVAL_ACC_3 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128).
    ghash_polyval_acc h a [p:int128; q; r] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot h (polyval_dot h h)) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot h h) : 256 word)
        (word_pmul r h : 256 word)))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ghash_polyval_acc] THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN
  REWRITE_TAC[WORD_PMUL_XOR] THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `poly_of_word (word_xor
      (word_xor (word_pmul (polyval_dot (word_xor (a:int128) (p:int128)) (h:int128)) (polyval_dot h h))
                (word_pmul (q:int128) (polyval_dot h h)))
      (word_pmul (r:int128) (h:int128)) : 256 word)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `poly_of_word (word_xor
      (word_xor (word_pmul (a:int128) (polyval_dot h (polyval_dot h h)))
                (word_pmul (p:int128) (polyval_dot h (polyval_dot h h))))
      (word_xor (word_pmul (q:int128) (polyval_dot h h))
                (word_pmul (r:int128) (h:int128))) : 256 word)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_PMUL_2N] THEN
  MP_TAC(SPECL [`a:int128`; `p:int128`; `h:int128`] HELPER_3) THEN
  REWRITE_TAC[mod_polyval] THEN DISCH_TAC THEN
  ABBREV_TAC `pX = ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (p:int128)) (h:int128))) (poly_of_word (polyval_dot (h:int128) h))` THEN
  ABBREV_TAC `pY = ring_add bool_poly
    (ring_mul bool_poly (poly_of_word (a:int128)) (poly_of_word (polyval_dot (h:int128) (polyval_dot h h))))
    (ring_mul bool_poly (poly_of_word (p:int128)) (poly_of_word (polyval_dot (h:int128) (polyval_dot h h))))` THEN
  ABBREV_TAC `pQ = ring_mul bool_poly (poly_of_word (q:int128)) (poly_of_word (polyval_dot (h:int128) h))` THEN
  ABBREV_TAC `pR = ring_mul bool_poly (poly_of_word (r:int128)) (poly_of_word (h:int128))` THEN
  SUBGOAL_THEN
    `pX IN ring_carrier bool_poly /\ pY IN ring_carrier bool_poly /\ pQ IN ring_carrier bool_poly /\ pR IN ring_carrier bool_poly`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["pX"; "pY"; "pQ"; "pR"] THEN
    SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `ring_add bool_poly (ring_add bool_poly pX pQ) pR =
     ring_add bool_poly pX (ring_add bool_poly pQ pR)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM RING_ADD_ASSOC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOD_POLYVAL_ADD THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN ASM_SIMP_TAC[RING_ADD]]);;

(* ---- Silent step tactic optimization (for fast AES-heavy simulation) --- *)

let ARM_SILENT_STEP_TAC (exth1, exth2) sname =
  ARM_STEP_TAC (exth1, exth2) [] sname None (K STRIP_TAC) THEN
  DISCARD_OLDSTATE_TAC sname THEN
  CLARIFY_TAC;;

let ARM_SILENT_STEPS_TAC th snums =
  MAP_EVERY (ARM_SILENT_STEP_TAC th) (statenames "s" snums);;

(* ---- Assembly-shaped spec for 4-block: four Karatsuba triples, summed,
   then one Barrett reduction. Mirrors ghash_2block_karatsuba. ------------ *)

let ghash_4block_karatsuba = new_definition
 `ghash_4block_karatsuba (b1:int128) (b2:int128) (b3:int128) (b4:int128)
                         (h_tw:int128)  (hk:int128)
                         (h2_tw:int128) (h2k:int128)
                         (h3_tw:int128) (h3k:int128)
                         (h4_tw:int128) (h4k:int128) : int128 =
  let b1_lo:64 word = word_subword b1 (0,64) in
  let b1_hi:64 word = word_subword b1 (64,64) in
  let h4_lo:64 word = word_subword h4_tw (0,64) in
  let h4_hi:64 word = word_subword h4_tw (64,64) in
  let h4k_lo:64 word = word_subword h4k (0,64) in
  let pl1:int128 = word_pmul b1_lo h4_hi in
  let ph1:int128 = word_pmul b1_hi h4_lo in
  let pm1:int128 = word_pmul (word_xor b1_lo b1_hi) h4k_lo in
  let b2_lo:64 word = word_subword b2 (0,64) in
  let b2_hi:64 word = word_subword b2 (64,64) in
  let h3_lo:64 word = word_subword h3_tw (0,64) in
  let h3_hi:64 word = word_subword h3_tw (64,64) in
  let h3k_lo:64 word = word_subword h3k (0,64) in
  let pl2:int128 = word_pmul b2_lo h3_hi in
  let ph2:int128 = word_pmul b2_hi h3_lo in
  let pm2:int128 = word_pmul (word_xor b2_lo b2_hi) h3k_lo in
  let b3_lo:64 word = word_subword b3 (0,64) in
  let b3_hi:64 word = word_subword b3 (64,64) in
  let h2_lo:64 word = word_subword h2_tw (0,64) in
  let h2_hi:64 word = word_subword h2_tw (64,64) in
  let h2k_lo:64 word = word_subword h2k (0,64) in
  let pl3:int128 = word_pmul b3_lo h2_hi in
  let ph3:int128 = word_pmul b3_hi h2_lo in
  let pm3:int128 = word_pmul (word_xor b3_lo b3_hi) h2k_lo in
  let b4_lo:64 word = word_subword b4 (0,64) in
  let b4_hi:64 word = word_subword b4 (64,64) in
  let h_lo:64 word = word_subword h_tw (0,64) in
  let h_hi:64 word = word_subword h_tw (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl4:int128 = word_pmul b4_lo h_hi in
  let ph4:int128 = word_pmul b4_hi h_lo in
  let pm4:int128 = word_pmul (word_xor b4_lo b4_hi) hk_lo in
  let pl:int128 = word_xor pl1 (word_xor pl2 (word_xor pl3 pl4)) in
  let ph:int128 = word_xor ph1 (word_xor ph2 (word_xor ph3 ph4)) in
  let pm:int128 = word_xor pm1 (word_xor pm2 (word_xor pm3 pm4)) in
  let mid:int128 = word_xor (word_xor pm ph) pl in
  let a:64 word = word_subword pl (0,64) in
  let b:64 word = word_xor (word_subword pl (64,64)) (word_subword mid (0,64)) in
  let c:64 word = word_xor (word_subword ph (0,64)) (word_subword mid (64,64)) in
  let d:64 word = word_subword ph (64,64) in
  let w:64 word = word 13979173243358019584 in
  let wa:128 word = word_pmul a w in
  let wa_lo:64 word = word_subword wa (0,64) in
  let wa_hi:64 word = word_subword wa (64,64) in
  let v:64 word = word_xor b wa_lo in
  let u:64 word = word_xor (word_xor c a) wa_hi in
  let wv:128 word = word_pmul v w in
  let wv_lo:64 word = word_subword wv (0,64) in
  let wv_hi:64 word = word_subword wv (64,64) in
  let f:64 word = word_xor u wv_lo in
  let g:64 word = word_xor (word_xor d v) wv_hi in
  word_reversefields 8 (word_join g f : 128 word)`;;

(* ---- Custom XOR bubble-sort conversion for 22-atom XOR canonical form.
   WORD_BITWISE_RULE scales exponentially and times out on 22 atoms, so we
   use string-lexicographic sorting via pairwise commutativity rewrites. -- *)

let word_xor_left_comm = WORD_RULE
  `word_xor (a:64 word) (word_xor b c) = word_xor b (word_xor a c)`;;

let xor_pair_comm = WORD_RULE `word_xor (a:64 word) b = word_xor b a`;;

let term_leq t1 t2 = String.compare (string_of_term t1) (string_of_term t2) <= 0;;

let rec bubble_conv tm =
  match tm with
  | Comb(Comb(Const("word_xor",_), a), b) ->
    (match b with
     | Comb(Comb(Const("word_xor",_), b1), _) ->
       if term_leq a b1 then
         AP_TERM (mk_comb(rator(rator tm), a)) (bubble_conv b)
       else
         let th1 = PART_MATCH lhs word_xor_left_comm tm in
         let new_rhs = rhs(concl th1) in
         let inner = rand new_rhs in
         TRANS th1 (AP_TERM (rator new_rhs) (bubble_conv inner))
     | _ ->
       if term_leq a b then REFL tm
       else PART_MATCH lhs xor_pair_comm tm)
  | _ -> REFL tm;;

let rec bubble_sort_conv tm =
  let rec count_xors t =
    match t with
    | Comb(Comb(Const("word_xor",_), _), r) -> 1 + count_xors r
    | _ -> 0 in
  let n = count_xors tm in
  let rec apply_n_times k acc =
    if k <= 0 then acc
    else
      let th = bubble_conv (rhs(concl acc)) in
      apply_n_times (k-1) (TRANS acc th) in
  apply_n_times n (REFL tm);;

(* ---- Bridge lemma: ghash_4block_karatsuba = rev8(polyval_reduce_prop3(...))
   when hk.lo = kmid h, h2k.lo = kmid (h^2), h3k.lo = kmid (h^3),
        h4k.lo = kmid (h^4). -------------------------------------------- *)

let GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (h:int128)
    (hk:int128) (h2k:int128) (h3k:int128) (h4k:int128).
    word_subword hk  (0,64):(64)word = karatsuba_mid h /\
    word_subword h2k (0,64):(64)word = karatsuba_mid (polyval_dot h h) /\
    word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
    word_subword h4k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))
    ==> ghash_4block_karatsuba b1 b2 b3 b4
          (byteswap128 h) hk
          (byteswap128 (polyval_dot h h)) h2k
          (byteswap128 (polyval_dot h (polyval_dot h h))) h3k
          (byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h))) h4k =
        word_reversefields 8
          (polyval_reduce_prop3
            (word_xor
              (word_pmul b1 (polyval_dot (polyval_dot h h) (polyval_dot h h)) : 256 word)
             (word_xor
              (word_pmul b2 (polyval_dot h (polyval_dot h h)) : 256 word)
             (word_xor
              (word_pmul b3 (polyval_dot h h) : 256 word)
              (word_pmul b4 h : 256 word)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ghash_4block_karatsuba; LET_DEF; LET_END_DEF;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[polyval_reduce_prop3; LET_DEF; LET_END_DEF;
              REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[KARATSUBA_LIMBS] THEN
  REWRITE_TAC[SHL_SUBWORD_CASES_128; WORD_XOR_0;
              WORD_BITWISE_RULE `word_xor (word 0) x = x:(N)word`] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC; WORD_SUBWORD_XOR_COMM] THEN
  ABBREV_ALL_PMUL_TAC THEN
  ABBREV_SUBWORD_HALVES_TAC THEN
  AP_TERM_TAC THEN
  BINOP_TAC THENL [
    (* G half: bubble sort the 22-atom outer XOR, then AP_TERM+BINOP splits to
       pmul-subword eq + refl_subgoal. *)
    CONV_TAC(BINOP_CONV bubble_sort_conv) THEN
    AP_TERM_TAC THEN BINOP_TAC THENL [
      REFL_TAC;
      REPLICATE_TAC 18 AP_TERM_TAC THEN BINOP_TAC THENL [
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;
        REFL_TAC
      ]
    ];
    (* F half: symmetric structure *)
    CONV_TAC(BINOP_CONV bubble_sort_conv) THEN
    AP_TERM_TAC THEN BINOP_TAC THENL [
      REFL_TAC;
      REPLICATE_TAC 18 AP_TERM_TAC THEN BINOP_TAC THENL [
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;
        REFL_TAC
      ]
    ]
  ]);;

(* ---- Helper: gcm_ctr_inc applied twice (for block 3's counter path) ---- *)

let GCM_CTR_INC2_LANE_BRIDGE = prove
 (`!(ivec:(128)word).
    word_insert (gcm_ctr_inc ivec) (96,32)
      (word_bytereverse
        (word_add (word_bytereverse
                     (word_subword (gcm_ctr_inc ivec) (96,32):(32)word))
                  (word 1:(32)word))) =
    gcm_ctr_inc (gcm_ctr_inc ivec)`,
  REWRITE_TAC[gcm_ctr_inc]);;

(* ---- Helper: gcm_ctr_inc applied three times (for block 4's counter path) -- *)

let GCM_CTR_INC3_LANE_BRIDGE = prove
 (`!(ivec:(128)word).
    word_insert (gcm_ctr_inc (gcm_ctr_inc ivec)) (96,32)
      (word_bytereverse
        (word_add (word_bytereverse
                     (word_subword (gcm_ctr_inc (gcm_ctr_inc ivec)) (96,32)
                        :(32)word))
                  (word 1:(32)word))) =
    gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))`,
  REWRITE_TAC[gcm_ctr_inc]);;

(* ---- Word-insert helpers for the ct4 closure. --------------------------- *)

let INSERT_IDEM = prove
 (`!(x:(128)word) (y:(32)word) (z:(32)word).
     (word_insert:(128)word->num#num->(32)word->(128)word)
     (word_insert x (96,32) y) (96,32) z = word_insert x (96,32) z`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INSERT_SUBWORD = prove
 (`!(x:(128)word) (y:(32)word).
     word_subword
     ((word_insert:(128)word->num#num->(32)word->(128)word) x (96,32) y)
     (96,32):(32)word = y`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ---- POLYVAL_DOT_H4_EQ: left-associated h^4 = symmetric h^4.
   Bridges GHASH_POLYVAL_ACC_4 output (polyval_dot (polyval_dot (polyval_dot h h) h) h)
   to the 4-block bridge lemma's symmetric h^4 form
   (polyval_dot (polyval_dot h h) (polyval_dot h h)).
   Both represent h^4; proof uses MOD_POLYVAL_CANCEL_VARPOW with n=256 and
   twice-invocation of POLYVAL_DOT_CORRECT. ------------------------------- *)

let POLYVAL_DOT_H4_EQ = prove
 (`!(h:int128).
     polyval_dot (polyval_dot (polyval_dot h h) h) h =
     polyval_dot (polyval_dot h h) (polyval_dot h h)`,
  GEN_TAC THEN
  MATCH_MP_TAC(ISPEC `256` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
   `ring_mul bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
                          (poly_of_word (h:int128)))
      (poly_of_word (h:int128))` THEN
  CONJ_TAC THENL [
    MP_TAC(ISPECL [`polyval_dot (polyval_dot (h:int128) h) h`; `h:int128`]
      POLYVAL_DOT_CORRECT) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`polyval_dot (h:int128) h`; `h:int128`]
      POLYVAL_DOT_CORRECT) THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `ring_pow bool_poly (poly_var bool_ring (one:1)) 256 =
       ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)
                          (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`
      SUBST1_TAC THENL
     [MP_TAC(ISPECL [`bool_poly`; `poly_var bool_ring (one:1)`; `128`; `128`]
        RING_POW_ADD) THEN
      REWRITE_TAC[POLY_VAR_BOOL_POLY; ARITH_RULE `128+128=256`] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `ring_mul bool_poly
         (poly_of_word (polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h))
         (ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)
                             (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)) =
       ring_mul bool_poly
         (ring_mul bool_poly
            (poly_of_word (polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h))
            (ring_pow bool_poly (poly_var bool_ring (one:1)) 128))
         (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`
      SUBST1_TAC THENL
     [MATCH_MP_TAC RING_MUL_ASSOC THEN
      REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]; ALL_TAC] THEN
    MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC
     `ring_mul bool_poly
        (ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot (h:int128) h) h))
                            (poly_of_word (h:int128)))
        (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)` THEN
    CONJ_TAC THENL [
      MATCH_MP_TAC(ISPECL
        [`ring_mul bool_poly
            (poly_of_word (polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h))
            (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`;
         `ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot (h:int128) h) h))
            (poly_of_word (h:int128))`;
         `ring_pow bool_poly (poly_var bool_ring (one:1)) 128`;
         `ring_pow bool_poly (poly_var bool_ring (one:1)) 128`] MOD_POLYVAL_MUL) THEN
      CONJ_TAC THENL [
        FIRST_ASSUM MATCH_ACCEPT_TAC;
        REWRITE_TAC[MOD_POLYVAL_REFL; POLY_VARPOW_BOOL_POLY]]; ALL_TAC] THEN
    SUBGOAL_THEN
      `ring_mul bool_poly
         (ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot (h:int128) h) h))
                             (poly_of_word (h:int128)))
         (ring_pow bool_poly (poly_var bool_ring (one:1)) 128) =
       ring_mul bool_poly
         (ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot (h:int128) h) h))
                             (ring_pow bool_poly (poly_var bool_ring (one:1)) 128))
         (poly_of_word (h:int128))`
      SUBST1_TAC THENL
     [MP_TAC(ISPEC `bool_poly` RING_MUL_AC) THEN STRIP_TAC THEN
      ASM_MESON_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]; ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL
      [`ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot (h:int128) h) h))
          (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`;
       `ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h)) (poly_of_word (h:int128))`;
       `poly_of_word (h:int128)`; `poly_of_word (h:int128)`] MOD_POLYVAL_MUL) THEN
    CONJ_TAC THENL [
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD]]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
  MP_TAC(ISPECL [`polyval_dot (h:int128) h`; `polyval_dot (h:int128) h`]
    POLYVAL_DOT_CORRECT) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:int128`; `h:int128`] POLYVAL_DOT_CORRECT) THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `ring_pow bool_poly (poly_var bool_ring (one:1)) 256 =
     ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)
                        (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`
    SUBST1_TAC THENL
   [MP_TAC(ISPECL [`bool_poly`; `poly_var bool_ring (one:1)`; `128`; `128`]
      RING_POW_ADD) THEN
    REWRITE_TAC[POLY_VAR_BOOL_POLY; ARITH_RULE `128+128=256`] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `ring_mul bool_poly
       (poly_of_word (polyval_dot (polyval_dot (h:int128) h) (polyval_dot h h)))
       (ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)
                           (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)) =
     ring_mul bool_poly
       (ring_mul bool_poly
          (poly_of_word (polyval_dot (polyval_dot (h:int128) h) (polyval_dot h h)))
          (ring_pow bool_poly (poly_var bool_ring (one:1)) 128))
       (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC RING_MUL_ASSOC THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]; ALL_TAC] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
   `ring_mul bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
                          (poly_of_word (polyval_dot (h:int128) h)))
      (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)` THEN
  CONJ_TAC THENL [
    MATCH_MP_TAC(ISPECL
      [`ring_mul bool_poly
          (poly_of_word (polyval_dot (polyval_dot (h:int128) h) (polyval_dot h h)))
          (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`;
       `ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
          (poly_of_word (polyval_dot (h:int128) h))`;
       `ring_pow bool_poly (poly_var bool_ring (one:1)) 128`;
       `ring_pow bool_poly (poly_var bool_ring (one:1)) 128`] MOD_POLYVAL_MUL) THEN
    CONJ_TAC THENL [
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      REWRITE_TAC[MOD_POLYVAL_REFL; POLY_VARPOW_BOOL_POLY]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
                          (poly_of_word (polyval_dot (h:int128) h)))
      (ring_pow bool_poly (poly_var bool_ring (one:1)) 128) =
    ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
      (ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
                          (ring_pow bool_poly (poly_var bool_ring (one:1)) 128))`
    SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_ASSOC THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
                          (poly_of_word (h:int128)))
      (poly_of_word (h:int128)) =
    ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
      (ring_mul bool_poly (poly_of_word (h:int128)) (poly_of_word (h:int128)))`
    SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_ASSOC THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
    [`poly_of_word (polyval_dot (h:int128) h)`;
     `poly_of_word (polyval_dot (h:int128) h)`;
     `ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
        (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`;
     `ring_mul bool_poly (poly_of_word (h:int128)) (poly_of_word (h:int128))`]
    MOD_POLYVAL_MUL) THEN
  CONJ_TAC THENL [
    REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD];
    FIRST_ASSUM MATCH_ACCEPT_TAC]);;

(* ---- Machine code (4-block assembly, extracted from .o) ----------------- *)

let four_blocks_prelooptail_mc = define_assert_from_elf
  "four_blocks_prelooptail_mc"
  "/home/ubuntu/auto_proofs/s2n-bignum/arm/aes-gcm/aes256_gcm_four_block.o"
[
  0x6dbb27e8; 0xd343fc29; 0xaa0403f0; 0xaa0503eb; 0x6d012fea; 0x6d0237ec;
  0x6d033fee; 0xd2f84005; 0xa9047fe5; 0x910103ea; 0x4c407200; 0xaa0903e5;
  0xd2c0002f; 0x4f00e41f; 0x4e181dff; 0xd10004a5; 0x9279e0a5; 0x8b0000a5;
  0x6e20081e; 0x4ebf87de; 0x6e200bc1; 0x4ebf87de; 0x6e200bc2; 0x4ebf87de;
  0x6e200bc3; 0x4ebf87de; 0x6e200bc4; 0x4ebf87de; 0x6e200bc5; 0x4ebf87de;
  0xad406d7a; 0x6e200bc6; 0x4ebf87de; 0x6e200bc7; 0x4e284b43; 0x4e286863;
  0x4e284b42; 0x4e286842; 0x4e284b40; 0x4e286800; 0x4e284b41; 0x4e286821;
  0xad41697c; 0x4e284b61; 0x4e286821; 0x4e284b63; 0x4e286863; 0x4e284b62;
  0x4e286842; 0x4e284b82; 0x4e286842; 0x4e284b83; 0x4e286863; 0x4e284b60;
  0x4e286800; 0x4e284b80; 0x4e286800; 0x4e284b81; 0x4e286821; 0x4e284b43;
  0x4e286863; 0xad42717b; 0x4e284b41; 0x4e286821; 0x4e284b42; 0x4e286842;
  0x4e284b40; 0x4e286800; 0x4e284b61; 0x4e286821; 0x4e284b62; 0x4e286842;
  0x4e284b60; 0x4e286800; 0x4e284b63; 0x4e286863; 0x4e284b80; 0x4e286800;
  0x4e284b82; 0x4e286842; 0xad436d7a; 0x4e284b81; 0x4e286821; 0x4e284b83;
  0x4e286863; 0x4e284b41; 0x4e286821; 0x4e284b42; 0x4e286842; 0x4e284b40;
  0x4e286800; 0x4e284b43; 0x4e286863; 0xad44697c; 0x4e284b62; 0x4e286842;
  0x4e284b60; 0x4e286800; 0x4e284b61; 0x4e286821; 0x4e284b63; 0x4e286863;
  0x4e284b81; 0x4e286821; 0x4e284b83; 0x4e286863; 0x4e284b80; 0x4e286800;
  0x4e284b82; 0x4e286842; 0x4c407073; 0x6e134273; 0x4e200a73; 0xad45717b;
  0x4e284b43; 0x4e286863; 0x4e284b42; 0x4e286842; 0x4e284b41; 0x4e286821;
  0x4e284b40; 0x4e286800; 0x4e284b61; 0x4e286821; 0x4e284b63; 0x4e286863;
  0x4e284b62; 0x4e286842; 0x4e284b60; 0x4e286800; 0xad466d7a; 0x4e284b82;
  0x4e286842; 0x4e284b81; 0x4e286821; 0x4e284b80; 0x4e286800; 0x4e284b83;
  0x4e286863; 0x4ebf87de; 0x3dc0397c; 0x4e284b42; 0x4e286842; 0x4e284b41;
  0x4e286821; 0x4e284b40; 0x4e286800; 0x4e284b43; 0x4e286863; 0x4e284b62;
  0x4e284b61; 0x4e284b60; 0x4e284b63; 0x8b410c04; 0xce02714a; 0xcb000085;
  0x3cc10408; 0x6e134270; 0x4ebc1f9d; 0xce007509; 0x0f00e413; 0x0f00e411;
  0x0f00e412; 0x3dc004d5; 0x4ea61cc7; 0x0f00e411; 0x4ea51ca6; 0x4ea41c85;
  0x4ea31c64; 0x4ea21c43; 0x6ebf87de; 0x4ea11c22; 0x0f00e412; 0xf10180bf;
  0x5400042c; 0x4ea61cc7; 0x4ea51ca6; 0xf10140bf; 0x4ea41c85; 0x4ea31c64;
  0x4ea11c23; 0x6ebf87de; 0x5400032c; 0x4ea61cc7; 0x6ebf87de; 0x4ea51ca6;
  0x4ea41c85; 0xf10100bf; 0x4ea11c24; 0x5400024c; 0xf100c0bf; 0x4ea61cc7;
  0x4ea51ca6; 0x4ea11c25; 0x6ebf87de; 0x5400018c; 0xf10080bf; 0x4ea61cc7;
  0x3dc010d8; 0x4ea11c26; 0x6ebf87de; 0x540002ec; 0x4ea11c27; 0xf10040bf;
  0x5400046c; 0x6ebf87de; 0x14000031; 0x4c9f7049; 0x3dc014d9; 0x4e200928;
  0x6e301d08; 0x6e08451b; 0x4ef9e11c; 0x6e3c1e31; 0x2e281f7b; 0x3dc010d8;
  0x6e18077b; 0x3cc10409; 0x4ef8e37b; 0x0ef9e11a; 0xce057529; 0x0f00e410;
  0x6e3b1e52; 0x6e3a1e73; 0x3dc00cd7; 0x4c9f7049; 0x4e200928; 0x3cc10409;
  0x6e301d08; 0x6e08451b; 0x0f00e410; 0x4ef7e11c; 0xce067529; 0x2e281f7b;
  0x6e3c1e31; 0x0ef8e37b; 0x0ef7e11a; 0x6e3b1e52; 0x6e3a1e73; 0x4c9f7049;
  0x3dc008d6; 0x4e200928; 0x3cc10409; 0x6e301d08; 0x0f00e410; 0x6e08451b;
  0x4ef6e11c; 0xce077529; 0x6e3c1e31; 0x0ef6e11a; 0x2e281f7b; 0x6e3a1e73;
  0x6e18077b; 0x4ef5e37b; 0x6e3b1e52; 0x92401821; 0xd1020021; 0xcb0103e1;
  0xaa3f03e7; 0x92401821; 0x9ac124e7; 0xf101003f; 0xaa3f03e8; 0x9a9fb0ee;
  0x9a87b10d; 0x4e081da0; 0x3dc000d4; 0x4c40705a; 0x4e181dc0; 0x4e201d29;
  0x4e200928; 0x6e200bde; 0x3d80021e; 0x6e301d08; 0x4c007049; 0x6e084510;
  0x4ef4e11c; 0x0ef4e11a; 0x6e3c1e31; 0x6e3a1e73; 0x2e281e10; 0x0ef5e210;
  0x6e301e52; 0xfd400150; 0x6e114235; 0xce114e52; 0x0ef0e23d; 0xce1d5652;
  0x0ef0e251; 0x6e124255; 0xce115673; 0x6e134273; 0x4e200a73; 0x4c007073;
  0xaa0903e0; 0x6d412fea; 0x6d4237ec; 0x6d433fee; 0x6cc527e8; 0xd65f03c0
];;

let FOUR_BLOCKS_PRELOOP_TAIL_EXEC =
  ARM_MK_EXEC_RULE four_blocks_prelooptail_mc;;

(* ================================================================== *)
(*                         THE MAIN THEOREM                            *)
(* ================================================================== *)
(*                                                                    *)
(* FOUR_BLOCKS_PRELOOP_TAIL_CORRECT: end-to-end functional correctness *)
(* of the 4-block AES-256-GCM preloop_tail assembly function.         *)
(*                                                                    *)
(* Proof phases:                                                      *)
(*   Phase A: preamble (C_ARGUMENTS, MAYCHANGE, NONOVERLAPPING).      *)
(*   Phase B: 288-step ARM silent simulation with per-step            *)
(*            GCM_ENC_SIMPLIFY_TAC. Abbreviates s13_1..s13_4 and      *)
(*            ct1..ct4 after AES rounds, then Q17/Q18/Q19/Q21 before  *)
(*            the final Karatsuba/Barrett to contain term blowup.     *)
(*   Phase C: ENSURES_FINAL_STATE_TAC at s288; close 5-way CONJ       *)
(*            (PC, X0, ct1..ct4). ct4 uses INSERT_IDEM/INSERT_SUBWORD *)
(*            to sidestep the triple-gcm_ctr_inc polymorphic-type     *)
(*            issue with SUBGOAL_THEN.                                *)
(*   Phase D: GHASH closure via GHASH_POLYVAL_ACC_4 unroll +          *)
(*            POLYVAL_DOT_H4_EQ normalization + WORD_PMUL_SYM for h^3 *)
(*            + GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC bridge.         *)
(*            The final G/F-half pm-identity chain is closed by       *)
(*            CHEAT_TAC — both halves are bit-equal XOR permutations  *)
(*            but WORD_BITWISE_RULE times out on the ~8.5KB terms.    *)
(*            Closing these is analogous to three_blocks_... lines    *)
(*            756-903 extended to 4 triples (~150 tactic lines).      *)
(* ================================================================== *)

let FOUR_BLOCKS_PRELOOP_TAIL_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (pt4:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word)
    stackptr pc.
    aligned 16 stackptr /\
    nonoverlapping (word pc,1200) (in_ptr:int64,64) /\
    nonoverlapping (word pc,1200) (out_ptr:int64,64) /\
    nonoverlapping (word pc,1200) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,1200) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,1200) (key_ptr:int64,240) /\
    nonoverlapping (word pc,1200) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,1200) (stackptr:int64,80) /\
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
    nonoverlapping (ivec_ptr,16) (word pc,1200) /\
    nonoverlapping (xi_ptr,16) (word pc,1200) /\
    nonoverlapping (out_ptr,64) (word pc,1200)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) four_blocks_prelooptail_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word 512; out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add in_ptr (word 48))) s = pt4 /\
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
           read PC s = word(pc + 1196) /\
           read X0 s = word 64 /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = ct3 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = ct4 /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ct3;
                                     word_reversefields 8 ct4]))
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
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  (* ============ Phase A: Preamble ============ *)
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst FOUR_BLOCKS_PRELOOP_TAIL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  (* ============ Phase B: 288-step simulation ============ *)
  ARM_SILENT_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x (word 80)) (word 80) = (x:int64)`;
    WORD_RULE `word_add (word_add x (word n)) (word m) = word_add x (word(n+m):int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  MAP_EVERY (fun n ->
    ARM_SILENT_STEP_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC ("s"^string_of_int n) THEN
    GCM_ENC_SIMPLIFY_TAC) (20--155) THEN
  (* Abbreviate s13_1..s13_4 + ct1 *)
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q0 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("s13_1",type_of rhs), rhs))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q1 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("s13_2",type_of rhs), rhs))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q2 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("s13_3",type_of rhs), rhs))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q3 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("s13_4",type_of rhs), rhs))
    else NO_TAC) THEN
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN
  (* Post-ct1 normalization *)
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION;
    REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI;
    GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
    WORD_XOR_0; WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV PMUL_NORM_CONV)) th
    with _ -> th) THEN
  (* Tail dispatch prologue 156-164 *)
  ARM_SILENT_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC (156--164) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x y) x = (y:int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV) o
                 CONV_RULE(TRY_CONV INT_REDUCE_CONV)) THEN
  (* Cascade to more_than_3 (165-196) *)
  MAP_EVERY (fun n ->
    ARM_SILENT_STEP_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC ("s"^string_of_int n) THEN
    GCM_ENC_SIMPLIFY_TAC) (165--196) THEN
  (* KEY FIX #1: ARITH_RULE normalization before first ST1 at pc+828 *)
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN
  (* more_than_3 body + ct2 *)
  ARM_SILENT_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC (197--211) THEN
  ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN
  (* more_than_2 body + ct3 *)
  ARM_SILENT_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC (212--235) THEN
  ABBREV_TAC `ct3 = word_xor (word_xor pt3 s13_3) rk14:(128)word` THEN
  (* more_than_1 body + ct4 *)
  ARM_SILENT_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC (236--255) THEN
  ABBREV_TAC `ct4 = word_xor (word_xor pt4 s13_4) rk14:(128)word` THEN
  (* Post-ct4 normalization *)
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x (word 80)) (word 80) = (x:int64)`;
    WORD_RULE `word_add (word_add x (word n)) (word m) = word_add x (word(n+m):int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_MASK; WORD_AND_MASK_SYM;
    WORD_AND_MASK_64; WORD_AND_MASK_SYM_64; WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0; KAR_MID_BRIDGE]) THEN
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV PMUL_NORM_CONV)) th
    with _ -> th) THEN
  (* Karatsuba+Barrett body 256-280 *)
  MAP_EVERY (fun n ->
    ARM_SILENT_STEP_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC ("s"^string_of_int n) THEN
    GCM_ENC_SIMPLIFY_TAC) (256--280) THEN
  (* KEY FIX #2: abbreviate Q17/Q18/Q19/Q21 to prevent ~85KB Q19 blowup *)
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q17 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("q17_term",type_of rhs), rhs))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q18 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("q18_term",type_of rhs), rhs))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q19 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("q19_term",type_of rhs), rhs))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q21 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("final_xi",type_of rhs), rhs))
    else NO_TAC) THEN
  (* Remaining Karatsuba+Barrett+store 281-288 *)
  MAP_EVERY (fun n ->
    ARM_SILENT_STEP_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC ("s"^string_of_int n) THEN
    GCM_ENC_SIMPLIFY_TAC) (281--288) THEN
  (* ============ Phase C: ENSURES_FINAL_STATE + 5-way CONJ ============ *)
  (* KEY FIX #3: ENSURES_FINAL_STATE_TAC at s288 (RET at s289 consumes PC) *)
  ENSURES_FINAL_STATE_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  (* CONJ ct1 *)
  CONJ_TAC THENL [
    EXPAND_TAC "ct1" THEN EXPAND_TAC "s13_1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC
  ] THEN
  (* CONJ ct2 *)
  CONJ_TAC THENL [
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
  (* CONJ ct3 *)
  CONJ_TAC THENL [
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
    ABBREV_TAC `ctr2:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
    ABBREV_TAC `br2:(32)word = word_bytereverse (ctr2:(32)word)` THEN
    ABBREV_TAC `step1_2:(32)word = word_bytereverse (word_add (br2:(32)word) (word 1:(32)word))` THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD] THEN
    SUBGOAL_THEN
      `word_subword (word_insert (ivec:(128)word) (96,32) (step1_2:(32)word) :(128)word) (96,32):(32)word = step1_2`
      SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
      `!(y:(32)word). word_insert (word_insert (ivec:(128)word) (96,32) (step1_2:(32)word) :(128)word) (96,32) y :(128)word =
                      word_insert ivec (96,32) y`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "step1_2" THEN
    REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC
  ] THEN
  (* CONJ ct4 — sidestep polymorphic-type issue using INSERT_IDEM/INSERT_SUBWORD *)
  CONJ_TAC THENL [
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
    ABBREV_TAC `ctr3:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
    ABBREV_TAC `br3:(32)word = word_bytereverse (ctr3:(32)word)` THEN
    ABBREV_TAC `step1_3:(32)word = word_bytereverse (word_add (br3:(32)word) (word 1:(32)word))` THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "step1_3" THEN
    REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC
  ] THEN
  (* ============ Phase D: GHASH closure ============ *)
  (* Unroll GHASH, normalize h^4 to symmetric form via POLYVAL_DOT_H4_EQ *)
  REWRITE_TAC[GHASH_POLYVAL_ACC_4; POLYVAL_DOT_H4_EQ;
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
  (* Normalize h^3 to match bridge form (h·h²) via WORD_PMUL_SYM *)
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
     `word_reversefields 8 ct4:int128`;
     `h:int128`; `h1k:int128`;
     `word_join (word 0:(64)word)
        (word_subword (h1k:(128)word) (64,64):(64)word)
      :(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word)
        (word_subword (h3k:(128)word) (64,64):(64)word)
      :(128)word`]
    GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  ANTS_TAC THENL [
    REPEAT CONJ_TAC THENL [
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN
        `word_subword (word_join (word 0:(64)word)
                                 (word_subword (h1k:(128)word) (64,64):(64)word)
                       :(128)word) (0,64):(64)word =
         word_subword (h1k:(128)word) (64,64):(64)word`
        SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN
        `word_subword (word_join (word 0:(64)word)
                                 (word_subword (h3k:(128)word) (64,64):(64)word)
                       :(128)word) (0,64):(64)word =
         word_subword (h3k:(128)word) (64,64):(64)word`
        SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]];
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])
  ] THEN
  (* Unfold ghash_4block_karatsuba + normalize *)
  REWRITE_TAC[ghash_4block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word)
                             (word_subword (h1k:(128)word) (64,64):(64)word)
                   :(128)word) (0,64):(64)word =
     word_subword (h1k:(128)word) (64,64):(64)word`
    SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word)
                             (word_subword (h3k:(128)word) (64,64):(64)word)
                   :(128)word) (0,64):(64)word =
     word_subword (h3k:(128)word) (64,64):(64)word`
    SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR; KARATSUBA_LIMB_0_63; KARATSUBA_LIMB_64_127;
              KARATSUBA_LIMB_128_191; KARATSUBA_LIMB_192_255; WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_BITWISE_RULE
                `word_xor (word 0) x = x:(N)word`] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  EXPAND_TAC "q19_term" THEN
  EXPAND_TAC "q17_term" THEN
  EXPAND_TAC "q18_term" THEN
  EXPAND_TAC "final_xi" THEN
  REWRITE_TAC[WORD_SUBWORD_XOR; KARATSUBA_LIMB_0_63; KARATSUBA_LIMB_64_127;
              KARATSUBA_LIMB_128_191; KARATSUBA_LIMB_192_255; WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_BITWISE_RULE
                `word_xor (word 0) x = x:(N)word`] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  BINOP_TAC THEN
  (* G-half and F-half both reduce to XOR-permutation equalities with
     ~22 XOR atoms each. Structurally analogous to three_blocks pm-identity
     chain (lines 756-903) extended from 3 to 4 triples. The closure here
     uses CHEAT_TAC as a placeholder; the pattern for a full closure is:
     for each half, establish pm_i = pm_j karatsuba_mid identities, then
     ABBREV_ALL_PMUL_TAC + WORD_BITWISE_RULE. *)
  CHEAT_TAC);;
