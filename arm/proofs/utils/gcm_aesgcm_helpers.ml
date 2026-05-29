(* ========================================================================= *)
(* Shared GCM AES-GCM proof helpers (extracted from 1-block claude_4.7).     *)
(*                                                                           *)
(* This file provides ONLY the helper definitions, lemmas, and tactics that  *)
(* the per-N-block claude_4.7 proofs share.  It does NOT include any         *)
(* machine-code definition or main theorem — those belong in the per-proof  *)
(* file.                                                                     *)
(*                                                                           *)
(* Loading this file is fast (~30 seconds), unlike loading the full 1-block *)
(* proof which takes ~12 minutes due to ARM simulation.                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/new_instructions.ml";;
needs "arm/proofs/utils/one_block_preloop_tail_spec.ml";;
needs "common/ghash_spec.ml";;

(* ---- Karatsuba limb extraction lemmas (256-bit word_pmul layout) --------- *)

let KARATSUBA_LIMB_0_63 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (0,64) : 64 word =
    word_subword xl (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_64_127 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (64,64) : 64 word =
    word_xor (word_subword xl (64,64)) (word_subword mid (0,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_128_191 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (128,64) : 64 word =
    word_xor (word_subword xh (0,64)) (word_subword mid (64,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_192_255 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (192,64) : 64 word =
    word_subword xh (64,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMBS = CONJ (CONJ KARATSUBA_LIMB_0_63 KARATSUBA_LIMB_64_127)
                           (CONJ KARATSUBA_LIMB_128_191 KARATSUBA_LIMB_192_255);;

(* ---- Pmul argument-order normalizer -------------------------------------- *)

let PMUL_NORM_CONV tm =
  match tm with
  | Comb(Comb(Const("word_pmul",_), a), b) ->
    if term_order a b then SPECL [a;b] WORD_PMUL_SYM
    else failwith "already normalized"
  | _ -> failwith "not word_pmul";;

(* ---- Assembly-shaped 1-block spec --------------------------------------- *)

let ghash_1block_karatsuba = new_definition
 `ghash_1block_karatsuba (input:int128) (h:int128) (hk:int128) : int128 =
  let a_lo:64 word = word_subword input (0,64) in
  let a_hi:64 word = word_subword input (64,64) in
  let h_lo:64 word = word_subword h (0,64) in
  let h_hi:64 word = word_subword h (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl:int128 = word_pmul a_lo h_hi in
  let ph:int128 = word_pmul a_hi h_lo in
  let pm:int128 = word_pmul (word_xor a_lo a_hi) hk_lo in
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

(* ---- polyval_dot expressed in Karatsuba + Prop3 form --------------------- *)

let POLYVAL_DOT_KARATSUBA = prove(
  `!(input:int128) (h:int128).
    polyval_dot input h =
    (let p_lo = word_pmul (word_subword input (0,64):(64)word)
                          (word_subword h (0,64):(64)word) : int128 in
     let p_hi = word_pmul (word_subword input (64,64):(64)word)
                          (word_subword h (64,64):(64)word) : int128 in
     let p_mid = word_pmul
        (word_xor (word_subword input (0,64):(64)word) (word_subword input (64,64)))
        (word_xor (word_subword h (0,64):(64)word) (word_subword h (64,64))) : int128 in
     let mid = word_xor (word_xor p_mid p_lo) p_hi in
     let a:64 word = word_subword p_lo (0,64) in
     let b:64 word = word_xor (word_subword p_lo (64,64)) (word_subword mid (0,64)) in
     let c:64 word = word_xor (word_subword p_hi (0,64)) (word_subword mid (64,64)) in
     let d:64 word = word_subword p_hi (64,64) in
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
     word_join g f : 128 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_dot; polyval_reduce_prop3; LET_DEF; LET_END_DEF;
              REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[KARATSUBA_LIMBS] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC]);;

(* ---- 1-block bridge ------------------------------------------------------ *)

let BYTESWAP128_SUBWORD_LO = prove(
  `!(h:int128). word_subword (byteswap128 h) (0,64):(64)word = word_subword h (64,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let BYTESWAP128_SUBWORD_HI = prove(
  `!(h:int128). word_subword (byteswap128 h) (64,64):(64)word = word_subword h (0,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_XOR_COMM = prove(
  `!(a:(N)word) (b:(N)word) n.
    word_subword (word_xor a (word_xor b c)) n:(M)word =
    word_subword (word_xor a (word_xor c b)) n`,
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT = prove(
  `!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==> ghash_1block_karatsuba input (byteswap128 h) hk =
        word_reversefields 8 (polyval_dot input h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI;
              REWRITE_RULE[LET_DEF; LET_END_DEF] POLYVAL_DOT_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC; WORD_SUBWORD_XOR_COMM]);;

(* ---- SIMD per-lane reversal fold lemmas ---------------------------------- *)

let REV64_LOWER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (0,8):(8)word) (word_subword xi (8,8):(8)word):(16)word)
                 (word_join (word_subword xi (16,8):(8)word) (word_subword xi (24,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (32,8):(8)word) (word_subword xi (40,8):(8)word):(16)word)
                 (word_join (word_subword xi (48,8):(8)word) (word_subword xi (56,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (0,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REV64_UPPER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (64,8):(8)word) (word_subword xi (72,8):(8)word):(16)word)
                 (word_join (word_subword xi (80,8):(8)word) (word_subword xi (88,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (96,8):(8)word) (word_subword xi (104,8):(8)word):(16)word)
                 (word_join (word_subword xi (112,8):(8)word) (word_subword xi (120,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REV64_128 = prove(
  `!(xi:(128)word).
    word_join
      (word_reversefields 8 (word_subword xi (64,64):(64)word))
      (word_reversefields 8 (word_subword xi (0,64):(64)word)):(128)word =
    word_subword (word_join (word_reversefields 8 xi:(128)word)
                            (word_reversefields 8 xi:(128)word):(256)word) (64,128)`,
  CONV_TAC WORD_BLAST);;

let WORD_SWAP_HALVES_INVOLUTION = prove(
  `!(a:(128)word).
    word_subword
      (word_join
        (word_subword (word_join a a:(256)word) (64,128):(128)word)
        (word_subword (word_join a a:(256)word) (64,128):(128)word):(256)word)
      (64,128):(128)word = a`,
  CONV_TAC WORD_BLAST);;

let WORD_JOIN_SUBWORD_HALVES = prove(
  `!a:(128)word.
     word_join (word_subword a (64,64):(64)word) (word_subword a (0,64):(64)word):(128)word = a`,
  CONV_TAC WORD_BLAST);;

let SIMD_SIMPLIFY_RULES = [REV64_LOWER_LANE; REV64_UPPER_LANE; REV64_128];;

let SIMD_SIMPLIFY_ASSUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th);;

(* ---- Mask / word simplification lemmas ----------------------------------- *)

let MASK_IS_ONES = prove(
  `!(x:(128)word).
    word_insert (word_insert x (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word =
    (word_not(word 0):(128)word)`, CONV_TAC WORD_BLAST);;
let WORD_AND_MASK = prove(
  `!(x:(128)word) (y:(128)word).
    word_and x (word_insert (word_insert y (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word) = x`,
  REWRITE_TAC[MASK_IS_ONES; WORD_AND_NOT0]);;
let WORD_AND_MASK_SYM = prove(
  `!(x:(128)word) (y:(128)word).
    word_and (word_insert (word_insert y (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word) x = x`,
  REWRITE_TAC[MASK_IS_ONES; WORD_AND_NOT0]);;
let BIF_MASK = prove(
  `!(d:(128)word) (n:(128)word) (m:(128)word).
    word_or (word_and d (word_insert (word_insert m (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word))
    (word_and n (word_not (word_insert (word_insert m (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word))) = d`,
  CONV_TAC WORD_BLAST);;
let WORD_ZX_ALLONES_64_128 = prove(
  `word_zx (word 18446744073709551615:(64)word):(128)word =
   word 18446744073709551615:(128)word`, CONV_TAC WORD_BLAST);;
let MASK_IS_ONES_64 = prove(
  `!(x:(128)word).
    word_insert (word_insert x (0,64) (word 18446744073709551615:(64)word):(128)word)
      (64,64) (word 18446744073709551615:(64)word):(128)word =
    (word_not(word 0):(128)word)`, CONV_TAC WORD_BLAST);;
let WORD_AND_MASK_64 = prove(
  `!(x:(128)word) (y:(128)word).
    word_and x (word_insert (word_insert y (0,64) (word 18446744073709551615:(64)word):(128)word)
      (64,64) (word 18446744073709551615:(64)word):(128)word) = x`,
  REWRITE_TAC[MASK_IS_ONES_64; WORD_AND_NOT0]);;
let WORD_AND_MASK_SYM_64 = prove(
  `!(x:(128)word) (y:(128)word).
    word_and (word_insert (word_insert y (0,64) (word 18446744073709551615:(64)word):(128)word)
      (64,64) (word 18446744073709551615:(64)word):(128)word) x = x`,
  REWRITE_TAC[MASK_IS_ONES_64; WORD_AND_NOT0]);;

(* Stack/pointer arithmetic normalizer *)
let STACK_PTR_CANCEL = WORD_RULE
  `!(x:(N)word) y. word_sub (word_add x y) y = x`;;

(* ---- Per-step cleanup (called after every ARM_STEPS_TAC step) ------------ *)
let GCM_ENC_SIMPLIFY_TAC =
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION;
    WORD_ZX_ALLONES_64_128; WORD_AND_MASK; WORD_AND_MASK_SYM; BIF_MASK;
    WORD_AND_MASK_64; WORD_AND_MASK_SYM_64]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th);;

(* ---- GHASH closure lemmas ------------------------------------------------ *)

let WORD_XOR_0_LEFT = WORD_BITWISE_RULE
  `word_xor (word 0) x = (x:(N)word)`;;

let WORD_INSERT_AS_JOIN_1 = prove(
  `!(a:(128)word) (b:(128)word).
    word_insert a (0,64) (word_subword b (64,64):(128)word) =
    (word_join (word_subword a (64,64):(64)word) (word_subword b (64,64):(64)word):(128)word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
              BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128;
              SUB_0; LE_0; ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COND_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 128 /\ ~(i < 64) ==> i - 64 < 64`;
               ARITH_RULE `i < 128 /\ ~(i < 64) ==> 64 + i - 64 = i`]);;

let WORD_INSERT_AS_JOIN_2 = prove(
  `!(a:(128)word) (b:(128)word).
    word_insert a (64,64) (word_subword b (0,64):(128)word) =
    (word_join (word_subword b (0,64):(64)word) (word_subword a (0,64):(64)word):(128)word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
              BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128;
              SUB_0; LE_0; ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COND_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `64 <= i /\ i < 128 ==> ~(i < 64)`;
               ARITH_RULE `64 <= i /\ i < 128 ==> i - 64 < 64`;
               ARITH_RULE `~(64 <= i /\ i < 128) /\ i < 128 ==> i < 64`;
               ARITH_RULE `0 + i = i`]);;

let KAR_SUBWORD_LEMMA = prove(
  `!(xi_rev:(128)word).
    word_subword
      (word_xor xi_rev
        (word_subword (word_join xi_rev xi_rev:(256)word) (64,128)))
      (0,64):(64)word =
    word_xor (word_subword xi_rev (0,64):(64)word)
             (word_subword xi_rev (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REVERSEFIELDS8_SUBWORD_LO = prove(
  `!(x:(128)word).
    word_reversefields 8 (word_subword x (0,64):(64)word) =
    word_subword (word_reversefields 8 x:(128)word) (64,64):(64)word`,
  CONV_TAC WORD_BLAST);;
let REVERSEFIELDS8_SUBWORD_HI = prove(
  `!(x:(128)word).
    word_reversefields 8 (word_subword x (64,64):(64)word) =
    word_subword (word_reversefields 8 x:(128)word) (0,64):(64)word`,
  CONV_TAC WORD_BLAST);;
let WORD_REVERSEFIELDS_XOR_8_128 = prove(
  `!(x:(128)word) (y:(128)word).
    word_reversefields 8 (word_xor x y) =
    word_xor (word_reversefields 8 x) (word_reversefields 8 y)`,
  CONV_TAC WORD_BLAST);;
let KAR_MID_BRIDGE = prove(
  `!(xi:(128)word) (ct:(128)word).
    word_xor (word_subword (word_reversefields 8 xi) (64,64):(64)word)
             (word_xor (word_subword (word_reversefields 8 ct) (64,64))
                       (word_subword (word_reversefields 8 (word_xor xi ct)) (0,64))) =
    word_xor (word_subword (word_reversefields 8 (word_xor xi ct)) (0,64))
             (word_subword (word_reversefields 8 (word_xor xi ct)) (64,64))`,
  REWRITE_TAC[WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  CONV_TAC WORD_RULE);;
let HALFSWAP_XOR = prove(
  `!(a:(128)word) (b:(128)word).
    word_xor
      (word_join (word_join (word_subword a (64,64):(64)word) (word_subword a (0,64):(64)word):(128)word)
                 (word_join (word_subword a (64,64):(64)word) (word_subword a (0,64):(64)word):(128)word):(256)word)
      (word_join b b:(256)word) =
    word_join (word_xor a b:(128)word) (word_xor a b:(128)word):(256)word`,
  CONV_TAC WORD_BLAST);;
let REV8_JOIN_FOLD = prove(
  `!(lo:(64)word) (hi:(64)word).
    word_join (word_reversefields 8 lo) (word_reversefields 8 hi):(128)word =
    word_reversefields 8 (word_join hi lo:(128)word)`,
  CONV_TAC WORD_BLAST);;

(* ---- Tactics for closing the GHASH subgoal -------------------------------- *)

let ABBREV_ALL_PMUL_TAC : tactic = fun (asl,w) ->
  let pms = find_terms (fun t -> try
    let (f,_) = dest_comb t in
    let (g,_) = dest_comb f in
    name_of g = "word_pmul"
    with _ -> false) w in
  let uniq = setify pms in
  let all_frees =
    frees w @ List.concat (map (fun (_,th) -> frees(concl th)) asl) in
  let rec process all n ts (asl,w) =
    match ts with
    | [] -> ALL_TAC (asl,w)
    | t :: rest ->
      let v = variant all (mk_var("pm" ^ string_of_int n, type_of t)) in
      (ABBREV_TAC (mk_eq(v, t)) THEN process (v::all) (n+1) rest) (asl,w) in
  process all_frees 0 uniq (asl,w);;

let PMUL_ARG_SORT_CONV tm =
  match tm with
  | Comb(Comb(Const("word_pmul",_), a), b) ->
    let rec collect t =
      try let l,r = dest_binary "word_xor" t in collect l @ collect r
      with _ -> [t] in
    let compare_term a b =
      if term_order a b then 1
      else if term_order b a then -1
      else 0 in
    let sort_xor x =
      let leaves = collect x in
      let sorted = sort (fun a b -> compare_term a b < 0) leaves in
      if leaves = sorted then None else
      let op = try rator(rator x) with _ -> failwith "no xor" in
      let rebuilt = end_itlist (fun a b -> mk_comb(mk_comb(op, a), b)) sorted in
      Some (WORD_RULE(mk_eq(x, rebuilt))) in
    (match (try sort_xor a with _ -> None) with
     | Some th -> AP_THM (AP_TERM (rator(rator tm)) th) b
     | None ->
       (match (try sort_xor b with _ -> None) with
        | Some th -> AP_TERM (mk_comb(rator(rator tm), a)) th
        | None -> failwith "already sorted or no xor"))
  | _ -> failwith "not word_pmul";;

let DOUBLE_SUBWORD_JOIN = prove(
  `!(x:(128)word).
    word_subword (word_subword (word_join x x:(256)word) (64,128):(128)word) (0,64):(64)word =
    word_subword x (64,64)`,
  CONV_TAC WORD_BLAST);;
let DOUBLE_SUBWORD_JOIN_HI = prove(
  `!(x:(128)word).
    word_subword (word_subword (word_join x x:(256)word) (64,128):(128)word) (64,64):(64)word =
    word_subword x (0,64)`,
  CONV_TAC WORD_BLAST);;
