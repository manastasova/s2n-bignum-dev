(* ========================================================================= *)
(* Correctness proof for one_block_aes256_gcm_preloop_tail (DIRECT version).  *)
(*                                                                           *)
(* Unlike the claude_4.7.ml sibling which uses a custom `ghash_1block_karatsuba`
   intermediate spec + a bridge lemma, this proof bridges the assembly to
   `polyval_dot` directly, reusing:
     - KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS  (assembly EOR3 tidy-up = Prop3 limbs)
     - BARRETT_REDUCTION_EQ_PROP3_REDUCTION (two-phase Barrett = Prop3 final)
     - PMUL_KARATSUBA                       (one word_pmul = 3 half-mults)
     - KARATSUBA_LIMBS                      (limb extraction)
     - PMUL_W_64_128                        (expand pmul by 0xC2...)
   All of these are in `arm/proofs/utils/gcm_gmult_v8_nist.ml`.
                                                                             *)
(* ========================================================================= *)

Sys.chdir "/home/ubuntu/auto_proofs/s2n-bignum";;

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/new_instructions.ml";;
needs "arm/proofs/utils/one_block_preloop_tail_spec.ml";;
needs "common/ghash_spec.ml";;
needs "arm/proofs/utils/gcm_gmult_v8_nist.ml";;

(* ---- Pmul argument-order normalizer -------------------------------------- *)

let PMUL_NORM_CONV tm =
  match tm with
  | Comb(Comb(Const("word_pmul",_), a), b) ->
    if term_order a b then SPECL [a;b] WORD_PMUL_SYM
    else failwith "already normalized"
  | _ -> failwith "not word_pmul";;

let WORD_XOR_ASSOC = WORD_BITWISE_RULE
  `word_xor (word_xor a b) c = word_xor a (word_xor b c):(N)word`;;

(* ---- Helper: bridge h's halves through byteswap128 ---------------------- *)

let BYTESWAP128_SUBWORD_LO = prove(
  `!(h:int128). word_subword (byteswap128 h) (0,64):(64)word = word_subword h (64,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let BYTESWAP128_SUBWORD_HI = prove(
  `!(h:int128). word_subword (byteswap128 h) (64,64):(64)word = word_subword h (0,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* ---- Machine code -------------------------------------------------------- *)

let one_block_prelooptail_2_mc = define_assert_from_elf
  "one_block_prelooptail_2_mc"
  "/home/ubuntu/auto_proofs/s2n-bignum/arm/aes-gcm/aes256_gcm_one_block.o"
[
  0x6dbb27e8; 0xd343fc29; 0xaa0403f0; 0xaa0503eb; 0x6d012fea; 0x6d0237ec;
  0x6d033fee; 0xd2f84005; 0xa9047fe5; 0x910103ea; 0x4c407200; 0xaa0903e5;
  0xd2c0002f; 0x4f00e41f; 0x4e181dff; 0xd10004a5; 0x9279e0a5; 0x8b0000a5;
  0x6e20081e; 0x4ebf87de; 0xad406d7a; 0x4e284b40; 0x4e286800; 0xad41697c;
  0x4e284b60; 0x4e286800; 0x4e284b80; 0x4e286800; 0xad42717b; 0x4e284b40;
  0x4e286800; 0x4e284b60; 0x4e286800; 0x4e284b80; 0x4e286800; 0xad436d7a;
  0x4e284b40; 0x4e286800; 0xad44697c; 0x4e284b60; 0x4e286800; 0x4e284b80;
  0x4e286800; 0x4c407073; 0x6e134273; 0x4e200a73; 0xad45717b; 0x4e284b40;
  0x4e286800; 0x4e284b60; 0x4e286800; 0xad466d7a; 0x4e284b80; 0x4e286800;
  0x3dc0397c; 0x4e284b40; 0x4e286800; 0x4e284b60; 0x8b410c04; 0x3cc10408;
  0x6e134270; 0x4ebc1f9d; 0xce007509; 0x0f00e413; 0x0f00e411; 0x0f00e412;
  0x3dc004d5; 0x92401821; 0xd1020021; 0xcb0103e1; 0xaa3f03e7; 0x92401821;
  0x9ac124e7; 0xf101003f; 0xaa3f03e8; 0x9a9fb0ee; 0x9a87b10d; 0x4e081da0;
  0x3dc000d4; 0x4c40705a; 0x4e181dc0; 0x4e201d29; 0x4e200928; 0x6e200bde;
  0x3d80021e; 0x6e301d08; 0x4c007049; 0x6e084510; 0x4ef4e11c; 0x0ef4e11a;
  0x6e3c1e31; 0x6e3a1e73; 0x2e281e10; 0x0ef5e210; 0x6e301e52; 0xfd400150;
  0x6e114235; 0xce114e52; 0x0ef0e23d; 0xce1d5652; 0x0ef0e251; 0x6e124255;
  0xce115673; 0x6e134273; 0x4e200a73; 0x4c007073; 0xaa0903e0; 0x6d412fea;
  0x6d4237ec; 0x6d433fee; 0x6cc527e8; 0xd65f03c0
];;

let ONE_BLOCK_PRELOOP_TAIL_EXEC =
  ARM_MK_EXEC_RULE one_block_prelooptail_2_mc;;

(* ---- SIMD per-lane reversal fold lemmas --------------------------------- *)

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

let SIMD_SIMPLIFY_RULES = [REV64_LOWER_LANE; REV64_UPPER_LANE; REV64_128];;

let SIMD_SIMPLIFY_ASSUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th);;

(* ---- Mask / word simplification lemmas ---------------------------------- *)

let WORD_AND_ONES_128 = prove(
  `!(x:(128)word). word_and x (word_not(word 0)) = x`, CONV_TAC WORD_BLAST);;
let BIF_ALLONES = prove(
  `!(d:(128)word) (n:(128)word).
    word_or (word_and d (word_not(word 0)))
            (word_and n (word_not(word_not(word 0)))) = d`, CONV_TAC WORD_BLAST);;
let MASK_IS_ONES = prove(
  `!(x:(128)word).
    word_insert (word_insert x (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word =
    (word_not(word 0):(128)word)`, CONV_TAC WORD_BLAST);;
let WORD_AND_MASK = prove(
  `!(x:(128)word) (y:(128)word).
    word_and x (word_insert (word_insert y (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word) = x`,
  REWRITE_TAC[MASK_IS_ONES; WORD_AND_ONES_128]);;
let WORD_AND_MASK_SYM = prove(
  `!(x:(128)word) (y:(128)word).
    word_and (word_insert (word_insert y (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word) x = x`,
  REWRITE_TAC[MASK_IS_ONES] THEN CONV_TAC WORD_BLAST);;
let BIF_MASK = prove(
  `!(d:(128)word) (n:(128)word) (m:(128)word).
    word_or (word_and d (word_insert (word_insert m (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word))
    (word_and n (word_not (word_insert (word_insert m (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word))) = d`,
  REWRITE_TAC[MASK_IS_ONES; BIF_ALLONES]);;
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
  REWRITE_TAC[MASK_IS_ONES_64; WORD_AND_ONES_128]);;
let WORD_AND_MASK_SYM_64 = prove(
  `!(x:(128)word) (y:(128)word).
    word_and (word_insert (word_insert y (0,64) (word 18446744073709551615:(64)word):(128)word)
      (64,64) (word 18446744073709551615:(64)word):(128)word) x = x`,
  REWRITE_TAC[MASK_IS_ONES_64] THEN CONV_TAC WORD_BLAST);;

let GCM_ENC_SIMPLIFY_TAC =
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION;
    WORD_ZX_ALLONES_64_128; WORD_AND_MASK; WORD_AND_MASK_SYM; BIF_MASK;
    WORD_AND_MASK_64; WORD_AND_MASK_SYM_64]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th);;

(* ---- GHASH closure lemmas ----------------------------------------------- *)

let WORD_OR_SELF = WORD_BITWISE_RULE `word_or x x = (x:(N)word)`;;

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

(* ---- Helper tactics for closing the GHASH goal -------------------------- *)

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

(* --- Tactic: abbreviate the 64-bit halves of pmul-abbreviation hypotheses.

   After ABBREV_ALL_PMUL_TAC introduces equalities of the form
     word_pmul X Y = pm_k   (where pm_k : (128)word)
   this tactic classifies each pmul by the shape of its left argument X:
     - X = word_xor _ _        -> label "m" (mid):  halves abbreviated xml / xmh
     - X = word_subword _ (0,64)  -> label "l" (low): halves xll / xlh
     - X = word_subword _ (64,64) -> label "h" (high): halves xhl / xhh
   Abbreviation targets are only added when the *halves* actually appear in the
   goal; `ABBREV_TAC` is idempotent and tolerates missing patterns.           *)
let ABBREV_PMUL_HALVES_TAC : tactic = fun (asl,w) ->
  let classify_pmul eqn =
    try
      let lhs, rhs = dest_eq eqn in
      let pmul, _ = dest_comb lhs in
      let pmul_fn, x_arg = dest_comb pmul in
      if name_of pmul_fn <> "word_pmul" then None
      else begin
        match x_arg with
        | Comb(Comb(Const("word_xor",_), _), _) -> Some ("m", rhs)
        | Comb(Comb(Const("word_subword",_), _), pair) ->
          (try
             let k_term, _ = dest_pair pair in
             let k = dest_small_numeral k_term in
             if k = 0 then Some ("l", rhs)
             else if k = 64 then Some ("h", rhs)
             else None
           with _ -> None)
        | _ -> None
      end
    with _ -> None in
  let pmul_vs =
    List.filter_map (fun (_, th) -> classify_pmul (concl th)) asl in
  let all_frees =
    frees w @ List.concat (map (fun (_,th) -> frees(concl th)) asl) in
  let subword_const =
    inst [`:128`, `:M`; `:64`, `:N`]
         `word_subword:(M)word->num#num->(N)word` in
  let rec process all tasks (asl,w) =
    match tasks with
    | [] -> ALL_TAC (asl,w)
    | (label, v_term) :: rest ->
      let vname = "x" ^ label in
      let vl_var = variant all (mk_var(vname ^ "l", `:(64)word`)) in
      let vh_var = variant all (mk_var(vname ^ "h", `:(64)word`)) in
      let el = mk_eq(vl_var,
          mk_comb(mk_comb(subword_const, v_term), `0,64`)) in
      let eh = mk_eq(vh_var,
          mk_comb(mk_comb(subword_const, v_term), `64,64`)) in
      (ABBREV_TAC el THEN ABBREV_TAC eh THEN
       process (vl_var::vh_var::all) rest) (asl,w) in
  process all_frees pmul_vs (asl,w);;

(* ================================================================== *)
(*                    THE PROOF (direct version)                      *)
(*                                                                    *)
(* Closure step: bridge assembly shape to polyval_dot using the four  *)
(* reusable lemmas                                                    *)
(*   1. KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS                            *)
(*   2. BARRETT_REDUCTION_EQ_PROP3_REDUCTION                          *)
(*   3. PMUL_KARATSUBA                                                *)
(*   4. KARATSUBA_LIMBS                                               *)
(* No custom implementation-shaped intermediate spec is used.         *)
(* ================================================================== *)

let ONE_BLOCK_PRELOOP_TAIL_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) stackptr pc.
    aligned 16 stackptr /\
    nonoverlapping (word pc,448) (in_ptr:int64,16) /\
    nonoverlapping (word pc,448) (out_ptr:int64,16) /\
    nonoverlapping (word pc,448) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,448) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,448) (key_ptr:int64,240) /\
    nonoverlapping (word pc,448) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,448) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,16) (out_ptr,16) /\
    nonoverlapping (in_ptr,16) (xi_ptr,16) /\
    nonoverlapping (in_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,16) (xi_ptr,16) /\
    nonoverlapping (out_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,16) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,16) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,16) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,16) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,448) /\
    nonoverlapping (xi_ptr,16) (word pc,448) /\
    nonoverlapping (out_ptr,16) (word pc,448)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) one_block_prelooptail_2_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word 128; out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h)
      (\s. let ct = word_xor pt (aes256_block_enc ivec rk0 rk1 rk2 rk3
                     rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           read PC s = word(pc + 444) /\
           read X0 s = word 16 /\
           read (memory :> bytes128 out_ptr) s = ct /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,16);
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

  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst ONE_BLOCK_PRELOOP_TAIL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue *)
  ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x (word 80)) (word 80) = (x:int64)`;
    WORD_RULE `word_add (word_add x (word n)) (word m) = word_add x (word(n+m):int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-84 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--84) THEN

  (* Abbreviate AES output *)
  ABBREV_TAC `ct = word_xor (word_xor pt (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese ivec rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13)) rk14:(128)word` THEN
  ABBREV_TAC `s13 = aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese ivec rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13:(128)word` THEN

  (* Steps 85-93 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (85--93) THEN
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

  (* Steps 94-111 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (94--111) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x (word 80)) (word 80) = (x:int64)`;
    WORD_RULE `word_add (word_add x (word n)) (word m) = word_add x (word(n+m):int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_MASK; WORD_AND_MASK_SYM;
    WORD_AND_MASK_64; WORD_AND_MASK_SYM_64;
    WORD_XOR_ASSOC; GSYM Q9; GSYM Q30; GSYM Q31; DREG]) THEN
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

  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (* ct subgoal *)
    EXPAND_TAC "ct" THEN EXPAND_TAC "s13" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    ASM_REWRITE_TAC[];

    (* GHASH subgoal (DIRECT): bridge to polyval_dot without intermediate spec *)
    (* Unfold ghash_polyval_acc, fold xi/ct XOR into xi⊕ct form *)
    REWRITE_TAC[ghash_polyval_acc; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
    (* Substitute word_xor xi (word_xor pt enc) = word_xor xi ct *)
    SUBGOAL_THEN
      `word_xor xi (word_xor pt
         (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                           rk8 rk9 rk10 rk11 rk12 rk13 rk14)) =
       word_xor xi ct:(128)word`
      (fun th -> REWRITE_TAC[th]) THENL [
      EXPAND_TAC "ct" THEN EXPAND_TAC "s13" THEN
      REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC];
      ALL_TAC
    ] THEN
    ASM_REWRITE_TAC[] THEN
    (* Normalize the stored tag in the LHS *)
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
                KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
                WORD_OR_SELF; WORD_XOR_ASSOC; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
                WORD_XOR_0; WORD_XOR_ASSOC;
                REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO;
                REVERSEFIELDS8_SUBWORD_HI] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN
    (* Unfold polyval_dot, apply PMUL_KARATSUBA and KARATSUBA_LIMBS,
       then PMUL_W_64_128 (expanding pmul by 0xC2... as shifts). *)
    REWRITE_TAC[polyval_dot;
                REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA;
                polyval_reduce_prop3; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[KARATSUBA_LIMBS] THEN
    REWRITE_TAC[PMUL_W_64_128] THEN
    (* Peel off outer word_reversefields *)
    MATCH_MP_TAC(MESON[]
      `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
    (* Apply KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS to bridge the assembly's
       mid-recombination to Prop3's limb form *)
    REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF]
                  KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS] THEN
    (* Substitute karatsuba_mid h = word_subword h1k (0,64) *)
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) &&
         name_of(rator(concl th) |> rand |> rator |> rator) = "word_subword"
      then REWRITE_TAC[SYM th] else failwith "no karatsuba_mid hyp") THEN
    (* Bridge byteswap128 h halves to h halves *)
    REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN
    (* Normalize pmul arg order so both sides agree *)
    CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN
    (* Apply BARRETT_REDUCTION_EQ_PROP3_REDUCTION to collapse the
       two-phase Barrett into Prop3's final form *)
    REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF]
                  BARRETT_REDUCTION_EQ_PROP3_REDUCTION] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    (* Clean up residual subword through word_join patterns *)
    REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI] THEN
    (* Abbreviate pmul outputs (xl=pmul a hl, xh=pmul b hh, xm=pmul(a xor b)(hl xor hh)). *)
    ABBREV_ALL_PMUL_TAC THEN
    REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_ASSOC] THEN
    CONV_TAC(TOP_DEPTH_CONV PMUL_ARG_SORT_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN
    ABBREV_ALL_PMUL_TAC THEN
    REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI] THEN
    (* Abbreviate the 64-bit halves of the three pmul outputs as
       xll/xlh, xhl/xhh, xml/xmh. ABBREV_PMUL_HALVES_TAC names them
       systematically (with primes for later-added pmuls). *)
    ABBREV_PMUL_HALVES_TAC THEN
    (* Collapse pmul duplicates: pm2=pm0, pm3=pm1, pm5=pm4. *)
    SUBGOAL_THEN `pm2:(128)word = pm0` ASSUME_TAC THENL [
      EXPAND_TAC "pm2" THEN EXPAND_TAC "pm0" THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128];
      ALL_TAC
    ] THEN
    SUBGOAL_THEN `pm3:(128)word = pm1` ASSUME_TAC THENL [
      EXPAND_TAC "pm3" THEN EXPAND_TAC "pm1" THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128];
      ALL_TAC
    ] THEN
    SUBGOAL_THEN `pm5:(128)word = pm4` ASSUME_TAC THENL [
      EXPAND_TAC "pm5" THEN EXPAND_TAC "pm4" THEN BINOP_TAC THENL [
        REWRITE_TAC[WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
        CONV_TAC WORD_BLAST;
        ASM_REWRITE_TAC[karatsuba_mid]
      ];
      ALL_TAC
    ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      ASSUME `pm2:(128)word = pm0`;
      ASSUME `pm3:(128)word = pm1`;
      ASSUME `pm5:(128)word = pm4`]) THEN
    SUBGOAL_THEN
      `xml''':(64)word = xll /\ xmh''':(64)word = xlh /\
       xml'':(64)word = xhl /\ xmh'':(64)word = xhh /\
       xml':(64)word = xml /\ xmh':(64)word = xmh`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    (* Collapse word_subword (word 0) *)
    SUBGOAL_THEN
      `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
       word_subword (word 0:(128)word) (64,64):(64)word = word 0`
      (fun th -> REWRITE_TAC[th]) THENL
      [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    REWRITE_TAC[WORD_XOR_0; WORD_XOR_ASSOC] THEN
    (* Abbreviate first-reduction pattern r1 *)
    ABBREV_TAC
      `r1:(128)word = word_xor (word_shl (word_zx (xll:(64)word):(128)word) 63)
         (word_xor (word_shl (word_zx xll:(128)word) 62)
                   (word_shl (word_zx xll:(128)word) 57))` THEN
    SUBGOAL_THEN
      `!y:(64)word.
         word_xor (word_subword (word_shl (word_zx (xll:(64)word):(128)word) 63)
                                 (0,64):(64)word)
         (word_xor (word_subword (word_shl (word_zx xll:(128)word) 62)
                                  (0,64):(64)word)
         (word_xor (word_subword (word_shl (word_zx xll:(128)word) 57)
                                  (0,64):(64)word) y)) =
         word_xor (word_subword (r1:(128)word) (0,64):(64)word) y`
      (LABEL_TAC "RL") THENL
      [GEN_TAC THEN EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
      `!y:(64)word.
         word_xor (word_subword (word_shl (word_zx (xll:(64)word):(128)word) 63)
                                 (64,64):(64)word)
         (word_xor (word_subword (word_shl (word_zx xll:(128)word) 62)
                                  (64,64):(64)word)
         (word_xor (word_subword (word_shl (word_zx xll:(128)word) 57)
                                  (64,64):(64)word) y)) =
         word_xor (word_subword (r1:(128)word) (64,64):(64)word) y`
      (LABEL_TAC "RH") THENL
      [GEN_TAC THEN EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    USE_THEN "RL" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "RH" (fun th -> REWRITE_TAC[th]) THEN
    (* Abbreviate inner shift arg t (LHS) and u (RHS) *)
    ABBREV_TAC
      `t:(64)word = word_xor xml (word_xor (word 0)
         (word_xor xll (word_xor xhl
         (word_xor (word_subword (r1:(128)word) (0,64):(64)word)
                   (xlh:(64)word)))))` THEN
    SUBGOAL_THEN
      `word_xor (word_subword (word_shl (word_zx (xll:(64)word):(128)word) 63)
                               (0,64):(64)word)
       (word_xor (word_subword (word_shl (word_zx xll:(128)word) 62)
                                (0,64):(64)word)
       (word_subword (word_shl (word_zx xll:(128)word) 57) (0,64):(64)word)) =
       word_subword (r1:(128)word) (0,64):(64)word` ASSUME_TAC THENL
      [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC
      `u:(64)word = word_xor (xlh:(64)word)
         (word_xor xml (word_xor xll (word_xor xhl
         (word_subword (r1:(128)word) (0,64):(64)word))))` THEN
    SUBGOAL_THEN `t:(64)word = u:(64)word` SUBST_ALL_TAC THENL
      [EXPAND_TAC "t" THEN EXPAND_TAC "u" THEN CONV_TAC WORD_BLAST;
       ALL_TAC] THEN
    (* Abbreviate second-reduction pattern r2 *)
    ABBREV_TAC
      `r2:(128)word = word_xor (word_shl (word_zx (u:(64)word):(128)word) 63)
         (word_xor (word_shl (word_zx u:(128)word) 62)
                   (word_shl (word_zx u:(128)word) 57))` THEN
    SUBGOAL_THEN
      `!y:(64)word.
         word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63)
                                 (0,64):(64)word)
         (word_xor (word_subword (word_shl (word_zx u:(128)word) 62)
                                  (0,64):(64)word)
         (word_xor (word_subword (word_shl (word_zx u:(128)word) 57)
                                  (0,64):(64)word) y)) =
         word_xor (word_subword (r2:(128)word) (0,64):(64)word) y`
      (LABEL_TAC "RL2") THENL
      [GEN_TAC THEN EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
      `!y:(64)word.
         word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63)
                                 (64,64):(64)word)
         (word_xor (word_subword (word_shl (word_zx u:(128)word) 62)
                                  (64,64):(64)word)
         (word_xor (word_subword (word_shl (word_zx u:(128)word) 57)
                                  (64,64):(64)word) y)) =
         word_xor (word_subword (r2:(128)word) (64,64):(64)word) y`
      (LABEL_TAC "RH2") THENL
      [GEN_TAC THEN EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
      `word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63)
                               (0,64):(64)word)
       (word_xor (word_subword (word_shl (word_zx u:(128)word) 62)
                                (0,64):(64)word)
       (word_subword (word_shl (word_zx u:(128)word) 57) (0,64):(64)word)) =
       word_subword (r2:(128)word) (0,64):(64)word` ASSUME_TAC THENL
      [EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
      `word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63)
                               (64,64):(64)word)
       (word_xor (word_subword (word_shl (word_zx u:(128)word) 62)
                                (64,64):(64)word)
       (word_subword (word_shl (word_zx u:(128)word) 57) (64,64):(64)word)) =
       word_subword (r2:(128)word) (64,64):(64)word` ASSUME_TAC THENL
      [EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    USE_THEN "RL2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "RH2" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "u" THEN CONV_TAC WORD_BLAST
  ]);;
