(* ========================================================================= *)
(* Correctness proof for two_blocks_aes256_gcm_preloop_tail (NEW SIMPLIFIED) *)
(*                                                                           *)
(* Mirrors the structure of                                                  *)
(*   one_block_aes256_gcm_preloop_tail_claude_4.7_simplified_new.ml          *)
(* with named tactics for each phase of the proof.                           *)
(*                                                                           *)
(* All shared helpers (KARATSUBA_LIMBS, GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT,*)
(* GCM_ENC_SIMPLIFY_TAC, ABBREV_ALL_PMUL_TAC, KAR_MID_BRIDGE, etc.) come     *)
(* from arm/proofs/utils/gcm_aesgcm_helpers.ml — loaded in ~4 min, vs. ~12  *)
(* min for the full 1-block proof file.                                     *)
(*                                                                           *)
(* New named tactics (the GCM analog of XTSENC_TAC for 2 blocks):            *)
(*                                                                           *)
(*   GCM_2BLOCK_POST_AES_NORMALIZE_TAC                                       *)
(*       Post-step-93 hyp normalisation (after AES rounds + ABBREV ct1).    *)
(*   GCM_2BLOCK_TAIL_DISPATCH_NORMALIZE_TAC                                  *)
(*       Post-step-99 normalisation, simplifies x5 = word 32 before the     *)
(*       b.gt branch.                                                        *)
(*   GCM_2BLOCK_POST_SIM_NORMALIZE_TAC                                       *)
(*       Post-step-153 normalisation (mirror of 1-block POST_SIM_NORMALIZE). *)
(*   GCM_CT1_STEP_TAC                                                        *)
(*       Closes the ct1 subgoal (recipe identical to 1-block GCM_CT_STEP).  *)
(*   GCM_CT2_STEP_TAC                                                        *)
(*       Closes the ct2 subgoal — extra LANE/CTR_WORD_INSERT chain because  *)
(*       the second counter is gcm_ctr_inc ivec.                             *)
(*   GCM_2BLOCK_GHASH_STEP_TAC                                               *)
(*       Closes the GHASH subgoal — applies the 2-block bridge then BINOP   *)
(*       G/F-half split, each closed by WORD_BITWISE_RULE on 64-bit halves. *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_aesgcm_helpers.ml";;

(* ---- Counter increment helper ------------------------------------------- *)

let gcm_ctr_inc = new_definition
  `gcm_ctr_inc (ivec:(128)word) : (128)word =
     word_insert ivec (96,32)
       (word_bytereverse
          (word_add (word_bytereverse
                       (word_subword ivec (96,32):(32)word))
                    (word 1:(32)word)))`;;

(* ---- Counter bridge: raw REV32+ADD+REV32 byte-join form = gcm_ctr_inc --- *)

let LANE0_BYTES_JOIN = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (24,8):(8)word)
                (word_subword a (16,8):(8)word):(16)word)
     (word_join (word_subword a (8,8):(8)word)
                (word_subword a (0,8):(8)word):(16)word)) :(32)word =
    word_subword a (0,32):(32)word`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE1_BYTES_JOIN = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (56,8):(8)word)
                (word_subword a (48,8):(8)word):(16)word)
     (word_join (word_subword a (40,8):(8)word)
                (word_subword a (32,8):(8)word):(16)word)) :(32)word =
    word_subword a (32,32):(32)word`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE2_BYTES_JOIN = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (88,8):(8)word)
                (word_subword a (80,8):(8)word):(16)word)
     (word_join (word_subword a (72,8):(8)word)
                (word_subword a (64,8):(8)word):(16)word)) :(32)word =
    word_subword a (64,32):(32)word`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE3_BYTES_JOIN_BE = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (96,8):(8)word)
                (word_subword a (104,8):(8)word):(16)word)
     (word_join (word_subword a (112,8):(8)word)
                (word_subword a (120,8):(8)word):(16)word)) :(32)word =
    word_bytereverse (word_subword a (96,32):(32)word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let CTR_WORD_INSERT = prove
 (`!a:(128)word. !x:(32)word.
    word_join
     (word_join x (word_subword a (64,32):(32)word):(64)word)
     (word_join (word_subword a (32,32):(32)word)
                (word_subword a (0,32):(32)word):(64)word) :(128)word =
    word_insert a (96,32) x`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let BYTEREVERSE_JOIN_FOLD = prove
 (`!a:(32)word.
     word_join (word_join (word_subword a (0,8):(8)word)
                          (word_subword a (8,8):(8)word):(16)word)
               (word_join (word_subword a (16,8):(8)word)
                          (word_subword a (24,8):(8)word):(16)word):(32)word =
     word_bytereverse a`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ---- Assembly-shaped 2-block spec --------------------------------------- *)

let ghash_2block_karatsuba = new_definition
 `ghash_2block_karatsuba (b1:int128) (b2:int128)
                         (h_tw:int128) (hk:int128)
                         (h2_tw:int128) (h2k:int128) : int128 =
  let b1_lo:64 word = word_subword b1 (0,64) in
  let b1_hi:64 word = word_subword b1 (64,64) in
  let h2_lo:64 word = word_subword h2_tw (0,64) in
  let h2_hi:64 word = word_subword h2_tw (64,64) in
  let h2k_lo:64 word = word_subword h2k (0,64) in
  let pl1:int128 = word_pmul b1_lo h2_hi in
  let ph1:int128 = word_pmul b1_hi h2_lo in
  let pm1:int128 = word_pmul (word_xor b1_lo b1_hi) h2k_lo in
  let b2_lo:64 word = word_subword b2 (0,64) in
  let b2_hi:64 word = word_subword b2 (64,64) in
  let h_lo:64 word = word_subword h_tw (0,64) in
  let h_hi:64 word = word_subword h_tw (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl2:int128 = word_pmul b2_lo h_hi in
  let ph2:int128 = word_pmul b2_hi h_lo in
  let pm2:int128 = word_pmul (word_xor b2_lo b2_hi) hk_lo in
  let pl:int128 = word_xor pl1 pl2 in
  let ph:int128 = word_xor ph1 ph2 in
  let pm:int128 = word_xor pm1 pm2 in
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

(* ---- Helper for bridge proof: subword cases for 256-bit shl/zx --------- *)

let SHL_SUBWORD_CASES_128 = prove
 (`(!x:(128)word. word_subword (word_shl (word_zx x:(256)word) 64) (0,64):(64)word = word 0) /\
   (!x:(128)word. word_subword (word_shl (word_zx x:(256)word) 64) (64,64):(64)word = word_subword x (0,64)) /\
   (!x:(128)word. word_subword (word_shl (word_zx x:(256)word) 64) (128,64):(64)word = word_subword x (64,64)) /\
   (!x:(128)word. word_subword (word_shl (word_zx x:(256)word) 64) (192,64):(64)word = word 0) /\
   (!x:(128)word. word_subword (word_shl (word_zx x:(256)word) 128) (0,64):(64)word = word 0) /\
   (!x:(128)word. word_subword (word_shl (word_zx x:(256)word) 128) (64,64):(64)word = word 0) /\
   (!x:(128)word. word_subword (word_shl (word_zx x:(256)word) 128) (128,64):(64)word = word_subword x (0,64)) /\
   (!x:(128)word. word_subword (word_shl (word_zx x:(256)word) 128) (192,64):(64)word = word_subword x (64,64)) /\
   (!x:(128)word. word_subword (word_zx x:(256)word) (0,64):(64)word = word_subword x (0,64)) /\
   (!x:(128)word. word_subword (word_zx x:(256)word) (64,64):(64)word = word_subword x (64,64)) /\
   (!x:(128)word. word_subword (word_zx x:(256)word) (128,64):(64)word = word 0) /\
   (!x:(128)word. word_subword (word_zx x:(256)word) (192,64):(64)word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ---- Helper tactic: abbreviate word_subword <variable> halves ----------- *)
let ABBREV_SUBWORD_HALVES_TAC : tactic = fun (asl,w) ->
  let halves = find_terms (fun t -> try
    let (f,n) = dest_comb t in
    let (g,x) = dest_comb f in
    name_of g = "word_subword" && is_var x &&
    (n = `(0,64)` || n = `(64,64)`)
  with _ -> false) w in
  let uniq = setify halves in
  let all_frees =
    frees w @ List.concat (map (fun (_,th) -> frees(concl th)) asl) in
  let rec process all n ts (asl,w) =
    match ts with
    | [] -> ALL_TAC (asl,w)
    | t :: rest ->
      let v = variant all (mk_var("h" ^ string_of_int n, type_of t)) in
      (ABBREV_TAC (mk_eq(v, t)) THEN process (v::all) (n+1) rest) (asl,w) in
  process all_frees 0 uniq (asl,w);;

(* ---- Bridge: ghash_2block_karatsuba = rev8(polyval_reduce_prop3(b1*h^2 + b2*h)) -- *)

let GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC = prove
 (`!(b1:int128) (b2:int128) (h:int128) (hk:int128) (h2k:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h /\
    word_subword h2k (0,64):(64)word = karatsuba_mid (polyval_dot h h)
    ==> ghash_2block_karatsuba b1 b2 (byteswap128 h) hk
                                (byteswap128 (polyval_dot h h)) h2k =
        word_reversefields 8
          (polyval_reduce_prop3
            (word_xor (word_pmul b1 (polyval_dot h h) : 256 word)
                      (word_pmul b2 h : 256 word)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ghash_2block_karatsuba; LET_DEF; LET_END_DEF;
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
  ABBREV_TAC
    `q1lo = word_subword
       (word_pmul (word_xor (h0:(64)word) h4)
                  (word 13979173243358019584:(64)word):(128)word)
       (0,64):(64)word` THEN
  ABBREV_TAC
    `q1hi = word_subword
       (word_pmul (word_xor (h0:(64)word) h4)
                  (word 13979173243358019584:(64)word):(128)word)
       (64,64):(64)word` THEN
  ABBREV_TAC
    `q2 = word_pmul
       (word_xor (h1:(64)word)
         (word_xor h5
         (word_xor h8
         (word_xor h10
         (word_xor h2
         (word_xor h6
         (word_xor h0 (word_xor h4 (q1lo:(64)word)))))))))
       (word 13979173243358019584:(64)word) :(128)word` THEN
  ABBREV_TAC
    `q2b = word_pmul
       (word_xor (h1:(64)word)
         (word_xor h8
         (word_xor h0
         (word_xor h2
         (word_xor h5
         (word_xor h10
         (word_xor h4 (word_xor h6 (q1lo:(64)word)))))))))
       (word 13979173243358019584:(64)word) :(128)word` THEN
  SUBGOAL_THEN `q2:(128)word = q2b` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q2"; "q2b"] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;
    ALL_TAC] THEN
  POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  AP_TERM_TAC THEN BINOP_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* ---- Machine code (2-block assembly) ------------------------------------ *)

let two_blocks_prelooptail_mc = define_assert_from_elf
  "two_blocks_prelooptail_mc"
  "/home/ubuntu/auto_proofs/s2n-bignum/arm/aes-gcm/two_blocks_aes256_gcm_preloop_tail.o"
[
  0x6dbb27e8; 0xd343fc29; 0xaa0403f0; 0xaa0503eb; 0x6d012fea; 0x6d0237ec;
  0x6d033fee; 0xd2f84005; 0xa9047fe5; 0x910103ea; 0x4c407200; 0xaa0903e5;
  0xd2c0002f; 0x4f00e41f; 0x4e181dff; 0xd10004a5; 0x9279e0a5; 0x8b0000a5;
  0x6e20081e; 0x4ebf87de; 0x6e200bc1; 0x4ebf87de; 0xad406d7a; 0x4e284b40;
  0x4e286800; 0x4e284b41; 0x4e286821; 0xad41697c; 0x4e284b61; 0x4e286821;
  0x4e284b60; 0x4e286800; 0x4e284b80; 0x4e286800; 0x4e284b81; 0x4e286821;
  0xad42717b; 0x4e284b41; 0x4e286821; 0x4e284b40; 0x4e286800; 0x4e284b61;
  0x4e286821; 0x4e284b60; 0x4e286800; 0x4e284b80; 0x4e286800; 0xad436d7a;
  0x4e284b81; 0x4e286821; 0x4e284b41; 0x4e286821; 0x4e284b40; 0x4e286800;
  0xad44697c; 0x4e284b60; 0x4e286800; 0x4e284b61; 0x4e286821; 0x4e284b81;
  0x4e286821; 0x4e284b80; 0x4e286800; 0x4c407073; 0x6e134273; 0x4e200a73;
  0xad45717b; 0x4e284b41; 0x4e286821; 0x4e284b40; 0x4e286800; 0x4e284b61;
  0x4e286821; 0x4e284b60; 0x4e286800; 0xad466d7a; 0x4e284b81; 0x4e286821;
  0x4e284b80; 0x4e286800; 0x3dc0397c; 0x4e284b41; 0x4e286821; 0x4e284b40;
  0x4e286800; 0x4e284b61; 0x4e284b60; 0x8b410c04; 0xcb000085; 0x3cc10408;
  0x6e134270; 0x4ebc1f9d; 0xce007509; 0x0f00e413; 0x0f00e411; 0x0f00e412;
  0x3dc004d5; 0x4ea11c27; 0xf10040bf; 0x5400006c; 0x6ebf87de; 0x14000011;
  0x4c9f7049; 0x3dc008d6;
  0x4e200928; 0x3cc10409; 0x6e301d08; 0x0f00e410; 0x6e08451b; 0x4ef6e11c;
  0xce077529; 0x6e3c1e31; 0x0ef6e11a; 0x2e281f7b; 0x6e3a1e73; 0x6e18077b;
  0x4ef5e37b; 0x6e3b1e52; 0x92401821; 0xd1020021; 0xcb0103e1; 0xaa3f03e7;
  0x92401821; 0x9ac124e7; 0xf101003f; 0xaa3f03e8; 0x9a9fb0ee; 0x9a87b10d;
  0x4e081da0; 0x3dc000d4; 0x4c40705a; 0x4e181dc0; 0x4e201d29; 0x4e200928;
  0x6e200bde; 0x3d80021e; 0x6e301d08; 0x4c007049; 0x6e084510; 0x4ef4e11c;
  0x0ef4e11a; 0x6e3c1e31; 0x6e3a1e73; 0x2e281e10; 0x0ef5e210; 0x6e301e52;
  0xfd400150; 0x6e114235; 0xce114e52; 0x0ef0e23d; 0xce1d5652; 0x0ef0e251;
  0x6e124255; 0xce115673; 0x6e134273; 0x4e200a73; 0x4c007073; 0xaa0903e0;
  0x6d412fea; 0x6d4237ec; 0x6d433fee; 0x6cc527e8; 0xd65f03c0
];;

let TWO_BLOCKS_PRELOOP_TAIL_EXEC =
  ARM_MK_EXEC_RULE two_blocks_prelooptail_mc;;

(* ================================================================== *)
(*           NAMED TACTICS — the GCM analog of XTSENC_TAC for 2 blocks *)
(* ================================================================== *)

(* GCM_2BLOCK_POST_AES_NORMALIZE_TAC : run after step 93 + ABBREV ct1.       *)
let GCM_2BLOCK_POST_AES_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION;
    REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI;
    GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
    WORD_XOR_0; WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV PMUL_NORM_CONV)) th
    with _ -> th);;

(* GCM_2BLOCK_TAIL_DISPATCH_NORMALIZE_TAC : simplifies x5 = word 32 before
   the b.gt at step 100. *)
let GCM_2BLOCK_TAIL_DISPATCH_NORMALIZE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x y) x = (y:int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV) o
                 CONV_RULE(TRY_CONV INT_REDUCE_CONV));;

(* GCM_2BLOCK_POST_SIM_NORMALIZE_TAC : post step 153 (Karatsuba+Barrett).   *)
let GCM_2BLOCK_POST_SIM_NORMALIZE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_MASK; WORD_AND_MASK_SYM;
    WORD_AND_MASK_64; WORD_AND_MASK_SYM_64;
    WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0; KAR_MID_BRIDGE]) THEN
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV PMUL_NORM_CONV)) th
    with _ -> th);;

(* GCM_CT1_STEP_TAC : closes the ct1 subgoal — same recipe as 1-block. *)
let GCM_CT1_STEP_TAC =
  EXPAND_TAC "ct1" THEN EXPAND_TAC "s13_1" THEN
  REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
  ASM_REWRITE_TAC[];;

(* GCM_CT2_STEP_TAC : closes ct2 — extra LANE/CTR_WORD_INSERT chain. *)
let GCM_CT2_STEP_TAC =
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
  REWRITE_TAC[BYTEREVERSE_JOIN_FOLD];;

(* GCM_2BLOCK_GHASH_STEP_TAC : the proven 2-block GHASH closure recipe.    *)
(* Uses common-pattern abbreviations: NO h-mappings.                       *)
let GCM_2BLOCK_GHASH_STEP_TAC =
  (* Apply 2-block GHASH unfolding + fold ct1, ct2 *)
  REWRITE_TAC[GHASH_POLYVAL_ACC_2; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
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
  (* Apply bridge lemma *)
  MP_TAC(SPECL [`word_reversefields 8 (word_xor xi ct1):int128`;
                `word_reversefields 8 ct2:int128`;
                `h:int128`; `h1k:int128`;
                `word_join (word 0:(64)word)
                   (word_subword (h1k:(128)word) (64,64):(64)word)
                 :(128)word`]
         GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
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
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_2block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word)
                             (karatsuba_mid (polyval_dot h h):(64)word)
                   :(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word`
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
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
  (* Common-pattern abbreviations: 10 atomic subwords *)
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  ABBREV_TAC `(uA0:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(uA1:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(uB0:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(uB1:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(uC0:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(uC1:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(uD0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(uD1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(uE0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(uE1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  (* Normalize XOR-AC of pmul args *)
  SUBGOAL_THEN
    `word_xor uA1 uA0 = word_xor uA0 uA1:(64)word /\
     word_xor uC1 (word_xor uB1 (word_xor uC0 uB0)) =
       word_xor (word_xor uC0 uB0) (word_xor uC1 uB1):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 6 inner pmul abbreviations *)
  ABBREV_TAC `(p1:(128)word) = word_pmul (uA0:(64)word) (uD0:(64)word)` THEN
  ABBREV_TAC `(p2:(128)word) = word_pmul (uA1:(64)word) (uD1:(64)word)` THEN
  ABBREV_TAC `(p3:(128)word) =
    word_pmul (word_xor (uA0:(64)word) (uA1:(64)word))
              (word_xor (uD0:(64)word) (uD1:(64)word))` THEN
  ABBREV_TAC `(p4:(128)word) =
    word_pmul (word_xor (uC0:(64)word) (uB0:(64)word)) (uE0:(64)word)` THEN
  ABBREV_TAC `(p5:(128)word) =
    word_pmul (word_xor (uC1:(64)word) (uB1:(64)word)) (uE1:(64)word)` THEN
  ABBREV_TAC `(p6:(128)word) =
    word_pmul (word_xor (word_xor (uC0:(64)word) (uB0:(64)word))
                       (word_xor (uC1:(64)word) (uB1:(64)word)))
              (word_xor (uE0:(64)word) (uE1:(64)word))` THEN
  (* Collapse subword-of-join-self via DOUBLE_SUBWORD_JOIN *)
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  (* 13 atomic z-vars for subwords of pmul outputs *)
  ABBREV_TAC `(z1:(64)word) = word_subword (p1:(128)word) (0,64)` THEN
  ABBREV_TAC `(z2:(64)word) = word_subword (p1:(128)word) (64,64)` THEN
  ABBREV_TAC `(z3:(64)word) = word_subword (p4:(128)word) (0,64)` THEN
  ABBREV_TAC `(z4:(64)word) = word_subword (p4:(128)word) (64,64)` THEN
  ABBREV_TAC `(z5:(64)word) = word_subword (p2:(128)word) (0,64)` THEN
  ABBREV_TAC `(z6:(64)word) = word_subword (p2:(128)word) (64,64)` THEN
  ABBREV_TAC `(z7:(64)word) = word_subword (p3:(128)word) (0,64)` THEN
  ABBREV_TAC `(z8:(64)word) = word_subword (p3:(128)word) (64,64)` THEN
  ABBREV_TAC `(z9:(64)word) = word_subword (p5:(128)word) (0,64)` THEN
  ABBREV_TAC `(zA:(64)word) = word_subword (p5:(128)word) (64,64)` THEN
  ABBREV_TAC `(zB:(64)word) = word_subword (p6:(128)word) (0,64)` THEN
  ABBREV_TAC `(zC:(64)word) = word_subword (p6:(128)word) (64,64)` THEN
  ABBREV_TAC `(zD:(64)word) =
    word_subword (word_pmul (word_xor (z1:(64)word) (z3:(64)word))
                            (word 13979173243358019584:(64)word):(128)word)
                 (0,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize the second pmul arg to share form with LHS *)
  SUBGOAL_THEN
    `word_pmul (word_xor (z3:(64)word) z1) (word 13979173243358019584:(64)word):(128)word
     = word_pmul (word_xor (z1:(64)word) z3) (word 13979173243358019584:(64)word):(128)word`
    (fun th -> REWRITE_TAC[th]) THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize the BIG pmul arg (XOR-AC) *)
  SUBGOAL_THEN
    `word_pmul (word_xor (z4:(64)word)
                (word_xor (z2:(64)word)
                (word_xor (zB:(64)word)
                (word_xor (z7:(64)word)
                (word_xor (z9:(64)word)
                (word_xor (z5:(64)word)
                (word_xor (z3:(64)word)
                (word_xor (z1:(64)word) (zD:(64)word))))))))) 
              (word 13979173243358019584:(64)word):(128)word =
     word_pmul (word_xor (z7:(64)word)
                (word_xor (zB:(64)word)
                (word_xor (z1:(64)word)
                (word_xor (z3:(64)word)
                (word_xor (z5:(64)word)
                (word_xor (z9:(64)word)
                (word_xor (zD:(64)word)
                (word_xor (z2:(64)word) (z4:(64)word))))))))) 
              (word 13979173243358019584:(64)word):(128)word` ASSUME_TAC THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* ABBREV qBigP and qSmallP *)
  ABBREV_TAC
    `qBigP = word_pmul
       (word_xor (z7:(64)word) (word_xor zB (word_xor z1 (word_xor z3
        (word_xor z5 (word_xor z9 (word_xor zD (word_xor z2 z4))))))))
       (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC
    `qSmallP = word_pmul (word_xor (z1:(64)word) z3)
                        (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC `qBigPL = word_subword (qBigP:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qBigPH = word_subword (qBigP:(128)word) (64,64):(64)word` THEN
  ABBREV_TAC `qSmallPH = word_subword (qSmallP:(128)word) (64,64):(64)word` THEN
  (* Final closure: word_join of XOR-AC equivalents on each half *)
  BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE];;


(* ================================================================== *)
(*                         THE PROOF                                   *)
(* ================================================================== *)

let TWO_BLOCKS_PRELOOP_TAIL_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word)
    stackptr pc.
    aligned 16 stackptr /\
    nonoverlapping (word pc,652) (in_ptr:int64,32) /\
    nonoverlapping (word pc,652) (out_ptr:int64,32) /\
    nonoverlapping (word pc,652) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,652) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,652) (key_ptr:int64,240) /\
    nonoverlapping (word pc,652) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,652) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,32) (out_ptr,32) /\
    nonoverlapping (in_ptr,32) (xi_ptr,16) /\
    nonoverlapping (in_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,32) (xi_ptr,16) /\
    nonoverlapping (out_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,32) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,32) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,32) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,32) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,652) /\
    nonoverlapping (xi_ptr,16) (word pc,652) /\
    nonoverlapping (out_ptr,32) (word pc,652)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) two_blocks_prelooptail_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word 256; out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h))
      (\s. let ct1 =
             word_xor pt1
               (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct2 =
             word_xor pt2
               (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4
                                 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12
                                 rk13 rk14) in
           read PC s = word(pc + 648) /\
           read X0 s = word 32 /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,32);
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
              fst TWO_BLOCKS_PRELOOP_TAIL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-92: AES rounds for both blocks *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--92) THEN

  (* Abbreviate s13_1 (Q0) and s13_2 (Q1) *)
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

  (* Step 93 + ABBREV ct1 + post-AES normalization *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [93] THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN
  GCM_2BLOCK_POST_AES_NORMALIZE_TAC THEN

  (* Steps 94-99 + tail-dispatch normalization *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (94--99) THEN
  GCM_2BLOCK_TAIL_DISPATCH_NORMALIZE_TAC THEN

  (* Step 100: b.gt branch (taken since 32 > 16) *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [100] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 101-110 + ABBREV ct2 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (101--110) THEN
  ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN

  (* Steps 111-153: 2-block Karatsuba + Barrett reduction *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (111--153) THEN

  (* Post-Karatsuba normalization, lifted into a named tactic *)
  GCM_2BLOCK_POST_SIM_NORMALIZE_TAC THEN

  (* Abbreviate Q19 (the assembled Karatsuba+Barrett result at s153) as
     `final_xi` BEFORE step 154's REV64 — avoids rev64 byte-level term
     explosion AND makes the GHASH closure tactic able to reverse the
     `final_xi = halfswap(...)` substitution. *)
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q19 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("final_xi",type_of rhs), rhs))
    else NO_TAC) THEN

  (* Steps 154-160: rev64 v19, st1, epilogue *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC (154--160) THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Three-way conjunction: ct1, ct2, GHASH. Use nested CONJ_TAC. *)
  CONJ_TAC THENL [
    GCM_CT1_STEP_TAC;
    CONJ_TAC THENL [
      GCM_CT2_STEP_TAC;
      GCM_2BLOCK_GHASH_STEP_TAC
    ]
  ]);;
