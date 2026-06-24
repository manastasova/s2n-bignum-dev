(* ========================================================================= *)
(* Correctness proof for two_blocks_aes256_gcm_preloop_tail                  *)
(* Postcondition uses ghash_polyval_acc (composable GHASH spec) for 2 blocks.*)
(*                                                                           *)
(* Structure (mirrors one_block_aes256_gcm_preloop_tail_claude_4.7.ml):       *)
(*  1. [DONE]    ghash_2block_karatsuba: assembly-shaped intermediate spec   *)
(*               (two Karatsuba triples, summed, then one Barrett reduction) *)
(*  2. [DONE]    GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC: algebraic bridge     *)
(*  3. [DONE]    TWO_BLOCKS_PRELOOP_TAIL_CORRECT: ARM simulation proof       *)
(*               (FULL FUNCTIONAL CORRECTNESS — interactively validated      *)
(*               end-to-end via the MCP server on 2026-05-05)               *)
(*                                                                           *)
(* Status (as of 2026-05-05): **ALL THREE PARTS PROVEN**                     *)
(*  - Steps 1-2 validated interactively. The bridge lemma proof uses         *)
(*    ABBREV_ALL_PMUL_TAC + ABBREV_SUBWORD_HALVES_TAC to reduce the 12KB    *)
(*    conclusion after Karatsuba expansion to a small XOR equality closed   *)
(*    by WORD_BITWISE_RULE after proving q2 = q2b (same 9 XOR atoms up to   *)
(*    commutativity).                                                      *)
(*  - Step 3 (main theorem) structure:                                      *)
(*    * Steps 1-160 ARM simulation (final_xi abbreviated before step 154   *)
(*      to avoid rev64 term blow-up)                                       *)
(*    * ct1 subgoal: CLOSED via EXPAND_TAC + aes256_block_enc unfold       *)
(*    * ct2 subgoal: CLOSED via FIRST_ASSUM SYM pattern + LANE lemmas +    *)
(*      BYTEREVERSE_JOIN_FOLD                                              *)
(*    * GHASH subgoal: CLOSED via bridge lemma + HALFSWAP_INVOLUTION +      *)
(*      BINOP split into G-half and F-half, each closed via                *)
(*      ABBREV_ALL_PMUL + ABBREV_SUBWORD_HALVES + pm_i identities +        *)
(*      h-var equalities + q1_fix/q2_big abbreviations + WORD_BITWISE_RULE.*)
(*                                                                           *)
(* Why a new file instead of extending two_blocks_..._direct.ml:              *)
(* The direct approach inlines the full Karatsuba+Barrett normalization in    *)
(* the proof, which causes 1.9MB term blowup after PMUL_KARATSUBA unfolding.  *)
(* The claude_4.7 pattern extracts the assembly shape into a standalone spec, *)
(* proves the bridge lemma ONCE, then folds the assembly output directly into *)
(* the bridge target.                                                         *)
(* ========================================================================= *)

Sys.chdir "/home/ubuntu/auto_proofs/s2n-bignum";;

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/new_instructions.ml";;
needs "arm/proofs/utils/one_block_preloop_tail_spec.ml";;
needs "common/ghash_spec.ml";;

(* Reuse 1-block infrastructure: KARATSUBA_LIMBS, PMUL_NORM_CONV,
   WORD_XOR_ASSOC, ghash_1block_karatsuba, POLYVAL_DOT_KARATSUBA,
   GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT, BYTESWAP128_SUBWORD_LO/HI,
   WORD_SUBWORD_XOR_COMM, REV64_*_LANE/128, WORD_SWAP_HALVES_INVOLUTION,
   SIMD_SIMPLIFY_ASSUM_TAC, mask lemmas, GCM_ENC_SIMPLIFY_TAC,
   WORD_OR_SELF, WORD_INSERT_AS_JOIN_1/_2, KAR_SUBWORD_LEMMA,
   REVERSEFIELDS8_SUBWORD_LO/HI, WORD_REVERSEFIELDS_XOR_8_128,
   KAR_MID_BRIDGE, HALFSWAP_XOR, REV8_JOIN_FOLD, ABBREV_ALL_PMUL_TAC,
   PMUL_ARG_SORT_CONV, DOUBLE_SUBWORD_JOIN, DOUBLE_SUBWORD_JOIN_HI. *)
needs "arm/proofs/aes-backup-notused/one_block_aes256_gcm_preloop_tail_claude_4.7.ml";;

(* ---- Counter increment helper ------------------------------------------- *)

(* Increments the 32-bit big-endian counter in lane 3 (bytes 12-15) of ivec.
   This matches the AES-GCM standard counter increment. *)
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

(* ---- Assembly-shaped spec for 2-block: two Karatsuba triples, summed,
   then one Barrett reduction (matches L256_enc_blocks_more_than_1 into
   L256_enc_blocks_less_than_1 flow in two_blocks_..._preloop_tail.S). -- *)

(* Inputs:
   - b1: first block XORed with running xi (after byte-reversal)
   - b2: second block (after byte-reversal)
   - h_tw  = byteswap128 h           (passed in register Q20)
   - hk    with hk.lo = karatsuba_mid h          (Q21)
   - h2_tw = byteswap128 (polyval_dot h h)       (Q22)
   - h2k   with h2k.lo = karatsuba_mid (polyval_dot h h)  (Q21.hi in practice,
           but we take a separate parameter for clean spec)

   NOTE: The two_blocks assembly uses Htable[1].lo for karatsuba_mid h and
   Htable[1].hi for karatsuba_mid (h^2) (i.e., both halves of h1k). For the
   spec we accept them as distinct parameters hk and h2k, each a 128-bit
   word whose lower 64 bits hold the relevant karatsuba_mid value. *)

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

(* ---- Helper: subword cases for word_shl/word_zx on 128-bit input ------- *)
(* Needed because the RHS polyval_reduce_prop3 unfolds via PMUL_KARATSUBA,
   exposing patterns like word_subword (word_shl (word_zx x:(256)word) 64)
   which don't reduce via standard WORD_SIMPLE_SUBWORD_CONV.                *)

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

(* Helper tactic: abbreviate word_subword <variable> (0,64)/(64,64) patterns.
   Used in the bridge proof to collapse the 12 distinct pm<i> halves into 12
   fresh 64-bit variables h0..h11, after which WORD_BITWISE_RULE can close
   the XOR-commutativity subgoal. *)

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

(* ---- Bridge: ghash_2block_karatsuba = rev8 (polyval_reduce_prop3 (...))
   when hk.lo = kmid h and h2k.lo = kmid (polyval_dot h h) ----------------- *)

(* Strategy:
   1. Unfold ghash_2block_karatsuba on LHS and polyval_reduce_prop3 +
      PMUL_KARATSUBA on RHS to expose the Karatsuba structure.
   2. Apply KARATSUBA_LIMBS + SHL_SUBWORD_CASES_128 to collapse the RHS
      subwords of word_shl/word_zx patterns.
   3. Apply WORD_SUBWORD_XOR to distribute subwords over the outer XOR
      of the two 256-bit products on the RHS.
   4. Normalize word_pmul argument order via PMUL_NORM_CONV.
   5. ABBREV_ALL_PMUL_TAC introduces pm0..pm8 for the 9 distinct pmul outputs.
   6. ABBREV_SUBWORD_HALVES_TAC introduces h0..h11 for the 12 distinct pmul
      halves, collapsing the conclusion to a small XOR expression.
   7. Abbreviate the two remaining inner pmul expressions (q1, q2, q2b).
   8. Prove q2 = q2b via EXPAND + WORD_BITWISE_RULE (XOR commutativity).
   9. Close the top-level equality via BINOP + WORD_BITWISE_RULE. *)

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
  (* At this point we have the key pmul inner arg q1 = pmul (h0 xor h4) w.
     Abbreviate its halves so the outer q2 / q2b pmuls stand on their own. *)
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
  (* Abbreviate the two remaining outer pmuls — they have the SAME 9-atom
     XOR argument up to commutativity. *)
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
  "/home/ubuntu/auto_proofs/s2n-bignum/arm/aes-gcm/aes256_gcm_two_block.o"
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
(*                         THE PROOF                                   *)
(* ================================================================== *)

(* PLAN (not yet fully proven end-to-end; see
   /home/ubuntu/.claude/.../memory/project_two_blocks_claude_4_7_plan.md):

   The main proof follows the 1-block claude_4.7 pattern exactly:
     1. REWRITE preamble + REPEAT STRIP_TAC + ENSURES_INIT_TAC
     2. Steps 1-19 prologue + GCM_ENC_SIMPLIFY_TAC
     3. Steps 20-92 (AES rounds for BOTH blocks) with per-step GCM_ENC_SIMPLIFY_TAC
     4. ABBREV_TAC s13_1 (Q0), s13_2 (Q1), ct1 (after step 93)
     5. Post-step-93 hyp normalization (the same RULE_ASSUM_TAC chain from
        1-block claude_4.7 lines 659-668)
     6. Steps 94-100 (tail dispatch, b.gt taken)
     7. Steps 101-110 + ABBREV_TAC ct2
     8. Steps 111-153 (Karatsuba+Barrett)
     9. Post-step-153 normalization (same as 1-block lines 692-708)
    10. Steps 154-160 + ENSURES_FINAL_STATE_TAC + ASM_REWRITE_TAC
    11. 3-way CONJ_TAC THENL:
        * ct1 subgoal: EXPAND_TAC "ct1"; EXPAND_TAC "s13_1";
                       REWRITE[aes256_block_enc; LET_DEF; LET_END_DEF;
                               WORD_XOR_ASSOC]; ASM_REWRITE_TAC[]
        * ct2 subgoal: EXPAND_TAC "ct2"; EXPAND_TAC "s13_2"; aes256_block_enc;
                       AP_TERM/AP_THM peel chain + LANE0/1/2/3_BYTES_JOIN +
                       CTR_WORD_INSERT + gcm_ctr_inc + BYTEREVERSE_JOIN_FOLD
        * GHASH subgoal:
             REWRITE_TAC[GHASH_POLYVAL_ACC_2; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
             (* Use bridge in reverse: replace Barrett form with ghash_2block_karatsuba *)
             FIRST_ASSUM(fun th ->
               FIRST_ASSUM(fun th2 ->
                 let both = CONJ th th2 in
                 REWRITE_TAC[GSYM(MATCH_MP GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC
                                          both)])) THEN
             REWRITE_TAC[ghash_2block_karatsuba; LET_DEF; LET_END_DEF] THEN
             CONV_TAC(DEPTH_CONV BETA_CONV) THEN
             (* Fold xi⊕pt1⊕aes=xi⊕ct1, pt2⊕aes=ct2 via SUBGOAL_THEN as in 1-block *)
             ASM_REWRITE_TAC[] THEN
             (* Identical closure chain to 1-block (just bigger — 6 pmuls vs 3) *)
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
             REWRITE_TAC[WORD_XOR_ASSOC; KAR_MID_BRIDGE] THEN
             ABBREV_ALL_PMUL_TAC THEN
             REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_ASSOC] THEN
             CONV_TAC(TOP_DEPTH_CONV PMUL_ARG_SORT_CONV) THEN
             REWRITE_TAC[WORD_XOR_ASSOC] THEN
             ABBREV_ALL_PMUL_TAC THEN
             REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI] THEN
             CONV_TAC WORD_BLAST
*)

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
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x (word 80)) (word 80) = (x:int64)`;
    WORD_RULE `word_add (word_add x (word n)) (word m) = word_add x (word(n+m):int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-92: CTR setup + 13 AES rounds on BOTH v0 and v1 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--92) THEN

  (* Abbreviate s13_1 (Q0, aese-chain from ivec), s13_2 (Q1, aese-chain
     from raw-byte counter form equal to gcm_ctr_inc ivec). *)
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

  (* Step 93: eor3 v9, v0, v8, v28 produces pt1⊕s13_1⊕rk14 = ct1 in Q9 *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [93] THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN

  (* Post-93 hyp normalization (mirrors 1-block claude_4.7 lines 659-668) *)
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

  (* Steps 94-99: tail setup (cmp x5,#16). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (94--99) THEN

  (* Simplify x5 = word 32 before the conditional branch *)
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x y) x = (y:int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV) o
                 CONV_RULE(TRY_CONV INT_REDUCE_CONV)) THEN

  (* Step 100: b.gt .L256_enc_blocks_more_than_1 (taken since 32 > 16) *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [100] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 101-110: store ct1, then eor3 produces ct2 in Q9. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (101--110) THEN
  ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN

  (* Steps 111-153: 2-block Karatsuba+Barrett reduction *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (111--153) THEN

  (* Post-step-153 hyp normalization (mirrors 1-block lines 692-708) *)
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x (word 80)) (word 80) = (x:int64)`;
    WORD_RULE `word_add (word_add x (word n)) (word m) = word_add x (word(n+m):int64)`]) THEN
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
    with _ -> th) THEN

  (* Steps 154-160: rev64 v19, st1, epilogue *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC (154--160) THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  CONJ_TAC THENL [
    (* ct1 subgoal *)
    EXPAND_TAC "ct1" THEN EXPAND_TAC "s13_1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC
  ] THEN
  CONJ_TAC THENL [
    (* ct2 subgoal *)
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

  (* GHASH subgoal: apply GHASH_POLYVAL_ACC_2 + GHASH_2BLOCK_KARATSUBA bridge *)
  REWRITE_TAC[GHASH_POLYVAL_ACC_2; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  (* Fold xi ⊕ pt1 ⊕ aes(...)  =  xi ⊕ ct1 *)
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
  (* Fold pt2 ⊕ aes(gcm_ctr_inc ivec, ...)  =  ct2 *)
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
  (* Now apply the bridge in reverse: replace
       word_reversefields 8 (polyval_reduce_prop3 (xor of two pmuls))
     with ghash_2block_karatsuba b1 b2 ...
     We need a witness for h2k such that h2k.lo = karatsuba_mid (polyval_dot h h).
     Use word_join (word 0) (h1k.hi), exploiting that h1k.hi = kmid (h^2). *)
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
  (* Goal now: ghash_2block_karatsuba <inst> = assembly-LHS *)
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
  (* Collapse LHS byte-expansion back to word_reversefields of halfswap *)
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  (* Peel off word_reversefields 8 *)
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  (* LHS = word_join(fx.lo)(fx.hi) = halfswap(halfswap(A)) = A by
     WORD_SWAP_HALVES_INVOLUTION, after substituting final_xi = halfswap(A). *)
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word`
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  (* Goal: A = word_join G F. Collapse A via standard rewrites. *)
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_SELF; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO;
              REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Collapse word_subword (word 0) patterns *)
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_BITWISE_RULE
                `word_xor (word 0) x = x:(N)word`] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Split A into word_join(A.hi)(A.lo) via inverse of WORD_JOIN_SUBWORD_HALVES,
     then BINOP gives 2 subgoals: one for G half, one for F half. The closures
     are nearly identical in structure but differ in which pm identities and
     h-var equalities are invoked. *)
  GEN_REWRITE_TAC (LAND_CONV) [GSYM WORD_JOIN_SUBWORD_HALVES] THEN
  BINOP_TAC THENL [
    (* ---- G half (high 64 bits) ---- *)
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[KARATSUBA_LIMB_0_63; KARATSUBA_LIMB_64_127;
                KARATSUBA_LIMB_128_191; KARATSUBA_LIMB_192_255;
                WORD_XOR_ASSOC] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(fun th ->
      try let c = concl th in let _, r = dest_eq c in
          if is_var r && String.length (name_of r) >= 2 &&
             String.sub (name_of r) 0 2 = "pm"
          then SYM th else th
      with _ -> th) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC
      `q1_fix = word_pmul (word_xor (h8:(64)word) h12)
                          (word 13979173243358019584:(64)word) :(128)word` THEN
    SUBGOAL_THEN
      `word_pmul (word_xor (h12:(64)word) h8)
                 (word 13979173243358019584:(64)word) :(128)word = q1_fix`
      (fun th -> REWRITE_TAC[th]) THENL
      [EXPAND_TAC "q1_fix" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
      `q2_big = word_pmul
        (word_xor h2 (word_xor h7 (word_xor (h8:(64)word)
        (word_xor h12 (word_xor h10 (word_xor h14
        (word_xor (word_subword (q1_fix:(128)word) (0,64):(64)word)
                  (word_xor h9 h13))))))))
        (word 13979173243358019584:(64)word) :(128)word` THEN
    ABBREV_TAC
      `q2_big_rhs = word_pmul
        (word_xor (h13:(64)word)
         (word_xor h9 (word_xor h7 (word_xor h2
         (word_xor h14 (word_xor h10 (word_xor h12 (word_xor h8
         (word_subword (q1_fix:(128)word) (0,64):(64)word)))))))))
        (word 13979173243358019584:(64)word) :(128)word` THEN
    SUBGOAL_THEN `q2_big:(128)word = q2_big_rhs` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["q2_big"; "q2_big_rhs"] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;
      ALL_TAC] THEN
    POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC WORD_BITWISE_RULE;

    (* ---- F half (low 64 bits) ---- *)
    (* Needs an extra ABBREV round because the F-half's LHS contains
       additional pmul terms (the low Karatsuba halves and the 2 inner
       mid-cancellation halves). *)
    ABBREV_ALL_PMUL_TAC THEN
    ABBREV_SUBWORD_HALVES_TAC THEN
    RULE_ASSUM_TAC(fun th ->
      try let c = concl th in let _, r = dest_eq c in
          if is_var r && String.length (name_of r) >= 2 &&
             String.sub (name_of r) 0 2 = "pm"
          then SYM th else th
      with _ -> th) THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[karatsuba_mid]) THEN
    RULE_ASSUM_TAC(fun th ->
      try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV PMUL_NORM_CONV)) th
      with _ -> th) THEN
    (* Establish the 4 pm identities pm0=pm10, pm1=pm13, pm4=pm11, pm5=pm12 *)
    SUBGOAL_THEN `(pm0:(128)word) = pm10` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `(pm1:(128)word) = pm13` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `(pm4:(128)word) = pm11` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `(pm5:(128)word) = pm12` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      ASSUME `(pm0:(128)word) = pm10`; ASSUME `(pm1:(128)word) = pm13`;
      ASSUME `(pm4:(128)word) = pm11`; ASSUME `(pm5:(128)word) = pm12`]) THEN
    ASM_REWRITE_TAC[] THEN
    (* F-half h-var equalities (5 of them) *)
    SUBGOAL_THEN `(h0:(64)word) = h4` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h2:(64)word) = h8` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h5:(64)word) = h13` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h6:(64)word) = h14` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h7:(64)word) = h15` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    (* Substitute pm pmul expressions into the conclusion by reversing the
       pm10/pm11/pm12/pm13/pm2/pm3 defining equations. *)
    REWRITE_TAC[WORD_SUBWORD_XOR; DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI] THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = `pm10:(128)word`
      then REWRITE_TAC[SYM th] else NO_TAC) THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = `pm11:(128)word`
      then REWRITE_TAC[SYM th] else NO_TAC) THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = `pm12:(128)word`
      then REWRITE_TAC[SYM th] else NO_TAC) THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = `pm13:(128)word`
      then REWRITE_TAC[SYM th] else NO_TAC) THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = `pm2:(128)word`
      then REWRITE_TAC[SYM th] else NO_TAC) THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = `pm3:(128)word`
      then REWRITE_TAC[SYM th] else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC
      `q1_fix = word_pmul (word_xor (h9:(64)word) h13)
                          (word 13979173243358019584:(64)word) :(128)word` THEN
    SUBGOAL_THEN
      `word_pmul (word_xor (h13:(64)word) h9)
                 (word 13979173243358019584:(64)word) :(128)word = q1_fix`
      (fun th -> REWRITE_TAC[th]) THENL
      [EXPAND_TAC "q1_fix" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
      `q2_big = word_pmul
        (word_xor h4 (word_xor h8 (word_xor (h9:(64)word)
        (word_xor h13 (word_xor h11 (word_xor h15
        (word_xor (word_subword (q1_fix:(128)word) (0,64):(64)word)
                  (word_xor h10 h14))))))))
        (word 13979173243358019584:(64)word) :(128)word` THEN
    ABBREV_TAC
      `q2_big_rhs = word_pmul
        (word_xor (h14:(64)word)
         (word_xor h10 (word_xor h8 (word_xor h4
         (word_xor h15 (word_xor h11 (word_xor h13 (word_xor h9
         (word_subword (q1_fix:(128)word) (0,64):(64)word)))))))))
        (word 13979173243358019584:(64)word) :(128)word` THEN
    SUBGOAL_THEN `q2_big:(128)word = q2_big_rhs` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["q2_big"; "q2_big_rhs"] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;
      ALL_TAC] THEN
    POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC WORD_BITWISE_RULE
  ]);;
