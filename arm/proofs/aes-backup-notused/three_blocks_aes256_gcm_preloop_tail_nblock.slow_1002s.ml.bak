(* ========================================================================= *)
(* three_blocks_aes256_gcm_preloop_tail_nblock.ml                            *)
(*                                                                           *)
(* The 3-block AES-GCM preloop_tail proof — N=3 INSTANCE of the generic     *)
(* N-block framework. This file STRUCTURALLY MIRRORS                          *)
(* two_blocks_aes256_gcm_preloop_tail_nblock.ml, scaled up to N=3.            *)
(*                                                                           *)
(* Reuses (no duplication) from gcm_aesgcm_nblock_helpers.ml:                 *)
(*   - All shared lemmas (LANE/CTR/BYTEREVERSE/gcm_ctr_inc, SHL_SUBWORD,    *)
(*     ABBREV_SUBWORD_HALVES_TAC)                                              *)
(*   - Generic Karatsuba spec (ghash_Nblock_karatsuba, kara_acc,             *)
(*     karatsuba_reduce_shared, karatsuba_block_pl/ph/pm)                      *)
(*   - INDUCTIVE BRIDGE (proven once): GHASH_NBLOCK_KARATSUBA_EQ_PROP3        *)
(*   - Per-block named tactics (ABBREV_FINAL_XI_TAC, GCM_NBLOCK_CT_STEP_TAC, *)
(*     GCM_NBLOCK_POST_AES/TAIL_DISPATCH/POST_SIM_NORMALIZE_TAC)               *)
(*                                                                           *)
(* PER-N CONTENT (only piece in this file):                                   *)
(*   - Machine code blob (three_blocks_prelooptail_mc) and EXEC               *)
(*   - ghash_3block_karatsuba (assembly-shape spec)                           *)
(*   - GHASH_3BLOCK_AS_NBLOCK (compatibility with ghash_Nblock_karatsuba)    *)
(*   - GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC — derived from inductive bridge *)
(*   - GCM_3BLOCK_GHASH_STEP_TAC (the N=3 closure: 12 atomic ABBREVs +        *)
(*     9 inner pmul ABBREVs + 19 z-vars, mirrors 2-block's 10+6+13)            *)
(*   - The main theorem THREE_BLOCKS_PRELOOP_TAIL_CORRECT                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/new_instructions.ml";;
needs "arm/proofs/utils/one_block_preloop_tail_spec.ml";;
needs "common/ghash_spec.ml";;
needs "arm/proofs/utils/gcm_aesgcm_helpers.ml";;
needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;

(* ========================================================================= *)
(*  PER-N: 3-block assembly-shape spec ghash_3block_karatsuba.               *)
(* ========================================================================= *)

let ghash_3block_karatsuba = new_definition
 `ghash_3block_karatsuba (b1:int128) (b2:int128) (b3:int128)
                         (h_tw:int128)  (hk:int128)
                         (h2_tw:int128) (h2k:int128)
                         (h3_tw:int128) (h3k:int128) : int128 =
  let b1_lo:64 word = word_subword b1 (0,64) in
  let b1_hi:64 word = word_subword b1 (64,64) in
  let h3_lo:64 word = word_subword h3_tw (0,64) in
  let h3_hi:64 word = word_subword h3_tw (64,64) in
  let h3k_lo:64 word = word_subword h3k (0,64) in
  let pl1:int128 = word_pmul b1_lo h3_hi in
  let ph1:int128 = word_pmul b1_hi h3_lo in
  let pm1:int128 = word_pmul (word_xor b1_lo b1_hi) h3k_lo in
  let b2_lo:64 word = word_subword b2 (0,64) in
  let b2_hi:64 word = word_subword b2 (64,64) in
  let h2_lo:64 word = word_subword h2_tw (0,64) in
  let h2_hi:64 word = word_subword h2_tw (64,64) in
  let h2k_lo:64 word = word_subword h2k (0,64) in
  let pl2:int128 = word_pmul b2_lo h2_hi in
  let ph2:int128 = word_pmul b2_hi h2_lo in
  let pm2:int128 = word_pmul (word_xor b2_lo b2_hi) h2k_lo in
  let b3_lo:64 word = word_subword b3 (0,64) in
  let b3_hi:64 word = word_subword b3 (64,64) in
  let h_lo:64 word = word_subword h_tw (0,64) in
  let h_hi:64 word = word_subword h_tw (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl3:int128 = word_pmul b3_lo h_hi in
  let ph3:int128 = word_pmul b3_hi h_lo in
  let pm3:int128 = word_pmul (word_xor b3_lo b3_hi) hk_lo in
  let pl:int128 = word_xor pl1 (word_xor pl2 pl3) in
  let ph:int128 = word_xor ph1 (word_xor ph2 ph3) in
  let pm:int128 = word_xor pm1 (word_xor pm2 pm3) in
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

(* ========================================================================= *)
(* RELATIONSHIP TO ghash_Nblock_karatsuba                                    *)
(* ========================================================================= *)

let GHASH_3BLOCK_AS_NBLOCK = prove
 (`!(b1:int128) (b2:int128) (b3:int128)
    (h_tw:int128)  (hk:int128)
    (h2_tw:int128) (h2k:int128)
    (h3_tw:int128) (h3k:int128).
    ghash_Nblock_karatsuba [(b1, h3_tw, h3k); (b2, h2_tw, h2k); (b3, h_tw, hk)] =
    ghash_3block_karatsuba b1 b2 b3 h_tw hk h2_tw h2k h3_tw h3k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_Nblock_karatsuba; ghash_3block_karatsuba;
              kara_acc; karatsuba_block_pl; karatsuba_block_ph;
              karatsuba_block_pm; karatsuba_reduce_shared;
              LET_DEF; LET_END_DEF; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC]);;

(* ========================================================================= *)
(* PER-N BRIDGE: ghash_3block_karatsuba ↔ polyval_reduce_prop3                *)
(*                                                                           *)
(* DERIVED from GHASH_NBLOCK_KARATSUBA_EQ_PROP3 (the inductive bridge)        *)
(* + GHASH_3BLOCK_AS_NBLOCK + GHASH_POLYVAL_ACC_3.                            *)
(* ========================================================================= *)

let GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (h:int128)
     (hk:int128) (h2k:int128) (h3k:int128).
    word_subword hk  (0,64):(64)word = karatsuba_mid h /\
    word_subword h2k (0,64):(64)word = karatsuba_mid (polyval_dot h h) /\
    word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h))
    ==> ghash_3block_karatsuba b1 b2 b3
          (byteswap128 h) hk
          (byteswap128 (polyval_dot h h)) h2k
          (byteswap128 (polyval_dot h (polyval_dot h h))) h3k =
        word_reversefields 8
          (polyval_reduce_prop3
            (word_xor
              (word_pmul b1 (polyval_dot h (polyval_dot h h)) : 256 word)
             (word_xor
              (word_pmul b2 (polyval_dot h h) : 256 word)
              (word_pmul b3 h : 256 word))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM GHASH_3BLOCK_AS_NBLOCK] THEN
  SUBGOAL_THEN
    `[(b1:int128, byteswap128 (polyval_dot h (polyval_dot h h)):int128, h3k:int128);
      (b2:int128, byteswap128 (polyval_dot h h):int128, h2k:int128);
      (b3:int128, byteswap128 h:int128, hk:int128)] =
     project_triples
       [(b1, byteswap128 (polyval_dot h (polyval_dot h h)), h3k, polyval_dot h (polyval_dot h h));
        (b2, byteswap128 (polyval_dot h h), h2k, polyval_dot h h);
        (b3, byteswap128 h, hk, h)]`
    SUBST1_TAC THENL [REWRITE_TAC[project_triples]; ALL_TAC] THEN
  MP_TAC(SPEC
    `[(b1:int128, byteswap128 (polyval_dot h (polyval_dot h h)):int128, h3k:int128, polyval_dot h (polyval_dot h h):int128);
      (b2:int128, byteswap128 (polyval_dot h h):int128, h2k:int128, polyval_dot h h:int128);
      (b3:int128, byteswap128 h:int128, hk:int128, h:int128)]
    :(int128#int128#int128#int128)list`
    GHASH_NBLOCK_KARATSUBA_EQ_PROP3) THEN
  ASM_REWRITE_TAC[kara_quad_ok; kara_quad_pmul; WORD_XOR_0_LEFT] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(*  PER-N: MACHINE CODE                                                      *)
(* ========================================================================= *)

let three_blocks_prelooptail_mc = define_assert_from_elf
  "three_blocks_prelooptail_mc"
  "/home/ubuntu/auto_proofs/s2n-bignum/arm/aes-gcm/three_blocks_aes256_gcm_preloop_tail.o"
[
  0x6dbb27e8; 0xd343fc29; 0xaa0403f0; 0xaa0503eb; 0x6d012fea; 0x6d0237ec;
  0x6d033fee; 0xd2f84005; 0xa9047fe5; 0x910103ea; 0x4c407200; 0xaa0903e5;
  0xd2c0002f; 0x4f00e41f; 0x4e181dff; 0xd10004a5; 0x9279e0a5; 0x8b0000a5;
  0x6e20081e; 0x4ebf87de; 0x6e200bc1; 0x4ebf87de; 0x6e200bc2; 0x4ebf87de;
  0x6e200bc3; 0x4ebf87de; 0x6e200bc4; 0x4ebf87de; 0x6e200bc5; 0x4ebf87de;
  0xad406d7a; 0x6e200bc6; 0x4ebf87de; 0x6e200bc7; 0x4e284b42; 0x4e286842;
  0x4e284b40; 0x4e286800; 0x4e284b41; 0x4e286821; 0xad41697c; 0x4e284b61;
  0x4e286821; 0x4e284b62; 0x4e286842; 0x4e284b82; 0x4e286842; 0x4e284b60;
  0x4e286800; 0x4e284b80; 0x4e286800; 0x4e284b81; 0x4e286821; 0xad42717b;
  0x4e284b41; 0x4e286821; 0x4e284b42; 0x4e286842; 0x4e284b40; 0x4e286800;
  0x4e284b61; 0x4e286821; 0x4e284b62; 0x4e286842; 0x4e284b60; 0x4e286800;
  0x4e284b80; 0x4e286800; 0x4e284b82; 0x4e286842; 0xad436d7a; 0x4e284b81;
  0x4e286821; 0x4e284b41; 0x4e286821; 0x4e284b42; 0x4e286842; 0x4e284b40;
  0x4e286800; 0xad44697c; 0x4e284b62; 0x4e286842; 0x4e284b60; 0x4e286800;
  0x4e284b61; 0x4e286821; 0x4e284b81; 0x4e286821; 0x4e284b80; 0x4e286800;
  0x4e284b82; 0x4e286842; 0x4c407073; 0x6e134273; 0x4e200a73; 0xad45717b;
  0x4e284b42; 0x4e286842; 0x4e284b41; 0x4e286821; 0x4e284b40; 0x4e286800;
  0x4e284b61; 0x4e286821; 0x4e284b62; 0x4e286842; 0x4e284b60; 0x4e286800;
  0xad466d7a; 0x4e284b82; 0x4e286842; 0x4e284b81; 0x4e286821; 0x4e284b80;
  0x4e286800; 0x4ebf87de; 0x3dc0397c; 0x4e284b42; 0x4e286842; 0x4e284b41;
  0x4e286821; 0x4e284b40; 0x4e286800; 0x4e284b62; 0x4e284b61; 0x4e284b60;
  0x8b410c04; 0xce02714a; 0xcb000085; 0x3cc10408; 0x6e134270; 0x4ebc1f9d;
  0xce007509; 0x0f00e413; 0x0f00e411; 0x0f00e412; 0x3dc004d5; 0x4ea61cc7;
  0x0f00e411; 0x4ea51ca6; 0x4ea41c85; 0x4ea31c64; 0x4ea21c43; 0x6ebf87de;
  0x4ea11c22; 0x0f00e412; 0xf10180bf; 0x5400042c; 0x4ea61cc7; 0x4ea51ca6;
  0xf10140bf; 0x4ea41c85; 0x4ea31c64; 0x4ea11c23; 0x6ebf87de; 0x5400032c;
  0x4ea61cc7; 0x6ebf87de; 0x4ea51ca6; 0x4ea41c85; 0xf10100bf; 0x4ea11c24;
  0x5400024c; 0xf100c0bf; 0x4ea61cc7; 0x4ea51ca6; 0x4ea11c25; 0x6ebf87de;
  0x5400018c; 0xf10080bf; 0x4ea61cc7; 0x3dc010d8; 0x4ea11c26; 0x6ebf87de;
  0x540000cc; 0x4ea11c27; 0xf10040bf; 0x5400024c; 0x6ebf87de; 0x14000020;
  0x3dc00cd7; 0x4c9f7049; 0x4e200928; 0x3cc10409; 0x6e301d08; 0x6e08451b;
  0x0f00e410; 0x4ef7e11c; 0xce067529; 0x2e281f7b; 0x6e3c1e31; 0x0ef8e37b;
  0x0ef7e11a; 0x6e3b1e52; 0x6e3a1e73; 0x4c9f7049; 0x3dc008d6; 0x4e200928;
  0x3cc10409; 0x6e301d08; 0x0f00e410; 0x6e08451b; 0x4ef6e11c; 0xce077529;
  0x6e3c1e31; 0x0ef6e11a; 0x2e281f7b; 0x6e3a1e73; 0x6e18077b; 0x4ef5e37b;
  0x6e3b1e52; 0x92401821; 0xd1020021; 0xcb0103e1; 0xaa3f03e7; 0x92401821;
  0x9ac124e7; 0xf101003f; 0xaa3f03e8; 0x9a9fb0ee; 0x9a87b10d; 0x4e081da0;
  0x3dc000d4; 0x4c40705a; 0x4e181dc0; 0x4e201d29; 0x4e200928; 0x6e200bde;
  0x3d80021e; 0x6e301d08; 0x4c007049; 0x6e084510; 0x4ef4e11c; 0x0ef4e11a;
  0x6e3c1e31; 0x6e3a1e73; 0x2e281e10; 0x0ef5e210; 0x6e301e52; 0xfd400150;
  0x6e114235; 0xce114e52; 0x0ef0e23d; 0xce1d5652; 0x0ef0e251; 0x6e124255;
  0xce115673; 0x6e134273; 0x4e200a73; 0x4c007073; 0xaa0903e0; 0x6d412fea;
  0x6d4237ec; 0x6d433fee; 0x6cc527e8; 0xd65f03c0
];;

let THREE_BLOCKS_PRELOOP_TAIL_EXEC =
  ARM_MK_EXEC_RULE three_blocks_prelooptail_mc;;

(* ========================================================================= *)
(* PER-BLOCK CIPHERTEXT CLOSURES (instances of GCM_NBLOCK_CT_STEP_TAC for     *)
(* N=3). Block 1 has ivec_1 = ivec; block 2 has ivec_2 = gcm_ctr_inc ivec;   *)
(* block 3 has ivec_3 = gcm_ctr_inc² ivec — the framework's CT_STEP for k≥2 *)
(* doesn't handle iterated counters, so we provide a custom CT3 here.        *)
(* ========================================================================= *)

let GCM_CT1_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 3 1;;
(* CT2 closure: use the framework's GCM_NBLOCK_CT_STEP_TAC 3 2 directly.
   The framework's right-associated pattern matches once the simulation
   normalizations (POST_AES + POST_SIM) put the XOR in standard form. *)
let GCM_CT2_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 3 2;;

(* CT3 for ivec_3 = gcm_ctr_inc² ivec — needs the second counter unfolding.
   Uses framework's right-associated pattern. *)
let GCM_CT3_STEP_TAC =
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
  ABBREV_TAC `ctr3:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
  ABBREV_TAC `br3:(32)word = word_bytereverse (ctr3:(32)word)` THEN
  ABBREV_TAC `step1_3:(32)word = word_bytereverse (word_add (br3:(32)word) (word 1:(32)word))` THEN
  REWRITE_TAC[BYTEREVERSE_JOIN_FOLD] THEN
  SUBGOAL_THEN
    `word_subword (word_insert (ivec:(128)word) (96,32) (step1_3:(32)word) :(128)word) (96,32):(32)word = step1_3`
    SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `!(y:(32)word). word_insert (word_insert (ivec:(128)word) (96,32) (step1_3:(32)word) :(128)word) (96,32) y :(128)word =
                    word_insert ivec (96,32) y`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  EXPAND_TAC "step1_3" THEN
  REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
  CONV_TAC WORD_RULE;;

(* ========================================================================= *)
(*  GHASH STEP TACTIC (N=3 instance) -- same template as 4/5/6/7 blocks.      *)
(*  Atoms -> inner pmuls -> z-vars -> qS/qB -> bubble_sort_conv closure.       *)
(* ========================================================================= *)

let GCM_3BLOCK_GHASH_STEP_TAC =
  REWRITE_TAC[GHASH_POLYVAL_ACC_3; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  SUBGOAL_THEN
    `word_xor xi (word_xor pt1
       (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                         rk8 rk9 rk10 rk11 rk12 rk13 rk14)) =
     word_xor xi ct1:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ct1" THEN EXPAND_TAC "s13_1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    ASM_REWRITE_TAC[]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_xor pt2
       (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4 rk5 rk6
                         rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) =
     ct2:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `ct2:(128)word` &&
         aconv (lhs(concl th)) `word_xor pt2 (word_xor s13_2 rk14):(128)word`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `s13_2:(128)word` &&
         not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT; gcm_ctr_inc] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BYTEREVERSE_JOIN_FOLD]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_xor pt3
       (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc ivec))
                         rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11
                         rk12 rk13 rk14) = ct3:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `ct3:(128)word` &&
         aconv (lhs(concl th)) `word_xor pt3 (word_xor s13_3 rk14):(128)word`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `s13_3:(128)word` &&
         not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT] THEN
    REWRITE_TAC[gcm_ctr_inc] THEN
    ABBREV_TAC `ctr3g:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
    ABBREV_TAC `br3g:(32)word = word_bytereverse (ctr3g:(32)word)` THEN
    ABBREV_TAC `step1_3g:(32)word = word_bytereverse (word_add (br3g:(32)word) (word 1:(32)word))` THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "step1_3g" THEN
    REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
    CONV_TAC WORD_RULE; ALL_TAC ] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`;
     `word_reversefields 8 ct3:int128`;
     `h:int128`;
     `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`]
    GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_3block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot h h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
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
  (* 14 atomic ABBREVs *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hf0:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hf1:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* 9 inner pmul ABBREVs *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hf0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hf1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 18 z-vars *)
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
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Normalize LHS mid-pmuls to abbreviated w?md. *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w3lo_l:(64)word) (word_xor w2lo_l (w1lo_l))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (w3lo_l))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w3md_l:(64)word) (word_xor w2md_l (word_xor w1md_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w3lo_h (word_xor w2lo_h (w1lo_h))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l ((word_subword (qS:(128)word) (0,64))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC] THEN
  BINOP_TAC THENL
   [CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;
    CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC];;

(* ========================================================================= *)
(*                         THE PROOF                                         *)
(*                                                                           *)
(* The pre/post-conditions STRUCTURALLY MIRROR the 2-block file's            *)
(* TWO_BLOCKS_PRELOOP_TAIL_CORRECT, scaled to N=3: pt1/pt2/pt3 inputs;       *)
(* ct1/ct2/ct3 outputs; htable adds h^2 and h^3 entries (h1k holds           *)
(* karatsuba_mid h in lo half + karatsuba_mid h^2 in hi half; h3k holds      *)
(* karatsuba_mid h^3 in lo half); word pc range 1024 (mc length); in_ptr/    *)
(* out_ptr range 48 (3 × 16-byte blocks); X0 post = word 48; X1 pre = 384.   *)
(*                                                                           *)
(* The proof body mirrors the 2-block proof structure scaled to 250 sim     *)
(* steps. ABBREV_FINAL_XI_TAC is applied AFTER step 246 (the final EOR3     *)
(* into Q19, vs 2-block's step 153) and BEFORE step 247's EXT/REV64.         *)
(* The GHASH closure follows the same template as the 4/5/6/7-block proofs: *)
(* atomic ABBREVs (c?lo/c?hi, xilo/xihi, hd/he/hf) -> inner pmul ABBREVs     *)
(* (w?lo/w?hi/w?md) -> z-vars -> qS/qB Barrett pmuls -> bubble_sort_conv      *)
(* XOR-AC closure. NO CHEAT_TAC; NO axioms.                                  *)
(* ========================================================================= *)

let THREE_BLOCKS_PRELOOP_TAIL_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word)
    stackptr pc.
    aligned 16 stackptr /\
    nonoverlapping (word pc,1024) (in_ptr:int64,48) /\
    nonoverlapping (word pc,1024) (out_ptr:int64,48) /\
    nonoverlapping (word pc,1024) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,1024) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,1024) (key_ptr:int64,240) /\
    nonoverlapping (word pc,1024) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,1024) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,48) (out_ptr,48) /\
    nonoverlapping (in_ptr,48) (xi_ptr,16) /\
    nonoverlapping (in_ptr,48) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,48) (xi_ptr,16) /\
    nonoverlapping (out_ptr,48) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,48) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,48) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,48) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,48) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,1024) /\
    nonoverlapping (xi_ptr,16) (word pc,1024) /\
    nonoverlapping (out_ptr,48) (word pc,1024)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) three_blocks_prelooptail_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word 384; out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)))
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
           read PC s = word(pc + 1020) /\
           read X0 s = word 48 /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = ct3 /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ct3]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,48);
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
              fst THREE_BLOCKS_PRELOOP_TAIL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue *)
  ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-138: AES rounds for all 3 blocks *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--138) THEN

  (* Abbreviate s13_1 (Q0), s13_2 (Q1), s13_3 (Q2) *)
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

  (* Step 139 + ABBREV ct1 + post-AES normalization *)
  ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [139] THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN
  GCM_NBLOCK_POST_AES_NORMALIZE_TAC THEN

  (* Steps 140-148: tail dispatch prologue *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (140--148) THEN
  GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC THEN

  (* Steps 149-172: cascade shuffles + b.gt taken (since 48 > 32) *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (149--172) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 173-188 + ABBREV ct2 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (173--188) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN
  ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN

  (* Steps 189-211 + ABBREV ct3 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (189--211) THEN
  ABBREV_TAC `ct3 = word_xor (word_xor pt3 s13_3) rk14:(128)word` THEN

  (* Steps 212-246: 3-block Karatsuba + Barrett reduction (final EOR3 at 246). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (212--246) THEN

  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN

  (* Abbreviate Q19 as `final_xi` BEFORE the EXT/REV64 byte-explosion. *)
  ABBREV_FINAL_XI_TAC THEN

  (* Step-by-step through the epilogue: ext, rev64, str, mov, ldp x4.
     Each ARM_STEPS_TAC [n] also folds through neighboring no-op-like
     instructions, so this 4-call sequence covers all 9 epilogue steps. *)
  ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [247] THEN
  ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [248] THEN
  ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [249] THEN
  ARM_STEPS_TAC THREE_BLOCKS_PRELOOP_TAIL_EXEC [250] THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Four-way conjunction: ct1, ct2, ct3, GHASH. *)
  CONJ_TAC THENL [
    GCM_CT1_STEP_TAC;
    CONJ_TAC THENL [
      GCM_CT2_STEP_TAC;
      CONJ_TAC THENL [
        GCM_CT3_STEP_TAC;
        GCM_3BLOCK_GHASH_STEP_TAC
      ]
    ]
  ]);;
