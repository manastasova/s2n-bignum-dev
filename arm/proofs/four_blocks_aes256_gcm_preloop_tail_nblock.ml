(* ========================================================================= *)
(* four_blocks_aes256_gcm_preloop_tail_nblock.ml                             *)
(*                                                                           *)
(* The 4-block AES-GCM preloop_tail proof — N=4 INSTANCE of the generic     *)
(* N-block framework. This file STRUCTURALLY MIRRORS                          *)
(* three_blocks_aes256_gcm_preloop_tail_nblock.ml, scaled up to N=4.          *)
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
(*   - Machine code blob (four_blocks_prelooptail_mc) and EXEC                *)
(*   - ghash_4block_karatsuba (assembly-shape spec)                           *)
(*   - GHASH_4BLOCK_AS_NBLOCK (compatibility with ghash_Nblock_karatsuba)    *)
(*   - GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC — derived from inductive bridge *)
(*   - POLYVAL_DOT_H4_EQ (h^4 left-assoc = symmetric)                         *)
(*   - GCM_4BLOCK_GHASH_STEP_TAC (the N=4 closure: 18 atomic ABBREVs +        *)
(*     12 inner pmul ABBREVs + 24 z-vars, mirrors 3-block's 14+9+18)          *)
(*   - The main theorem FOUR_BLOCKS_PRELOOP_TAIL_CORRECT                      *)
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
(*  PER-N: 4-block assembly-shape spec ghash_4block_karatsuba.               *)
(* ========================================================================= *)

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

(* ========================================================================= *)
(* RELATIONSHIP TO ghash_Nblock_karatsuba                                    *)
(* ========================================================================= *)

let GHASH_4BLOCK_AS_NBLOCK = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128)
    (h_tw:int128)  (hk:int128)
    (h2_tw:int128) (h2k:int128)
    (h3_tw:int128) (h3k:int128)
    (h4_tw:int128) (h4k:int128).
    ghash_Nblock_karatsuba [(b1, h4_tw, h4k); (b2, h3_tw, h3k);
                            (b3, h2_tw, h2k); (b4, h_tw, hk)] =
    ghash_4block_karatsuba b1 b2 b3 b4 h_tw hk h2_tw h2k h3_tw h3k h4_tw h4k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_Nblock_karatsuba; ghash_4block_karatsuba;
              kara_acc; karatsuba_block_pl; karatsuba_block_ph;
              karatsuba_block_pm; karatsuba_reduce_shared;
              LET_DEF; LET_END_DEF; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC]);;

(* ========================================================================= *)
(* PER-N BRIDGE: ghash_4block_karatsuba ↔ polyval_reduce_prop3                *)
(*                                                                           *)
(* DERIVED from GHASH_NBLOCK_KARATSUBA_EQ_PROP3 (the inductive bridge)        *)
(* + GHASH_4BLOCK_AS_NBLOCK + GHASH_POLYVAL_ACC_4 + POLYVAL_DOT_H4_EQ.        *)
(* ========================================================================= *)

let GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (h:int128)
     (hk:int128) (h2k:int128) (h3k:int128) (h4k:int128).
    word_subword hk  (0,64):(64)word = karatsuba_mid h /\
    word_subword h2k (0,64):(64)word = karatsuba_mid (polyval_dot h h) /\
    word_subword h3k (0,64):(64)word =
      karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
    word_subword h4k (0,64):(64)word =
      karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))
    ==> ghash_4block_karatsuba b1 b2 b3 b4
          (byteswap128 h) hk
          (byteswap128 (polyval_dot h h)) h2k
          (byteswap128 (polyval_dot h (polyval_dot h h))) h3k
          (byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h))) h4k =
        word_reversefields 8
          (polyval_reduce_prop3
            (word_xor
              (word_pmul b1 (polyval_dot (polyval_dot h h) (polyval_dot h h))
                : 256 word)
             (word_xor
              (word_pmul b2 (polyval_dot h (polyval_dot h h)) : 256 word)
              (word_xor
                (word_pmul b3 (polyval_dot h h) : 256 word)
                (word_pmul b4 h : 256 word)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM GHASH_4BLOCK_AS_NBLOCK] THEN
  SUBGOAL_THEN
    `[(b1:int128, byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)):int128, h4k:int128);
      (b2:int128, byteswap128 (polyval_dot h (polyval_dot h h)):int128, h3k:int128);
      (b3:int128, byteswap128 (polyval_dot h h):int128, h2k:int128);
      (b4:int128, byteswap128 h:int128, hk:int128)] =
     project_triples
       [(b1, byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)),
           h4k, polyval_dot (polyval_dot h h) (polyval_dot h h));
        (b2, byteswap128 (polyval_dot h (polyval_dot h h)),
           h3k, polyval_dot h (polyval_dot h h));
        (b3, byteswap128 (polyval_dot h h), h2k, polyval_dot h h);
        (b4, byteswap128 h, hk, h)]`
    SUBST1_TAC THENL [REWRITE_TAC[project_triples]; ALL_TAC] THEN
  MP_TAC(SPEC
    `[(b1:int128, byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)):int128,
         h4k:int128, polyval_dot (polyval_dot h h) (polyval_dot h h):int128);
      (b2:int128, byteswap128 (polyval_dot h (polyval_dot h h)):int128,
         h3k:int128, polyval_dot h (polyval_dot h h):int128);
      (b3:int128, byteswap128 (polyval_dot h h):int128, h2k:int128, polyval_dot h h:int128);
      (b4:int128, byteswap128 h:int128, hk:int128, h:int128)]
    :(int128#int128#int128#int128)list`
    GHASH_NBLOCK_KARATSUBA_EQ_PROP3) THEN
  ASM_REWRITE_TAC[kara_quad_ok; kara_quad_pmul; WORD_XOR_0_LEFT] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* POLYVAL_DOT_H4_EQ: left-associated h^4 = symmetric h^4.                    *)
(* Bridges GHASH_POLYVAL_ACC_4 output (polyval_dot (polyval_dot              *)
(* (polyval_dot h h) h) h) to the bridge lemma's symmetric h^4 form           *)
(* (polyval_dot (polyval_dot h h) (polyval_dot h h)).                          *)
(* ========================================================================= *)

(* ========================================================================= *)
(* INSERT_IDEM / INSERT_SUBWORD : helpers for ct3/ct4 closures.               *)
(* ========================================================================= *)

(* ========================================================================= *)
(*  PER-N: MACHINE CODE                                                      *)
(* ========================================================================= *)

let four_blocks_prelooptail_mc = define_assert_from_elf
  "four_blocks_prelooptail_mc"
  "/home/ubuntu/auto_proofs/s2n-bignum/arm/aes-gcm/four_blocks_aes256_gcm_preloop_tail.o"
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

(* ========================================================================= *)
(* PER-BLOCK CIPHERTEXT CLOSURES (instances of GCM_NBLOCK_CT_STEP_TAC for     *)
(* N=4). Block 1 has ivec_1 = ivec; block k≥2 has ivec_k = gcm_ctr_inc^{k-1} *)
(* ivec — the framework's CT_STEP for k≥2 doesn't handle iterated counters,  *)
(* so we provide custom CT3/CT4 here.                                         *)
(* ========================================================================= *)

let GCM_CT1_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 4 1;;
let GCM_CT2_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 4 2;;

(* CT3 for ivec_3 = gcm_ctr_inc² ivec — needs the second counter unfolding.
   Uses INSERT_IDEM/INSERT_SUBWORD to sidestep the polymorphic-type issue. *)
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
  REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  EXPAND_TAC "step1_3" THEN
  REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
  CONV_TAC WORD_RULE;;

(* CT4 for ivec_4 = gcm_ctr_inc³ ivec — three-deep counter unfolding. *)
let GCM_CT4_STEP_TAC =
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
  ABBREV_TAC `ctr4:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
  ABBREV_TAC `br4:(32)word = word_bytereverse (ctr4:(32)word)` THEN
  ABBREV_TAC `step1_4:(32)word = word_bytereverse (word_add (br4:(32)word) (word 1:(32)word))` THEN
  REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  EXPAND_TAC "step1_4" THEN
  REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
  CONV_TAC WORD_RULE;;

(* ========================================================================= *)
(*  GHASH STEP TACTIC (N=4 instance)                                          *)
(*                                                                           *)
(* Mirrors the 3-block style scaled to N=4. Key extra steps vs 3-block:       *)
(*   - 18 atomic ABBREVs (4 ct + xi + 4 H powers, vs 3-block's 14)            *)
(*   - 12 inner pmul ABBREVs (3 per block × 4 blocks, vs 3-block's 9)         *)
(*   - 24 z-vars (lo+hi for 12 pmuls, vs 3-block's 18)                        *)
(*   - Byte-form folding for the BIG mid pmul: the karatsuba_mid expansion   *)
(*     of (xi⊕ct1) leaves byte forms (rev8 pt1)_hi etc. that need to be      *)
(*     re-folded to uH0/uH1 atoms before the inner pmul ABBREVs match.        *)
(*   - 21-atom XOR-AC closure uses bubble_sort_conv (WORD_BITWISE_RULE        *)
(*     times out on 21+ atoms).                                                *)
(* ========================================================================= *)

let GCM_4BLOCK_GHASH_STEP_TAC =
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
  (* 18 atomic ABBREVs (4 cts + xi + 4 H powers) *)
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  ABBREV_TAC `(uA0:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(uA1:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (64,64)` THEN
  ABBREV_TAC `(uB0:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(uB1:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(uG0:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(uG1:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(uH0:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(uH1:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(uC0:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(uC1:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(uD0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(uD1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(uE0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(uE1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ABBREV_TAC `(uF0:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(uF1:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(uK0:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(uK1:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Byte-form fold: the karatsuba_mid expansion of (xi⊕ct1) leaves
     (rev8 pt1)_lo ⊕ (rev8 s13_1)_lo ⊕ (rev8 rk14)_lo and the corresponding
     hi form distributed in the goal. Re-fold them back to uH0/uH1 atoms
     (since uH0/uH1 = subword(rev8 ct1)(lo/hi) and ct1 = pt1⊕s13_1⊕rk14). *)
  SUBGOAL_THEN
    `(word_xor (word_subword (word_reversefields 8 (pt1:(128)word)) (0,64))
               (word_xor (word_subword (word_reversefields 8 (s13_1:(128)word)) (0,64))
                         (word_subword (word_reversefields 8 (rk14:(128)word)) (0,64))) :(64)word
      = uH0) /\
     (word_xor (word_subword (word_reversefields 8 (pt1:(128)word)) (64,64))
               (word_xor (word_subword (word_reversefields 8 (s13_1:(128)word)) (64,64))
                         (word_subword (word_reversefields 8 (rk14:(128)word)) (64,64))) :(64)word
      = uH1)`
    (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THENL
       [EXPAND_TAC "uH0" THEN EXPAND_TAC "ct1" THEN
        REWRITE_TAC[GSYM WORD_REVERSEFIELDS_XOR_8_128; GSYM WORD_SUBWORD_XOR];
        EXPAND_TAC "uH1" THEN EXPAND_TAC "ct1" THEN
        REWRITE_TAC[GSYM WORD_REVERSEFIELDS_XOR_8_128; GSYM WORD_SUBWORD_XOR]];
     ALL_TAC] THEN
  (* BIG-mid-pmul fold: the karatsuba_mid argument inside the BIG outer pmul
     contains (uC1 ⊕ pt1_hi ⊕ s13_1_hi ⊕ rk14_hi ⊕ uC0 ⊕ uH0)  (after the lo
     bytes were just folded to uH0). Split into G-half and F-half then re-fold
     to (uC0⊕uH0) ⊕ (uC1⊕uH1). *)
  SUBGOAL_THEN
    `word_xor (uC1:(64)word)
       (word_xor (word_subword (word_reversefields 8 (pt1:(128)word)) (64,64))
        (word_xor (word_subword (word_reversefields 8 (s13_1:(128)word)) (64,64))
         (word_xor (word_subword (word_reversefields 8 (rk14:(128)word)) (64,64))
                   (word_xor uC0 uH0)))) =
     word_xor (word_xor uH0 uC0) (word_xor uH1 uC1):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL
    [SUBGOAL_THEN
       `word_xor (uC1:(64)word)
          (word_xor (word_subword (word_reversefields 8 (pt1:(128)word)) (64,64))
           (word_xor (word_subword (word_reversefields 8 (s13_1:(128)word)) (64,64))
            (word_xor (word_subword (word_reversefields 8 (rk14:(128)word)) (64,64))
                      (word_xor uC0 uH0)))) =
        word_xor
          (word_xor (uC1:(64)word)
            (word_xor (word_subword (word_reversefields 8 (pt1:(128)word)) (64,64))
             (word_xor (word_subword (word_reversefields 8 (s13_1:(128)word)) (64,64))
                       (word_subword (word_reversefields 8 (rk14:(128)word)) (64,64)))))
          (word_xor uC0 uH0)`
       SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
     REWRITE_TAC[GSYM WORD_REVERSEFIELDS_XOR_8_128; GSYM WORD_SUBWORD_XOR] THEN
     EXPAND_TAC "ct1" THEN
     REWRITE_TAC[GSYM WORD_REVERSEFIELDS_XOR_8_128; GSYM WORD_SUBWORD_XOR] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
     ALL_TAC] THEN
  (* Normalize XOR-AC of small pmul args BEFORE inner pmul ABBREVs (mirrors
     3-block recipe). The last 2 conjuncts collapse the flattened (assoc-r)
     form back into the paired (assoc-l) form that p1_mid uses. *)
  SUBGOAL_THEN
    `(word_xor uC0 uH0 = word_xor uH0 uC0:(64)word) /\
     (word_xor uC1 uH1 = word_xor uH1 uC1:(64)word) /\
     (word_xor uA1 uA0 = word_xor uA0 uA1:(64)word) /\
     (word_xor uB1 uB0 = word_xor uB0 uB1:(64)word) /\
     (word_xor uG1 uG0 = word_xor uG0 uG1:(64)word) /\
     (word_xor uC1 (word_xor uH1 (word_xor uC0 uH0)) =
        word_xor (word_xor uH0 uC0) (word_xor uH1 uC1):(64)word) /\
     (word_xor uC0 (word_xor uH0 (word_xor uC1 uH1)) =
        word_xor (word_xor uH0 uC0) (word_xor uH1 uC1):(64)word)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 12 inner pmul ABBREVs (3 per block × 4 blocks) *)
  ABBREV_TAC `(p1_lo:(128)word) =
    word_pmul (word_xor (uH0:(64)word) (uC0:(64)word)) (uK0:(64)word)` THEN
  ABBREV_TAC `(p1_hi:(128)word) =
    word_pmul (word_xor (uH1:(64)word) (uC1:(64)word)) (uK1:(64)word)` THEN
  ABBREV_TAC `(p1_mid:(128)word) =
    word_pmul (word_xor (word_xor (uH0:(64)word) (uC0:(64)word))
                       (word_xor (uH1:(64)word) (uC1:(64)word)))
              (word_xor (uK0:(64)word) (uK1:(64)word))` THEN
  ABBREV_TAC `(p2_lo:(128)word) = word_pmul (uG0:(64)word) (uF0:(64)word)` THEN
  ABBREV_TAC `(p2_hi:(128)word) = word_pmul (uG1:(64)word) (uF1:(64)word)` THEN
  ABBREV_TAC `(p2_mid:(128)word) =
    word_pmul (word_xor (uG0:(64)word) (uG1:(64)word))
              (word_xor (uF0:(64)word) (uF1:(64)word))` THEN
  ABBREV_TAC `(p3_lo:(128)word) = word_pmul (uB0:(64)word) (uE0:(64)word)` THEN
  ABBREV_TAC `(p3_hi:(128)word) = word_pmul (uB1:(64)word) (uE1:(64)word)` THEN
  ABBREV_TAC `(p3_mid:(128)word) =
    word_pmul (word_xor (uB0:(64)word) (uB1:(64)word))
              (word_xor (uE0:(64)word) (uE1:(64)word))` THEN
  ABBREV_TAC `(p4_lo:(128)word) = word_pmul (uA0:(64)word) (uD0:(64)word)` THEN
  ABBREV_TAC `(p4_hi:(128)word) = word_pmul (uA1:(64)word) (uD1:(64)word)` THEN
  ABBREV_TAC `(p4_mid:(128)word) =
    word_pmul (word_xor (uA0:(64)word) (uA1:(64)word))
              (word_xor (uD0:(64)word) (uD1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  (* 24 z-vars for lo/hi subwords of 12 inner pmuls *)
  ABBREV_TAC `(z1_lo:(64)word) = word_subword (p1_lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(z1_hi:(64)word) = word_subword (p1_lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(z2_lo:(64)word) = word_subword (p1_hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(z2_hi:(64)word) = word_subword (p1_hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(z3_lo:(64)word) = word_subword (p1_mid:(128)word) (0,64)` THEN
  ABBREV_TAC `(z3_hi:(64)word) = word_subword (p1_mid:(128)word) (64,64)` THEN
  ABBREV_TAC `(z4_lo:(64)word) = word_subword (p2_lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(z4_hi:(64)word) = word_subword (p2_lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(z5_lo:(64)word) = word_subword (p2_hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(z5_hi:(64)word) = word_subword (p2_hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(z6_lo:(64)word) = word_subword (p2_mid:(128)word) (0,64)` THEN
  ABBREV_TAC `(z6_hi:(64)word) = word_subword (p2_mid:(128)word) (64,64)` THEN
  ABBREV_TAC `(z7_lo:(64)word) = word_subword (p3_lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(z7_hi:(64)word) = word_subword (p3_lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(z8_lo:(64)word) = word_subword (p3_hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(z8_hi:(64)word) = word_subword (p3_hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(z9_lo:(64)word) = word_subword (p3_mid:(128)word) (0,64)` THEN
  ABBREV_TAC `(z9_hi:(64)word) = word_subword (p3_mid:(128)word) (64,64)` THEN
  ABBREV_TAC `(zA_lo:(64)word) = word_subword (p4_lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(zA_hi:(64)word) = word_subword (p4_lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(zB_lo:(64)word) = word_subword (p4_hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(zB_hi:(64)word) = word_subword (p4_hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(zC_lo:(64)word) = word_subword (p4_mid:(128)word) (0,64)` THEN
  ABBREV_TAC `(zC_hi:(64)word) = word_subword (p4_mid:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Normalize the small pmul on the RHS to share the (z1_lo,z4_lo,z7_lo,zA_lo)
     form used by zD and qSmallP. *)
  SUBGOAL_THEN
    `word_pmul (word_xor (zA_lo:(64)word) (word_xor z7_lo (word_xor z4_lo z1_lo)))
               (word 13979173243358019584:(64)word):(128)word =
     word_pmul (word_xor (z1_lo:(64)word) (word_xor z4_lo (word_xor z7_lo zA_lo)))
               (word 13979173243358019584:(64)word):(128)word`
    (fun th -> REWRITE_TAC[th]) THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `(zD:(64)word) =
    word_subword (word_pmul
      (word_xor (z1_lo:(64)word)
       (word_xor (z4_lo:(64)word) (word_xor (z7_lo:(64)word) (zA_lo:(64)word))))
      (word 13979173243358019584:(64)word):(128)word) (0,64)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize BIG outer pmul arg (XOR-AC of all 17 z-atoms). WORD_RULE times
     out on 17 atoms; WORD_BITWISE_RULE handles it. *)
  SUBGOAL_THEN
    `word_pmul
       (word_xor (zC_lo:(64)word)
        (word_xor z9_lo
        (word_xor z6_lo
        (word_xor z3_lo
        (word_xor zA_lo
        (word_xor z7_lo
        (word_xor z4_lo
        (word_xor z1_lo
        (word_xor zB_lo
        (word_xor z8_lo
        (word_xor z5_lo
        (word_xor z2_lo
        (word_xor zD
        (word_xor zA_hi (word_xor z7_hi (word_xor z4_hi z1_hi))))))))))))))))
       (word 13979173243358019584:(64)word):(128)word =
     word_pmul
       (word_xor (z1_hi:(64)word)
        (word_xor z4_hi
        (word_xor z7_hi
        (word_xor zA_hi
        (word_xor z3_lo
        (word_xor z6_lo
        (word_xor z9_lo
        (word_xor zC_lo
        (word_xor z2_lo
        (word_xor z5_lo
        (word_xor z8_lo
        (word_xor zB_lo
        (word_xor z1_lo
        (word_xor z4_lo (word_xor z7_lo (word_xor zA_lo zD))))))))))))))))
       (word 13979173243358019584:(64)word):(128)word`
    ASSUME_TAC THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* 5 outer ABBREVs: qBigP, qSmallP, qBigPL, qBigPH, qSmallPH. *)
  ABBREV_TAC
    `qBigP = word_pmul
       (word_xor (z1_hi:(64)word)
        (word_xor z4_hi
        (word_xor z7_hi
        (word_xor zA_hi
        (word_xor z3_lo
        (word_xor z6_lo
        (word_xor z9_lo
        (word_xor zC_lo
        (word_xor z2_lo
        (word_xor z5_lo
        (word_xor z8_lo
        (word_xor zB_lo
        (word_xor z1_lo
        (word_xor z4_lo (word_xor z7_lo (word_xor zA_lo zD))))))))))))))))
       (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC
    `qSmallP = word_pmul
       (word_xor (z1_lo:(64)word) (word_xor z4_lo (word_xor z7_lo zA_lo)))
       (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC `qBigPL = word_subword (qBigP:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qBigPH = word_subword (qBigP:(128)word) (64,64):(64)word` THEN
  ABBREV_TAC `qSmallPH = word_subword (qSmallP:(128)word) (64,64):(64)word` THEN
  (* Each BINOP half has 22 atoms — beyond WORD_BITWISE_RULE's reach. Both
     sides are XOR-AC equal (same multiset of atoms in different order); use
     bubble_sort_conv to canonicalize each side via XOR commutativity, then
     REFL_TAC closes each half. Each half takes ~10s. *)
  BINOP_TAC THENL
   [CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;
    CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC];;

(* ========================================================================= *)
(*                         THE PROOF                                         *)
(* ========================================================================= *)

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

  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst FOUR_BLOCKS_PRELOOP_TAIL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue *)
  ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-155: AES rounds for all 4 blocks *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--155) THEN

  (* Abbreviate s13_1..s13_4 (Q0..Q3) *)
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

  (* Step 156 + ABBREV ct1 + post-AES normalization *)
  ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [156] THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN
  GCM_NBLOCK_POST_AES_NORMALIZE_TAC THEN

  (* Steps 157-164: tail dispatch prologue *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (157--164) THEN
  GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC THEN

  (* Steps 165-196: cascade through more_than_3 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (165--196) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 197-211 + ABBREV ct2 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (197--211) THEN
  ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN

  (* Steps 212-235 + ABBREV ct3 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (212--235) THEN
  ABBREV_TAC `ct3 = word_xor (word_xor pt3 s13_3) rk14:(128)word` THEN

  (* Steps 236-255 + ABBREV ct4 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (236--255) THEN
  ABBREV_TAC `ct4 = word_xor (word_xor pt4 s13_4) rk14:(128)word` THEN

  (* Steps 256-280: 4-block Karatsuba + Barrett reduction *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (256--280) THEN

  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN

  (* Abbreviate Q19 as `final_xi` BEFORE the EXT/REV64 byte-explosion. *)
  ABBREV_FINAL_XI_TAC THEN

  (* Steps 281-288: epilogue (ext, rev64, str, mov, ldp x4) *)
  ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [281] THEN
  ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [282] THEN
  ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [283] THEN
  ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [284] THEN
  ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [285] THEN
  ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [286] THEN
  ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [287] THEN
  ARM_STEPS_TAC FOUR_BLOCKS_PRELOOP_TAIL_EXEC [288] THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Five-way conjunction: ct1, ct2, ct3, ct4, GHASH. *)
  CONJ_TAC THENL [
    GCM_CT1_STEP_TAC;
    CONJ_TAC THENL [
      GCM_CT2_STEP_TAC;
      CONJ_TAC THENL [
        GCM_CT3_STEP_TAC;
        CONJ_TAC THENL [
          GCM_CT4_STEP_TAC;
          GCM_4BLOCK_GHASH_STEP_TAC
        ]
      ]
    ]
  ]);;
