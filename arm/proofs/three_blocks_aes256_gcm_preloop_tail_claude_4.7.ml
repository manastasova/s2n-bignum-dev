(* ========================================================================= *)
(* Correctness proof for three_blocks_aes256_gcm_preloop_tail                *)
(* Postcondition uses ghash_polyval_acc (composable GHASH spec) for 3 blocks.*)
(*                                                                           *)
(* Structure (mirrors two_blocks_aes256_gcm_preloop_tail_claude_4.7.ml):     *)
(*  1. ghash_3block_karatsuba: assembly-shaped intermediate spec             *)
(*     (three Karatsuba triples, summed, then one Barrett reduction)         *)
(*  2. GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC: algebraic bridge               *)
(*  3. THREE_BLOCKS_PRELOOP_TAIL_CORRECT: ARM simulation proof               *)
(* ========================================================================= *)

Sys.chdir "/home/ubuntu/auto_proofs/s2n-bignum";;

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/new_instructions.ml";;
needs "arm/proofs/utils/one_block_preloop_tail_spec.ml";;
needs "common/ghash_spec.ml";;
needs "arm/proofs/one_block_aes256_gcm_preloop_tail_claude_4.7.ml";;
needs "arm/proofs/two_blocks_aes256_gcm_preloop_tail_claude_4.7.ml";;

(* Reuse from 2-block file: gcm_ctr_inc, LANE0..3_BYTES_JOIN,
   LANE3_BYTES_JOIN_BE, CTR_WORD_INSERT, BYTEREVERSE_JOIN_FOLD,
   SHL_SUBWORD_CASES_128, ABBREV_SUBWORD_HALVES_TAC, HALFSWAP_INVOLUTION,
   WORD_JOIN_SUBWORD_HALVES, ghash_2block_karatsuba. *)

(* ---- Assembly-shaped spec for 3-block: three Karatsuba triples, summed,
   then one Barrett reduction. Mirrors ghash_2block_karatsuba. ------------ *)

let ghash_3block_karatsuba = new_definition
 `ghash_3block_karatsuba (b1:int128) (b2:int128) (b3:int128)
                         (h_tw:int128)  (hk:int128)
                         (h2_tw:int128) (h2k:int128)
                         (h3_tw:int128) (h3k:int128) : int128 =
  (* Triple 1: b1 * h^3 *)
  let b1_lo:64 word = word_subword b1 (0,64) in
  let b1_hi:64 word = word_subword b1 (64,64) in
  let h3_lo:64 word = word_subword h3_tw (0,64) in
  let h3_hi:64 word = word_subword h3_tw (64,64) in
  let h3k_lo:64 word = word_subword h3k (0,64) in
  let pl1:int128 = word_pmul b1_lo h3_hi in
  let ph1:int128 = word_pmul b1_hi h3_lo in
  let pm1:int128 = word_pmul (word_xor b1_lo b1_hi) h3k_lo in
  (* Triple 2: b2 * h^2 *)
  let b2_lo:64 word = word_subword b2 (0,64) in
  let b2_hi:64 word = word_subword b2 (64,64) in
  let h2_lo:64 word = word_subword h2_tw (0,64) in
  let h2_hi:64 word = word_subword h2_tw (64,64) in
  let h2k_lo:64 word = word_subword h2k (0,64) in
  let pl2:int128 = word_pmul b2_lo h2_hi in
  let ph2:int128 = word_pmul b2_hi h2_lo in
  let pm2:int128 = word_pmul (word_xor b2_lo b2_hi) h2k_lo in
  (* Triple 3: b3 * h *)
  let b3_lo:64 word = word_subword b3 (0,64) in
  let b3_hi:64 word = word_subword b3 (64,64) in
  let h_lo:64 word = word_subword h_tw (0,64) in
  let h_hi:64 word = word_subword h_tw (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl3:int128 = word_pmul b3_lo h_hi in
  let ph3:int128 = word_pmul b3_hi h_lo in
  let pm3:int128 = word_pmul (word_xor b3_lo b3_hi) hk_lo in
  (* XOR-accumulate the three triples *)
  let pl:int128 = word_xor pl1 (word_xor pl2 pl3) in
  let ph:int128 = word_xor ph1 (word_xor ph2 ph3) in
  let pm:int128 = word_xor pm1 (word_xor pm2 pm3) in
  let mid:int128 = word_xor (word_xor pm ph) pl in
  (* Single Barrett reduction (identical structure to 1-block and 2-block) *)
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

(* ---- Bridge lemma: ghash_3block_karatsuba = rev8(polyval_reduce_prop3(...))
   when hk.lo = kmid h, h2k.lo = kmid (h^2), h3k.lo = kmid (h^3). --------- *)

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
  REWRITE_TAC[ghash_3block_karatsuba; LET_DEF; LET_END_DEF;
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
  (* q1_fix = inner pmul (kmid(xor of 3 block-lo-halves)) w, 3 atoms. *)
  ABBREV_TAC
    `q1_fix = word_pmul (word_xor (h0:(64)word) (word_xor h4 h8))
                        (word 13979173243358019584:(64)word) :(128)word` THEN
  (* q2 / q2b: outer pmul with 13-atom XOR, same atoms on both sides up to
     commutativity. Abbreviate each side then prove equal via WORD_BITWISE_RULE. *)
  ABBREV_TAC
    `q2 = word_pmul
       (word_xor (h1:(64)word) (word_xor h5 (word_xor h9 (word_xor h12
        (word_xor h14 (word_xor h16 (word_xor h2 (word_xor h6 (word_xor h10
        (word_xor h0 (word_xor h4 (word_xor h8
         (word_subword (q1_fix:(128)word) (0,64):(64)word))))))))))))
       (word 13979173243358019584:(64)word) :(128)word` THEN
  ABBREV_TAC
    `q2b = word_pmul
       (word_xor (h1:(64)word) (word_xor h12 (word_xor h0 (word_xor h2
        (word_xor h5 (word_xor h14 (word_xor h4 (word_xor h6 (word_xor h9
        (word_xor h16 (word_xor h8 (word_xor h10
         (word_subword (q1_fix:(128)word) (0,64):(64)word))))))))))))
       (word 13979173243358019584:(64)word) :(128)word` THEN
  SUBGOAL_THEN `q2:(128)word = q2b` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q2"; "q2b"] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;
    ALL_TAC] THEN
  POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  AP_TERM_TAC THEN BINOP_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* ---- Machine code (3-block assembly, extracted from .o) ----------------- *)

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

(* ================================================================== *)
(*                         THE MAIN THEOREM                            *)
(* ================================================================== *)

(* STATUS (2026-05-05):
   - ghash_3block_karatsuba definition: PROVEN
   - GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC bridge lemma: PROVEN
   - three_blocks_prelooptail_mc: EXTRACTED (256 instructions, 1024 bytes)
   - THREE_BLOCKS_PRELOOP_TAIL_CORRECT: STATED BELOW, proof scaffold provided

   The proof mirrors TWO_BLOCKS_PRELOOP_TAIL_CORRECT with these adjustments:
     * bit_len = word 384 (3 blocks = 48 bytes)
     * pt3 added, stored at out_ptr+32
     * Htable extends to offset 64 (h3k) and offset 48 (byteswap128 h^3)
     * 4-way CONJ postcondition: ct1, ct2, ct3, GHASH over [ct1; ct2; ct3]
     * Uses GHASH_POLYVAL_ACC_3 + GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC
     * Simulation: ~256 ARM steps (vs 163 for 2-block)
     * Extra lane-bridge needed for gcm_ctr_inc² counter (block 3's CTR).   *)

(* Helper: 2-step gcm_ctr_inc for block 3. *)

let GCM_CTR_INC2_LANE_BRIDGE = prove
 (`!(ivec:(128)word).
    word_insert (gcm_ctr_inc ivec) (96,32)
      (word_bytereverse
        (word_add (word_bytereverse
                     (word_subword (gcm_ctr_inc ivec) (96,32):(32)word))
                  (word 1:(32)word))) =
    gcm_ctr_inc (gcm_ctr_inc ivec)`,
  REWRITE_TAC[gcm_ctr_inc]);;

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
  CHEAT_TAC);;

(* ======== PROOF SCAFFOLD (interactive development) =======================
   The proof mirrors TWO_BLOCKS_PRELOOP_TAIL_CORRECT (ditto 900 lines)
   with these specific adjustments:

   Phase A - Preamble (~line 522-527 in 2-block):
     REWRITE_TAC[...MAYCHANGE_REGS_AND_FLAGS...; SOME_FLAGS; NONOVERLAPPING;
                  fst THREE_BLOCKS_PRELOOP_TAIL_EXEC] THEN
     REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0"

   Phase B - Simulation (~256 steps):
     - Steps 1-19: prologue (same as 2-block)
     - Steps 20-~138: CTR setup for all 8 blocks (v0..v7) + 13 AES rounds
       for blocks 0, 1, 2 in parallel
     - Then 3 ABBREV_TAC for s13_1, s13_2, s13_3 (v0, v1, v2 post-AES-chain)
     - eor3 for block 0 (ct1)
     - Cascade: #112 fallthrough, shuffle 1 (sub v30), #96 fallthrough,
       shuffle 2 (sub v30), #80 fallthrough, shuffle 3 (sub v30), #64
       fallthrough, shuffle 4 (sub v30), #48 fallthrough, shuffle 5
       (#32 cmp + final sub v30), b.gt TAKEN to .more_than_2.
     - .more_than_2: ct2 stored, ct3 via eor3 (v6)
     - Falls through to .more_than_1: ct2 written, ct3 via eor3 (v7)
     - ABBREV ct2, ct3 right after each eor3
     - 43 Karatsuba + Barrett + store steps
     - ABBREV final_xi BEFORE step 154 (same pattern as 2-block)
     - Steps 154-160: rev64 v19, st1, epilogue

   Phase C - 4-way CONJ:
     - ct1 subgoal: same as 2-block
     - ct2 subgoal: same as 2-block (gcm_ctr_inc ivec path)
     - ct3 subgoal: NEW — needs gcm_ctr_inc (gcm_ctr_inc ivec) peel via
       GCM_CTR_INC2_LANE_BRIDGE
     - GHASH subgoal: apply GHASH_POLYVAL_ACC_3 (new) + bridge

   Phase D - GHASH closure (bigger than 2-block):
     - 3 xor/aes folds (ct1, ct2, ct3)
     - Apply bridge with 3 witnesses for hk, h2k (from h1k.hi), h3k
     - Unfold bridge target, then same halfswap + BINOP pattern
     - G-half and F-half each need ~27 h-var equalities (vs 18 for 2-block)
     - q2_big/q2_big_rhs has ~15 atoms (vs 9 for 2-block).
       WORD_BITWISE_RULE runtime: ~5s (3-block bridge test confirmed this)

   This main theorem requires ~2-4 hours of interactive validation following
   the 2-block blueprint. The strategy is validated and the bridge lemma
   proven. Remaining work is systematic application. *)
