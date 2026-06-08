(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* aes256_gcm_five_block.ml                                                *)
(*                                                                         *)
(* The 5-block AES-256-GCM separate-blocks encrypt proof — the N=5         *)
(* instance of the generic N-block framework. STRUCTURALLY MIRRORS         *)
(* aes256_gcm_four_block.ml, scaled up to N=5.                             *)
(*                                                                         *)
(* PER-N CONTENT (only piece in this file):                                *)
(*   - Machine code blob (aes256_gcm_five_block_mc) and EXEC               *)
(*   - ghash_5block_karatsuba (assembly-shape spec)                        *)
(*   - GHASH_5BLOCK_AS_NBLOCK (compatibility with ghash_Nblock_karatsuba)  *)
(*   - GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC — derived from inductive bridge *)
(*   - GCM_5BLOCK_GHASH_STEP_TAC + main theorem FIVE_BLOCKS_PRELOOP_TAIL_CORRECT *)
(* ========================================================================= *)

(* All dependencies (base/AES/ghash_spec/aesgcm helpers) are pulled in       *)
(* transitively by the N-block framework file below.                          *)
needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;

(* ========================================================================= *)
(*  PER-N: 5-block assembly-shape spec ghash_5block_karatsuba.               *)
(* ========================================================================= *)

let ghash_5block_karatsuba = new_definition
 `ghash_5block_karatsuba (b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128)
                         (h_tw:int128)  (hk:int128)
                         (h2_tw:int128) (h2k:int128)
                         (h3_tw:int128) (h3k:int128)
                         (h4_tw:int128) (h4k:int128)
                         (h5_tw:int128) (h5k:int128) : int128 =
  let b1_lo:64 word = word_subword b1 (0,64) in
  let b1_hi:64 word = word_subword b1 (64,64) in
  let h5_lo:64 word = word_subword h5_tw (0,64) in
  let h5_hi:64 word = word_subword h5_tw (64,64) in
  let h5k_lo:64 word = word_subword h5k (0,64) in
  let pl1:int128 = word_pmul b1_lo h5_hi in
  let ph1:int128 = word_pmul b1_hi h5_lo in
  let pm1:int128 = word_pmul (word_xor b1_lo b1_hi) h5k_lo in
  let b2_lo:64 word = word_subword b2 (0,64) in
  let b2_hi:64 word = word_subword b2 (64,64) in
  let h4_lo:64 word = word_subword h4_tw (0,64) in
  let h4_hi:64 word = word_subword h4_tw (64,64) in
  let h4k_lo:64 word = word_subword h4k (0,64) in
  let pl2:int128 = word_pmul b2_lo h4_hi in
  let ph2:int128 = word_pmul b2_hi h4_lo in
  let pm2:int128 = word_pmul (word_xor b2_lo b2_hi) h4k_lo in
  let b3_lo:64 word = word_subword b3 (0,64) in
  let b3_hi:64 word = word_subword b3 (64,64) in
  let h3_lo:64 word = word_subword h3_tw (0,64) in
  let h3_hi:64 word = word_subword h3_tw (64,64) in
  let h3k_lo:64 word = word_subword h3k (0,64) in
  let pl3:int128 = word_pmul b3_lo h3_hi in
  let ph3:int128 = word_pmul b3_hi h3_lo in
  let pm3:int128 = word_pmul (word_xor b3_lo b3_hi) h3k_lo in
  let b4_lo:64 word = word_subword b4 (0,64) in
  let b4_hi:64 word = word_subword b4 (64,64) in
  let h2_lo:64 word = word_subword h2_tw (0,64) in
  let h2_hi:64 word = word_subword h2_tw (64,64) in
  let h2k_lo:64 word = word_subword h2k (0,64) in
  let pl4:int128 = word_pmul b4_lo h2_hi in
  let ph4:int128 = word_pmul b4_hi h2_lo in
  let pm4:int128 = word_pmul (word_xor b4_lo b4_hi) h2k_lo in
  let b5_lo:64 word = word_subword b5 (0,64) in
  let b5_hi:64 word = word_subword b5 (64,64) in
  let h_lo:64 word = word_subword h_tw (0,64) in
  let h_hi:64 word = word_subword h_tw (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl5:int128 = word_pmul b5_lo h_hi in
  let ph5:int128 = word_pmul b5_hi h_lo in
  let pm5:int128 = word_pmul (word_xor b5_lo b5_hi) hk_lo in
  let pl:int128 = word_xor pl1 (word_xor pl2 (word_xor pl3 (word_xor pl4 pl5))) in
  let ph:int128 = word_xor ph1 (word_xor ph2 (word_xor ph3 (word_xor ph4 ph5))) in
  let pm:int128 = word_xor pm1 (word_xor pm2 (word_xor pm3 (word_xor pm4 pm5))) in
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

let GHASH_5BLOCK_AS_NBLOCK = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128)
    (h_tw:int128)  (hk:int128)
    (h2_tw:int128) (h2k:int128)
    (h3_tw:int128) (h3k:int128)
    (h4_tw:int128) (h4k:int128)
    (h5_tw:int128) (h5k:int128).
    ghash_Nblock_karatsuba [(b1, h5_tw, h5k); (b2, h4_tw, h4k);
                            (b3, h3_tw, h3k); (b4, h2_tw, h2k);
                            (b5, h_tw, hk)] =
    ghash_5block_karatsuba b1 b2 b3 b4 b5 h_tw hk h2_tw h2k h3_tw h3k h4_tw h4k h5_tw h5k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_Nblock_karatsuba; ghash_5block_karatsuba;
              kara_acc; karatsuba_block_pl; karatsuba_block_ph;
              karatsuba_block_pm; karatsuba_reduce_shared;
              LET_DEF; LET_END_DEF; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC]);;

(* ========================================================================= *)
(* PER-N BRIDGE: ghash_5block_karatsuba ↔ polyval_reduce_prop3                *)
(* DERIVED from GHASH_NBLOCK_KARATSUBA_EQ_PROP3 (the inductive bridge)        *)
(* ========================================================================= *)

let GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128) (h:int128)
     (hk:int128) (h2k:int128) (h3k:int128) (h4k:int128) (h5k:int128).
    word_subword hk  (0,64):(64)word = karatsuba_mid h /\
    word_subword h2k (0,64):(64)word = karatsuba_mid (polyval_dot h h) /\
    word_subword h3k (0,64):(64)word =
      karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
    word_subword h4k (0,64):(64)word =
      karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
    word_subword h5k (0,64):(64)word =
      karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h)
    ==> ghash_5block_karatsuba b1 b2 b3 b4 b5
          (byteswap128 h) hk
          (byteswap128 (polyval_dot h h)) h2k
          (byteswap128 (polyval_dot h (polyval_dot h h))) h3k
          (byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h))) h4k
          (byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h)) h5k =
        word_reversefields 8
          (polyval_reduce_prop3
            (word_xor
              (word_pmul b1 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h)
                : 256 word)
             (word_xor
              (word_pmul b2 (polyval_dot (polyval_dot h h) (polyval_dot h h)) : 256 word)
              (word_xor
                (word_pmul b3 (polyval_dot h (polyval_dot h h)) : 256 word)
                (word_xor
                  (word_pmul b4 (polyval_dot h h) : 256 word)
                  (word_pmul b5 h : 256 word))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM GHASH_5BLOCK_AS_NBLOCK] THEN
  SUBGOAL_THEN
    `[(b1:int128, byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):int128, h5k:int128);
      (b2:int128, byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)):int128, h4k:int128);
      (b3:int128, byteswap128 (polyval_dot h (polyval_dot h h)):int128, h3k:int128);
      (b4:int128, byteswap128 (polyval_dot h h):int128, h2k:int128);
      (b5:int128, byteswap128 h:int128, hk:int128)] =
     project_triples
       [(b1, byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h),
           h5k, polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h);
        (b2, byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)),
           h4k, polyval_dot (polyval_dot h h) (polyval_dot h h));
        (b3, byteswap128 (polyval_dot h (polyval_dot h h)), h3k, polyval_dot h (polyval_dot h h));
        (b4, byteswap128 (polyval_dot h h), h2k, polyval_dot h h);
        (b5, byteswap128 h, hk, h)]`
    SUBST1_TAC THENL [REWRITE_TAC[project_triples]; ALL_TAC] THEN
  MP_TAC(SPEC
    `[(b1:int128, byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):int128,
         h5k:int128, polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h:int128);
      (b2:int128, byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)):int128,
         h4k:int128, polyval_dot (polyval_dot h h) (polyval_dot h h):int128);
      (b3:int128, byteswap128 (polyval_dot h (polyval_dot h h)):int128, h3k:int128, polyval_dot h (polyval_dot h h):int128);
      (b4:int128, byteswap128 (polyval_dot h h):int128, h2k:int128, polyval_dot h h:int128);
      (b5:int128, byteswap128 h:int128, hk:int128, h:int128)]
    :(int128#int128#int128#int128)list`
    GHASH_NBLOCK_KARATSUBA_EQ_PROP3) THEN
  ASM_REWRITE_TAC[kara_quad_ok; kara_quad_pmul; WORD_XOR_0_LEFT] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* GHASH_POLYVAL_ACC_5 (5-block specialization of GHASH_POLYVAL_ACC_BATCHED)
   is defined in arm/proofs/utils/gcm_aesgcm_helpers.ml (ACC_2..4 are in
   common/ghash_spec.ml; ACC_5/6/7 are derived in the helpers file). *)

(* ========================================================================= *)
(* POLYVAL_DOT_H5_EQ: left-associated h^5 = symmetric h^5.                    *)
(* Bridges GHASH_POLYVAL_ACC_5 output to the bridge lemma's symmetric form.   *)
(* Derived from POLYVAL_DOT_H4_EQ via congruence rewrite.                     *)
(* ========================================================================= *)

(* First prove H4_EQ as a sub-lemma; H5_EQ derives from it via congruence. *)
(* ========================================================================= *)

(* ========================================================================= *)
(*  PER-N: MACHINE CODE                                                      *)
(* ========================================================================= *)

let aes256_gcm_five_block_mc = define_assert_from_elf
  "aes256_gcm_five_block_mc"
  "arm/aes-gcm/aes256_gcm_five_block.o"
[
  0x6dbb27e8;       (* arm_STP D8 D9 SP (Preimmediate_Offset (iword (-- &80))) *)
  0xd343fc29;       (* arm_LSR X9 X1 3 *)
  0xaa0403f0;       (* arm_MOV X16 X4 *)
  0xaa0503eb;       (* arm_MOV X11 X5 *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0xd2f84005;       (* arm_MOVZ X5 (word 49664) 48 *)
  0xa9047fe5;       (* arm_STP X5 XZR SP (Immediate_Offset (iword (&64))) *)
  0x910103ea;       (* arm_ADD X10 SP (rvalue (word 64)) *)
  0x4c407200;       (* arm_LDR Q0 X16 No_Offset *)
  0xaa0903e5;       (* arm_MOV X5 X9 *)
  0xd2c0002f;       (* arm_MOVZ X15 (word 1) 32 *)
  0x4f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x4e181dff;       (* arm_INS_GEN Q31 X15 64 64 *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0x9279e0a5;       (* arm_AND X5 X5 (rvalue (word 18446744073709551488)) *)
  0x8b0000a5;       (* arm_ADD X5 X5 X0 *)
  0x6e20081e;       (* arm_REV32_VEC Q30 Q0 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 128 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0xce02714a;       (* arm_EOR3 Q10 Q10 Q2 Q28 *)
  0xce04718c;       (* arm_EOR3 Q12 Q12 Q4 Q28 *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0xad4354d4;       (* arm_LDP Q20 Q21 X6 (Immediate_Offset (iword (&96))) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea21c43;       (* arm_MOV_VEC Q3 Q2 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea11c22;       (* arm_MOV_VEC Q2 Q1 128 *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0xf10180bf;       (* arm_CMP X5 (rvalue (word 96)) *)
  0x5400042c;       (* arm_BGT (word 132) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x5400032c;       (* arm_BGT (word 100) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x5400024c;       (* arm_BGT (word 72) *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x5400034c;       (* arm_BGT (word 104) *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x540004ac;       (* arm_BGT (word 148) *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x5400062c;       (* arm_BGT (word 196) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x14000040;       (* arm_B (word 256) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2 Q28 Q8 Q20 64 *)
  0xce047529;       (* arm_EOR3 Q9 Q9 Q4 Q29 *)
  0x0ef4e11a;       (* arm_PMULL Q26 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0ef5e37b;       (* arm_PMULL Q27 Q27 Q21 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef9e11c;       (* arm_PMULL2 Q28 Q8 Q25 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef8e37b;       (* arm_PMULL2 Q27 Q27 Q24 64 *)
  0x0ef9e11a;       (* arm_PMULL Q26 Q8 Q25 64 *)
  0xce057529;       (* arm_EOR3 Q9 Q9 Q5 Q29 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x4ef7e11c;       (* arm_PMULL2 Q28 Q8 Q23 64 *)
  0xce067529;       (* arm_EOR3 Q9 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef8e37b;       (* arm_PMULL Q27 Q27 Q24 64 *)
  0x0ef7e11a;       (* arm_PMULL Q26 Q8 Q23 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef6e11c;       (* arm_PMULL2 Q28 Q8 Q22 64 *)
  0xce077529;       (* arm_EOR3 Q9 Q9 Q7 Q29 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef6e11a;       (* arm_PMULL Q26 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x4ef5e37b;       (* arm_PMULL2 Q27 Q27 Q21 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x92401821;       (* arm_AND X1 X1 (rvalue (word 127)) *)
  0xd1020021;       (* arm_SUB X1 X1 (rvalue (word 128)) *)
  0xcb0103e1;       (* arm_NEG X1 X1 *)
  0xaa3f03e7;       (* arm_MVN X7 XZR *)
  0x92401821;       (* arm_AND X1 X1 (rvalue (word 127)) *)
  0x9ac124e7;       (* arm_LSRV X7 X7 X1 *)
  0xf101003f;       (* arm_CMP X1 (rvalue (word 64)) *)
  0xaa3f03e8;       (* arm_MVN X8 XZR *)
  0x9a9fb0ee;       (* arm_CSEL X14 X7 XZR Condition_LT *)
  0x9a87b10d;       (* arm_CSEL X13 X8 X7 Condition_LT *)
  0x4e081da0;       (* arm_INS_GEN Q0 X13 0 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4c40705a;       (* arm_LDR Q26 X2 No_Offset *)
  0x4e181dc0;       (* arm_INS_GEN Q0 X14 64 64 *)
  0x4e201d29;       (* arm_AND_VEC Q9 Q9 Q0 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 128 *)
  0x6ee01f49;       (* arm_BIF Q9 Q26 Q0 128 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2 Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL Q16 Q16 Q21 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x0ef0e23d;       (* arm_PMULL Q29 Q17 Q16 64 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x0ef0e251;       (* arm_PMULL Q17 Q18 Q16 64 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0xce115673;       (* arm_EOR3 Q19 Q19 Q17 Q21 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x6cc527e8;       (* arm_LDP D8 D9 SP (Postimmediate_Offset (iword (&80))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let FIVE_BLOCKS_PRELOOP_TAIL_EXEC =
  ARM_MK_EXEC_RULE aes256_gcm_five_block_mc;;

(* ========================================================================= *)
(* PER-BLOCK CIPHERTEXT CLOSURES                                              *)
(* Each block k closes via the shared GCM_NBLOCK_CT_STEP_TAC N k, which       *)
(* handles ivec_k = gcm_ctr_inc^{k-1} ivec for any k.                         *)
(* ========================================================================= *)

let GCM_CT1_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 5 1;;
let GCM_CT2_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 5 2;;

(* CT3 for ivec_3 = gcm_ctr_inc² ivec — needs the second counter unfolding.
   Uses INSERT_IDEM/INSERT_SUBWORD to sidestep the polymorphic-type issue. *)
let GCM_CT3_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 5 3;;

let GCM_CT4_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 5 4;;

let GCM_CT5_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 5 5;;

(* ========================================================================= *)
(* BUBBLE-SORT CONVERSION FOR XOR CANONICAL FORM                              *)
(*                                                                           *)
(* WORD_BITWISE_RULE blows up exponentially on 21-atom XOR-AC equalities;    *)
(* we use string-lexicographic bubble sort via pairwise commutativity.        *)
(* ========================================================================= *)

(* ========================================================================= *)
(*  GHASH STEP TACTIC (N=5 instance)                                          *)
(*                                                                           *)
(* Same cNlo/wKmd/qS/qB/bubble_sort template as the 4/6/7-block files,        *)
(* scaled to N=5: 22 atomic ABBREVs (5 ct + xi + 5 H powers), 15 inner pmul   *)
(* ABBREVs (3 per block), 30 z-vars, and the qS/qB Barrett pmuls, closed by   *)
(* bubble_sort_conv (XOR-AC canonicalisation).                                *)
(* ========================================================================= *)

let GCM_5BLOCK_GHASH_STEP_TAC =
  REWRITE_TAC[GHASH_POLYVAL_ACC_5; POLYVAL_DOT_H5_EQ;
              GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  (* Fold xi+pt1+aes = xi+ct1 *)
  SUBGOAL_THEN
    `word_xor xi (word_xor pt1
       (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                         rk8 rk9 rk10 rk11 rk12 rk13 rk14)) =
     word_xor xi ct1:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ct1" THEN EXPAND_TAC "s13_1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    ASM_REWRITE_TAC[]; ALL_TAC ] THEN
  (* Fold pt2+aes = ct2 *)
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
  (* Fold pt3+aes(ctr^2) = ct3 *)
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
  (* Fold pt4+aes(ctr^3) = ct4 *)
  SUBGOAL_THEN
    `word_xor pt4
       (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))
                         rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11
                         rk12 rk13 rk14) = ct4:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `ct4:(128)word` &&
         aconv (lhs(concl th)) `word_xor pt4 (word_xor s13_4 rk14):(128)word`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `s13_4:(128)word` &&
         not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT] THEN
    REWRITE_TAC[gcm_ctr_inc] THEN
    ABBREV_TAC `ctr4g:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
    ABBREV_TAC `br4g:(32)word = word_bytereverse (ctr4g:(32)word)` THEN
    ABBREV_TAC `step1_4g:(32)word = word_bytereverse (word_add (br4g:(32)word) (word 1:(32)word))` THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "step1_4g" THEN
    REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
    CONV_TAC WORD_RULE; ALL_TAC ] THEN
  (* Fold pt5+aes(ctr^4) = ct5 *)
  SUBGOAL_THEN
    `word_xor pt5
       (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))
                         rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11
                         rk12 rk13 rk14) = ct5:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `ct5:(128)word` &&
         aconv (lhs(concl th)) `word_xor pt5 (word_xor s13_5 rk14):(128)word`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `s13_5:(128)word` &&
         not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT] THEN
    REWRITE_TAC[gcm_ctr_inc] THEN
    ABBREV_TAC `ctr5g:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
    ABBREV_TAC `br5g:(32)word = word_bytereverse (ctr5g:(32)word)` THEN
    ABBREV_TAC `step1_5g:(32)word = word_bytereverse (word_add (br5g:(32)word) (word 1:(32)word))` THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "step1_5g" THEN
    REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
    CONV_TAC WORD_RULE; ALL_TAC ] THEN
  (* Normalize h^4 then h^3 left-assoc -> symmetric (to match the 5-block bridge). *)
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h =
     polyval_dot (polyval_dot h h) (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[POLYVAL_DOT_H4_EQ_LOCAL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  (* Apply 5-block bridge. *)
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`; `word_reversefields 8 ct3:int128`;
     `word_reversefields 8 ct4:int128`; `word_reversefields 8 ct5:int128`;
     `h:int128`; `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word`;
     `h5k:int128`]
    GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
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
  REWRITE_TAC[ghash_5block_karatsuba; LET_DEF; LET_END_DEF] THEN
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
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* 22 atomic ABBREVs *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c4lo:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c4hi:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c5lo:(64)word) = word_subword (word_reversefields 8 (ct5:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c5hi:(64)word) = word_subword (word_reversefields 8 (ct5:(128)word)) (64,64)` THEN
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
  ABBREV_TAC `(hh0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hh1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* 15 inner pmul ABBREVs *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hh0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hh1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hh0:(64)word) (hh1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hg0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hg1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (hf0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (hf1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w4lo:(128)word) = word_pmul (c4lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w4hi:(128)word) = word_pmul (c4hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w4md:(128)word) = word_pmul (word_xor (c4hi:(64)word) (c4lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w5lo:(128)word) = word_pmul (c5lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w5hi:(128)word) = word_pmul (c5hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w5md:(128)word) = word_pmul (word_xor (c5hi:(64)word) (c5lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hh0:(64)word) (hh1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 30 z-vars *)
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
  ABBREV_TAC `(w5lo_l:(64)word) = word_subword (w5lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5lo_h:(64)word) = word_subword (w5lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5hi_l:(64)word) = word_subword (w5hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5hi_h:(64)word) = word_subword (w5hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5md_l:(64)word) = word_subword (w5md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5md_h:(64)word) = word_subword (w5md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Normalize LHS mid-pmuls to the abbreviated w?md (swapped xor arg order). *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c4lo:(64)word) (c4hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w4md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w4md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c5lo:(64)word) (c5hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w5md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w5md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hh0:(64)word) (hh1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul; fold both XOR orderings. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w5lo_l:(64)word) (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l w1lo_l)))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l w5lo_l)))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold the LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w5md_l:(64)word) (word_xor w4md_l (word_xor w3md_l (word_xor w2md_l (word_xor w1md_l (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w5hi_l (word_xor w4hi_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w5lo_h (word_xor w4lo_h (word_xor w3lo_h (word_xor w2lo_h (w1lo_h))))))))))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w4lo_h (word_xor w5lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w4md_l (word_xor w5md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w4hi_l (word_xor w5hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l ((word_subword (qS:(128)word) (0,64))))))))))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC] THEN
  (* Final: both word_join halves are XOR-AC equal. *)
  BINOP_TAC THENL
   [CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;
    CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC];;

(* ========================================================================= *)
(*                         THE PROOF                                         *)
(*                                                                           *)
(* INTERACTIVELY VERIFIED THROUGH STEP 180 (PC = pc + 720):                   *)
(*  - Steps 1-19 (prologue): all preconditions converted to s0 hypotheses,    *)
(*    PC reaches word(pc + 76) after stp/ldp/movi prologue + ld1 ivec         *)
(*  - All h-power htable slots present: byteswap128(h^k) for k in {1,2,3,4,5} *)
(*  - All 5 plaintext blocks pt1..pt5 in memory                                *)
(*  - Steps 20-155: AES rounds for 5 blocks (reach round 11 + ldp loads)      *)
(*  - Steps 156-180: AES continues to round 13: Q0..Q4 = aese(...,rk13),      *)
(*    Q28 = rk14, ready for final aese xor with rk14                          *)
(*                                                                           *)
(* REMAINING (in commented body below): ~163 more simulation steps after     *)
(* step 180 (final aese xor with rk14, ABBREV_TAC s13_1..s13_5, post-AES     *)
(* normalize, tail dispatch into more_than_4 cascade, store ct1..ct5,        *)
(* GHASH karatsuba reduce, store final xi), then GHASH STEP TAC scaling      *)
(* to N=5 atom counts. This work is intractable in single-session work.      *)
(* ========================================================================= *)
(*  PARTIAL-FINAL-BLOCK GHASH CLOSER (masked ct5) + cascade/mask helpers.     *)
(* ========================================================================= *)

let GCM_5BLOCK_GHASH_STEP_MASKED_TAC =
  REWRITE_TAC[GHASH_POLYVAL_ACC_5; POLYVAL_DOT_H5_EQ;
              GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  (* Fold xi+pt1+aes = xi+ct1 *)
  SUBGOAL_THEN
    `word_xor xi (word_xor pt1
       (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                         rk8 rk9 rk10 rk11 rk12 rk13 rk14)) =
     word_xor xi ct1:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ct1" THEN EXPAND_TAC "s13_1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    ASM_REWRITE_TAC[]; ALL_TAC ] THEN
  (* Fold pt2+aes = ct2 *)
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
  (* Fold pt3+aes(ctr^2) = ct3 *)
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
  (* Fold pt4+aes(ctr^3) = ct4 *)
  SUBGOAL_THEN
    `word_xor pt4
       (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))
                         rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11
                         rk12 rk13 rk14) = ct4:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `ct4:(128)word` &&
         aconv (lhs(concl th)) `word_xor pt4 (word_xor s13_4 rk14):(128)word`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `s13_4:(128)word` &&
         not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT] THEN
    REWRITE_TAC[gcm_ctr_inc] THEN
    ABBREV_TAC `ctr4g:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
    ABBREV_TAC `br4g:(32)word = word_bytereverse (ctr4g:(32)word)` THEN
    ABBREV_TAC `step1_4g:(32)word = word_bytereverse (word_add (br4g:(32)word) (word 1:(32)word))` THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "step1_4g" THEN
    REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
    CONV_TAC WORD_RULE; ALL_TAC ] THEN
  (* Fold pt5+aes(ctr^4) = ct5 *)
  SUBGOAL_THEN
    `word_xor pt5
       (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))
                         rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11
                         rk12 rk13 rk14) = ct5:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `ct5:(128)word` &&
         aconv (lhs(concl th)) `word_xor pt5 (word_xor s13_5 rk14):(128)word`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `s13_5:(128)word` &&
         not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT] THEN
    REWRITE_TAC[gcm_ctr_inc] THEN
    ABBREV_TAC `ctr5g:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
    ABBREV_TAC `br5g:(32)word = word_bytereverse (ctr5g:(32)word)` THEN
    ABBREV_TAC `step1_5g:(32)word = word_bytereverse (word_add (br5g:(32)word) (word 1:(32)word))` THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "step1_5g" THEN
    REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
    CONV_TAC WORD_RULE; ALL_TAC ] THEN
  (* Partial last block: abbreviate the mask and the masked block ctm5, and
     bridge the simulator's word_and mask ct5 to ctm5 = word_and ct5 mask. *)
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm5 = word_and (ct5:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct5:(128)word) = ctm5`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm5" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  (* Normalize h^4 then h^3 left-assoc -> symmetric (to match the 5-block bridge). *)
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h =
     polyval_dot (polyval_dot h h) (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[POLYVAL_DOT_H4_EQ_LOCAL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  (* Apply 5-block bridge. *)
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`; `word_reversefields 8 ct3:int128`;
     `word_reversefields 8 ct4:int128`; `word_reversefields 8 ctm5:int128`;
     `h:int128`; `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word`;
     `h5k:int128`]
    GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
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
  REWRITE_TAC[ghash_5block_karatsuba; LET_DEF; LET_END_DEF] THEN
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
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* 22 atomic ABBREVs *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c4lo:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c4hi:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c5lo:(64)word) = word_subword (word_reversefields 8 (ctm5:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c5hi:(64)word) = word_subword (word_reversefields 8 (ctm5:(128)word)) (64,64)` THEN
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
  ABBREV_TAC `(hh0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hh1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* 15 inner pmul ABBREVs *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hh0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hh1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hh0:(64)word) (hh1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hg0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hg1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (hf0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (hf1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w4lo:(128)word) = word_pmul (c4lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w4hi:(128)word) = word_pmul (c4hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w4md:(128)word) = word_pmul (word_xor (c4hi:(64)word) (c4lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w5lo:(128)word) = word_pmul (c5lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w5hi:(128)word) = word_pmul (c5hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w5md:(128)word) = word_pmul (word_xor (c5hi:(64)word) (c5lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hh0:(64)word) (hh1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 30 z-vars *)
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
  ABBREV_TAC `(w5lo_l:(64)word) = word_subword (w5lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5lo_h:(64)word) = word_subword (w5lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5hi_l:(64)word) = word_subword (w5hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5hi_h:(64)word) = word_subword (w5hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5md_l:(64)word) = word_subword (w5md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5md_h:(64)word) = word_subword (w5md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Normalize LHS mid-pmuls to the abbreviated w?md (swapped xor arg order). *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c4lo:(64)word) (c4hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w4md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w4md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c5lo:(64)word) (c5hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w5md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w5md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hh0:(64)word) (hh1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul; fold both XOR orderings. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w5lo_l:(64)word) (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l w1lo_l)))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l w5lo_l)))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold the LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w5md_l:(64)word) (word_xor w4md_l (word_xor w3md_l (word_xor w2md_l (word_xor w1md_l (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w5hi_l (word_xor w4hi_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w5lo_h (word_xor w4lo_h (word_xor w3lo_h (word_xor w2lo_h (w1lo_h))))))))))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w4lo_h (word_xor w5lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w4md_l (word_xor w5md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w4hi_l (word_xor w5hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l ((word_subword (qS:(128)word) (0,64))))))))))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC] THEN
  (* Final: both word_join halves are XOR-AC equal. *)
  BINOP_TAC THENL
   [CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;
    CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC];;

let FIVEBLOCK_USHR = prove
 (`!byte_len. byte_len <= 16 ==>
     word_ushr (word (512 + 8 * byte_len):int64) 3 = word (64 + byte_len)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `512 + 8 * byte_len = 8 * (64 + byte_len)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC);;

let FIVEBLOCK_MASK_REG = prove
 (`!byte_len (b0:int128). 1 <= byte_len /\ byte_len <= 16 ==>
    (word_insert
     ((word_insert (b0:int128)
        (0,64)
        (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
              ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
                ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
         then word 18446744073709551615:int64
         else word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)))):int128)
     (64,64)
     (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
           ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
             ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
        then word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127))
        else word 0:int64)
    : int128)
    = word (2 EXP (8 * byte_len) - 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NBLOCK_WORD_INSERT_BOTH_LANES] THEN
  SPEC_TAC(`byte_len:num`,`byte_len:num`) THEN GEN_TAC THEN
  NBLOCK_MASK_PEEL_TAC 1);;

(* ------------------------------------------------------------------------- *)
(* Tail-dispatch cascade branch resolution.  With a symbolic byte_len the     *)
(* total length is X5 = word_ushr (word (512 + 8*byte_len)) 3 = 64 + byte_len *)
(* (four leading full blocks + the partial last block).  Each cmp/b.gt in the *)
(* cascade (thresholds 96,80,64 (taken),48,32,16) leaves the PC as an          *)
(* if-then-else on the signed-greater-than condition; FIVEBLOCK_GT_COND        *)
(* collapses that to t < 64 + byte_len (TOTAL_LANES = 64), which the byte_len  *)
(* bounds then decide.                                                         *)
(* ------------------------------------------------------------------------- *)

let IVAL_WORD_SUB_SMALL = prove
 (`!a t. a < 2 EXP 63 /\ t < 2 EXP 63 ==>
     ival(word_sub (word a:int64) (word t)) = &a - &t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_sub; WORD_IWORD; GSYM IWORD_INT_SUB] THEN
  REWRITE_TAC[IVAL_IWORD_GALOIS] THEN
  REWRITE_TAC[DIMINDEX_64; IWORD_INT_SUB; WORD_IWORD; GSYM word_sub] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_INT_ARITH_TAC);;

let FIVEBLOCK_GT_COND = prove
 (`!byte_len t. byte_len <= 16 /\ t <= 96 ==>
    ((~(val (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word t)) = 0) /\
      (ival (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word t)) < &0 <=>
       ~(ival (word_ushr (word (512 + 8 * byte_len):int64) 3) - &t =
         ival (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word t)))))
     <=> t < 64 + byte_len)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FIVEBLOCK_USHR] THEN
  REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  ASM_SIMP_TAC[IVAL_WORD_SUB_SMALL; NBLOCK_IVAL_WORD_SMALL;
               ARITH_RULE `byte_len <= 16 ==> 64 + byte_len < 2 EXP 63`;
               ARITH_RULE `t <= 96 ==> t < 2 EXP 63`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LT] THEN
  ASM_INT_ARITH_TAC);;

let FIVEBLOCK_GT_COND_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 80 <= t /\ t <= 96 ==>
    ((~(val (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word t)) = 0) /\
      (ival (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word t)) < &0 <=>
       ~(ival (word_ushr (word (512 + 8 * byte_len):int64) 3) - &t =
         ival (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FIVEBLOCK_GT_COND; ARITH_RULE `80 <= t /\ t <= 96 ==> t <= 96`] THEN
  ASM_ARITH_TAC);;

let FIVEBLOCK_GT_COND_TRUE = prove
 (`!byte_len. 1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word 64)) = 0) /\
      (ival (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word 64)) < &0 <=>
       ~(ival (word_ushr (word (512 + 8 * byte_len):int64) 3) - &64 =
         ival (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word 64)))))
     <=> T)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FIVEBLOCK_GT_COND; ARITH_RULE `64 <= 96`] THEN
  ASM_ARITH_TAC);;

let FIVEBLOCK_CASC96 = prove
 (`!byte_len. byte_len <= 16 ==>
    ((~(val (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word 96)) = 0) /\
      (ival (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word 96)) < &0 <=>
       ~(ival (word_ushr (word (512 + 8 * byte_len):int64) 3) - &96 =
         ival (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word 96))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIVEBLOCK_GT_COND_FALSE THEN ASM_ARITH_TAC);;
let FIVEBLOCK_CASC80 = prove
 (`!byte_len. byte_len <= 16 ==>
    ((~(val (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word 80)) = 0) /\
      (ival (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word 80)) < &0 <=>
       ~(ival (word_ushr (word (512 + 8 * byte_len):int64) 3) - &80 =
         ival (word_sub (word_ushr (word (512 + 8 * byte_len):int64) 3) (word 80))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIVEBLOCK_GT_COND_FALSE THEN ASM_ARITH_TAC);;

(* Resolve any pending cascade if-then-else PC by rewriting every threshold's
   signed-gt condition to its truth value, then collapsing the conditional.
   Each instance matches only its own threshold, so applying all is safe. *)
let FIVEBLOCK_CASCADE_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE[
        MATCH_MP FIVEBLOCK_CASC96 bl16; MATCH_MP FIVEBLOCK_CASC80 bl16;
       
        MATCH_MP FIVEBLOCK_GT_COND_TRUE (CONJ bl1 bl16); COND_CLAUSES]) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;

(* ========================================================================= *)

let FIVE_BLOCKS_PRELOOP_TAIL_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (pt4:(128)word) (pt5:(128)word)
    (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,1400) (in_ptr:int64,80) /\
    nonoverlapping (word pc,1400) (out_ptr:int64,80) /\
    nonoverlapping (word pc,1400) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,1400) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,1400) (key_ptr:int64,240) /\
    nonoverlapping (word pc,1400) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,1400) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,80) (out_ptr,80) /\
    nonoverlapping (in_ptr,80) (xi_ptr,16) /\
    nonoverlapping (in_ptr,80) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,80) (xi_ptr,16) /\
    nonoverlapping (out_ptr,80) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,80) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,80) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,80) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,80) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,1400) /\
    nonoverlapping (xi_ptr,16) (word pc,1400) /\
    nonoverlapping (out_ptr,80) (word pc,1400)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_five_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (512 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add in_ptr (word 48))) s = pt4 /\
           read (memory :> bytes128 (word_add in_ptr (word 64))) s = pt5 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = out0 /\
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
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s =
             byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h))
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
           let ct5 =
             word_xor pt5
               (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))
                                 rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8
                                 rk9 rk10 rk11 rk12 rk13 rk14) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm5 = word_and ct5 mask in
           read PC s = word(pc + 1372) /\
           read X0 s = word (64 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = ct3 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = ct4 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s =
             word_or ctm5 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ct3;
                                     word_reversefields 8 ct4;
                                     word_reversefields 8 ctm5]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,80);
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
              fst FIVE_BLOCKS_PRELOOP_TAIL_EXEC] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN

  (* Prologue *)
  ARM_STEPS_TAC FIVE_BLOCKS_PRELOOP_TAIL_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* AES rounds for all 5 blocks + initial tail prep, steps 20-200 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FIVE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--200) THEN

  (* Abbreviate s13_1..s13_5 from Q0,Q1,Q3,Q4,Q5 (Q2 duplicates Q1 due to the
     cascade's mov v3,v2 register shuffle; counter-aware term_match picks them). *)
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q0 (s:armstate) = (x:int128)`) (concl th)
    then let r=rand(concl th) in ABBREV_TAC(mk_eq(mk_var("s13_1",type_of r),r)) else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q1 (s:armstate) = (x:int128)`) (concl th)
    then let r=rand(concl th) in ABBREV_TAC(mk_eq(mk_var("s13_2",type_of r),r)) else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q3 (s:armstate) = (x:int128)`) (concl th)
    then let r=rand(concl th) in ABBREV_TAC(mk_eq(mk_var("s13_3",type_of r),r)) else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q4 (s:armstate) = (x:int128)`) (concl th)
    then let r=rand(concl th) in ABBREV_TAC(mk_eq(mk_var("s13_4",type_of r),r)) else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q5 (s:armstate) = (x:int128)`) (concl th)
    then let r=rand(concl th) in ABBREV_TAC(mk_eq(mk_var("s13_5",type_of r),r)) else NO_TAC) THEN

  (* ct1 + post-AES normalize + tail dispatch normalize. After the dispatch
     normalize, restore 2 EXP 64 so the ciphertext stores' nonoverlapping checks
     succeed. *)
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN
  GCM_NBLOCK_POST_AES_NORMALIZE_TAC THEN
  GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Tail-dispatch cascade (more_than_4) + store ct1..ct5 + GHASH karatsuba
     accumulate.  With symbolic byte_len each b.gt leaves the PC as a
     conditional; resolve after every step (fall-throughs at 96/80 then the
     taken branch at 64).  Restore 2 EXP 64 after each step (the stores need it). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FIVE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN
    FIVEBLOCK_CASCADE_TAC) (201--240) THEN
  ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FIVE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`])) (241--260) THEN
  ABBREV_TAC `ct3 = word_xor (word_xor pt3 s13_3) rk14:(128)word` THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FIVE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`])) (261--270) THEN
  ABBREV_TAC `ct4 = word_xor (word_xor pt4 s13_4) rk14:(128)word` THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FIVE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`])) (271--282) THEN
  ABBREV_TAC `ct5 = word_xor (word_xor pt5 s13_5) rk14:(128)word` THEN

  (* Steps 283-295: finish building the partial-block mask register (Q0). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FIVE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`])) (283--295) THEN

  (* Collapse the data-dependent mask register Q0 to word (2^(8*byte_len) - 1)
     before the AND_VEC / bif. *)
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FIVEBLOCK_MASK_REG th])) THEN

  (* Steps 296-318: AND_VEC, bif (partial store fixup), GHASH karatsuba +
     Barrett reduction (up to the final EOR3 in Q19). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC FIVE_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`])) (296--318) THEN

  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN

  (* Abbreviate Q19 as `final_xi` BEFORE the EXT/REV64 byte-explosion. *)
  ABBREV_FINAL_XI_TAC THEN

  (* Epilogue (ext, rev64, str, mov, ldp x4): plain stepping, NO
     GCM_ENC_SIMPLIFY (it re-expands final_xi into a 100KB term, hanging the str).
     Stop at s326 (PC = pc+1372, just before the RET at pc+1372). *)
  ARM_STEPS_TAC FIVE_BLOCKS_PRELOOP_TAIL_EXEC (319--326) THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN
  (* Collapse the mask register that survives into the ct5 store goal, and
     reduce X0 = word(64+byte_len). *)
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FIVEBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[FIVEBLOCK_USHR] THEN

  (* After ASM_SIMP discharges the PC and X0 conjuncts the remaining goals are
     the ct1..ct4 stores, the masked ct5 store, and the GHASH over
     [ct1; ct2; ct3; ct4; ctm5]. *)
  REPEAT CONJ_TAC THENL [
    GCM_CT1_STEP_TAC;
    GCM_CT2_STEP_TAC;
    GCM_CT3_STEP_TAC;
    GCM_CT4_STEP_TAC;
    (* masked ct5 store: establish word_xor pt5 aes = ct5, fold it on the spec
       side and collapse the bif's double mask (NBLOCK_MASK_IDEM). *)
    SUBGOAL_THEN
      `word_xor pt5
         (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))
                           rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11
                           rk12 rk13 rk14) = ct5:(128)word`
      ASSUME_TAC THENL [
      FIRST_ASSUM(fun th ->
        if is_eq(concl th) && rand(concl th) = `ct5:(128)word` &&
           aconv (lhs(concl th)) `word_xor pt5 (word_xor s13_5 rk14):(128)word`
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      FIRST_ASSUM(fun th ->
        if is_eq(concl th) && rand(concl th) = `s13_5:(128)word` &&
           not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
      REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN;
                  LANE3_BYTES_JOIN_BE; CTR_WORD_INSERT] THEN
      REWRITE_TAC[gcm_ctr_inc] THEN
      ABBREV_TAC `ctr5g:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
      ABBREV_TAC `br5g:(32)word = word_bytereverse (ctr5g:(32)word)` THEN
      ABBREV_TAC `step1_5g:(32)word = word_bytereverse (word_add (br5g:(32)word) (word 1:(32)word))` THEN
      REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "step1_5g" THEN
      REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[NBLOCK_MASK_IDEM];
    GCM_5BLOCK_GHASH_STEP_MASKED_TAC
  ]);;




