(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* GCM-256 definitions per NIST SP 800-38D, using AES-256 cipher.            *)
(*                                                                           *)
(* Extends common/gcm.ml (AES-128) with AES-256 variants. Reuses inc32,      *)
(* gf128_mul, and ghash from gcm.ml since they are AES-independent.          *)
(* ========================================================================= *)

needs "common/gcm.ml";;

(* ========================================================================= *)
(* GCTR-256: Counter-mode encryption using AES-256 (Algorithm 3 variant).    *)
(* ========================================================================= *)

let gctr256 = define
  `gctr256 (ks:(128 word) list) (icb:128 word) ([] : (128 word) list) =
     ([] : (128 word) list) /\
   gctr256 ks icb (CONS x rest) =
     CONS (word_xor x (aes256_cipher icb ks)) (gctr256 ks (inc32 icb) rest)`;;

let GCTR256_STEP_CONV ks_def =
  ONCE_REWRITE_CONV [gctr256] THENC
  REWRITE_CONV [ks_def] THENC
  ONCE_DEPTH_CONV (FIPS197_ENCRYPT_FAST_CONV aes256_cipher ks_def) THENC
  DEPTH_CONV WORD_RED_CONV THENC
  ONCE_DEPTH_CONV (REWRITE_CONV [inc32] THENC
    TOP_DEPTH_CONV let_CONV THENC
    DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV));;

let rec GCTR256_CONV ks_def tm =
  try
    let th = GCTR256_STEP_CONV ks_def tm in
    let rhs = rand (concl th) in
    (try let th2 = RAND_CONV (GCTR256_CONV ks_def) rhs in TRANS th th2
     with _ -> th)
  with _ -> REWRITE_CONV [gctr256] tm;;

(* ========================================================================= *)
(* GCM-AE-256: Authenticated Encryption with AES-256 (Algorithm 4 variant).  *)
(*                                                                           *)
(* Constraints: 96-bit IV, full 128-bit blocks, pre-expanded key schedule.   *)
(* Returns (ciphertext blocks, 128-bit tag).                                 *)
(* ========================================================================= *)

let gcm256_ae = new_definition
 `gcm256_ae (ks:(128 word) list) (iv:96 word)
            (P:(128 word) list) (A:(128 word) list) =
  let H = aes256_cipher (word 0) ks in
  let J0 : 128 word = word_join iv (word 1 : 32 word) in
  let C = gctr256 ks (inc32 J0) P in
  let len_block : 128 word =
    word_join (word (128 * LENGTH A) : 64 word)
              (word (128 * LENGTH C) : 64 word) in
  let S = ghash H (word 0) (APPEND A (APPEND C [len_block])) in
  let tag = word_xor S (aes256_cipher J0 ks) in
  (C, tag)`;;

(* ========================================================================= *)
(* GCM-AD-256: Authenticated Decryption with AES-256 (Algorithm 5 variant).  *)
(*                                                                           *)
(* Returns SOME plaintext if tag verifies, NONE otherwise.                   *)
(* ========================================================================= *)

let gcm256_ad = new_definition
 `gcm256_ad (ks:(128 word) list) (iv:96 word)
            (C:(128 word) list) (A:(128 word) list) (tag:128 word) =
  let H = aes256_cipher (word 0) ks in
  let J0 : 128 word = word_join iv (word 1 : 32 word) in
  let P = gctr256 ks (inc32 J0) C in
  let len_block : 128 word =
    word_join (word (128 * LENGTH A) : 64 word)
              (word (128 * LENGTH C) : 64 word) in
  let S = ghash H (word 0) (APPEND A (APPEND C [len_block])) in
  let tag' = word_xor S (aes256_cipher J0 ks) in
  if tag' = tag then SOME P else NONE`;;

(* ========================================================================= *)
(* KATs: NIST SP 800-38D Test Case 13 (AES-256, 1-block P, empty A)          *)
(* Key: 0x0000...0 (32 bytes), IV: 0x0000...0 (12 bytes)                    *)
(* PT:  0x0000...0 (16 bytes)                                                *)
(* CT:  0xCEA7403D4D606B6E074EC5D3BAF39D18                                  *)
(* Tag: 0xD0D1C8A799996BF0265B98B5D48AB919                                  *)
(* ========================================================================= *)

(* Deconstructed KAT: each step proved individually.                          *)
(* H  = 0xDC95C078A2408989AD48A21492842087 (= aes256(0, key=0))              *)
(* CT = 0xCEA7403D4D606B6E074EC5D3BAF39D18 (= aes256(2, key=0) XOR 0)       *)
(* S  = 0x83DE425C5EDC5D498F382C441041CA92 (GHASH output)                    *)
(* EK0= 0x530F8AFBC74536B9A963B4F1C4CB738B (= aes256(1, key=0))             *)
(* Tag= 0xD0D1C8A799996BF0265B98B5D48AB919 (= S XOR EK0)                    *)

(* Step 1: H = AES-256(key=0, pt=0) *)
let tc13_H = FIPS197_ENCRYPT_FAST_CONV aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE
  `aes256_cipher (word 0 : 128 word) AESAVS_ZERO_KEY_256_SCHEDULE`;;

(* Step 2: GCTR — encrypt one zero block with counter = 2 *)
let tc13_gctr = GCTR256_CONV AESAVS_ZERO_KEY_256_SCHEDULE
  `gctr256 AESAVS_ZERO_KEY_256_SCHEDULE (word 2 : 128 word)
           [word 0 : 128 word]`;;

(* Step 3: GHASH — hash [CT; len_block] with H *)
(* H = 293207715084841176535342243128575008903 *)
(* CT = 274689383638147443066989238707276717336 *)
(* len_block = 128 *)
let tc13_gh0 = GHASH_STEP_CONV
  `ghash (word 293207715084841176535342243128575008903) (word 0 : 128 word)
         [word 274689383638147443066989238707276717336
         ; word 128]`;;

let tc13_gh1 = CONV_RULE (RAND_CONV GHASH_STEP_CONV) tc13_gh0;;

let tc13_ghash = CONV_RULE (RAND_CONV (REWRITE_CONV [ghash])) tc13_gh1;;

(* Step 4: EK0 = AES-256(key=0, J0=1) *)
let tc13_aes_j0 = FIPS197_ENCRYPT_FAST_CONV aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE
  `aes256_cipher (word 1 : 128 word) AESAVS_ZERO_KEY_256_SCHEDULE`;;

(* Step 5: Tag = S XOR EK0 *)
(* S = 175282903307801498547036460559768865426 *)
(* EK0 = 110406627023491326144955789200396612491 *)
let tc13_tag = WORD_RED_CONV
  `word_xor (word 175282903307801498547036460559768865426)
            (word 110406627023491326144955789200396612491) : 128 word`;;
