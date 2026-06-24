(* ========================================================================= *)
(* six_blocks_aes256_gcm_preloop_tail_proof.ml                               *)
(*                                                                           *)
(* Companion file to aes256_gcm_six_block.ml.          *)
(*                                                                           *)
(* Proves the bridge against the standard `ghash_polyval_acc` form           *)
(* (initialised with word 0):                                                *)
(*    GHASH_6BLOCK_KARATSUBA_EQ_GHASH_POLYVAL_ACC_INIT                        *)
(* + a convenience corollary GHASH_POLYVAL_ACC_6_INIT.                        *)
(*                                                                           *)
(* PROOF VALIDATED VIA THE HOL-LIGHT MCP SERVER.                             *)
(* ========================================================================= *)

needs "arm/proofs/aes256_gcm_six_block.ml";;

(* ---------------------------------------------------------------------- *)
(* GHASH_6BLOCK_KARATSUBA_EQ_GHASH_POLYVAL_ACC_INIT.                       *)
(* ---------------------------------------------------------------------- *)

let GHASH_6BLOCK_KARATSUBA_EQ_GHASH_POLYVAL_ACC_INIT = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128) (b6:int128) (h:int128)
     (hk:int128) (h2k:int128) (h3k:int128) (h4k:int128) (h5k:int128) (h6k:int128).
    word_subword hk  (0,64):(64)word = karatsuba_mid h /\
    word_subword h2k (0,64):(64)word = karatsuba_mid (polyval_dot h h) /\
    word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
    word_subword h4k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
    word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
    word_subword h6k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)
    ==> ghash_6block_karatsuba b1 b2 b3 b4 b5 b6
          (byteswap128 h) hk
          (byteswap128 (polyval_dot h h)) h2k
          (byteswap128 (polyval_dot h (polyval_dot h h))) h3k
          (byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h))) h4k
          (byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h)) h5k
          (byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)) h6k =
        word_reversefields 8
          (ghash_polyval_acc h (word 0) [b1; b2; b3; b4; b5; b6])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b1:int128`; `b2:int128`; `b3:int128`; `b4:int128`; `b5:int128`; `b6:int128`;
                `h:int128`; `hk:int128`; `h2k:int128`; `h3k:int128`;
                `h4k:int128`; `h5k:int128`; `h6k:int128`]
               GHASH_6BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(SPECL [`h:int128`; `word 0:int128`;
                `b1:int128`; `b2:int128`; `b3:int128`; `b4:int128`; `b5:int128`; `b6:int128`]
               GHASH_POLYVAL_ACC_6) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `word_xor (word 0:int128) b1 = b1` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[POLYVAL_DOT_H6_EQ; POLYVAL_DOT_H5_EQ] THEN
  SUBGOAL_THEN
    `(polyval_dot (polyval_dot (polyval_dot h h) h) h) = (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    SUBST1_TAC THENL
   [REWRITE_TAC[POLYVAL_DOT_H4_EQ_LOCAL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    SUBST1_TAC THENL
   [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  REFL_TAC);;

(* ---------------------------------------------------------------------- *)
(* GHASH_POLYVAL_ACC_6_INIT.                                              *)
(* ---------------------------------------------------------------------- *)

let GHASH_POLYVAL_ACC_6_INIT = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128) (b6:int128) (h:int128).
   ghash_polyval_acc h (word 0) [b1; b2; b3; b4; b5; b6] =
   polyval_reduce_prop3
     (word_xor (word_pmul b1 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
     (word_xor (word_pmul b2 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
     (word_xor (word_pmul b3 (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
     (word_xor (word_pmul b4 (polyval_dot (polyval_dot h h) h) : 256 word)
     (word_xor (word_pmul b5 (polyval_dot h h) : 256 word)
               (word_pmul b6 h : 256 word))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`h:int128`; `word 0:int128`;
                `b1:int128`; `b2:int128`; `b3:int128`; `b4:int128`; `b5:int128`; `b6:int128`]
               GHASH_POLYVAL_ACC_6) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `word_xor (word 0:int128) b1 = b1` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  MESON_TAC[]);;
