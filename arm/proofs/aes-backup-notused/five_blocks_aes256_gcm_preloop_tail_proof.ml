(* ========================================================================= *)
(* five_blocks_aes256_gcm_preloop_tail_proof.ml                              *)
(*                                                                           *)
(* Companion file to aes256_gcm_five_block.ml.         *)
(*                                                                           *)
(* The parent nblock file proves the assembly-shape karatsuba bridge against *)
(* polyval_reduce_prop3:                                                     *)
(*    GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC                                  *)
(* This file proves the analogous bridge against the standard                *)
(* `ghash_polyval_acc` form (initialised with word 0). This is the form      *)
(* that appears in the FIVE_BLOCKS_PRELOOP_TAIL_CORRECT postcondition's      *)
(* xi_ptr write, so the corollary below provides the exact rewrite that the  *)
(* main theorem's GHASH closure needs to apply.                              *)
(*                                                                           *)
(* The corollary composes:                                                   *)
(*    GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC                                  *)
(*  + GHASH_POLYVAL_ACC_5                                                    *)
(*  + POLYVAL_DOT_H5_EQ + POLYVAL_DOT_H4_EQ_LOCAL                            *)
(*  + WORD_XOR_0 / WORD_PMUL_SYM                                             *)
(* via standard equational reasoning.                                        *)
(*                                                                           *)
(* PROOF VALIDATED INTERACTIVELY VIA THE HOL-LIGHT MCP SERVER (2026-05-31).  *)
(* The 14 tactics below were applied one at a time, each validated against   *)
(* the goal state, and the final theorem closes cleanly.                     *)
(* ========================================================================= *)

needs "arm/proofs/aes256_gcm_five_block.ml";;

(* ---------------------------------------------------------------------- *)
(* GHASH_5BLOCK_KARATSUBA_EQ_GHASH_POLYVAL_ACC_INIT.                       *)
(*                                                                         *)
(* Bridges the assembly-shape `ghash_5block_karatsuba` reducer to the      *)
(* standard `ghash_polyval_acc` form initialised with word 0 (i.e. the    *)
(* form used in the postcondition of FIVE_BLOCKS_PRELOOP_TAIL_CORRECT).   *)
(* ---------------------------------------------------------------------- *)

let GHASH_5BLOCK_KARATSUBA_EQ_GHASH_POLYVAL_ACC_INIT = prove
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
          (ghash_polyval_acc h (word 0) [b1; b2; b3; b4; b5])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b1:int128`; `b2:int128`; `b3:int128`; `b4:int128`; `b5:int128`;
                `h:int128`; `hk:int128`; `h2k:int128`; `h3k:int128`;
                `h4k:int128`; `h5k:int128`]
               GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(SPECL [`h:int128`; `word 0:int128`;
                `b1:int128`; `b2:int128`; `b3:int128`; `b4:int128`; `b5:int128`]
               GHASH_POLYVAL_ACC_5) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `word_xor (word 0:int128) b1 = b1` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[POLYVAL_DOT_H5_EQ] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h =
     polyval_dot (polyval_dot h h) (polyval_dot h h)`
    SUBST1_TAC THENL
   [REWRITE_TAC[POLYVAL_DOT_H4_EQ_LOCAL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h =
     polyval_dot h (polyval_dot h h)`
    SUBST1_TAC THENL
   [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  REFL_TAC);;

(* ---------------------------------------------------------------------- *)
(* GHASH_POLYVAL_ACC_5_INIT.                                              *)
(*                                                                         *)
(* Convenience corollary: when the initial GHASH accumulator is 0, the    *)
(* polyval_acc form simplifies to the symmetric h^5 reduce.                *)
(* ---------------------------------------------------------------------- *)

let GHASH_POLYVAL_ACC_5_INIT = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128) (h:int128).
   ghash_polyval_acc h (word 0)
     [b1; b2; b3; b4; b5] =
   polyval_reduce_prop3
     (word_xor
       (word_pmul b1 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
      (word_xor
       (word_pmul b2 (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
      (word_xor
       (word_pmul b3 (polyval_dot (polyval_dot h h) h) : 256 word)
      (word_xor
       (word_pmul b4 (polyval_dot h h) : 256 word)
       (word_pmul b5 h : 256 word)))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`h:int128`; `word 0:int128`;
                `b1:int128`; `b2:int128`; `b3:int128`; `b4:int128`; `b5:int128`]
               GHASH_POLYVAL_ACC_5) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `word_xor (word 0:int128) b1 = b1` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  MESON_TAC[]);;

(* ========================================================================= *)
(* FIVE_BLOCKS_PRELOOP_TAIL_CORRECT — top-level Hoare triple.                *)
(*                                                                           *)
(* The proof body uncommented from the original 1-block proof file pattern   *)
(* (aes256_gcm_one_block.ml) and scaled to 5 blocks:                          *)
(*   - 1-block:  ARM_STEPS_TAC (1--84) AES rounds                             *)
(*               (85--93) EOR + post-AES                                      *)
(*               (94--103) GHASH karatsuba                                    *)
(*               (104--111) epilogue                                          *)
(*   - 5-block:  ARM_STEPS_TAC (1--180) AES rounds for 5 blocks               *)
(*               s13_1..s13_5 ABBREVs                                         *)
(*               step 181 + ct1 ABBREV + post-AES normalize                   *)
(*               steps through more_than_4 cascade for ct2..ct5               *)
(*               GHASH karatsuba reduction + final_xi ABBREV                  *)
(*               epilogue + 6-way conjunction split                           *)
(*                                                                           *)
(* The aes256_gcm_five_block.ml file currently has the   *)
(* main theorem body wrapped in `(* ... *)` because the closure tactic       *)
(* GCM_5BLOCK_GHASH_STEP_TAC is structurally a 4-block tactic that needs     *)
(* scaling to 22 atomic ABBREVs (vs 18) + 21-atom XOR-AC closure for 5      *)
(* blocks. Without that scaling, the GHASH conjunct of the final 6-way       *)
(* split cannot close.                                                       *)
(*                                                                           *)
(* The corollary GHASH_5BLOCK_KARATSUBA_EQ_GHASH_POLYVAL_ACC_INIT proven     *)
(* above provides the EXACT rewrite that the GHASH closure needs once the    *)
(* simulation has reduced the trace to `ghash_5block_karatsuba(...)`. With  *)
(* this corollary in hand, the GHASH conjunct collapses in one rewrite to   *)
(* `word_reversefields 8 (ghash_polyval_acc h (word 0) [b1;..;b5])`, which  *)
(* matches the postcondition exactly (since `xi = word 0` in the standard    *)
(* preloop_tail entry).                                                      *)
(*                                                                           *)
(* The full simulation (343 instructions × 5 blocks of state evolution) +   *)
(* the 22-atom GHASH closure adaptation requires multiple sessions to land  *)
(* — see project_five_blocks_progress in user memory for the validated      *)
(* simulation prefix (steps 1-195, PC = pc + 780).                           *)
(* ========================================================================= *)
