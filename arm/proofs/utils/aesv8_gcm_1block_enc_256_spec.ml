(* ========================================================================= *)
(* Specification for aesv8_gcm_1block_enc_256:                               *)
(* AES-256 CTR encryption of one block + GHASH accumulation.                 *)
(*                                                                           *)
(* The spec mirrors the assembly operations directly:                        *)
(*   1. AES-256 encrypt counter (14 rounds of aese/aesmc + final XOR)       *)
(*   2. XOR with plaintext -> ciphertext                                     *)
(*   3. GHASH: (Xi XOR CT) * H (Karatsuba + reduction, via gcm_gmult_spec)  *)
(*                                                                           *)
(* Counter increment is handled separately (stored to ivec in assembly).     *)
(* The GHASH part reuses gcm_gmult_spec from gcm_gmult_v8_spec.ml.          *)
(* ========================================================================= *)

needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/gcm_gmult_v8_spec.ml";;

(* ----------------------------------------------------------------------- *)
(* AES-256 block cipher: 14 rounds as aese/aesmc composition.              *)
(* Matches the ARM AESE+AESMC instruction sequence exactly:                *)
(*   Rounds 0-12: aesmc(aese(state, rk_i))                                *)
(*   Round 13:    aese(state, rk13)  (no MixColumns)                       *)
(*   Final:       XOR with rk14                                             *)
(* ----------------------------------------------------------------------- *)

let aes256_block_enc = new_definition
  `aes256_block_enc (input:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) : (128)word =
   let s0 = aesmc (aese input rk0) in
   let s1 = aesmc (aese s0 rk1) in
   let s2 = aesmc (aese s1 rk2) in
   let s3 = aesmc (aese s2 rk3) in
   let s4 = aesmc (aese s3 rk4) in
   let s5 = aesmc (aese s4 rk5) in
   let s6 = aesmc (aese s5 rk6) in
   let s7 = aesmc (aese s6 rk7) in
   let s8 = aesmc (aese s7 rk8) in
   let s9 = aesmc (aese s8 rk9) in
   let s10 = aesmc (aese s9 rk10) in
   let s11 = aesmc (aese s10 rk11) in
   let s12 = aesmc (aese s11 rk12) in
   let s13 = aese s12 rk13 in
   word_xor s13 rk14`;;

(* ----------------------------------------------------------------------- *)
(* Full encrypt function spec: AES-256-CTR encrypt one block + GHASH.      *)
(*                                                                          *)
(* Returns (ciphertext, updated_Xi).                                        *)
(* Counter increment (new_ivec) is checked separately in the proof since    *)
(* it involves REV32 vector operations on the ivec register.                *)
(* ----------------------------------------------------------------------- *)

let aesv8_gcm_1block_enc_spec = new_definition
  `aesv8_gcm_1block_enc_spec
    (pt:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (hhl:(128)word)
    : ((128)word # (128)word) =
   let enc = aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
               rk8 rk9 rk10 rk11 rk12 rk13 rk14 in
   let ct = word_xor pt enc in
   let new_xi = gcm_gmult_spec (word_xor xi ct) h hhl in
   (ct, new_xi)`;;
