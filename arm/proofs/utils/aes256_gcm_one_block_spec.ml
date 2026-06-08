(* ========================================================================= *)
(* Specification for aes256_gcm_one_block:                      *)
(* AES-256 CTR encryption of one block + GHASH accumulation.                 *)
(*                                                                           *)
(* This is the 1-block path through aws-lc's aesv8_gcm_8x_enc_256 kernel.   *)
(* The spec is mathematically identical to aesv8_gcm_1block_enc_spec:        *)
(*   1. AES-256 encrypt counter (14 rounds of aese/aesmc + final XOR)       *)
(*   2. XOR with plaintext -> ciphertext                                     *)
(*   3. GHASH: (Xi XOR CT) * H (Karatsuba + reduction, via gcm_gmult_spec)  *)
(*                                                                           *)
(* Reuses aes256_block_enc and gcm_gmult_spec from existing specs.           *)
(* ========================================================================= *)

needs "arm/proofs/utils/aesv8_gcm_1block_enc_256_spec.ml";;

(* ----------------------------------------------------------------------- *)
(* The spec is the same as aesv8_gcm_1block_enc_spec since the 8x kernel   *)
(* produces the same mathematical result for 1 block. We reuse the          *)
(* existing aes256_block_enc and gcm_gmult_spec definitions directly.       *)
(*                                                                          *)
(* Returns (ciphertext, updated_Xi).                                        *)
(* ----------------------------------------------------------------------- *)

let aes256_gcm_one_block_enc_spec = new_definition
  `aes256_gcm_one_block_enc_spec
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
