(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-256-GCM encrypt — the COMPLETE single binary (all length paths).      *)
(*                                                                           *)
(* This mirrors the upstream AES-XTS proof (arm/proofs/aes_xts_encrypt.ml):  *)
(* ONE machine-code blob (aes256_gcm_mc) handling every input length via its *)
(* internal length-dispatch cascade, with per-length-band correctness        *)
(* lemmas proved against that single binary and dispatched at the top.       *)
(*                                                                           *)
(* This file proves the 1-block case, taking the                            *)
(* .L256_enc_blocks_less_than_1 branch, exactly as the XTS LT_2BLOCK band    *)
(* lemma proves its short case against the one XTS binary.                   *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;

(* print_literal_from_elf "arm/aes-gcm/aes256_gcm.o";; *)
let aes256_gcm_mc = define_assert_from_elf
  "aes256_gcm_mc"
  "arm/aes-gcm/aes256_gcm.o"
[
  0xd503201f;       (* arm_NOP *)
  0xb4008f61;       (* arm_CBZ X1 (word 4588) *)
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
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
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
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x540054aa;       (* arm_BGE (word 2708) *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0xce007108;       (* arm_EOR3 Q8 Q8 Q0 Q28 *)
  0x6e200bc0;       (* arm_REV32_VEC Q0 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce017129;       (* arm_EOR3 Q9 Q9 Q1 Q28 *)
  0xce03716b;       (* arm_EOR3 Q11 Q11 Q3 Q28 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0xce02714a;       (* arm_EOR3 Q10 Q10 Q2 Q28 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac812448;       (* arm_STP Q8 Q9 X2 (Postimmediate_Offset (iword (&32))) *)
  0xac812c4a;       (* arm_STP Q10 Q11 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce04718c;       (* arm_EOR3 Q12 Q12 Q4 Q28 *)
  0xce0771ef;       (* arm_EOR3 Q15 Q15 Q7 Q28 *)
  0xce0671ce;       (* arm_EOR3 Q14 Q14 Q6 Q28 *)
  0xce0571ad;       (* arm_EOR3 Q13 Q13 Q5 Q28 *)
  0xac81344c;       (* arm_STP Q12 Q13 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 128 *)
  0xac813c4e;       (* arm_STP Q14 Q15 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x54002aaa;       (* arm_BGE (word 1364) *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 128 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef9e111;       (* arm_PMULL2 Q17 Q8 Q25 64 *)
  0x0ef9e113;       (* arm_PMULL Q19 Q8 Q25 64 *)
  0x4ef7e130;       (* arm_PMULL2 Q16 Q9 Q23 64 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x0ef7e137;       (* arm_PMULL Q23 Q9 Q23 64 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x4ef4e169;       (* arm_PMULL2 Q9 Q11 Q20 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x4ef6e15d;       (* arm_PMULL2 Q29 Q10 Q22 64 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x0ef4e174;       (* arm_PMULL Q20 Q11 Q20 64 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x0ef6e156;       (* arm_PMULL Q22 Q10 Q22 64 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef5e15d;       (* arm_PMULL2 Q29 Q10 Q21 64 *)
  0x4ef8e112;       (* arm_PMULL2 Q18 Q8 Q24 64 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef8e118;       (* arm_PMULL Q24 Q8 Q24 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x0ef5e155;       (* arm_PMULL Q21 Q10 Q21 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4ef9e188;       (* arm_PMULL2 Q8 Q12 Q25 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef9e199;       (* arm_PMULL Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef7e1aa;       (* arm_PMULL2 Q10 Q13 Q23 64 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef7e1b7;       (* arm_PMULL Q23 Q13 Q23 64 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef8e190;       (* arm_PMULL2 Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL Q24 Q12 Q24 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef6e1cb;       (* arm_PMULL2 Q11 Q14 Q22 64 *)
  0x0ef6e1d6;       (* arm_PMULL Q22 Q14 Q22 64 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4ef4e1ec;       (* arm_PMULL2 Q12 Q15 Q20 64 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x0ef4e1f4;       (* arm_PMULL Q20 Q15 Q20 64 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x4ef5e1cd;       (* arm_PMULL2 Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL Q21 Q14 Q21 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x6e200bd4;       (* arm_REV32_VEC Q20 Q30 8 128 *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef0e23d;       (* arm_PMULL Q29 Q17 Q16 64 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e200bd6;       (* arm_REV32_VEC Q22 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x6e200bd7;       (* arm_REV32_VEC Q23 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xce02714a;       (* arm_EOR3 Q10 Q10 Q2 Q28 *)
  0x6e200bd9;       (* arm_REV32_VEC Q25 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0xce0571ad;       (* arm_EOR3 Q13 Q13 Q5 Q28 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x0ef0e251;       (* arm_PMULL Q17 Q18 Q16 64 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0xce04718c;       (* arm_EOR3 Q12 Q12 Q4 Q28 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 128 *)
  0xce03716b;       (* arm_EOR3 Q11 Q11 Q3 Q28 *)
  0x4eb91f23;       (* arm_MOV_VEC Q3 Q25 128 *)
  0xce017129;       (* arm_EOR3 Q9 Q9 Q1 Q28 *)
  0xce007108;       (* arm_EOR3 Q8 Q8 Q0 Q28 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac812448;       (* arm_STP Q8 Q9 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb71ee2;       (* arm_MOV_VEC Q2 Q23 128 *)
  0xce0771ef;       (* arm_EOR3 Q15 Q15 Q7 Q28 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0xac812c4a;       (* arm_STP Q10 Q11 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce0671ce;       (* arm_EOR3 Q14 Q14 Q6 Q28 *)
  0x4eb61ec1;       (* arm_MOV_VEC Q1 Q22 128 *)
  0xac81344c;       (* arm_STP Q12 Q13 X2 (Postimmediate_Offset (iword (&32))) *)
  0xac813c4e;       (* arm_STP Q14 Q15 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb41e80;       (* arm_MOV_VEC Q0 Q20 128 *)
  0x54ffd5ab;       (* arm_BLT (word 2095796) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 128 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 128 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4ef9e111;       (* arm_PMULL2 Q17 Q8 Q25 64 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef7e130;       (* arm_PMULL2 Q16 Q9 Q23 64 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef9e113;       (* arm_PMULL Q19 Q8 Q25 64 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4ef6e15d;       (* arm_PMULL2 Q29 Q10 Q22 64 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x0ef7e137;       (* arm_PMULL Q23 Q9 Q23 64 *)
  0x4ef4e169;       (* arm_PMULL2 Q9 Q11 Q20 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x0ef6e156;       (* arm_PMULL Q22 Q10 Q22 64 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef8e112;       (* arm_PMULL2 Q18 Q8 Q24 64 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ef4e174;       (* arm_PMULL Q20 Q11 Q20 64 *)
  0x0ef8e118;       (* arm_PMULL Q24 Q8 Q24 64 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4ef5e15d;       (* arm_PMULL2 Q29 Q10 Q21 64 *)
  0x0ef5e155;       (* arm_PMULL Q21 Q10 Q21 64 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ef9e188;       (* arm_PMULL2 Q8 Q12 Q25 64 *)
  0x0ef9e199;       (* arm_PMULL Q25 Q12 Q25 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef7e1aa;       (* arm_PMULL2 Q10 Q13 Q23 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef7e1b7;       (* arm_PMULL Q23 Q13 Q23 64 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4ef6e1cb;       (* arm_PMULL2 Q11 Q14 Q22 64 *)
  0x0ef6e1d6;       (* arm_PMULL Q22 Q14 Q22 64 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ef8e190;       (* arm_PMULL2 Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL Q24 Q12 Q24 64 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef4e1ec;       (* arm_PMULL2 Q12 Q15 Q20 64 *)
  0x4ef5e1cd;       (* arm_PMULL2 Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL Q21 Q14 Q21 64 *)
  0x0ef4e1f4;       (* arm_PMULL Q20 Q15 Q20 64 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x0ef0e23d;       (* arm_PMULL Q29 Q17 Q16 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x0ef0e251;       (* arm_PMULL Q17 Q18 Q16 64 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0xad4564d8;       (* arm_LDP Q24 Q25 X6 (Immediate_Offset (iword (&160))) *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0xad4354d4;       (* arm_LDP Q20 Q21 X6 (Immediate_Offset (iword (&96))) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0xad445cd6;       (* arm_LDP Q22 Q23 X6 (Immediate_Offset (iword (&128))) *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xf101c0bf;       (* arm_CMP X5 (rvalue (word 112)) *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x540005ec;       (* arm_BGT (word 188) *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
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
  0x540005ec;       (* arm_BGT (word 188) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x540006ac;       (* arm_BGT (word 212) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x540007ac;       (* arm_BGT (word 244) *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x540008ac;       (* arm_BGT (word 276) *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x54000a0c;       (* arm_BGT (word 320) *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x54000b6c;       (* arm_BGT (word 364) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x14000069;       (* arm_B (word 420) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef9e111;       (* arm_PMULL2 Q17 Q8 Q25 64 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x6e084712;       (* arm_INS Q18 Q24 0 64 64 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0xce017529;       (* arm_EOR3 Q9 Q9 Q1 Q29 *)
  0x0ef2e372;       (* arm_PMULL Q18 Q27 Q18 64 *)
  0x0ef9e113;       (* arm_PMULL Q19 Q8 Q25 64 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x0ef7e11a;       (* arm_PMULL Q26 Q8 Q23 64 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef7e11c;       (* arm_PMULL2 Q28 Q8 Q23 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e37b;       (* arm_PMULL Q27 Q27 Q24 64 *)
  0xce027529;       (* arm_EOR3 Q9 Q9 Q2 Q29 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef6e11c;       (* arm_PMULL2 Q28 Q8 Q22 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL Q26 Q8 Q22 64 *)
  0x4ef5e37b;       (* arm_PMULL2 Q27 Q27 Q21 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0xce037529;       (* arm_EOR3 Q9 Q9 Q3 Q29 *)
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
  0xd65f03c0;       (* arm_RET X30 *)
  0x52800000;       (* arm_MOV W0 (rvalue (word 0)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let AES256_GCM_EXEC = ARM_MK_EXEC_RULE aes256_gcm_mc;;

(* ========================================================================= *)
(* Shared simulation combinators for the length-band branch lemmas.          *)
(*                                                                           *)
(* In the spirit of the AES-XTS proof's named sub-tactics (AESENC_TAC,       *)
(* XTSENC_TAC, ...), these factor out the repeated "step + simplify" loops   *)
(* and length-bound discharges so each branch lemma reads declaratively.     *)
(* (Unlike XTS, GCM cannot share a tail sub-triple across bands: the band    *)
(* seam carries a half-finished Karatsuba accumulator, not a closed spec     *)
(* predicate, so each band re-simulates.)                                    *)
(* ========================================================================= *)

(* The length precondition `1 <= byte_len /\ byte_len <= 16`, reassembled    *)
(* from the two split assumptions for use with MATCH_MP.                      *)
let GCM_BOUNDS = CONJ (ASSUME `1 <= byte_len`) (ASSUME `byte_len <= 16`);;

(* Simulate steps a..b, simplifying the encryption state after each step.    *)
let GCM_RUN a b : tactic =
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES256_GCM_EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC) (a--b);;

(* Same as GCM_RUN but runs an extra tactic (e.g. a branch-cascade resolver) *)
(* after each step.                                                          *)
let GCM_RUN_THEN (extra:tactic) a b : tactic =
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC THEN extra) (a--b);;

(* Discharge a length lemma `1 <= byte_len /\ byte_len <= 16 ==> P` into the  *)
(* assumptions (used to collapse the cbz / in-loop guard conditionals).      *)
let GCM_BND lemma : tactic = RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP lemma GCM_BOUNDS]);;

(* Discharge an upper-bound-only lemma `byte_len <= 16 ==> P`.                *)
let GCM_BND16 lemma : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP lemma (ASSUME `byte_len <= 16`)]);;

(* Entry boilerplate: unfold the triple, strip, init, run the nop + cbz x1   *)
(* (steps 1-2), and discharge the cbz guard with the given per-band lemma.   *)
let GCM_INIT_TAC cbz_lemma : tactic =
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst AES256_GCM_EXEC] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (1--2) THEN GCM_BND cbz_lemma;;

(* The shared prologue (steps 3-19): stack/frame setup, with the stack-ptr   *)
(* and constant-offset folding.  Identical in every length band.             *)
let GCM_PROLOGUE_TAC : tactic =
  ARM_STEPS_TAC AES256_GCM_EXEC (3--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC;;

(* The in-loop guard: add x4 (264), collapse X5 to in_ptr with the given     *)
(* lemma so cmp x0,x5 (265) compares equal, then b.ge (266) into the tail.   *)
let GCM_INLOOP_GUARD_TAC x5_lemma : tactic =
  ARM_STEPS_TAC AES256_GCM_EXEC [264] THEN GCM_BND x5_lemma THEN
  ARM_STEPS_TAC AES256_GCM_EXEC [265] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL]) THEN
  ARM_STEPS_TAC AES256_GCM_EXEC [266];;

(* ========================================================================= *)
(* The 1-block case, taking the .L256_enc_blocks_less_than_1 branch.         *)
(*                                                                           *)
(* Mirrors the AES-XTS LT_kBLOCK band lemmas: a length-restricted (1 <=      *)
(* byte_len <= 16) correctness statement proved against the SINGLE full      *)
(* binary aes256_gcm_mc.  The 8-lane prologue runs in full; the in-loop      *)
(* guard (cmp x0,x5; b.ge) is taken into the tail; the tail length cascade   *)
(* (cmp x5,#0x70..#0x10) all falls through; the b .L256_enc_blocks_less_     *)
(* than_1 lands on the shared masked-store + GHASH + Barrett-reduce tail,    *)
(* which is byte-identical to the standalone one-block routine — so its      *)
(* GHASH/mask closers (GCM_CT_STEP_TAC, GCM_GHASH_STEP_MASKED_TAC, and the   *)
(* ONE_BLOCK lemmas) apply verbatim.                                         *)
(* ========================================================================= *)

(* All the GHASH / mask / cascade closers reused by the 1-, 2- and 3-block    *)
(* branch proofs below come from this shared file (pure algebra, no machine    *)
(* code), so we do not re-prove the per-N standalone correctness theorems.     *)
needs "arm/proofs/utils/gcm_one_block_closers.ml";;
needs "arm/proofs/utils/gcm_two_block_closers.ml";;
needs "arm/proofs/utils/gcm_three_block_closers.ml";;

(* --- arithmetic side-lemmas for the branch resolution -------------------- *)

(* cbz x1 at entry: bit_len = 8*byte_len is nonzero for byte_len >= 1. *)
let GCM_CBZ_LEMMA = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(8*byte_len):int64) = 8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* word_sub (word n) (word 1) = word (n-1) for 1 <= n <= 16. *)
let GCM_WSUB1 = prove
 (`1 <= n /\ n <= 16 ==> word_sub (word n:int64) (word 1) = word (n - 1)`,
  STRIP_TAC THEN REWRITE_TAC[WORD_SUB] THEN
  COND_CASES_TAC THENL
   [AP_TERM_TAC THEN ASM_ARITH_TAC; POP_ASSUM MP_TAC THEN ASM_ARITH_TAC]);;

(* word_and with the high mask (~0x7f) clears small values. *)
let GCM_ANDMASK0 = prove
 (`!m. m < 128 ==> word_and (word m:int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(word 18446744073709551488:int64) = word_not (word (2 EXP 7 - 1))` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_NOT_MASK] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `val(word m:int64) = m` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m DIV 2 EXP 7 = 0` SUBST1_TAC THENL
   [REWRITE_TAC[DIV_EQ_0] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_VAL]);;

(* In-loop guard: X5 = in_ptr + ((byte_len-1) & ~0x7f) is the address where
    the full-128-byte-chunk region ends (the main-loop bound). For <= 16 bytes
    there are no full chunks, so the offset is 0 and X5 = in_ptr; then cmp x0,x5
    compares equal and the b.ge into the tail is taken. *)
(* MILA TODO:: RENAME GCM_LOOP_END_EQ_INPTR_1BLOCK *)
let GCM_X5_LEMMA = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (8*byte_len):int64) 3 = word byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB1] THEN
  SUBGOAL_THEN `word_and (word (byte_len-1):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* The tail length register X5 = (in_ptr + byte_len) - in_ptr = word byte_len. *)
let GCM_X5TAIL_LEMMA = prove
 (`byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (8*byte_len):int64) 3)) in_ptr = word byte_len`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (8*byte_len):int64) 3 = word byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* Each tail-cascade b.gt (cmp x5,#t for t in 16..112) is NOT taken when the
   tail length byte_len <= 16. *)
let GCM_CASC_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 16 <= t /\ t <= 112 ==>
    ((~(val (word_sub (word byte_len:int64) (word t)) = 0) /\
      (ival (word_sub (word byte_len:int64) (word t)) < &0 <=>
       ~(ival (word byte_len:int64) - &t = ival (word_sub (word byte_len:int64) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(word byte_len:int64) = &byte_len` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word byte_len:int64) (word t) = iword(&byte_len - &t)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&byte_len - &t):int64) = &byte_len - &t` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 63 = 9223372036854775808`] THEN
    SUBGOAL_THEN `&byte_len:int <= &16 /\ &16:int <= &t /\ &t:int <= &112` MP_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
    INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  SUBGOAL_THEN `&byte_len:int <= &16 /\ &16:int <= &t` MP_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
  INT_ARITH_TAC);;

(* Resolve any pending tail-cascade b.gt PC conditional (thresholds 16..112)
   to its fall-through by rewriting the signed-gt test to F. *)
let GCM_CASCADE_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE(
      (map (fun t -> MATCH_MP GCM_CASC_FALSE (CONJ bl16
              (CONJ (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `16 <= t`))
                    (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `t <= 112`)))))
           [16;32;48;64;80;96;112]) @ [COND_CLAUSES])) THEN
    ASSUME_TAC bl16
  else NO_TAC);;

(* --- the 1-block correctness theorem ------------------------------------- *)

let AES256_GCM_ENCRYPT_LT_1BLOCK_CONCRETE = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,16) (out_ptr,16) /\
    nonoverlapping (in_ptr,16) (xi_ptr,16) /\
    nonoverlapping (in_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,16) (xi_ptr,16) /\
    nonoverlapping (out_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,16) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,16) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,16) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,16) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,16) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt /\
           read (memory :> bytes128 out_ptr) s = out0 /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h)
      (\s. let ct = word_xor pt (aes256_block_enc ivec rk0 rk1 rk2 rk3
                     rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm = word_and ct mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word byte_len /\
           read (memory :> bytes128 out_ptr) s =
             word_or ctm (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ctm]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,16);
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
  (* Entry + nop/cbz (1-2): byte_len >= 1 so the cbz is not taken. *)
  GCM_INIT_TAC GCM_CBZ_LEMMA THEN

  (* Prologue (3-19) + 8-lane counter setup & AES rounds (20-263). *)
  GCM_PROLOGUE_TAC THEN
  GCM_RUN 20 263 THEN

  (* In-loop guard (264-266): X5 collapses to in_ptr so b.ge is taken. *)
  GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA THEN

  (* Tail entry loads (267-272); collapse the tail length X5 = byte_len. *)
  GCM_RUN 267 272 THEN GCM_BND16 GCM_X5TAIL_LEMMA THEN

  (* Tail length cascade (273-321): every cmp x5,#0x70..#0x10; b.gt falls
     through for a single block. *)
  GCM_RUN_THEN GCM_CASCADE_TAC 273 321 THEN

  (* b .L256_enc_blocks_less_than_1 (322) -> the shared masked tail. *)
  ARM_STEPS_TAC AES256_GCM_EXEC [322] THEN GCM_ENC_SIMPLIFY_TAC THEN

  (* Abbreviate the block-0 AES output (`ct`/`s13`) so the shared one-block
     closures fold it back. *)
  ABBREV_TAC `s13 = aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese ivec rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13:(128)word` THEN
  ABBREV_TAC `ct = word_xor (word_xor pt s13) rk14 :(128)word` THEN

  (* Tail mask build (323-336); collapse the data-dependent mask register Q0
     to word (2^(8*byte_len) - 1). *)
  GCM_RUN 323 336 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP NBLOCK_MASK_REG th])) THEN

  (* AND_VEC, bif, masked store, GHASH Karatsuba up to the final EOR3 (337-359). *)
  GCM_RUN 337 359 THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN
  ABBREV_FINAL_XI_TAC THEN

  (* EXT, REV64, ST1, MOV, LDP*4 (360-367) — Q19 opaque.  Stop at RET (pc+4588). *)
  ARM_STEPS_TAC AES256_GCM_EXEC (360--367) THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[ONE_BLOCK_USHR_BYTELEN; ONE_BLOCK_MASK_IDEM] THEN
  CONJ_TAC THENL [GCM_CT_STEP_TAC; GCM_GHASH_STEP_MASKED_TAC]);;

(* ---- skipped 2-8 block CONCRETE proofs for fast 1-block test ---- *)

let AES256_GCM_ENCRYPT_LT_0BLOCK_CONCRETE = prove
 (gcm_0b_goal,
  (* Entry + nop (1); cbz x1 (2) is TAKEN since X1 = 0, jumping to pc+4592;    *)
  (* mov w0,#0 (3) lands at the RET (pc+4596).                                  *)
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst AES256_GCM_EXEC] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* COMBINED CORRECTNESS THEOREM (XTS-style dispatch over the per-block bands) *)
(*                                                                           *)
(* Recursive byte-list spec aes256_gcm_encrypt / gcm_final_xi + the bridge   *)
(* lemmas relating each band's concrete word-level postcondition to the     *)
(* abstract spec, then AES256_GCM_ENCRYPT_CORRECT dispatching by input        *)
(* length (currently scoped to val len <= 16: the 0-block + 1-block bands).   *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Recursive AES-256-GCM encrypt specification over a plaintext byte list,    *)
(* mirroring the AES-XTS spec (arm/proofs/xts_reference/aes_xts_encrypt_spec   *)
(* + aes-xts-armv8.ml).  Reuses XTS's mode-agnostic byte/word conversions and  *)
(* byte_list_at memory predicate, and the existing GCM per-block primitives    *)
(* (aes256_block_enc, gcm_ctr_inc, ghash_polyval_acc).                         *)
(* ========================================================================= *)

(* --- byte<->word conversions + memory predicate (verbatim from XTS) --- *)
let bytes_to_int128 = define
  `bytes_to_int128 (bs : byte list) : int128 =
    word_join
      (word_join
        (word_join (word_join (EL 15 bs) (EL 14 bs) : int16) (word_join (EL 13 bs) (EL 12 bs) : int16) : int32)
        (word_join (word_join (EL 11 bs) (EL 10 bs) : int16) (word_join (EL 9 bs) (EL 8 bs) : int16) : int32) : int64)
      (word_join
        (word_join (word_join (EL 7 bs) (EL 6 bs) : int16) (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
        (word_join (word_join (EL 3 bs) (EL 2 bs) : int16) (word_join (EL 1 bs) (EL 0 bs) : int16) : int32) : int64)`;;

let int128_to_bytes = define
  `int128_to_bytes (w : int128) : byte list =
     [word_subword w (0, 8); word_subword w (8, 8); word_subword w (16, 8); word_subword w (24, 8);
      word_subword w (32, 8); word_subword w (40, 8); word_subword w (48, 8); word_subword w (56, 8);
      word_subword w (64, 8); word_subword w (72, 8); word_subword w (80, 8); word_subword w (88, 8);
      word_subword w (96, 8); word_subword w (104, 8); word_subword w (112, 8); word_subword w (120, 8)]`;;

let byte_list_at = define
  `byte_list_at (m : byte list) (m_p : int64) (len:int64) s =
    ! i. i < val len ==> read (memory :> bytes8(word_add m_p (word i))) s = EL i m`;;


(* ---- spec + bridges + 1BLOCK_ABS ---- *)

let gcm_ctr_iter = new_recursive_definition num_RECURSION
  `gcm_ctr_iter 0 (ivec:(128)word) = ivec /\
   gcm_ctr_iter (SUC n) (ivec:(128)word) = gcm_ctr_inc (gcm_ctr_iter n ivec)`;;

let gcm_keystream = new_definition
  `gcm_keystream (i:num) (ivec:(128)word) (rks:int128 list) : (128)word =
     aes256_block_enc (gcm_ctr_iter i ivec)
       (EL 0 rks) (EL 1 rks) (EL 2 rks) (EL 3 rks) (EL 4 rks) (EL 5 rks) (EL 6 rks) (EL 7 rks)
       (EL 8 rks) (EL 9 rks) (EL 10 rks) (EL 11 rks) (EL 12 rks) (EL 13 rks) (EL 14 rks)`;;

(* --- recursive full-block ciphertext (int128 blocks) --- *)
let gcm_ct_rec = new_specification ["gcm_ct_rec"]
  (prove_general_recursive_function_exists
    `?gcm_ct_rec.
       ! (i:num) (nfull:num) (P:byte list) (ivec:(128)word) (rks:int128 list).
         gcm_ct_rec i nfull P ivec rks : (int128 list) =
           if nfull = 0 then []
           else
             let blk = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
             let ct = word_xor blk (gcm_keystream i ivec rks) in
             CONS ct (gcm_ct_rec (i + 1) (nfull - 1) P ivec rks)`);;

(* --- recursive full-block ciphertext (flat byte list) --- *)
let gcm_ct_bytes_rec = new_specification ["gcm_ct_bytes_rec"]
  (prove_general_recursive_function_exists
    `?gcm_ct_bytes_rec.
       ! (i:num) (nfull:num) (P:byte list) (ivec:(128)word) (rks:int128 list).
         gcm_ct_bytes_rec i nfull P ivec rks : (byte list) =
           if nfull = 0 then []
           else
             let blk = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
             let ct = word_xor blk (gcm_keystream i ivec rks) in
             APPEND (int128_to_bytes ct) (gcm_ct_bytes_rec (i + 1) (nfull - 1) P ivec rks)`);;

(* --- masked partial-tail ciphertext block: read the full 16-byte block then  *)
(* mask to `tail` bytes (the binary reads a full block and masks).            *)
let gcm_ctm_tail = new_definition
  `gcm_ctm_tail (i:num) (tail:num) (P:byte list) (ivec:(128)word) (rks:int128 list) : (128)word =
     let blk = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
     let ct = word_xor blk (gcm_keystream i ivec rks) in
     word_and ct (word (2 EXP (8 * tail) - 1))`;;

(* --- list of GHASH input blocks: full blocks ++ masked tail --- *)
let gcm_ghash_blocks = new_definition
  `gcm_ghash_blocks (len:num) (P:byte list) (ivec:(128)word) (rks:int128 list) : (int128 list) =
     let tail = len - 16 * ((len - 1) DIV 16) in
     let nfull = (len - 1) DIV 16 in
     APPEND (gcm_ct_rec 0 nfull P ivec rks)
            [gcm_ctm_tail nfull tail P ivec rks]`;;

(* --- the ciphertext byte list (output): full block bytes ++ first `tail`     *)
(* bytes of the masked partial block; [] for empty input.                     *)
let aes256_gcm_encrypt = new_definition
  `aes256_gcm_encrypt (len:num) (P:byte list) (ivec:(128)word) (rks:int128 list) : (byte list) =
     let tail = len - 16 * ((len - 1) DIV 16) in
     let nfull = (len - 1) DIV 16 in
     if len = 0 then []
     else APPEND (gcm_ct_bytes_rec 0 nfull P ivec rks)
                 (SUB_LIST (0, tail) (int128_to_bytes (gcm_ctm_tail nfull tail P ivec rks)))`;;

(* --- the final GHASH accumulator Xi; unchanged for empty input. --- *)
let gcm_final_xi = new_definition
  `gcm_final_xi (len:num) (P:byte list) (ivec:(128)word) (rks:int128 list)
                (xi:(128)word) (h:(128)word) : (128)word =
     if len = 0 then xi
     else word_reversefields 8
       (ghash_polyval_acc h (word_reversefields 8 xi)
          (MAP (\b. word_reversefields 8 b) (gcm_ghash_blocks len P ivec rks)))`;;

(* ========================================================================= *)
(* Bridge lemmas: concrete 1-block band postcondition <-> abstract spec.      *)
(* ========================================================================= *)

let KS0_LEMMA = prove(
  `gcm_keystream 0 ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] =
   aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14`,
  REWRITE_TAC[gcm_keystream; gcm_ctr_iter] THEN
  REWRITE_TAC(map num_CONV [`14`;`13`;`12`;`11`;`10`;`9`;`8`;`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[EL; HD; TL]);;

let NFULL0_LEMMA = prove(
  `!n. 1 <= n /\ n <= 16 ==> (n - 1) DIV 16 = 0 /\ n - 16 * ((n-1) DIV 16) = n`,
  REPEAT STRIP_TAC THENL
   [SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(n-1) DIV 16 = 0` SUBST1_TAC THENL
     [SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let SUB_LIST_0_16 = prove(
  `!l:(byte)list. LENGTH l = 16 ==> SUB_LIST (0,16) l = l`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM (ASSUME `LENGTH(l:byte list) = 16`)] THEN
  REWRITE_TAC[SUB_LIST_LENGTH]);;

let EL_16_8_CLAUSES = (CONJUNCTS o prove)
 (`EL 0 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a0 /\
   EL 1 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a1 /\
   EL 2 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a2 /\
   EL 3 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a3 /\
   EL 4 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a4 /\
   EL 5 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a5 /\
   EL 6 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a6 /\
   EL 7 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a7 /\
   EL 8 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a8 /\
   EL 9 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a9 /\
   EL 10 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a10 /\
   EL 11 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a11 /\
   EL 12 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a12 /\
   EL 13 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a13 /\
   EL 14 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a14 /\
   EL 15 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a15`,
  REWRITE_TAC(map num_CONV [`15`;`14`;`13`;`12`;`11`;`10`;`9`;`8`;`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[EL; HD; TL]);;

let BYTES128_TO_BYTES8_THM = prove(
  `!pos bl_ptr s.
    read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
    bytes_to_int128
      [read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x0)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x1)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x2)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x3)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x4)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x5)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x6)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x7)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x8)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x9)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xa)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xb)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xc)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xd)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xe)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xf)))) s]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bytes_to_int128] THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  GEN_REWRITE_TAC TOP_DEPTH_CONV [READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ONCE_REWRITE_TAC [ARITH_RULE `pos + 0 = (pos:num)`] THEN REFL_TAC);;

let LIST_OF_EL_16 = prove(
  `!l:(byte)list. LENGTH l = 16 ==>
     [EL 0 l; EL 1 l; EL 2 l; EL 3 l; EL 4 l; EL 5 l; EL 6 l; EL 7 l;
      EL 8 l; EL 9 l; EL 10 l; EL 11 l; EL 12 l; EL 13 l; EL 14 l; EL 15 l] = l`,
  REWRITE_TAC[ARITH_RULE `16 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))))))))))`] THEN
  REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC(map num_CONV [`15`;`14`;`13`;`12`;`11`;`10`;`9`;`8`;`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[EL; HD; TL]);;

let GCM_VAL16 = WORD_REDUCE_CONV `val(word 16:int64)`;;

let BYTE_LIST_AT_16_BYTES128 = prove(
  `!pt_in in_ptr s. byte_list_at pt_in in_ptr (word 16) s /\ LENGTH pt_in = 16
     ==> read (memory :> bytes128 in_ptr) s = bytes_to_int128 pt_in`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `in_ptr = word_add in_ptr (word 0):int64` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[BYTES128_TO_BYTES8_THM] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  FIRST_X_ASSUM(fun th -> if (try fst(dest_const(repeat rator (concl th)))="byte_list_at" with _->false)
    then ASSUME_TAC(REWRITE_RULE[byte_list_at; GCM_VAL16] th) else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) then
    (MAP_EVERY (fun i -> ASSUME_TAC(REWRITE_RULE[ARITH; WORD_ADD_0](MATCH_MP th (ARITH_RULE(vsubst[mk_small_numeral i,`i:num`] `i < 16`)))))
      [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]) else NO_TAC)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LIST_OF_EL_16]);;

let SUBWORD_BYTES_TO_INT128 = prove(
 `!b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 i. i < 16
   ==> word_subword (bytes_to_int128 [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]) (8*i,8):byte =
       EL i [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[bytes_to_int128] THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC WORD_BLAST);;

let BYTES128_TO_BYTES8_0 = REWRITE_RULE[ADD_CLAUSES; WORD_ADD_0] (SPEC `0` BYTES128_TO_BYTES8_THM);;

let BYTE8_OF_BYTES128 = prove(
 `!p s i. i < 16 ==> read (memory :> bytes8 (word_add p (word i))) s =
                     word_subword (read (memory :> bytes128 p) s) (8*i,8)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [BYTES128_TO_BYTES8_0] THEN
  ASM_SIMP_TAC[SUBWORD_BYTES_TO_INT128] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN REWRITE_TAC[WORD_ADD_0]);;

let EL_SUB_LIST_0 = prove(
 `!(l:A list) n i. i < n ==> EL i (SUB_LIST(0,n) l) = EL i l`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[SUB_LIST_CLAUSES];
    ASM_CASES_TAC `n = 0` THENL [ASM_MESON_TAC[LT]; ALL_TAC] THEN
    SUBGOAL_THEN `n = SUC(n-1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[EL; HD; TL] THEN
    SUBGOAL_THEN `i = SUC(i-1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL; TL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let EL_INT128_TO_BYTES = prove(
 `!w i. i < 16 ==> EL i (int128_to_bytes w):byte = word_subword w (8*i,8)`,
  GEN_TAC THEN REWRITE_TAC[int128_to_bytes] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[]);;

let MASK_BYTE_OUT = prove(
 `!(ct:int128) (out0:int128) (n:num) (i:num).
    i < n /\ n <= 16
    ==> word_subword (word_or (word_and ct (word (2 EXP (8*n) - 1):int128))
                              (word_and out0 (word_not (word (2 EXP (8*n) - 1):int128)))) (8*i,8):byte =
        word_subword ct (8*i,8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_NOT;
              BIT_MASK_WORD; DIMINDEX_8; DIMINDEX_128] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * i + j < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * i + j < 8 * n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let XI_BRIDGE_1B = prove(
 `!len pt_in ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14 xi h.
    1 <= val(len:int64) /\ val len <= 16 /\ LENGTH pt_in = 16
    ==> word_reversefields 8
          (ghash_polyval_acc h (word_reversefields 8 xi)
            [word_reversefields 8
               (word_and (word_xor (bytes_to_int128 pt_in)
                            (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14))
                         (word (2 EXP (8 * val len) - 1)))]) =
        gcm_final_xi (val len) pt_in ivec
          [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[gcm_final_xi] THEN
  SUBGOAL_THEN `~(val(len:int64) = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPEC `val(len:int64)` NFULL0_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[gcm_ct_rec; APPEND; MAP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[SUB_LIST_0_16; MULT_CLAUSES; ARITH_RULE `0 * 16 = 0`] THEN
  REWRITE_TAC[KS0_LEMMA]);;

let OUT_BRIDGE_1B = prove(
 `!len pt_in out0 ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14 out_ptr s.
    1 <= val(len:int64) /\ val len <= 16 /\ LENGTH pt_in = 16 /\
    read (memory :> bytes128 out_ptr) s =
      word_or (word_and (word_xor (bytes_to_int128 pt_in)
                          (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14))
                        (word (2 EXP (8 * val len) - 1)))
              (word_and out0 (word_not (word (2 EXP (8 * val len) - 1):int128)))
    ==> byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec
                        [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                     out_ptr len s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[byte_list_at] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < 16` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BYTE8_OF_BYTES128] THEN
  REWRITE_TAC[aes256_gcm_encrypt] THEN
  MP_TAC(SPEC `val(len:int64)` NFULL0_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `~(val(len:int64) = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[gcm_ct_bytes_rec; APPEND] THEN
  ASM_SIMP_TAC[EL_SUB_LIST_0] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[SUB_LIST_0_16; MULT_CLAUSES; ARITH_RULE `0 * 16 = 0`; KS0_LEMMA] THEN
  ASM_SIMP_TAC[EL_INT128_TO_BYTES] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MASK_BYTE_OUT] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_AND; BIT_MASK_WORD; DIMINDEX_8; DIMINDEX_128] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * i + j < 128 /\ 8 * i + j < 8 * val(len:int64)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ===== N-block generic bridges ===== *)

let NFULL_LEMMA' = prove(
  `!nfull tail. 1 <= tail /\ tail <= 16
     ==> ((16 * nfull + tail) - 1) DIV 16 = nfull /\
         (16 * nfull + tail) - 16 * (((16 * nfull + tail) - 1) DIV 16) = tail`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((16 * nfull + tail) - 1) DIV 16 = nfull` ASSUME_TAC THENL
   [SUBGOAL_THEN `(16 * nfull + tail) - 1 = nfull * 16 + (tail - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    SUBGOAL_THEN `(tail - 1) DIV 16 = 0` SUBST1_TAC THENL
     [SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC; ARITH_TAC];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* --- EL of a SUB_LIST at general start offset --- *)
let EL_SUB_LIST_GEN = prove(
 `!m (l:A list) n i. m + n <= LENGTH l /\ i < n ==> EL i (SUB_LIST(m,n) l) = EL (m+i) l`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THENL
   [MESON_TAC[EL_SUB_LIST_0]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC m + n <= 0)`] THEN
  REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `SUC (m + n) <= 0` THEN ARITH_TAC;
    REWRITE_TAC[SUB_LIST_CLAUSES; EL; TL] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* --- block-k input bridge: the k-th 128-bit block read = bytes_to_int128 of  *)
(* the k-th 16-byte sublist of the plaintext byte list. --- *)
let BYTE_LIST_AT_BLOCK = prove(
 `!pt_in in_ptr nblk k s.
    (!i. i < 16 * nblk ==> read (memory :> bytes8 (word_add in_ptr (word i))) s = EL i pt_in) /\
    LENGTH pt_in = 16 * nblk /\ k < nblk
    ==> read (memory :> bytes128 (word_add in_ptr (word (16 * k)))) s =
        bytes_to_int128 (SUB_LIST (16 * k, 16) pt_in)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BYTES128_TO_BYTES8_THM] THEN
  REWRITE_TAC[bytes_to_int128] THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  SUBGOAL_THEN
   `!j. j < 16 ==> read (memory :> bytes8 (word_add in_ptr (word (16 * k + j)))) s =
                   EL j (SUB_LIST(16*k,16) (pt_in:byte list))`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `16 * k + 16 <= LENGTH(pt_in:byte list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_SUB_LIST_GEN] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `16 * k + j`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    REWRITE_TAC EL_16_8_CLAUSES THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC(map (fun i ->
      MATCH_MP th (ARITH_RULE(vsubst[mk_small_numeral i,`j:num`]`j<16`)))
      [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15])) THEN
    REWRITE_TAC[ADD_CLAUSES]]);;

(* --- one-step unfolds of the recursive ciphertext builders --- *)
let GCM_CT_REC_STEP = prove(
  `gcm_ct_rec i 0 P ivec rks = [] /\
   gcm_ct_rec i (SUC m) P ivec rks =
     CONS (word_xor (bytes_to_int128 (SUB_LIST(i*16,16) P)) (gcm_keystream i ivec rks))
          (gcm_ct_rec (i+1) m P ivec rks)`,
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [gcm_ct_rec] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF; ADD1]);;

let GCM_CT_BYTES_REC_STEP = prove(
  `gcm_ct_bytes_rec i 0 P ivec rks = [] /\
   gcm_ct_bytes_rec i (SUC m) P ivec rks =
     APPEND (int128_to_bytes (word_xor (bytes_to_int128 (SUB_LIST(i*16,16) P)) (gcm_keystream i ivec rks)))
            (gcm_ct_bytes_rec (i+1) m P ivec rks)`,
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [gcm_ct_bytes_rec] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF; ADD1]);;

(* --- keystream at iterate i in terms of gcm_ctr_iter --- *)
let KS_ITER = prove(
  `!i. gcm_keystream i ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] =
       aes256_block_enc (gcm_ctr_iter i ivec) rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14`,
  GEN_TAC THEN REWRITE_TAC[gcm_keystream] THEN
  REWRITE_TAC(map num_CONV [`14`;`13`;`12`;`11`;`10`;`9`;`8`;`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[EL; HD; TL]);;

let CTR_ITER_CLAUSES = (CONJUNCTS o prove)(
  `gcm_ctr_iter 0 ivec = ivec /\
   gcm_ctr_iter 1 ivec = gcm_ctr_inc ivec /\
   gcm_ctr_iter 2 ivec = gcm_ctr_inc (gcm_ctr_inc ivec) /\
   gcm_ctr_iter 3 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)) /\
   gcm_ctr_iter 4 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) /\
   gcm_ctr_iter 5 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) /\
   gcm_ctr_iter 6 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))) /\
   gcm_ctr_iter 7 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))))`,
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[gcm_ctr_iter]);;

(* --- small DIV/MOD helpers for the recursive EL lemma --- *)
let ADD16_DIV = prove(`!j. (j + 16) DIV 16 = j DIV 16 + 1`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `j + 16 = 1 * 16 + j`] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC);;
let ADD16_MOD = prove(`!j. (j + 16) MOD 16 = j MOD 16`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `j + 16 = 1 * 16 + j`] THEN
  SIMP_TAC[MOD_MULT_ADD; ARITH_EQ]);;

(* --- byte i of the recursive full-block ciphertext byte list --- *)
let EL_GCM_CT_BYTES_REC = prove(
 `!nfull base P ivec rks i.
    i < 16 * nfull
    ==> EL i (gcm_ct_bytes_rec base nfull P ivec rks) =
        word_subword (word_xor (bytes_to_int128 (SUB_LIST(16*(base + i DIV 16),16) P))
                               (gcm_keystream (base + i DIV 16) ivec rks))
                     (8 * (i MOD 16), 8)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; LT] THEN ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[GCM_CT_BYTES_REC_STEP] THEN
    SUBGOAL_THEN `LENGTH(int128_to_bytes (word_xor (bytes_to_int128 (SUB_LIST(base*16,16) P)) (gcm_keystream base ivec rks))) = 16`
        ASSUME_TAC THENL [REWRITE_TAC[int128_to_bytes; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i < 16` THENL
     [SUBGOAL_THEN `i DIV 16 = 0 /\ i MOD 16 = i` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_SIMP_TAC[DIV_LT; MOD_LT]; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      ASM_SIMP_TAC[EL_APPEND] THEN
      ASM_SIMP_TAC[EL_INT128_TO_BYTES] THEN
      REWRITE_TAC[MULT_AC];
      ASM_SIMP_TAC[EL_APPEND] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`base + 1`; `P:byte list`; `ivec:(128)word`; `rks:int128 list`; `i - 16`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `i = (i - 16) + 16` (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD16_DIV; ADD16_MOD] THEN
      REWRITE_TAC[ARITH_RULE `(base + 1) + j = base + (j + 1)`]]]);;

let LENGTH_GCM_CT_BYTES_REC = prove(
 `!nfull base P ivec rks. LENGTH(gcm_ct_bytes_rec base nfull P ivec rks) = 16 * nfull`,
  INDUCT_TAC THEN REWRITE_TAC[GCM_CT_BYTES_REC_STEP; LENGTH; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; int128_to_bytes; LENGTH] THEN ARITH_TAC);;

(* --- GENERIC OUTPUT BRIDGE: N-1 full ct stores + masked tail = byte_list_at spec --- *)
let OUT_BRIDGE_GEN = prove(
 `!nfull tail pt_in ivec rks out0 out_ptr (len:int64) s.
    1 <= tail /\ tail <= 16 /\ val len = 16 * nfull + tail /\
    (!k. k < nfull
         ==> read (memory :> bytes128 (word_add out_ptr (word (16 * k)))) s =
             word_xor (bytes_to_int128 (SUB_LIST(16*k,16) pt_in)) (gcm_keystream k ivec rks)) /\
    read (memory :> bytes128 (word_add out_ptr (word (16 * nfull)))) s =
      word_or (word_and (word_xor (bytes_to_int128 (SUB_LIST(16*nfull,16) pt_in)) (gcm_keystream nfull ivec rks))
                        (word (2 EXP (8 * tail) - 1)))
              (word_and out0 (word_not (word (2 EXP (8 * tail) - 1):int128)))
    ==> byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec rks) out_ptr len s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[byte_list_at] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[aes256_gcm_encrypt] THEN
  MP_TAC(SPECL [`nfull:num`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i < 16 * nfull` THENL
   [(* full-block region *)
    SUBGOAL_THEN `EL i (APPEND (gcm_ct_bytes_rec 0 nfull pt_in ivec rks)
         (SUB_LIST (0,tail) (int128_to_bytes (gcm_ctm_tail nfull tail pt_in ivec rks)))) =
       EL i (gcm_ct_bytes_rec 0 nfull pt_in ivec rks)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[EL_APPEND; LENGTH_GCM_CT_BYTES_REC]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_GCM_CT_BYTES_REC; ADD_CLAUSES] THEN
    SUBGOAL_THEN `word_add out_ptr (word i):int64 =
         word_add (word_add out_ptr (word (16 * (i DIV 16)))) (word (i MOD 16))`
       SUBST1_TAC THENL
     [SUBGOAL_THEN `i = 16 * (i DIV 16) + i MOD 16` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
       [MESON_TAC[DIVISION_SIMP]; ALL_TAC] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add out_ptr (word (16 * (i DIV 16))):int64`; `s:armstate`; `i MOD 16`] BYTE8_OF_BYTES128) THEN
    ANTS_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    SUBGOAL_THEN `i DIV 16 < nfull` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) then MP_TAC(SPEC `i DIV 16` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    (* tail region *)
    SUBGOAL_THEN `LENGTH(gcm_ct_bytes_rec 0 nfull pt_in ivec rks) = 16 * nfull` ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_GCM_CT_BYTES_REC]; ALL_TAC] THEN
    SUBGOAL_THEN `EL i (APPEND (gcm_ct_bytes_rec 0 nfull pt_in ivec rks)
         (SUB_LIST (0,tail) (int128_to_bytes (gcm_ctm_tail nfull tail pt_in ivec rks)))) =
       EL (i - 16 * nfull) (SUB_LIST (0,tail) (int128_to_bytes (gcm_ctm_tail nfull tail pt_in ivec rks)))`
       SUBST1_TAC THENL
     [ASM_SIMP_TAC[EL_APPEND]; ALL_TAC] THEN
    ABBREV_TAC `j = i - 16 * nfull` THEN
    SUBGOAL_THEN `j < tail /\ j < 16 /\ i = 16 * nfull + j` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "j" THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_SUB_LIST_0; EL_INT128_TO_BYTES] THEN
    REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `word_add out_ptr (word (16 * nfull + j)):int64 =
         word_add (word_add out_ptr (word (16 * nfull))) (word j)` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add out_ptr (word (16 * nfull)):int64`; `s:armstate`; `j:num`] BYTE8_OF_BYTES128) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    ASM_SIMP_TAC[MASK_BYTE_OUT] THEN
    REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_AND; BIT_MASK_WORD; DIMINDEX_8; DIMINDEX_128] THEN
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* --- input block read directly from byte_list_at (for the pre-impl) --- *)
let INPUT_BLOCK_BL = prove(
 `!pt_in in_ptr nblk k s.
    byte_list_at pt_in in_ptr (word (16 * nblk)) s /\ LENGTH pt_in = 16 * nblk /\
    val(word(16 * nblk):int64) = 16 * nblk /\ k < nblk
    ==> read (memory :> bytes128 (word_add in_ptr (word (16 * k)))) s =
        bytes_to_int128 (SUB_LIST (16 * k, 16) pt_in)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BYTE_LIST_AT_BLOCK THEN
  EXISTS_TAC `nblk:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if free_in `byte_list_at` (concl th) then
     MP_TAC(REWRITE_RULE[byte_list_at] th) else NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

(* --- all 8 input-block reads from a 128-byte byte_list_at (for the dispatch pre-impl) --- *)
let INPUT_READS_128 = prove(
 `!pt_in in_ptr s.
    byte_list_at pt_in in_ptr (word 128) s /\ LENGTH pt_in = 128
   ==> read (memory :> bytes128 in_ptr) s = bytes_to_int128 (SUB_LIST (0,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 16))) s = bytes_to_int128 (SUB_LIST (16,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 32))) s = bytes_to_int128 (SUB_LIST (32,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 48))) s = bytes_to_int128 (SUB_LIST (48,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 64))) s = bytes_to_int128 (SUB_LIST (64,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 80))) s = bytes_to_int128 (SUB_LIST (80,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 96))) s = bytes_to_int128 (SUB_LIST (96,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 112))) s = bytes_to_int128 (SUB_LIST (112,16) pt_in)`,
  let INB k = (MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`8`;mk_small_numeral k;`s:armstate`] INPUT_BLOCK_BL) THEN
               CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
               ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_THEN ACCEPT_TAC]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word 128:int64) = 16 * 8` ASSUME_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [INB 0; INB 1; INB 2; INB 3; INB 4; INB 5; INB 6; INB 7]);;

(* --- gcm_final_xi unfold for nonempty input --- *)
let GCM_FINAL_XI_UNFOLD = prove(
 `!len pt_in ivec rks xi h. ~(len = 0)
   ==> gcm_final_xi len pt_in ivec rks xi h =
       word_reversefields 8
         (ghash_polyval_acc h (word_reversefields 8 xi)
            (MAP (\b. word_reversefields 8 b) (gcm_ghash_blocks len pt_in ivec rks)))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[gcm_final_xi]);;


(* ===== N-block bridges already loaded from gcm_nblock_bridges content ===== *)

(* ===== GHASH_BLOCKS_1..8 ===== *)

let GHASH_BLOCKS_1 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 0 + tail) pt_in ivec rks =
        [ word_and (word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`0`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GHASH_BLOCKS_2 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 1 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`1`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;


let GHASH_BLOCKS_3 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 2 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`2`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;


let GHASH_BLOCKS_4 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 3 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(48,16) pt_in)) (gcm_keystream 3 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`3`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;


let GHASH_BLOCKS_5 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 4 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(48,16) pt_in)) (gcm_keystream 3 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(64,16) pt_in)) (gcm_keystream 4 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`4`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;


let GHASH_BLOCKS_6 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 5 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(48,16) pt_in)) (gcm_keystream 3 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(64,16) pt_in)) (gcm_keystream 4 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(80,16) pt_in)) (gcm_keystream 5 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`5`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;


let GHASH_BLOCKS_7 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 6 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(48,16) pt_in)) (gcm_keystream 3 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(64,16) pt_in)) (gcm_keystream 4 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(80,16) pt_in)) (gcm_keystream 5 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(96,16) pt_in)) (gcm_keystream 6 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`6`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;


let GHASH_BLOCKS_8 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 7 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(48,16) pt_in)) (gcm_keystream 3 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(64,16) pt_in)) (gcm_keystream 4 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(80,16) pt_in)) (gcm_keystream 5 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(96,16) pt_in)) (gcm_keystream 6 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(112,16) pt_in)) (gcm_keystream 7 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`7`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;


(* ===== abstract band lemmas 0,1,2..8 ===== *)

let AES256_GCM_ENCRYPT_LT_0BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    val (len:int64) = 0 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
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
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = byteswap128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = byteswap128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
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
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `len:int64 = word 0` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_0; aes256_gcm_encrypt; gcm_final_xi; byte_list_at; VAL_WORD_0;
              LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;`out_ptr:int64`;`xi_ptr:int64`;`ivec_ptr:int64`;`key_ptr:int64`;`htable_ptr:int64`;
    `co0:(128)word`;`xi:(128)word`;`stackptr:int64`;`pc:num`]
   AES256_GCM_ENCRYPT_LT_0BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]); ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;


let AES256_GCM_ENCRYPT_LT_1BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    1 <= val len /\ val len <= 16 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
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
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = byteswap128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = byteswap128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
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
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\ val len = 16 * 0 + (val len - 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - 0` THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = 0 + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;
    `out_ptr:int64`;
    `xi_ptr:int64`;
    `ivec_ptr:int64`;
    `key_ptr:int64`;
    `htable_ptr:int64`;
    `bytes_to_int128 (SUB_LIST(0,16) pt_in)`;
    `co0:(128)word`;
    `ivec:(128)word`;
    `rk0:(128)word`;
    `rk1:(128)word`;
    `rk2:(128)word`;
    `rk3:(128)word`;
    `rk4:(128)word`;
    `rk5:(128)word`;
    `rk6:(128)word`;
    `rk7:(128)word`;
    `rk8:(128)word`;
    `rk9:(128)word`;
    `rk10:(128)word`;
    `rk11:(128)word`;
    `rk12:(128)word`;
    `rk13:(128)word`;
    `rk14:(128)word`;
    `xi:(128)word`;
    `h:(128)word`;
    `h1k:(128)word`;
    `byte_len:num`;
    `stackptr:int64`;
    `pc:num`]
   AES256_GCM_ENCRYPT_LT_1BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [ASM_ARITH_TAC; NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; REWRITE_TAC[WORD_VAL]];
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`0`; `byte_len:num`; `co0:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          GEN_TAC THEN REWRITE_TAC[ARITH_RULE `~(k < 0)`];
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * 0 + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;`[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]:int128 list`] GHASH_BLOCKS_1) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `8 * byte_len = 8 * val(len:int64)` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`x:armstate`] INPUT_READS_128) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;
