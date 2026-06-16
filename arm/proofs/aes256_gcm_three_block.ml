(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* aes256_gcm_three_block.ml                                               *)
(*                                                                         *)
(* The 3-block AES-256-GCM separate-blocks encrypt proof — the N=3         *)
(* instance of the generic N-block framework. STRUCTURALLY MIRRORS         *)
(* aes256_gcm_four_block.ml, scaled down to N=3.                           *)
(*                                                                         *)
(* PER-N CONTENT (only piece in this file):                                *)
(*   - Machine code blob (aes256_gcm_three_block_mc) and EXEC              *)
(*   - ghash_3block_karatsuba (assembly-shape spec)                        *)
(*   - GHASH_3BLOCK_AS_NBLOCK (compatibility with ghash_Nblock_karatsuba)  *)
(*   - GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC — derived from inductive bridge *)
(*   - GCM_3BLOCK_GHASH_STEP_TAC + main theorem AES256_GCM_THREE_BLOCK_CORRECT *)
(*                                                                         *)
(* PERFORMANCE: the GF Barrett reduce funnels the whole accumulator into   *)
(* one register (Q19, ~38k nodes), so the eor3 mid-reduce explodes if      *)
(* stepped concretely. The fix abbreviates ONLY Q19 to an opaque acc19     *)
(* just before that step (Q17/Q18 stay concrete so the Barrett pmulls      *)
(* still compute), keeps it opaque through ABBREV_FINAL_XI, then bridges   *)
(* the half-swapped final_xi shape back for the GHASH closer (see          *)
(* HALFSWAP_JOIN_SELF / HALFSWAP_REV8_LEMMA in the helpers).               *)
(* ========================================================================= *)

(* All dependencies (base/AES/ghash_spec/aesgcm helpers) are pulled in       *)
(* transitively by the N-block framework file below.                          *)
needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;
(* The variable-length (1-48 byte) combined proof at the end of this file     *)
(* reuses the one-block masking/GHASH closers (ONE_BLOCK_MASK_REG,            *)
(* GCM_CT_STEP_TAC, GCM_GHASH_STEP_MASKED_TAC) for the SHORT (1-16B) band and *)
(* the two-block GHASH machinery (ghash_2block_karatsuba,                     *)
(* GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC, GCM_2BLOCK_GHASH_STEP_MASKED_TAC)   *)
(* for the MID (17-32B) band.                                                 *)

(* The Karatsuba bridge (ghash_3block_karatsuba <-> polyval_reduce_prop3) and
   the GHASH / mask / cascade closers used below are shared with the other
   block-count proofs and live in this utils file (pure algebra). *)
needs "arm/proofs/utils/gcm_one_block_closers.ml";;
needs "arm/proofs/utils/gcm_two_block_closers.ml";;
needs "arm/proofs/utils/gcm_three_block_closers.ml";;

let aes256_gcm_three_block_mc = define_assert_from_elf
  "aes256_gcm_three_block_mc"
  "arm/aes-gcm/aes256_gcm_three_block.o"
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
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0xce02714a;       (* arm_EOR3 Q10 Q10 Q2 Q28 *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
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
  0x5400018c;       (* arm_BGT (word 48) *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x540000cc;       (* arm_BGT (word 24) *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x5400024c;       (* arm_BGT (word 72) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x14000020;       (* arm_B (word 128) *)
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

let AES256_GCM_THREE_BLOCK_EXEC =
  ARM_MK_EXEC_RULE aes256_gcm_three_block_mc;;

(* The half-swap lemmas used by this file's only-Q19 fast reduce
   (HALFSWAP_JOIN_SELF, HALFSWAP_REV8_LEMMA, JOIN_SUBWORD_IDENT) are defined in
   arm/proofs/utils/gcm_aesgcm_helpers.ml, alongside the related REV8_JOIN_FOLD
   / REVERSEFIELDS8_SUBWORD_LO/HI family. *)

(* ========================================================================= *)
(* PER-BLOCK CIPHERTEXT CLOSURES                                              *)
(* Each block k closes via the shared GCM_NBLOCK_CT_STEP_TAC N k, which       *)
(* handles ivec_k = gcm_ctr_inc^{k-1} ivec for any k.                         *)
(* ========================================================================= *)

let GCM_CT1_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 3 1;;
let GCM_CT2_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 3 2;;
let GCM_CT3_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 3 3;;

let AES256_GCM_THREE_BLOCK_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,1028) (in_ptr:int64,48) /\
    nonoverlapping (word pc,1028) (out_ptr:int64,48) /\
    nonoverlapping (word pc,1028) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,1028) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,1028) (key_ptr:int64,240) /\
    nonoverlapping (word pc,1028) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,1028) (stackptr:int64,80) /\
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
    nonoverlapping (ivec_ptr,16) (word pc,1028) /\
    nonoverlapping (xi_ptr,16) (word pc,1028) /\
    nonoverlapping (out_ptr,48) (word pc,1028)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_three_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (256 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = out0 /\
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
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm3 = word_and ct3 mask in
           read PC s = word(pc + 1024) /\
           read X0 s = word (32 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s =
             word_or ctm3 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ctm3]))
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
              fst AES256_GCM_THREE_BLOCK_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue *)
  ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-138: AES rounds for all 3 blocks *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
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
  ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [139] THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN
  GCM_NBLOCK_POST_AES_NORMALIZE_TAC THEN

  (* Steps 140-148: tail dispatch prologue *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (140--148) THEN
  GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC THEN

  (* Step 148 (the first cmp #96 / b.gt) already left the PC as a conditional;
     resolve it, then continue. *)
  THREEBLOCK_CASCADE_TAC THEN

  (* Steps 149-172: tail-dispatch cascade.  With symbolic byte_len each b.gt
     leaves the PC as a conditional; resolve it after every step with
     THREEBLOCK_CASCADE_TAC (the fall-throughs at 96/80/64/48 then the taken
     branch at 32).  Then normalise the 2^64 literal. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC THEN THREEBLOCK_CASCADE_TAC) (149--172) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 173-188 + ABBREV ct2.  The cmp #32 / b.gt taken branch sits at
     trace step 175 (just inside this range), so keep resolving conditionals. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC THEN THREEBLOCK_CASCADE_TAC) (173--188) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN
  ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN

  (* Steps 189-211 + ABBREV ct3 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (189--211) THEN
  ABBREV_TAC `ct3 = word_xor (word_xor pt3 s13_3) rk14:(128)word` THEN

  (* Steps 212-221: build the partial-block mask register (Q0). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (212--221) THEN

  (* Collapse the data-dependent mask register Q0 to word (2^(8*byte_len) - 1)
     before the AND_VEC / bif. *)
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP THREEBLOCK_MASK_REG th])) THEN

  (* Steps 222-243: AND_VEC, bif (partial store fixup), then build the
     Karatsuba accumulator.  Q17/Q18 concrete; Q19 ~38k nodes at s243. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (222--243) THEN

  (* SPEED FIX (only-Q19).  The eor3 distributes word_subword over the
     38k-node Q19 (~480s all-concrete).  Abbreviate ONLY Q19 to an opaque
     `acc19` (Q17/Q18 stay concrete, so the Barrett MODULO pmulls still
     compute and leave no dangling reads); the eor3 then operates on the
     opaque acc19 in ~5s. *)
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q19 (s:armstate) = (x:int128)`) (concl th)
    then ABBREV_TAC(mk_eq(mk_var("acc19",`:int128`), rand(concl th)))
    else NO_TAC) THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (244--246) THEN

  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN

  (* Abbreviate Q19 as `final_xi` while acc19 is still opaque — this captures
     `final_xi = word_subword (word_join (rev8 acc19) (rev8 acc19)) (64,128)`,
     a small term.  Fold the half-swap (HALFSWAP_JOIN_SELF) so final_xi's def
     becomes `word_join (..rev8 acc19 lo..) (..rev8 acc19 hi..)` — the
     word_join shape the closer's REV64/REV8/MATCH_MP_TAC chain expects — then
     expand acc19 to its concrete value (Q17/Q18 were concrete, no dangling
     reads). *)
  ABBREV_FINAL_XI_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HALFSWAP_JOIN_SELF]) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `acc19:(128)word`
    then RULE_ASSUM_TAC(REWRITE_RULE[SYM th]) else NO_TAC) THEN
  (* Bridge: pull `word_reversefields 8` outside the subwords so final_xi's
     value-definition is `word_join (rev8 _) (rev8 _)`-shaped — the form the
     closer's REV8_JOIN_FOLD + MATCH_MP_TAC chain folds to a
     `word_reversefields 8`-headed term.  Without this the only-Q19 fast path
     leaves final_xi `word_join (word_subword (rev8 _) _) ...`-shaped and
     MATCH_MP_TAC fails to match. *)
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try fst(dest_const(repeat rator (lhs(concl th)))) = "word_join"
        with _ -> false)
    then ASSUME_TAC(REWRITE_RULE[GSYM REVERSEFIELDS8_SUBWORD_HI;
                                 GSYM REVERSEFIELDS8_SUBWORD_LO] th)
    else NO_TAC) THEN

  (* Epilogue: ext, rev64, str, mov, ldp x4.  Stop at s251 (PC = pc+1024,
     just before the RET at pc+1024). *)
  ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC (247--251) THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN
  (* Collapse the mask register that survives into the ct3 store goal, and
     reduce X0 = word(32+byte_len). *)
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP THREEBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[THREEBLOCK_USHR] THEN

  (* After ASM_SIMP discharges the PC and X0 conjuncts the remaining goals are
     the ct1/ct2 stores, the masked ct3 store, and the GHASH over
     [ct1; ct2; ctm3]. *)
  REPEAT CONJ_TAC THENL [
    GCM_CT1_STEP_TAC;
    GCM_CT2_STEP_TAC;
    (* masked ct3 store: establish word_xor pt3 aes = ct3, fold it on the spec
       side and collapse the bif's double mask (NBLOCK_MASK_IDEM). *)
    SUBGOAL_THEN
      `word_xor pt3
         (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc ivec))
                           rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11
                           rk12 rk13 rk14) = ct3:(128)word`
      ASSUME_TAC THENL [
      EXPAND_TAC "ct3" THEN
      REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      FIRST_ASSUM(fun th ->
        if is_eq(concl th) && rand(concl th) = `s13_3:(128)word` &&
           not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
      REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN;
                  LANE3_BYTES_JOIN_BE; CTR_WORD_INSERT] THEN
      REWRITE_TAC[gcm_ctr_inc] THEN
      ABBREV_TAC `ctr3g:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
      ABBREV_TAC `br3g:(32)word = word_bytereverse (ctr3g:(32)word)` THEN
      ABBREV_TAC `step1_3g:(32)word = word_bytereverse (word_add (br3g:(32)word) (word 1:(32)word))` THEN
      REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "step1_3g" THEN
      REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[NBLOCK_MASK_IDEM];
    GCM_3BLOCK_GHASH_STEP_MASKED_TAC
  ]);;





(* ========================================================================= *)
(*       VARIABLE-LENGTH (1-48 byte) COMBINED CORRECTNESS                     *)
(*                                                                           *)
(* The routine branches internally on the total input length (the tail       *)
(* dispatch cascade cmp #96..#16).  Following the upstream AES-XTS design we  *)
(* prove one band lemma per length range -- all against this same machine    *)
(* code -- and dispatch between them in the combined theorem with nested      *)
(* ASM_CASES_TAC on the length:                                               *)
(*   * SHORT  1 <= n <= 16 : the .less_than_1 tail (one masked block stored,  *)
(*            single-block GHASH) -- byte-identical to the one-block algo, so  *)
(*            it reuses the one-block masking/GHASH closers directly.          *)
(*   * MID    17 <= n <= 32 : the .more_than_1 tail (one full block + one     *)
(*            partial block, GHASH over [ct1; ctm2]) -- the two-block algo,    *)
(*            so it reuses the two-block GHASH machinery.                       *)
(*   * LONG   33 <= n <= 48 : the full three-block path proved above           *)
(*            (AES256_GCM_THREE_BLOCK_CORRECT) at byte_len := n - 32.          *)
(* ========================================================================= *)

(* The one-block masked-GHASH closer GCM_GHASH_STEP_MASKED_TAC starts with a  *)
(* FIRST_ASSUM that picks the htable karatsuba_mid bridge assumption.  The     *)
(* three-block precondition carries THREE such assumptions (h, h^2, h^3); a    *)
(* bare FIRST_ASSUM stops at the first MATCH_MP success (the h^3 one) whose    *)
(* rewrite is a no-op, so the real h^1 bridge never fires.  Wrapping the       *)
(* rewrite in CHANGED_TAC forces FIRST_ASSUM to skip no-op matches.  The rest  *)
(* of the closer body is identical to the one-block version.                   *)
let GCM_GHASH_STEP_MASKED_TAC_3 =
  REWRITE_TAC[ghash_polyval_acc; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  FIRST_ASSUM(fun th ->
    CHANGED_TAC(REWRITE_TAC[GSYM(MATCH_MP GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT th)])) THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm = word_and (ct:(128)word) mask` THEN
  SUBGOAL_THEN
    `word_xor pt (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                   rk8 rk9 rk10 rk11 rk12 rk13 rk14) = ct`
    (fun th -> REWRITE_TAC[th]) THENL [
    MAP_EVERY EXPAND_TAC ["ct"; "s13"] THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC];
    ALL_TAC
  ] THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct:(128)word) = ctm`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm" THEN CONV_TAC WORD_BITWISE_RULE;
    ALL_TAC
  ] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word`
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
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
  REWRITE_TAC[WORD_XOR_ASSOC; KAR_MID_BRIDGE; WORD_SUBWORD_0;
              WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_ASSOC; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[KAR_MID_BRIDGE; WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[karatsuba_mid] THEN
  ABBREV_TAC `(uA0:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ctm)) (0,64)` THEN
  ABBREV_TAC `(uA1:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ctm)) (64,64)` THEN
  ABBREV_TAC `(uD0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(uD1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(p1:(128)word) = word_pmul (uA0:(64)word) (uD0:(64)word)` THEN
  ABBREV_TAC `(p2:(128)word) = word_pmul (uA1:(64)word) (uD1:(64)word)` THEN
  ABBREV_TAC `(p3:(128)word) =
    word_pmul (word_xor (uA0:(64)word) (uA1:(64)word))
              (word_xor (uD0:(64)word) (uD1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  ABBREV_TAC `(z1:(64)word) = word_subword (p1:(128)word) (0,64)` THEN
  ABBREV_TAC `(z2:(64)word) = word_subword (p1:(128)word) (64,64)` THEN
  ABBREV_TAC `(z3:(64)word) = word_subword (p2:(128)word) (0,64)` THEN
  ABBREV_TAC `(z4:(64)word) = word_subword (p2:(128)word) (64,64)` THEN
  ABBREV_TAC `(z5:(64)word) = word_subword (p3:(128)word) (0,64)` THEN
  ABBREV_TAC `(z6:(64)word) = word_subword (p3:(128)word) (64,64)` THEN
  ABBREV_TAC `(zD:(64)word) =
    word_subword (word_pmul (z1:(64)word) (word 13979173243358019584:(64)word):(128)word)
                 (0,64)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (z2:(64)word)
                (word_xor z5
                (word_xor z3
                (word_xor z1 zD))))
               (word 13979173243358019584:(64)word):(128)word =
     word_pmul (word_xor (z5:(64)word)
                (word_xor z1
                (word_xor z3
                (word_xor zD z2))))
               (word 13979173243358019584:(64)word):(128)word`
    ASSUME_TAC THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
    `qBigP = word_pmul
       (word_xor (z5:(64)word) (word_xor z1 (word_xor z3 (word_xor zD z2))))
       (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC
    `qSmallP = word_pmul (z1:(64)word)
                        (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC `qBigPL = word_subword (qBigP:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qBigPH = word_subword (qBigP:(128)word) (64,64):(64)word` THEN
  ABBREV_TAC `qSmallPH = word_subword (qSmallP:(128)word) (64,64):(64)word` THEN
  BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE];;

(* ------------------------------------------------------------------------- *)
(* SHORT band (1 <= byte_len <= 16): the .less_than_1 single-block tail.       *)
(* ------------------------------------------------------------------------- *)

(* Tail-dispatch cascade for the SHORT band.  After the X5 ushr is reduced to *)
(* `word byte_len` (step 148), the cascade flags are compared against          *)
(* `word byte_len` directly.  For total = byte_len <= 16 every threshold       *)
(* 96..16 falls through (t < byte_len is false), reaching the .less_than_1     *)
(* entry.                                                                       *)
let THREE_SHORT_GT_COND = prove
 (`!byte_len t. byte_len <= 16 /\ t <= 96 ==>
    ((~(val (word_sub (word byte_len:int64) (word t)) = 0) /\
      (ival (word_sub (word byte_len:int64) (word t)) < &0 <=>
       ~(ival (word byte_len:int64) - &t =
         ival (word_sub (word byte_len:int64) (word t)))))
     <=> t < byte_len)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  ASM_SIMP_TAC[IVAL_WORD_SUB_SMALL; NBLOCK_IVAL_WORD_SMALL;
               ARITH_RULE `byte_len <= 16 ==> byte_len < 2 EXP 63`;
               ARITH_RULE `t <= 96 ==> t < 2 EXP 63`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN ASM_INT_ARITH_TAC);;

let THREE_SHORT_GT_COND_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 16 <= t /\ t <= 96 ==>
    ((~(val (word_sub (word byte_len:int64) (word t)) = 0) /\
      (ival (word_sub (word byte_len:int64) (word t)) < &0 <=>
       ~(ival (word byte_len:int64) - &t =
         ival (word_sub (word byte_len:int64) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[THREE_SHORT_GT_COND; ARITH_RULE `16 <= t /\ t <= 96 ==> t <= 96`] THEN
  ASM_ARITH_TAC);;

let SHORT_DCASC96 = prove
 (`byte_len <= 16 ==>
    ((~(val (word_sub (word byte_len:int64) (word 96)) = 0) /\
      (ival (word_sub (word byte_len:int64) (word 96)) < &0 <=>
       ~(ival (word byte_len:int64) - &96 = ival (word_sub (word byte_len:int64) (word 96))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC THREE_SHORT_GT_COND_FALSE THEN ASM_ARITH_TAC);;
let SHORT_DCASC80 = prove
 (`byte_len <= 16 ==>
    ((~(val (word_sub (word byte_len:int64) (word 80)) = 0) /\
      (ival (word_sub (word byte_len:int64) (word 80)) < &0 <=>
       ~(ival (word byte_len:int64) - &80 = ival (word_sub (word byte_len:int64) (word 80))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC THREE_SHORT_GT_COND_FALSE THEN ASM_ARITH_TAC);;
let SHORT_DCASC64 = prove
 (`byte_len <= 16 ==>
    ((~(val (word_sub (word byte_len:int64) (word 64)) = 0) /\
      (ival (word_sub (word byte_len:int64) (word 64)) < &0 <=>
       ~(ival (word byte_len:int64) - &64 = ival (word_sub (word byte_len:int64) (word 64))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC THREE_SHORT_GT_COND_FALSE THEN ASM_ARITH_TAC);;
let SHORT_DCASC48 = prove
 (`byte_len <= 16 ==>
    ((~(val (word_sub (word byte_len:int64) (word 48)) = 0) /\
      (ival (word_sub (word byte_len:int64) (word 48)) < &0 <=>
       ~(ival (word byte_len:int64) - &48 = ival (word_sub (word byte_len:int64) (word 48))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC THREE_SHORT_GT_COND_FALSE THEN ASM_ARITH_TAC);;
let SHORT_DCASC32 = prove
 (`byte_len <= 16 ==>
    ((~(val (word_sub (word byte_len:int64) (word 32)) = 0) /\
      (ival (word_sub (word byte_len:int64) (word 32)) < &0 <=>
       ~(ival (word byte_len:int64) - &32 = ival (word_sub (word byte_len:int64) (word 32))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC THREE_SHORT_GT_COND_FALSE THEN ASM_ARITH_TAC);;
let SHORT_DCASC16 = prove
 (`byte_len <= 16 ==>
    ((~(val (word_sub (word byte_len:int64) (word 16)) = 0) /\
      (ival (word_sub (word byte_len:int64) (word 16)) < &0 <=>
       ~(ival (word byte_len:int64) - &16 = ival (word_sub (word byte_len:int64) (word 16))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC THREE_SHORT_GT_COND_FALSE THEN ASM_ARITH_TAC);;

let THREE_CASCADE_SHORT_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[
      MATCH_MP SHORT_DCASC96 bl16; MATCH_MP SHORT_DCASC80 bl16;
      MATCH_MP SHORT_DCASC64 bl16; MATCH_MP SHORT_DCASC48 bl16;
      MATCH_MP SHORT_DCASC32 bl16; MATCH_MP SHORT_DCASC16 bl16; COND_CLAUSES]) THEN
    ASSUME_TAC bl16
  else NO_TAC);;

let AES256_GCM_THREE_BLOCK_SHORT_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word)
    (pt2:(128)word) (pt3:(128)word) byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,1028) (in_ptr:int64,48) /\
    nonoverlapping (word pc,1028) (out_ptr:int64,48) /\
    nonoverlapping (word pc,1028) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,1028) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,1028) (key_ptr:int64,240) /\
    nonoverlapping (word pc,1028) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,1028) (stackptr:int64,80) /\
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
    nonoverlapping (ivec_ptr,16) (word pc,1028) /\
    nonoverlapping (xi_ptr,16) (word pc,1028) /\
    nonoverlapping (out_ptr,48) (word pc,1028)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_three_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
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
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
             byteswap128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s =
             byteswap128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)))
      (\s. let ct =
             word_xor pt
               (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm = word_and ct mask in
           read PC s = word(pc + 1024) /\
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
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst AES256_GCM_THREE_BLOCK_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-138: prologue + AES rounds for all 3 blocks. *)
  ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--138) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q0 (s:armstate) = (x:int128)`) (concl th)
    then ABBREV_TAC(mk_eq(mk_var("s13",type_of(rand(concl th))), rand(concl th)))
    else NO_TAC) THEN

  (* Step 139 + ABBREV ct + post-AES normalization. *)
  ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [139] THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  ABBREV_TAC `ct = word_xor (word_xor pt s13) rk14:(128)word` THEN
  GCM_NBLOCK_POST_AES_NORMALIZE_TAC THEN

  (* Steps 140-148 + tail dispatch normalization; reduce the X5 ushr. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (140--148) THEN
  GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC THEN
  SUBGOAL_THEN `word_ushr (word (8 * byte_len):int64) 3 = word byte_len`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC; ALL_TAC] THEN

  (* Steps 149-180: the tail-dispatch cascade.  For total = byte_len <= 16,    *)
  (* every cmp/b.gt falls through to the .less_than_1 entry (pc + 844).  The   *)
  (* flags are now over `word byte_len` (the ushr is already reduced), so the  *)
  (* SHORT cascade resolver works over byte_len directly.                       *)
  THREE_CASCADE_SHORT_TAC THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC THEN THREE_CASCADE_SHORT_TAC) (149--180) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 181-208: mask build for the single masked block. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (181--208) THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP ONE_BLOCK_MASK_REG th])) THEN

  (* Steps 209-215: AND_VEC / bif / Karatsuba accumulator.  Abbreviate Q19 to *)
  (* an opaque acc19 BEFORE the final eor3-low so the eor3/ext/rev64 stay      *)
  (* cheap (only-Q19 trick). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (209--215) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q19 (s:armstate) = (x:int128)`) (concl th)
    then ABBREV_TAC(mk_eq(mk_var("acc19",`:int128`), rand(concl th)))
    else NO_TAC) THEN

  (* Steps 216-218: eor3 / ext / rev64 over the opaque acc19. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (216--218) THEN

  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN
  ABBREV_FINAL_XI_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HALFSWAP_JOIN_SELF]) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `acc19:(128)word`
    then RULE_ASSUM_TAC(REWRITE_RULE[SYM th]) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try fst(dest_const(repeat rator (lhs(concl th)))) = "word_join"
        with _ -> false)
    then ASSUME_TAC(REWRITE_RULE[GSYM REVERSEFIELDS8_SUBWORD_HI;
                                 GSYM REVERSEFIELDS8_SUBWORD_LO] th)
    else NO_TAC) THEN

  (* Steps 219-225: ext / rev64 / str / mov / ldp x4; stop at the RET addr. *)
  ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC (219--225) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[ONE_BLOCK_USHR_BYTELEN; ONE_BLOCK_MASK_IDEM] THEN
  CONJ_TAC THENL [GCM_CT_STEP_TAC; GCM_GHASH_STEP_MASKED_TAC_3]);;

(* ------------------------------------------------------------------------- *)
(* MID band (17 <= n <= 32): the .more_than_1 two-block tail (full block 1 +   *)
(* partial block 2, GHASH over [ct1; ctm2]).  Parameterized by byte_len with   *)
(* total = 16 + byte_len (1 <= byte_len <= 16).  Reuses the two-block GHASH    *)
(* machinery for the masked GHASH closure; the cascade/mask helpers below are  *)
(* the analogues of the three-block ones over `word (128 + 8 * byte_len)`.     *)
(* ------------------------------------------------------------------------- *)

let MIDBLOCK_USHR = prove
 (`!byte_len. byte_len <= 16 ==>
     word_ushr (word (128 + 8 * byte_len):int64) 3 = word (16 + byte_len)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `128 + 8 * byte_len = 8 * (16 + byte_len)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC);;

let MIDBLOCK_GT_COND = prove
 (`!byte_len t. byte_len <= 16 /\ t <= 96 ==>
    ((~(val (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word t)) = 0) /\
      (ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word t)) < &0 <=>
       ~(ival (word_ushr (word (128 + 8 * byte_len):int64) 3) - &t =
         ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word t)))))
     <=> t < 16 + byte_len)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MIDBLOCK_USHR] THEN
  REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  ASM_SIMP_TAC[IVAL_WORD_SUB_SMALL; NBLOCK_IVAL_WORD_SMALL;
               ARITH_RULE `byte_len <= 16 ==> 16 + byte_len < 2 EXP 63`;
               ARITH_RULE `t <= 96 ==> t < 2 EXP 63`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LT] THEN
  ASM_INT_ARITH_TAC);;

let MIDBLOCK_GT_COND_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 32 <= t /\ t <= 96 ==>
    ((~(val (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word t)) = 0) /\
      (ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word t)) < &0 <=>
       ~(ival (word_ushr (word (128 + 8 * byte_len):int64) 3) - &t =
         ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MIDBLOCK_GT_COND; ARITH_RULE `32 <= t /\ t <= 96 ==> t <= 96`] THEN
  ASM_ARITH_TAC);;

let MIDBLOCK_GT_COND_TRUE = prove
 (`!byte_len. 1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 16)) = 0) /\
      (ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 16)) < &0 <=>
       ~(ival (word_ushr (word (128 + 8 * byte_len):int64) 3) - &16 =
         ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 16)))))
     <=> T)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MIDBLOCK_GT_COND; ARITH_RULE `16 <= 96`] THEN
  ASM_ARITH_TAC);;

let MIDBLOCK_CASC96 = prove
 (`!byte_len. byte_len <= 16 ==>
    ((~(val (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 96)) = 0) /\
      (ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 96)) < &0 <=>
       ~(ival (word_ushr (word (128 + 8 * byte_len):int64) 3) - &96 =
         ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 96))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MIDBLOCK_GT_COND_FALSE THEN ASM_ARITH_TAC);;
let MIDBLOCK_CASC80 = prove
 (`!byte_len. byte_len <= 16 ==>
    ((~(val (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 80)) = 0) /\
      (ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 80)) < &0 <=>
       ~(ival (word_ushr (word (128 + 8 * byte_len):int64) 3) - &80 =
         ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 80))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MIDBLOCK_GT_COND_FALSE THEN ASM_ARITH_TAC);;
let MIDBLOCK_CASC64 = prove
 (`!byte_len. byte_len <= 16 ==>
    ((~(val (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 64)) = 0) /\
      (ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 64)) < &0 <=>
       ~(ival (word_ushr (word (128 + 8 * byte_len):int64) 3) - &64 =
         ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 64))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MIDBLOCK_GT_COND_FALSE THEN ASM_ARITH_TAC);;
let MIDBLOCK_CASC48 = prove
 (`!byte_len. byte_len <= 16 ==>
    ((~(val (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 48)) = 0) /\
      (ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 48)) < &0 <=>
       ~(ival (word_ushr (word (128 + 8 * byte_len):int64) 3) - &48 =
         ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 48))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MIDBLOCK_GT_COND_FALSE THEN ASM_ARITH_TAC);;
let MIDBLOCK_CASC32 = prove
 (`!byte_len. byte_len <= 16 ==>
    ((~(val (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 32)) = 0) /\
      (ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 32)) < &0 <=>
       ~(ival (word_ushr (word (128 + 8 * byte_len):int64) 3) - &32 =
         ival (word_sub (word_ushr (word (128 + 8 * byte_len):int64) 3) (word 32))))) <=> F)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MIDBLOCK_GT_COND_FALSE THEN ASM_ARITH_TAC);;

let MIDBLOCK_CASCADE_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE[
        MATCH_MP MIDBLOCK_CASC96 bl16; MATCH_MP MIDBLOCK_CASC80 bl16;
        MATCH_MP MIDBLOCK_CASC64 bl16; MATCH_MP MIDBLOCK_CASC48 bl16;
        MATCH_MP MIDBLOCK_CASC32 bl16;
        MATCH_MP MIDBLOCK_GT_COND_TRUE (CONJ bl1 bl16); COND_CLAUSES]) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;

let MIDBLOCK_MASK_REG = prove
 (`!byte_len (b0:int128). 1 <= byte_len /\ byte_len <= 16 ==>
    (word_insert
     ((word_insert (b0:int128)
        (0,64)
        (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
              ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
                ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
         then word 18446744073709551615:int64
         else word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)))):int128)
     (64,64)
     (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
           ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
             ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
        then word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127))
        else word 0:int64)
    : int128)
    = word (2 EXP (8 * byte_len) - 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NBLOCK_WORD_INSERT_BOTH_LANES] THEN
  SPEC_TAC(`byte_len:num`,`byte_len:num`) THEN GEN_TAC THEN
  NBLOCK_MASK_PEEL_TAC 1);;

(* MID GHASH closer: two-block GHASH algebra with the three-block-model        *)
(* final_xi reshape.  The leading folds (ct1, ct2, ctm2, the GHASH_2BLOCK      *)
(* bridge) match the two-block closer; the final_xi handling uses the          *)
(* three-block half-swap reshape (MESON rev8 + WORD_SWAP_HALVES_INVOLUTION +    *)
(* WORD_INSERT_AS_JOIN) since the three-block model yields the clean half-swap  *)
(* final_xi shape `word_subword (word_join (rev8 fx) (rev8 fx)) (64,128)`.      *)
let MID_GHASH_PREFIX =
  REWRITE_TAC[GHASH_POLYVAL_ACC_2; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
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
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm2 = word_and (ct2:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct2:(128)word) = ctm2`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm2" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ctm2:int128`;
     `h:int128`;
     `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`]
    GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_2block_karatsuba; LET_DEF; LET_END_DEF] THEN
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
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR];;

let GCM_3BLOCK_MID_GHASH_STEP_MASKED_TAC =
  MID_GHASH_PREFIX THEN
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ctm2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ctm2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (he0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (he1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
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
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w2lo_l:(64)word) (w1lo_l)) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (w2lo_l)) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w2md_l:(64)word) (word_xor w1md_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w2lo_h (w1lo_h))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w1lo_l (word_xor w2lo_l ((word_subword (qS:(128)word) (0,64))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC] THEN
  BINOP_TAC THENL
   [CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;
    CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC];;

let AES256_GCM_THREE_BLOCK_MID_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word)
    (pt3:(128)word) byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,1028) (in_ptr:int64,48) /\
    nonoverlapping (word pc,1028) (out_ptr:int64,48) /\
    nonoverlapping (word pc,1028) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,1028) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,1028) (key_ptr:int64,240) /\
    nonoverlapping (word pc,1028) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,1028) (stackptr:int64,80) /\
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
    nonoverlapping (ivec_ptr,16) (word pc,1028) /\
    nonoverlapping (xi_ptr,16) (word pc,1028) /\
    nonoverlapping (out_ptr,48) (word pc,1028)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_three_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (128 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = out0 /\
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
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
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
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm2 = word_and ct2 mask in
           read PC s = word(pc + 1024) /\
           read X0 s = word (16 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s =
             word_or ctm2 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ctm2]))
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
              fst AES256_GCM_THREE_BLOCK_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-138: prologue + AES rounds for all 3 blocks. *)
  ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--138) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q0 (s:armstate) = (x:int128)`) (concl th)
    then ABBREV_TAC(mk_eq(mk_var("s13_1",type_of(rand(concl th))), rand(concl th))) else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q1 (s:armstate) = (x:int128)`) (concl th)
    then ABBREV_TAC(mk_eq(mk_var("s13_2",type_of(rand(concl th))), rand(concl th))) else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q2 (s:armstate) = (x:int128)`) (concl th)
    then ABBREV_TAC(mk_eq(mk_var("s13_3",type_of(rand(concl th))), rand(concl th))) else NO_TAC) THEN

  (* Step 139 + ABBREV ct1 + post-AES normalization. *)
  ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [139] THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN
  GCM_NBLOCK_POST_AES_NORMALIZE_TAC THEN

  (* Steps 140-148 + tail-dispatch normalization. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (140--148) THEN
  GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC THEN

  (* Steps 149-178: tail-dispatch cascade.  For total = 16 + byte_len, the     *)
  (* thresholds 96..32 fall through and the cmp #16 b.gt IS taken to the        *)
  (* .more_than_1 two-block entry (pc + 780).  Normalise the 2^64 literal       *)
  (* before the first block-1 ciphertext store.                                 *)
  MIDBLOCK_CASCADE_TAC THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC THEN MIDBLOCK_CASCADE_TAC) (149--178) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 179-195 + ABBREV ct2 (block 2 ciphertext). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (179--195) THEN
  ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN

  (* Steps 196-208: build the partial-block mask register Q0, then collapse it *)
  (* to word (2^(8*byte_len) - 1) before the AND_VEC / bif. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (196--208) THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MIDBLOCK_MASK_REG th])) THEN

  (* Steps 209-232: AND_VEC, bif, the two-block Karatsuba accumulator and       *)
  (* Barrett reduce up to (and including) the ext of the reduced accumulator.   *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (209--232) THEN

  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN
  ABBREV_FINAL_XI_TAC THEN

  (* Steps 233-239: rev64 / str / mov / ldp x4; stop at the RET addr. *)
  ARM_STEPS_TAC AES256_GCM_THREE_BLOCK_EXEC (233--239) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP MIDBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[MIDBLOCK_USHR] THEN

  (* The remaining goals are the block-1 store, the masked block-2 store, and  *)
  (* the GHASH over [ct1; ctm2]. *)
  REPEAT CONJ_TAC THENL [
    GCM_CT1_STEP_TAC;
    SUBGOAL_THEN
      `word_xor pt2
         (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4 rk5 rk6
                           rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) = ct2:(128)word`
      ASSUME_TAC THENL [
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
      REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN;
                  LANE3_BYTES_JOIN_BE; CTR_WORD_INSERT; gcm_ctr_inc] THEN
      AP_TERM_TAC THEN REWRITE_TAC[BYTEREVERSE_JOIN_FOLD];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[NBLOCK_MASK_IDEM];
    GCM_3BLOCK_MID_GHASH_STEP_MASKED_TAC
  ]);;

(* ------------------------------------------------------------------------- *)
(* LONG band (33 <= n <= 48): pure reuse of the full three-block proof at      *)
(* byte_len := n - 32.                                                         *)
(* ------------------------------------------------------------------------- *)

let AES256_GCM_THREE_BLOCK_LONG_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word)
    n stackptr pc.
    33 <= n /\ n <= 48 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,1028) (in_ptr:int64,48) /\
    nonoverlapping (word pc,1028) (out_ptr:int64,48) /\
    nonoverlapping (word pc,1028) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,1028) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,1028) (key_ptr:int64,240) /\
    nonoverlapping (word pc,1028) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,1028) (stackptr:int64,80) /\
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
    nonoverlapping (ivec_ptr,16) (word pc,1028) /\
    nonoverlapping (xi_ptr,16) (word pc,1028) /\
    nonoverlapping (out_ptr,48) (word pc,1028)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_three_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * n); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = out0 /\
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
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
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
           let mask = word (2 EXP (8 * (n - 32)) - 1):(128)word in
           let ctm3 = word_and ct3 mask in
           read PC s = word(pc + 1024) /\
           read X0 s = word n /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s =
             word_or ctm3 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ctm3]))
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
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word (256 + 8 * (n - 32)):int64 = word (8 * n)` ASSUME_TAC THENL
   [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word (32 + (n - 32)):int64 = word n` ASSUME_TAC THENL
   [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`in_ptr:int64`; `out_ptr:int64`; `xi_ptr:int64`; `ivec_ptr:int64`;
     `key_ptr:int64`; `htable_ptr:int64`;
     `pt1:(128)word`; `pt2:(128)word`; `pt3:(128)word`; `out0:(128)word`; `ivec:(128)word`;
     `rk0:(128)word`; `rk1:(128)word`; `rk2:(128)word`; `rk3:(128)word`;
     `rk4:(128)word`; `rk5:(128)word`; `rk6:(128)word`; `rk7:(128)word`;
     `rk8:(128)word`; `rk9:(128)word`; `rk10:(128)word`; `rk11:(128)word`;
     `rk12:(128)word`; `rk13:(128)word`; `rk14:(128)word`;
     `xi:(128)word`; `h:(128)word`; `h1k:(128)word`; `h3k:(128)word`;
     `n - 32`; `stackptr:int64`; `pc:num`] AES256_GCM_THREE_BLOCK_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Frame widening: the SHORT band touches only out_ptr,16 while the combined  *)
(* theorem advertises out_ptr,48.  This subsumption widens it.                 *)
(* ------------------------------------------------------------------------- *)

let FRAME_SUBSUMED_16_48 = prove
 (`(MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [memory :> bytes(out_ptr:int64,16); memory :> bytes(xi_ptr:int64,16); memory :> bytes(ivec_ptr:int64,16)] ,,
    MAYCHANGE [SP] ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes64 stackptr; memory :> bytes64 (word_add stackptr (word 8));
               memory :> bytes64 (word_add stackptr (word 16)); memory :> bytes64 (word_add stackptr (word 24));
               memory :> bytes64 (word_add stackptr (word 32)); memory :> bytes64 (word_add stackptr (word 40));
               memory :> bytes64 (word_add stackptr (word 48)); memory :> bytes64 (word_add stackptr (word 56));
               memory :> bytes64 (word_add stackptr (word 64)); memory :> bytes64 (word_add stackptr (word 72))])
   subsumed
   (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [memory :> bytes(out_ptr:int64,48); memory :> bytes(xi_ptr:int64,16); memory :> bytes(ivec_ptr:int64,16)] ,,
    MAYCHANGE [SP] ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes64 stackptr; memory :> bytes64 (word_add stackptr (word 8));
               memory :> bytes64 (word_add stackptr (word 16)); memory :> bytes64 (word_add stackptr (word 24));
               memory :> bytes64 (word_add stackptr (word 32)); memory :> bytes64 (word_add stackptr (word 40));
               memory :> bytes64 (word_add stackptr (word 48)); memory :> bytes64 (word_add stackptr (word 56));
               memory :> bytes64 (word_add stackptr (word 64)); memory :> bytes64 (word_add stackptr (word 72))])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* COMBINED: 1 <= n <= 48.  Dispatch on (n <= 16) and (n <= 32) to the three  *)
(* band lemmas (the AES-XTS variable-length pattern).                          *)
(* ------------------------------------------------------------------------- *)

let AES256_GCM_THREE_BLOCK_COMBINED_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word)
    n stackptr pc.
    1 <= n /\ n <= 48 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,1028) (in_ptr:int64,48) /\
    nonoverlapping (word pc,1028) (out_ptr:int64,48) /\
    nonoverlapping (word pc,1028) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,1028) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,1028) (key_ptr:int64,240) /\
    nonoverlapping (word pc,1028) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,1028) (stackptr:int64,80) /\
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
    nonoverlapping (ivec_ptr,16) (word pc,1028) /\
    nonoverlapping (xi_ptr,16) (word pc,1028) /\
    nonoverlapping (out_ptr,48) (word pc,1028)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_three_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * n); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128
             (word_add out_ptr (word (if n <= 16 then 0 else if n <= 32 then 16 else 32)))) s = out0 /\
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
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)))
      (\s. read PC s = word(pc + 1024) /\
           read X0 s = word n /\
           (if n <= 16
            then let ct = word_xor pt1
                          (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                            rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
                 let mask = word (2 EXP (8 * n) - 1):(128)word in
                 let ctm = word_and ct mask in
                 read (memory :> bytes128 out_ptr) s =
                   word_or ctm (word_and out0 (word_not mask)) /\
                 read (memory :> bytes128 xi_ptr) s =
                   word_reversefields 8
                     (ghash_polyval_acc h (word_reversefields 8 xi)
                                          [word_reversefields 8 ctm])
            else if n <= 32
            then let ct1 = word_xor pt1
                           (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                             rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
                 let ct2 = word_xor pt2
                           (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3
                                rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
                 let mask = word (2 EXP (8 * (n - 16)) - 1):(128)word in
                 let ctm2 = word_and ct2 mask in
                 read (memory :> bytes128 out_ptr) s = ct1 /\
                 read (memory :> bytes128 (word_add out_ptr (word 16))) s =
                   word_or ctm2 (word_and out0 (word_not mask)) /\
                 read (memory :> bytes128 xi_ptr) s =
                   word_reversefields 8
                     (ghash_polyval_acc h (word_reversefields 8 xi)
                                          [word_reversefields 8 ct1;
                                           word_reversefields 8 ctm2])
            else let ct1 = word_xor pt1
                           (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                             rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
                 let ct2 = word_xor pt2
                           (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3
                                rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
                 let ct3 = word_xor pt3
                           (aes256_block_enc (gcm_ctr_inc (gcm_ctr_inc ivec))
                                rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7 rk8 rk9 rk10 rk11
                                rk12 rk13 rk14) in
                 let mask = word (2 EXP (8 * (n - 32)) - 1):(128)word in
                 let ctm3 = word_and ct3 mask in
                 read (memory :> bytes128 out_ptr) s = ct1 /\
                 read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
                 read (memory :> bytes128 (word_add out_ptr (word 32))) s =
                   word_or ctm3 (word_and out0 (word_not mask)) /\
                 read (memory :> bytes128 xi_ptr) s =
                   word_reversefields 8
                     (ghash_polyval_acc h (word_reversefields 8 xi)
                                          [word_reversefields 8 ct1;
                                           word_reversefields 8 ct2;
                                           word_reversefields 8 ctm3])))
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
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `n <= 16` THENL [
    (* SHORT band: 1 <= n <= 16, widen frame out_ptr,16 -> out_ptr,48. *)
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr:int64,16); memory :> bytes(xi_ptr:int64,16); memory :> bytes(ivec_ptr:int64,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr; memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16)); memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32)); memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48)); memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64)); memory :> bytes64 (word_add stackptr (word 72))]` THEN
    REWRITE_TAC[FRAME_SUBSUMED_16_48] THEN
    MP_TAC(REWRITE_RULE[WORD_ADD_0](ISPECL
      [`in_ptr:int64`; `out_ptr:int64`; `xi_ptr:int64`; `ivec_ptr:int64`;
       `key_ptr:int64`; `htable_ptr:int64`;
       `pt1:(128)word`; `out0:(128)word`; `ivec:(128)word`;
       `rk0:(128)word`; `rk1:(128)word`; `rk2:(128)word`; `rk3:(128)word`;
       `rk4:(128)word`; `rk5:(128)word`; `rk6:(128)word`; `rk7:(128)word`;
       `rk8:(128)word`; `rk9:(128)word`; `rk10:(128)word`; `rk11:(128)word`;
       `rk12:(128)word`; `rk13:(128)word`; `rk14:(128)word`;
       `xi:(128)word`; `h:(128)word`; `h1k:(128)word`; `h3k:(128)word`;
       `pt2:(128)word`; `pt3:(128)word`; `n:num`; `stackptr:int64`; `pc:num`]
      AES256_GCM_THREE_BLOCK_SHORT_CORRECT)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[];
    ASM_CASES_TAC `n <= 32` THENL [
      (* MID band: 17 <= n <= 32, frame already out_ptr,48. *)
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `word (if n <= 16 then 0 else if n <= 32 then 16 else 32):int64 = word 16` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `word (128 + 8 * (n - 16)):int64 = word (8 * n)` ASSUME_TAC THENL
       [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `word (16 + (n - 16)):int64 = word n` ASSUME_TAC THENL
       [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL
        [`in_ptr:int64`; `out_ptr:int64`; `xi_ptr:int64`; `ivec_ptr:int64`;
         `key_ptr:int64`; `htable_ptr:int64`;
         `pt1:(128)word`; `pt2:(128)word`; `out0:(128)word`; `ivec:(128)word`;
         `rk0:(128)word`; `rk1:(128)word`; `rk2:(128)word`; `rk3:(128)word`;
         `rk4:(128)word`; `rk5:(128)word`; `rk6:(128)word`; `rk7:(128)word`;
         `rk8:(128)word`; `rk9:(128)word`; `rk10:(128)word`; `rk11:(128)word`;
         `rk12:(128)word`; `rk13:(128)word`; `rk14:(128)word`;
         `xi:(128)word`; `h:(128)word`; `h1k:(128)word`; `h3k:(128)word`;
         `pt3:(128)word`; `n - 16`; `stackptr:int64`; `pc:num`]
        AES256_GCM_THREE_BLOCK_MID_CORRECT) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ADD_0];
      (* LONG band: 33 <= n <= 48, frame already out_ptr,48. *)
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `word (if n <= 16 then 0 else if n <= 32 then 16 else 32):int64 = word 32` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL
        [`in_ptr:int64`; `out_ptr:int64`; `xi_ptr:int64`; `ivec_ptr:int64`;
         `key_ptr:int64`; `htable_ptr:int64`;
         `pt1:(128)word`; `pt2:(128)word`; `pt3:(128)word`; `out0:(128)word`; `ivec:(128)word`;
         `rk0:(128)word`; `rk1:(128)word`; `rk2:(128)word`; `rk3:(128)word`;
         `rk4:(128)word`; `rk5:(128)word`; `rk6:(128)word`; `rk7:(128)word`;
         `rk8:(128)word`; `rk9:(128)word`; `rk10:(128)word`; `rk11:(128)word`;
         `rk12:(128)word`; `rk13:(128)word`; `rk14:(128)word`;
         `xi:(128)word`; `h:(128)word`; `h1k:(128)word`; `h3k:(128)word`;
         `n:num`; `stackptr:int64`; `pc:num`]
        AES256_GCM_THREE_BLOCK_LONG_CORRECT) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ADD_0]
    ]
  ]);;
