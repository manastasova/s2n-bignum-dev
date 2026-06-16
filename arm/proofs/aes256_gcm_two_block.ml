(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* aes256_gcm_two_block.ml                                                 *)
(*                                                                         *)
(* The 2-block AES-256-GCM separate-blocks encrypt proof — the N=2         *)
(* instance of the generic N-block framework. STRUCTURALLY MIRRORS         *)
(* aes256_gcm_three_block.ml, scaled down to N=2.                          *)
(*                                                                         *)
(* PER-N CONTENT (only piece in this file):                                *)
(*   - Machine code blob (aes256_gcm_two_block_mc) and EXEC                *)
(*   - ghash_2block_karatsuba (assembly-shape spec)                        *)
(*   - GHASH_2BLOCK_AS_NBLOCK (compatibility with ghash_Nblock_karatsuba)  *)
(*   - GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC — derived from inductive bridge *)
(*   - GCM_2BLOCK_GHASH_STEP_TAC + main theorem AES256_GCM_TWO_BLOCK_CORRECT *)
(* ========================================================================= *)

(* All dependencies (base/AES/ghash_spec/aesgcm helpers) are pulled in       *)
(* transitively by the N-block framework file below.                          *)
needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;
(* The 1-16 byte (single-block) tail of this routine is byte-identical to the
   one-block routine's algorithm, so the combined 1-32 byte proof below reuses
   the one-block masking/GHASH closers (ONE_BLOCK_MASK_REG, GCM_CT_STEP_TAC,
   GCM_GHASH_STEP_MASKED_TAC, ...) directly. *)

(* ========================================================================= *)
(*  PER-N: 2-block assembly-shape spec ghash_2block_karatsuba.               *)
(* ========================================================================= *)


(* The Karatsuba bridge (ghash_2block_karatsuba <-> polyval_reduce_prop3) and
   the GHASH / mask / branch closers used below are shared with the other
   block-count proofs and live in this utils file (pure algebra). *)
needs "arm/proofs/utils/gcm_one_block_closers.ml";;
needs "arm/proofs/utils/gcm_two_block_closers.ml";;
needs "arm/proofs/utils/gcm_three_block_closers.ml";;

let aes256_gcm_two_block_mc = define_assert_from_elf
  "aes256_gcm_two_block_mc"
  "arm/aes-gcm/aes256_gcm_two_block.o"
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
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x5400006c;       (* arm_BGT (word 12) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x14000011;       (* arm_B (word 68) *)
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

let AES256_GCM_TWO_BLOCK_EXEC =
  ARM_MK_EXEC_RULE aes256_gcm_two_block_mc;;

(* ========================================================================= *)
(* PER-BLOCK CIPHERTEXT CLOSURES (instances of GCM_NBLOCK_CT_STEP_TAC for     *)
(* N=2). Block 1 has ivec_1 = ivec (no LANE/CTR chain); block 2 has         *)
(* ivec_2 = gcm_ctr_inc ivec (LANE/CTR/BYTEREVERSE chain).                    *)
(* ========================================================================= *)

let GCM_CT1_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 2 1;;
let GCM_CT2_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 2 2;;

(* ========================================================================= *)

let AES256_GCM_TWO_BLOCK_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,656) (in_ptr:int64,32) /\
    nonoverlapping (word pc,656) (out_ptr:int64,32) /\
    nonoverlapping (word pc,656) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,656) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,656) (key_ptr:int64,240) /\
    nonoverlapping (word pc,656) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,656) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,32) (out_ptr,32) /\
    nonoverlapping (in_ptr,32) (xi_ptr,16) /\
    nonoverlapping (in_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,32) (xi_ptr,16) /\
    nonoverlapping (out_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,32) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,32) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,32) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,32) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,656) /\
    nonoverlapping (xi_ptr,16) (word pc,656) /\
    nonoverlapping (out_ptr,32) (word pc,656)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_two_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (128 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h))
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
           read PC s = word(pc + 652) /\
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
       MAYCHANGE [memory :> bytes(out_ptr,32);
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
              fst AES256_GCM_TWO_BLOCK_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue *)
  ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-92: AES rounds for both blocks *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--92) THEN

  (* Abbreviate s13_1 (Q0) and s13_2 (Q1) *)
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

  (* Step 93 + ABBREV ct1 + post-AES normalization *)
  ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [93] THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN
  GCM_NBLOCK_POST_AES_NORMALIZE_TAC THEN

  (* Steps 94-99 + tail-dispatch normalization *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (94--99) THEN
  GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC THEN

  (* Step 100: the b.gt cascade branch.  Stepping it leaves the PC as an
     if-then-else on byte_len; resolve it: for a partial final block
     (1 <= byte_len <= 16) the total length 16+byte_len exceeds 16, so the
     branch is taken and the PC becomes the definite in-cascade target. *)
  ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [100] THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TWOBLOCK_BRANCH th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 101-110 + ABBREV ct2 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (101--110) THEN
  ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN

  (* Steps 111-135: 2-block Karatsuba up to the partial-block mask build. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (111--135) THEN

  (* Collapse the data-dependent partial-block mask register to
     word (2^(8*byte_len) - 1) before the bif/masked store. *)
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TWOBLOCK_MASK_REG th])) THEN

  (* Steps 136-154: bif (masked store fixup), masked-block GHASH + reduction. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (136--154) THEN

  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN

  (* Abbreviate Q19 as `final_xi` BEFORE step 155's REV64 *)
  ABBREV_FINAL_XI_TAC THEN

  (* Steps 155-161: rev64 v19, st1, epilogue (stop before the RET). *)
  ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC (155--161) THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN
  (* Collapse the mask register that survives into the ciphertext store goal,
     and reduce X0 = word(16+byte_len). *)
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP TWOBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[TWOBLOCK_USHR] THEN

  (* After ASM_SIMP discharges the PC and X0 conjuncts the remaining goals are
     the ct1 store, the masked ct2 store, and the GHASH over [ct1; ctm2]. *)
  REPEAT CONJ_TAC THENL [
    (* ct1 store (full block) *)
    GCM_CT1_STEP_TAC;
    (* masked ct2 store: establish word_xor pt2 aes = ct2, fold it on the spec
       side and collapse the bif's double mask (NBLOCK_MASK_IDEM). *)
    SUBGOAL_THEN
      `word_xor pt2
         (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4 rk5 rk6
                           rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) = ct2:(128)word`
      ASSUME_TAC THENL [
      EXPAND_TAC "ct2" THEN
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
    (* GHASH over [ct1; ctm2] *)
    GCM_2BLOCK_GHASH_STEP_MASKED_TAC
  ]);;

(* ========================================================================= *)
(*       VARIABLE-LENGTH (1-32 byte) COMBINED CORRECTNESS                     *)
(*                                                                           *)
(* The routine branches internally on the input length (cmp x5,#16):         *)
(*   * total <= 16 bytes  -> the `.L256_enc_blocks_less_than_1` tail, which   *)
(*                           is byte-identical to the one-block algorithm     *)
(*                           (one masked block stored, single-block GHASH);   *)
(*   * 17 <= total <= 32  -> the two-block path proved above.                 *)
(* Following the upstream AES-XTS design, we prove one band lemma per length  *)
(* range (both against this same machine code) and dispatch between them in   *)
(* the combined theorem with ASM_CASES_TAC on the length.                     *)
(* ========================================================================= *)

(* --- Helper arithmetic for the short-path branch resolution --------------- *)

(* ival of the wrapping subtraction word(n) - word(16) for n <= 16. *)
let IVAL_SUB_AUX = prove
 (`!n. n <= 16 ==> ival (word_sub (word n:int64) (word 16)) = &n - &16`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word n:int64) (word 16) = iword(&n - &16)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `n:num` INT_POS) THEN ASM_ARITH_TAC);;

(* The wrapping subtraction is zero exactly when n = 16. *)
let VAL_SUB_AUX = prove
 (`!n. n <= 16 ==> (val (word_sub (word n:int64) (word 16)) = 0 <=> n = 16)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64] THEN
  SUBGOAL_THEN `val(word n:int64) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word 16:int64) = 16` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* For a total of n <= 16 bytes the `cmp x5,#16; b.gt` is NOT taken, so the
   cascade falls through to pc+400 (the `b .L256_enc_blocks_less_than_1`). *)
let TWOBLOCK_BRANCH_SHORT = prove
 (`!n pc. 1 <= n /\ n <= 16 ==>
    (if ~(val (word_sub (word n:int64) (word 16)) = 0) /\
        (ival (word_sub (word n:int64) (word 16)) < &0 <=>
         ~(ival (word n:int64) - &16 = ival (word_sub (word n:int64) (word 16))))
     then word (pc + 408):int64
     else word (pc + 400)) = word (pc + 400)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival (word n:int64) = &n` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `n:num` IVAL_SUB_AUX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `n:num` VAL_SUB_AUX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[INT_SUB_REFL] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[INT_ARITH `&n - &16 < &0 <=> &n < &16`; INT_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;

(* The combined MAYCHANGE frame widens the short path's out_ptr footprint from
   16 to 32 bytes; this subsumption discharges that widening. *)
let FRAME_SUBSUMED_16_32 = prove
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
       MAYCHANGE [memory :> bytes(out_ptr:int64,32); memory :> bytes(xi_ptr:int64,16); memory :> bytes(ivec_ptr:int64,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr; memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16)); memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32)); memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48)); memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64)); memory :> bytes64 (word_add stackptr (word 72))])`,
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   SUBSUMED_MAYCHANGE_TAC);;

(* ----------------------------------------------------------------------- *)
(* SHORT band: 1 <= n <= 16.  cmp x5,#16 falls through to the              *)
(* `.L256_enc_blocks_less_than_1` single-block masking tail.  This is the  *)
(* one-block algorithm embedded in the two-block binary, so the proof      *)
(* reuses the one-block masking helpers and GHASH closer verbatim.         *)
(* ----------------------------------------------------------------------- *)

let AES256_GCM_TWO_BLOCK_SHORT_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word)
    (pt2:(128)word) byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,656) (in_ptr:int64,32) /\
    nonoverlapping (word pc,656) (out_ptr:int64,32) /\
    nonoverlapping (word pc,656) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,656) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,656) (key_ptr:int64,240) /\
    nonoverlapping (word pc,656) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,656) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,32) (out_ptr,32) /\
    nonoverlapping (in_ptr,32) (xi_ptr,16) /\
    nonoverlapping (in_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,32) (xi_ptr,16) /\
    nonoverlapping (out_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,32) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,32) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,32) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,32) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,656) /\
    nonoverlapping (xi_ptr,16) (word pc,656) /\
    nonoverlapping (out_ptr,32) (word pc,656)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_two_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h))
      (\s. let ct = word_xor pt
                     (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                       rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm = word_and ct mask in
           read PC s = word(pc + 652) /\
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
              fst AES256_GCM_TWO_BLOCK_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue (shared across all N). *)
  ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-92: AES rounds for both blocks (block 2's keystream is computed
     but, on the short path, never stored or GHASHed). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--92) THEN

  (* Abbreviate the block-1 AES output as `s13`/`ct`, matching the one-block
     proof's names so its closers apply verbatim. *)
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q0 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("s13",type_of rhs), rhs))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q1 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("s13_2",type_of rhs), rhs))
    else NO_TAC) THEN

  ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [93] THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  ABBREV_TAC `ct = word_xor (word_xor pt s13) rk14:(128)word` THEN
  GCM_NBLOCK_POST_AES_NORMALIZE_TAC THEN

  (* Steps 94-99 + tail-dispatch normalization. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (94--99) THEN
  GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC THEN

  (* Reduce the returned byte length x9 = (8*byte_len)>>3 to word byte_len. *)
  SUBGOAL_THEN `word_ushr (word (8 * byte_len):int64) 3 = word byte_len` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_ushr (word (8 * byte_len):int64) 3 = word byte_len`]) THEN

  (* Step 100: the b.gt cascade branch is NOT taken (total <= 16), so the PC
     falls through to pc+400. *)
  ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [100] THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TWOBLOCK_BRANCH_SHORT th])) THEN

  (* Steps 101-102: sub v30 + `b .L256_enc_blocks_less_than_1` jump to pc+472. *)
  ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC (101--102) THEN

  (* Steps 103-116: build the partial-block mask register (Q0). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (103--116) THEN

  (* Collapse the data-dependent mask register to word (2^(8*byte_len)-1). *)
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP ONE_BLOCK_MASK_REG th])) THEN

  (* The counter store `str q30,[x16]` needs the nonoverlapping facts in their
     `2 EXP 64` form (the tail-dispatch normalization left them as a literal). *)
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 117-139: mask the block, bif fixup, counter+block stores, GHASH
     Karatsuba up to the final low-fold EOR3 in Q19. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (117--139) THEN

  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN
  ABBREV_FINAL_XI_TAC THEN

  (* Steps 140-147: EXT, REV64, ST1, MOV, LDP*4 (stop before the RET). *)
  ARM_STEPS_TAC AES256_GCM_TWO_BLOCK_EXEC (140--147) THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[ONE_BLOCK_USHR_BYTELEN; ONE_BLOCK_MASK_IDEM] THEN
  CONJ_TAC THENL [
    GCM_CT_STEP_TAC;
    GCM_GHASH_STEP_MASKED_TAC
  ]);;

(* ----------------------------------------------------------------------- *)
(* LONG band: 17 <= n <= 32.  cmp x5,#16 takes b.gt into the two-block      *)
(* path; this is exactly AES256_GCM_TWO_BLOCK_CORRECT instantiated at       *)
(* byte_len := n - 16 (the partial-final-block size), bridged via the       *)
(* arithmetic identities 8*n = 128 + 8*(n-16) and 16 + (n-16) = n.          *)
(* ----------------------------------------------------------------------- *)

let AES256_GCM_TWO_BLOCK_LONG_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word)
    n stackptr pc.
    17 <= n /\ n <= 32 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,656) (in_ptr:int64,32) /\
    nonoverlapping (word pc,656) (out_ptr:int64,32) /\
    nonoverlapping (word pc,656) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,656) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,656) (key_ptr:int64,240) /\
    nonoverlapping (word pc,656) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,656) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,32) (out_ptr,32) /\
    nonoverlapping (in_ptr,32) (xi_ptr,16) /\
    nonoverlapping (in_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,32) (xi_ptr,16) /\
    nonoverlapping (out_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,32) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,32) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,32) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,32) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,656) /\
    nonoverlapping (xi_ptr,16) (word pc,656) /\
    nonoverlapping (out_ptr,32) (word pc,656)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_two_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * n); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h))
      (\s. let ct1 =
             word_xor pt1
               (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct2 =
             word_xor pt2
               (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4
                                 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12
                                 rk13 rk14) in
           let mask = word (2 EXP (8 * (n - 16)) - 1):(128)word in
           let ctm2 = word_and ct2 mask in
           read PC s = word(pc + 652) /\
           read X0 s = word n /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s =
             word_or ctm2 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ctm2]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,32);
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
     `xi:(128)word`; `h:(128)word`; `h1k:(128)word`;
     `n - 16`; `stackptr:int64`; `pc:num`] AES256_GCM_TWO_BLOCK_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ----------------------------------------------------------------------- *)
(* COMBINED: 1 <= n <= 32.  Dispatch on (n <= 16) to the two band lemmas    *)
(* (the AES-XTS variable-length pattern).                                   *)
(* ----------------------------------------------------------------------- *)

let AES256_GCM_TWO_BLOCK_COMBINED_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word)
    n stackptr pc.
    1 <= n /\ n <= 32 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,656) (in_ptr:int64,32) /\
    nonoverlapping (word pc,656) (out_ptr:int64,32) /\
    nonoverlapping (word pc,656) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,656) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,656) (key_ptr:int64,240) /\
    nonoverlapping (word pc,656) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,656) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,32) (out_ptr,32) /\
    nonoverlapping (in_ptr,32) (xi_ptr,16) /\
    nonoverlapping (in_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,32) (xi_ptr,16) /\
    nonoverlapping (out_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,32) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,32) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,32) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,32) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,656) /\
    nonoverlapping (xi_ptr,16) (word pc,656) /\
    nonoverlapping (out_ptr,32) (word pc,656)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_two_block_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * n); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128
             (word_add out_ptr (word (if n <= 16 then 0 else 16)))) s = out0 /\
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
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h))
      (\s. read PC s = word(pc + 652) /\
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
            else let ct1 = word_xor pt1
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
                                           word_reversefields 8 ctm2])))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,32);
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
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `n <= 16` THENL
   [(* SHORT band: 1 <= n <= 16, widen frame from out_ptr,16 to out_ptr,32. *)
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
    REWRITE_TAC[FRAME_SUBSUMED_16_32] THEN
    MP_TAC(REWRITE_RULE[WORD_ADD_0](ISPECL
      [`in_ptr:int64`; `out_ptr:int64`; `xi_ptr:int64`; `ivec_ptr:int64`;
       `key_ptr:int64`; `htable_ptr:int64`;
       `pt1:(128)word`; `out0:(128)word`; `ivec:(128)word`;
       `rk0:(128)word`; `rk1:(128)word`; `rk2:(128)word`; `rk3:(128)word`;
       `rk4:(128)word`; `rk5:(128)word`; `rk6:(128)word`; `rk7:(128)word`;
       `rk8:(128)word`; `rk9:(128)word`; `rk10:(128)word`; `rk11:(128)word`;
       `rk12:(128)word`; `rk13:(128)word`; `rk14:(128)word`;
       `xi:(128)word`; `h:(128)word`; `h1k:(128)word`;
       `pt2:(128)word`; `n:num`; `stackptr:int64`; `pc:num`]
      AES256_GCM_TWO_BLOCK_SHORT_CORRECT)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(CONV_RULE(ONCE_DEPTH_CONV let_CONV) th)) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];
    (* LONG band: 17 <= n <= 32, frame already out_ptr,32. *)
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
      [`in_ptr:int64`; `out_ptr:int64`; `xi_ptr:int64`; `ivec_ptr:int64`;
       `key_ptr:int64`; `htable_ptr:int64`;
       `pt1:(128)word`; `pt2:(128)word`; `out0:(128)word`; `ivec:(128)word`;
       `rk0:(128)word`; `rk1:(128)word`; `rk2:(128)word`; `rk3:(128)word`;
       `rk4:(128)word`; `rk5:(128)word`; `rk6:(128)word`; `rk7:(128)word`;
       `rk8:(128)word`; `rk9:(128)word`; `rk10:(128)word`; `rk11:(128)word`;
       `rk12:(128)word`; `rk13:(128)word`; `rk14:(128)word`;
       `xi:(128)word`; `h:(128)word`; `h1k:(128)word`;
       `n:num`; `stackptr:int64`; `pc:num`]
      AES256_GCM_TWO_BLOCK_LONG_CORRECT) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> MP_TAC th)] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]]);;



