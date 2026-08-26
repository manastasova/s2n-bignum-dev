(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* GCM_INIT_V8: expand the GHASH hash key H into the PMULL/v8 power table.    *)
(* Correctness against the POLYVAL/GHASH algebraic spec in                    *)
(* common/polyval_ghash.ml.  X0 = Htable (192 bytes written), X1 = H.         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/polyval_ghash.ml";;
needs "common/karatsuba_pmul.ml";;      (* PMUL_KARATSUBA; ~0.5s on top of the above *)

(**** print_literal_from_elf "arm/gcm/gcm_init_v8.o";;
 ****)

let gcm_init_v8_mc = define_assert_from_elf
 "gcm_init_v8_mc" "arm/gcm/gcm_init_v8.o"
[
  0x4c407c31;       (* arm_LDR Q17 X1 No_Offset *)
  0x4f07e433;       (* arm_MOVI Q19 (word 16276538888567251425) *)
  0x4f795673;       (* arm_SHL_VEC Q19 Q19 57 64 128 *)
  0x6e114223;       (* arm_EXT Q3 Q17 Q17 64 *)
  0x6f410672;       (* arm_USHR_VEC Q18 Q19 63 64 128 *)
  0x4e0c0631;       (* arm_DUP_ELEM Q17 Q17 32 128 1 *)
  0x6e134250;       (* arm_EXT Q16 Q18 Q19 64 *)
  0x6f410472;       (* arm_USHR_VEC Q18 Q3 63 64 128 *)
  0x4f210631;       (* arm_SSHR_VEC Q17 Q17 31 32 128 *)
  0x4e301e52;       (* arm_AND_VEC Q18 Q18 Q16 128 *)
  0x4f415463;       (* arm_SHL_VEC Q3 Q3 1 64 128 *)
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0x4e311e10;       (* arm_AND_VEC Q16 Q16 Q17 128 *)
  0x4eb21c63;       (* arm_ORR_VEC Q3 Q3 Q18 128 *)
  0x6e301c74;       (* arm_EOR_VEC Q20 Q3 Q16 128 *)
  0x6e144294;       (* arm_EXT Q20 Q20 Q20 64 *)
  0x4c9f7c14;       (* arm_STR Q20 X0 (Postimmediate_Offset (word 16)) *)
  0x6e144290;       (* arm_EXT Q16 Q20 Q20 64 *)
  0x4ef4e280;       (* arm_PMULL2_VEC Q0 Q20 Q20 64 *)
  0x6e341e10;       (* arm_EOR_VEC Q16 Q16 Q20 128 *)
  0x0ef4e282;       (* arm_PMULL_VEC Q2 Q20 Q20 64 *)
  0x0ef0e201;       (* arm_PMULL_VEC Q1 Q16 Q16 64 *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c11;       (* arm_EOR_VEC Q17 Q0 Q18 128 *)
  0x6e114236;       (* arm_EXT Q22 Q17 Q17 64 *)
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e114215;       (* arm_EXT Q21 Q16 Q17 64 *)
  0x4c9f7c15;       (* arm_STR Q21 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f7c16;       (* arm_STR Q22 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef6e280;       (* arm_PMULL2_VEC Q0 Q20 Q22 64 *)
  0x4ef6e2c5;       (* arm_PMULL2_VEC Q5 Q22 Q22 64 *)
  0x0ef6e282;       (* arm_PMULL_VEC Q2 Q20 Q22 64 *)
  0x0ef6e2c7;       (* arm_PMULL_VEC Q7 Q22 Q22 64 *)
  0x0ef1e201;       (* arm_PMULL_VEC Q1 Q16 Q17 64 *)
  0x0ef1e226;       (* arm_PMULL_VEC Q6 Q17 Q17 64 *)
  0x6e024010;       (* arm_EXT Q16 Q0 Q2 64 *)
  0x6e0740b1;       (* arm_EXT Q17 Q5 Q7 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e271ca4;       (* arm_EOR_VEC Q4 Q5 Q7 128 *)
  0x6e311cc6;       (* arm_EOR_VEC Q6 Q6 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e241cc6;       (* arm_EOR_VEC Q6 Q6 Q4 128 *)
  0x0ef3e0a4;       (* arm_PMULL_VEC Q4 Q5 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e0844c7;       (* arm_INS Q7 Q6 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e1804a6;       (* arm_INS Q6 Q5 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e241cc5;       (* arm_EOR_VEC Q5 Q6 Q4 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x6e0540a4;       (* arm_EXT Q4 Q5 Q5 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x0ef3e0a5;       (* arm_PMULL_VEC Q5 Q5 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 128 *)
  0x6e321c10;       (* arm_EOR_VEC Q16 Q0 Q18 128 *)
  0x6e241cb1;       (* arm_EOR_VEC Q17 Q5 Q4 128 *)
  0x6e104217;       (* arm_EXT Q23 Q16 Q16 64 *)
  0x6e114239;       (* arm_EXT Q25 Q17 Q17 64 *)
  0x6e1642d2;       (* arm_EXT Q18 Q22 Q22 64 *)
  0x6e371e10;       (* arm_EOR_VEC Q16 Q16 Q23 128 *)
  0x6e391e31;       (* arm_EOR_VEC Q17 Q17 Q25 128 *)
  0x6e361e52;       (* arm_EOR_VEC Q18 Q18 Q22 128 *)
  0x6e114218;       (* arm_EXT Q24 Q16 Q17 64 *)
  0x4c9f6c17;       (* arm_STP3 Q23 Q24 Q25 X0 (Postimmediate_Offset (word 48)) *)
  0x4ef7e2c0;       (* arm_PMULL2_VEC Q0 Q22 Q23 64 *)
  0x4ef7e2e5;       (* arm_PMULL2_VEC Q5 Q23 Q23 64 *)
  0x0ef7e2c2;       (* arm_PMULL_VEC Q2 Q22 Q23 64 *)
  0x0ef7e2e7;       (* arm_PMULL_VEC Q7 Q23 Q23 64 *)
  0x0ef2e201;       (* arm_PMULL_VEC Q1 Q16 Q18 64 *)
  0x0ef0e206;       (* arm_PMULL_VEC Q6 Q16 Q16 64 *)
  0x6e024010;       (* arm_EXT Q16 Q0 Q2 64 *)
  0x6e0740b1;       (* arm_EXT Q17 Q5 Q7 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e271ca4;       (* arm_EOR_VEC Q4 Q5 Q7 128 *)
  0x6e311cc6;       (* arm_EOR_VEC Q6 Q6 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e241cc6;       (* arm_EOR_VEC Q6 Q6 Q4 128 *)
  0x0ef3e0a4;       (* arm_PMULL_VEC Q4 Q5 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e0844c7;       (* arm_INS Q7 Q6 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e1804a6;       (* arm_INS Q6 Q5 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e241cc5;       (* arm_EOR_VEC Q5 Q6 Q4 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x6e0540a4;       (* arm_EXT Q4 Q5 Q5 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x0ef3e0a5;       (* arm_PMULL_VEC Q5 Q5 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 128 *)
  0x6e321c10;       (* arm_EOR_VEC Q16 Q0 Q18 128 *)
  0x6e241cb1;       (* arm_EOR_VEC Q17 Q5 Q4 128 *)
  0x6e10421a;       (* arm_EXT Q26 Q16 Q16 64 *)
  0x6e11423c;       (* arm_EXT Q28 Q17 Q17 64 *)
  0x6e1642d2;       (* arm_EXT Q18 Q22 Q22 64 *)
  0x6e3a1e10;       (* arm_EOR_VEC Q16 Q16 Q26 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e361e52;       (* arm_EOR_VEC Q18 Q18 Q22 128 *)
  0x6e11421b;       (* arm_EXT Q27 Q16 Q17 64 *)
  0x4c9f6c1a;       (* arm_STP3 Q26 Q27 Q28 X0 (Postimmediate_Offset (word 48)) *)
  0x4efae2c0;       (* arm_PMULL2_VEC Q0 Q22 Q26 64 *)
  0x4efce2c5;       (* arm_PMULL2_VEC Q5 Q22 Q28 64 *)
  0x0efae2c2;       (* arm_PMULL_VEC Q2 Q22 Q26 64 *)
  0x0efce2c7;       (* arm_PMULL_VEC Q7 Q22 Q28 64 *)
  0x0ef2e201;       (* arm_PMULL_VEC Q1 Q16 Q18 64 *)
  0x0ef2e226;       (* arm_PMULL_VEC Q6 Q17 Q18 64 *)
  0x6e024010;       (* arm_EXT Q16 Q0 Q2 64 *)
  0x6e0740b1;       (* arm_EXT Q17 Q5 Q7 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e301c21;       (* arm_EOR_VEC Q1 Q1 Q16 128 *)
  0x6e271ca4;       (* arm_EOR_VEC Q4 Q5 Q7 128 *)
  0x6e311cc6;       (* arm_EOR_VEC Q6 Q6 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e241cc6;       (* arm_EOR_VEC Q6 Q6 Q4 128 *)
  0x0ef3e0a4;       (* arm_PMULL_VEC Q4 Q5 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e0844c7;       (* arm_INS Q7 Q6 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e1804a6;       (* arm_INS Q6 Q5 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e241cc5;       (* arm_EOR_VEC Q5 Q6 Q4 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x6e0540a4;       (* arm_EXT Q4 Q5 Q5 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x0ef3e0a5;       (* arm_PMULL_VEC Q5 Q5 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e271c84;       (* arm_EOR_VEC Q4 Q4 Q7 128 *)
  0x6e321c10;       (* arm_EOR_VEC Q16 Q0 Q18 128 *)
  0x6e241cb1;       (* arm_EOR_VEC Q17 Q5 Q4 128 *)
  0x6e10421d;       (* arm_EXT Q29 Q16 Q16 64 *)
  0x6e11423f;       (* arm_EXT Q31 Q17 Q17 64 *)
  0x6e3d1e10;       (* arm_EOR_VEC Q16 Q16 Q29 128 *)
  0x6e3f1e31;       (* arm_EOR_VEC Q17 Q17 Q31 128 *)
  0x6e11421e;       (* arm_EXT Q30 Q16 Q17 64 *)
  0x4c006c1d;       (* arm_STP3 Q29 Q30 Q31 X0 No_Offset *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let GCM_INIT_V8_EXEC = ARM_MK_EXEC_RULE gcm_init_v8_mc;;

(* ========================================================================= *)
(* MACHINE CHECK for the human-approved htable_mem mid-slot orientation fix.  *)
(*                                                                            *)
(* The four packed-mid slots of `htable_mem` (common/polyval_ghash.ml) were   *)
(* corrected 2026-08-26 to store the LOWER power's karatsuba_mid in the LOW    *)
(* 64 bits and the HIGHER power's in the HIGH 64 bits, matching REF_MID        *)
(* (tests/ref_gcm_init.c:177-178, verified byte-for-byte vs. real assembly     *)
(* over 2000 inputs).  This lemma makes that orientation an explicit,          *)
(* machine-checked claim about each slot's LOW/HIGH lanes rather than an       *)
(* implicit reading of HOL's `word_join` argument order.                       *)
(* ========================================================================= *)

let HTABLE_MEM_MID_LANES = prove
 (`!h:int128. !ptr:int64. !s:armstate.
    htable_mem h ptr s
    ==> word_subword
          (read (memory :> bytes128 (word_add ptr (word 16))) s) (0,64):64 word =
          karatsuba_mid(h_power h 0) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 16))) s) (64,64):64 word =
          karatsuba_mid(h_power h 1) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 64))) s) (0,64):64 word =
          karatsuba_mid(h_power h 2) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 64))) s) (64,64):64 word =
          karatsuba_mid(h_power h 3) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 112))) s) (0,64):64 word =
          karatsuba_mid(h_power h 4) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 112))) s) (64,64):64 word =
          karatsuba_mid(h_power h 5) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 160))) s) (0,64):64 word =
          karatsuba_mid(h_power h 6) /\
        word_subword
          (read (memory :> bytes128 (word_add ptr (word 160))) s) (64,64):64 word =
          karatsuba_mid(h_power h 7)`,
  REWRITE_TAC[htable_mem] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST);;

(* Concrete-byte KAT (the check that would have caught the original error):   *)
(* at the fixed "ByteSwap" hash key H_mem = 0x0807..0102..08 (from            *)
(* tests/ref_gcm_init.c gcm_init_v8_kats[5], whose expected Htable bytes were  *)
(* produced by the verbatim AWS-LC C reference and verified vs. real assembly  *)
(* over 2000 inputs), the spec's first three slot expressions evaluate to      *)
(* exactly the C reference numerals.  The internal key is                      *)
(* ghash_twist(byteswap128 H_mem) (the half-swap convention).  This covers     *)
(* BOTH layout patterns: byteswap128 (slots 0,2) and the fixed packed-mid      *)
(* orientation word_join(kmid higher)(kmid lower) (slot 1), so a lower/higher  *)
(* swap in either would fail this proof.  Numerals below decompose as          *)
(* out[2i+1]*2^64 + out[2i], out[] = ref_gcm_init_v8(H_mem):                    *)
(*   slot0 = byteswap128(H^1),  slot1 = pack(kmid H^2, kmid H^1),  slot2 = bsw(H^2). *)
let HTABLE_MEM_KAT_FIRST3 = prove
 (`byteswap128
     (h_power
       (ghash_twist(byteswap128 (word 0x08070605040302010102030405060708:int128))) 0) =
     word 21340584272258163075941918885976739344 /\
   word_join
     (karatsuba_mid
       (h_power
         (ghash_twist(byteswap128 (word 0x08070605040302010102030405060708:int128))) 1)
       :64 word)
     (karatsuba_mid
       (h_power
         (ghash_twist(byteswap128 (word 0x08070605040302010102030405060708:int128))) 0)
       :64 word):128 word =
     word 180621838512046301753057854212163635730 /\
   byteswap128
     (h_power
       (ghash_twist(byteswap128 (word 0x08070605040302010102030405060708:int128))) 1) =
     word 181047608966400424755469230121728647223`,
  CONV_TAC(REWRITE_CONV[num_CONV `1`; h_power] THENC
    REWRITE_CONV[polyval_dot; polyval_reduce_prop3; byteswap128; karatsuba_mid;
                 ghash_twist; POLYVAL_TWIST_CONST] THENC
    TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV WORD_RED_CONV THENC WORD_REDUCE_CONV));;

(* ========================================================================= *)
(* Phase 3: the twist (PC 0x0 -> 0x44).                                       *)
(*                                                                            *)
(* The first 17 instructions load the raw 128-bit hash key H from [X1],       *)
(* compute the x-twist in the internal (half-swapped) representation, and     *)
(* store the result as Htable[0] via `st1 {v20.2d},[x0],#16`.                 *)
(*                                                                            *)
(* HALF-SWAP BYTE-ORDER CONVENTION (the linchpin of the whole proof):         *)
(*                                                                            *)
(*   Let  H  = read (memory :> bytes128 H_ptr) s   be the raw little-endian   *)
(*   128-bit value in memory.  `byteswap128` swaps the two 64-bit halves      *)
(*   (word0 <-> word1); it is the HOL image of the `ext v,v,#8` the routine   *)
(*   applies immediately after the load.  Then                                *)
(*                                                                            *)
(*        Htable[0]  =  byteswap128 (ghash_twist (byteswap128 H)).            *)
(*                                                                            *)
(*   Equivalently: the algebraic ("polynomial-basis") GHASH key that the      *)
(*   spec calls H is  byteswap128 H_mem, i.e. the memory value with its two   *)
(*   64-bit halves swapped.  All the internal PMULL math (Phases 4-7) runs    *)
(*   on that half-swapped representation, and every stored entry is the       *)
(*   byteswap128 of the corresponding internal power (see `htable_mem`,       *)
(*   whose first slot is `byteswap128 (h_power h 0) = byteswap128 h`).         *)
(*                                                                            *)
(*   The carry bit that `ghash_twist` tests as `bit 127` is, in the internal  *)
(*   representation, the top bit of `byteswap128 H` = `bit 63 H`; the routine *)
(*   broadcasts exactly that bit via `dup v17.4s,v17.s[1]` + `sshr ...,#31`.   *)
(*                                                                            *)
(* The whole equality is a fixed-width bit identity, closed by `BITBLAST_TAC` *)
(* (the conditional in `ghash_twist` is left in place so the SAME carry bit   *)
(* governs both sides; do NOT `COND_CASES_TAC` first, or the bit-blaster      *)
(* loses the shared assumption and the two branches no longer line up).       *)
(* ========================================================================= *)

let GCM_INIT_V8_TWIST = prove
 (`!Htable H_ptr H pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192) /\
    nonoverlapping (Htable, 192) (H_ptr, 16)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [Htable; H_ptr] s /\
              read (memory :> bytes128 H_ptr) s = H)
         (\s. read PC s = word (pc + 0x44) /\
              read (memory :> bytes128 Htable) s =
                byteswap128(ghash_twist(byteswap128 H)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `H_ptr:int64`; `H:int128`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst GCM_INIT_V8_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SOME_FLAGS; MODIFIABLE_SIMD_REGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[byteswap128; ghash_twist; POLYVAL_TWIST_CONST] THEN
  BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 4: the squaring / multiply-reduce block (H^2), PC 0x44 -> 0x9c.      *)
(*                                                                            *)
(* Precondition (recovered by Phase 7 after stepping the twist): v20 holds    *)
(* the stored, byteswapped key  byteswap128 h1  (h1 the internal algebraic    *)
(* key = ghash_twist(byteswap128 H_mem)); v19 holds Gueron's reduction        *)
(* constant  w = 0xC200000000000000; X0 points at Htable+16.                  *)
(*                                                                            *)
(* The block computes H^2 = polyval_dot h1 h1 (one carryless square + a       *)
(* two-phase Gueron reduction), stores the Karatsuba-mid pack at Htable[1]     *)
(* and byteswap128(H^2) at Htable[2], and leaves byteswap128(H^2) in Q22 for   *)
(* the next power block.  The postcondition also pins the two Karatsuba        *)
(* "folds" the block leaves live for the H^3/H^4 block (Phase 5): Q16 =        *)
(* word_xor h1 (byteswap128 h1) (both lanes = karatsuba_mid h1) and Q17 =      *)
(* word_xor (H^2) (byteswap128 (H^2)) (both lanes = karatsuba_mid(H^2)).       *)
(* These are the true hardware values at 0x9c (machine-checked here by the     *)
(* same 22-step run), so Phase 5 need not re-derive them.                      *)
(*                                                                            *)
(* PROOF STRATEGY (algebraic, NOT a brute bit-blast — a symbolic word_pmul is *)
(* opaque to WORD_BLAST):                                                     *)
(*   1. symbolic-step the 22 instructions and read off the raw store values;  *)
(*   2. unfold the spec (polyval_dot / prop3 / karatsuba_mid / byteswap128),   *)
(*      rewrite the wide square with PMUL_KARATSUBA, collapse the Karatsuba    *)
(*      middle for a square with FROB64, abbreviate the two half-products     *)
(*      PAA,PBB and (after lane normalization) their four lanes + the two      *)
(*      reduction pmul-by-w results QA,QV, so the goal becomes PMUL-FREE over  *)
(*      opaque atoms;                                                         *)
(*   3. close each 128-bit store equality per 64-bit lane: WORD_EQ_128_LANES   *)
(*      splits it into its two lanes, NORM1 pushes word_subword through        *)
(*      word_join/word_xor down to the opaque atoms, and WORD_BITWISE_RULE     *)
(*      discharges the resulting pure-XOR lane identity.  This is bit-count-   *)
(*      INDEPENDENT: WORD_BLAST on the ~640-bit combined identity times out    *)
(*      (BDD blow-up superlinear in bit count), whereas the per-lane word-     *)
(*      level close does not care about the bit width.                        *)
(*                                                                            *)
(* NOTE ON Htable[1] ORDER (a spec discrepancy found while proving this):      *)
(*   The routine stores the H^1/H^2 Karatsuba-mid pack as                     *)
(*     word_join (karatsuba_mid (polyval_dot h1 h1)) (karatsuba_mid h1),       *)
(*   i.e. karatsuba_mid h1 in the LOW 64 bits (bytes 0..7) and                 *)
(*   karatsuba_mid(H^2) in the HIGH 64 bits (bytes 8..15).  This is what the   *)
(*   hardware actually writes (confirmed here by symbolic execution of the ISA *)
(*   model, and independently by the byte-exact import layout).  It is the     *)
(*   SWAP of `htable_mem`'s packed-mid slot                                    *)
(*   `word_join (karatsuba_mid(h_power h 0)) (karatsuba_mid(h_power h 1))`      *)
(*   (common/polyval_ghash.ml): since HOL `word_join a b` places `a` in the    *)
(*   HIGH half, that definition puts karatsuba_mid h1 in the HIGH half — the   *)
(*   opposite of the hardware.  The byteswap128 slots (Htable[0],[2],...) are  *)
(*   unaffected.  The lemma below therefore states the ACTUAL stored value;    *)
(*   htable_mem's four packed-mid slots need their two karatsuba_mid arguments *)
(*   swapped for Phase 7 to compose (flagged to the human).                   *)
(* ========================================================================= *)

(* --- lane-normalization conversion: subword-of-{join,zx} and subword-of-xor *)
let NORM1 = TOP_DEPTH_CONV (WORD_SIMPLE_SUBWORD_CONV ORELSEC REWR_CONV WORD_SUBWORD_XOR);;

(* subword lanes of a byteswapped operand, and the mid of a byteswapped key   *)
let SUBWORD_BS_LEMMAS = prove
 (`(!h:int128. word_subword (byteswap128 h) (0,64):64 word = word_subword h (64,64)) /\
   (!h:int128. word_subword (byteswap128 h) (64,64):64 word = word_subword h (0,64)) /\
   (!h:int128. word_subword (word_join (byteswap128 h) (byteswap128 h):256 word) (64,128):128 word = h) /\
   (!h:int128. word_subword (word_xor (byteswap128 h) h) (0,64):64 word =
               word_xor (word_subword h (0,64)) (word_subword h (64,64)))`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* Frobenius: for a SQUARE the Karatsuba middle collapses to p_lo XOR p_hi.    *)
let FROB64 = prove
 (`!a b:64 word. word_pmul (word_xor a b) (word_xor a b) : 128 word =
                 word_xor (word_pmul a a : 128 word) (word_pmul b b : 128 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [WORD_PMUL_SYM] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* Karatsuba decomposition of the wide square word_pmul h1 h1.                 *)
let KARA_H1 = CONV_RULE(TOP_DEPTH_CONV let_CONV)
                (ISPECL [`h1:int128`;`h1:int128`] PMUL_KARATSUBA);;

(* subword lanes of  shl(zx x) k  (aligned to the two shift amounts used).     *)
let SHL_LANES =
 [ WORD_BLAST `(word_subword (word_shl (word_zx (x:128 word):256 word) 64) (0,64):64 word) = (word 0:64 word)`;
   WORD_BLAST `(word_subword (word_shl (word_zx (x:128 word):256 word) 64) (64,64):64 word) = word_subword x (0,64)`;
   WORD_BLAST `(word_subword (word_shl (word_zx (x:128 word):256 word) 64) (128,64):64 word) = word_subword x (64,64)`;
   WORD_BLAST `(word_subword (word_shl (word_zx (x:128 word):256 word) 128) (0,64):64 word) = (word 0:64 word)`;
   WORD_BLAST `(word_subword (word_shl (word_zx (x:128 word):256 word) 128) (64,64):64 word) = (word 0:64 word)`;
   WORD_BLAST `(word_subword (word_shl (word_zx (x:128 word):256 word) 128) (128,64):64 word) = word_subword x (0,64)`;
   WORD_BLAST `(word_subword (word_shl (word_zx (x:128 word):256 word) 128) (192,64):64 word) = word_subword x (64,64)` ];;

(* word_insert (a Gueron INS) expressed as a word_join of lanes.               *)
let INS_LANES =
 [ WORD_BLAST `(word_insert (x:128 word) (0,64) (v:128 word) :128 word) =
               (word_join (word_subword x (64,64):64 word) (word_subword v (0,64):64 word) :128 word)`;
   WORD_BLAST `(word_insert (x:128 word) (64,64) (v:128 word) :128 word) =
               (word_join (word_subword v (0,64):64 word) (word_subword x (0,64):64 word) :128 word)`;
   WORD_BLAST `(word_subword (word_shl (word_zx (x:128 word):256 word) 64) (192,64):64 word) = (word 0:64 word)` ];;

let XOR0 = WORD_BLAST `(!x:64 word. word_xor x (word 0) = x) /\
                       (!x:64 word. word_xor (word 0) x = x)`;;

(* VEQ2: the assembly's 2nd Gueron pmul-by-w argument equals the spec's        *)
(* (both reduce to  word_subword QA (0,64)  XOR  HAA); unifying them lets the  *)
(* two pmul-by-w results be abbreviated to a single opaque QV.                 *)
let VEQ2 = WORD_BITWISE_RULE
  `word_xor (word_subword (QA:128 word) (0,64):64 word)
            (word_xor (word_xor (LBB:64 word) (LAA:64 word))
                      (word_xor (HAA:64 word) (word_xor LAA LBB))) =
   word_xor (word_xor HAA (word_xor (word_xor (word_xor LAA LBB) LAA) LBB))
            (word_subword QA (0,64))`;;

(* two 128-bit words are equal iff their two 64-bit lanes agree.               *)
let WORD_EQ_128_LANES = prove
 (`!x y:128 word.
     (word_subword x (0,64):64 word = word_subword y (0,64)) /\
     (word_subword x (64,64):64 word = word_subword y (64,64))
     ==> x = y`,
  CONV_TAC WORD_BLAST);;

let GCM_INIT_V8_H2 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x44) /\
              read X0 s = word_add Htable (word 16) /\
              read Q19 s = word 0xC200000000000000 /\
              read Q20 s = byteswap128 h1)
         (\s. read PC s = word (pc + 0x9c) /\
              read Q19 s = word 0xC200000000000000 /\
              read Q20 s = byteswap128 h1 /\
              read Q22 s = byteswap128 (polyval_dot h1 h1) /\
              read Q16 s = word_xor h1 (byteswap128 h1) /\
              read Q17 s = word_xor (polyval_dot h1 h1)
                                    (byteswap128 (polyval_dot h1 h1)) /\
              read X0 s = word_add Htable (word 48) /\
              read (memory :> bytes128 (word_add Htable (word 16))) s =
                word_join (karatsuba_mid (polyval_dot h1 h1)) (karatsuba_mid h1) /\
              read (memory :> bytes128 (word_add Htable (word 32))) s =
                byteswap128 (polyval_dot h1 h1))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `h1:int128`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst GCM_INIT_V8_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SOME_FLAGS; MODIFIABLE_SIMD_REGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--22) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (* --- unfold spec, Karatsuba-decompose the square, collapse the mid --- *)
  REWRITE_TAC[SUBWORD_BS_LEMMAS] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid; byteswap128; KARA_H1] THEN
  REWRITE_TAC[FROB64] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  (* --- abbreviate the two half-products, normalize lanes to fixpoint --- *)
  ABBREV_TAC `PAA = word_pmul (word_subword (h1:int128) (0,64):64 word)
                              (word_subword h1 (0,64):64 word):128 word` THEN
  ABBREV_TAC `PBB = word_pmul (word_subword (h1:int128) (64,64):64 word)
                              (word_subword h1 (64,64):64 word):128 word` THEN
  REWRITE_TAC(SHL_LANES @ INS_LANES) THEN CONV_TAC NORM1 THEN
  REWRITE_TAC(SHL_LANES @ INS_LANES) THEN CONV_TAC NORM1 THEN
  REWRITE_TAC(SHL_LANES @ INS_LANES) THEN CONV_TAC NORM1 THEN
  REWRITE_TAC[XOR0] THEN
  (* --- abbreviate the four product lanes + the first pmul-by-w (QA) --- *)
  ABBREV_TAC `LAA = word_subword (PAA:128 word) (0,64):64 word` THEN
  ABBREV_TAC `HAA = word_subword (PAA:128 word) (64,64):64 word` THEN
  ABBREV_TAC `LBB = word_subword (PBB:128 word) (0,64):64 word` THEN
  ABBREV_TAC `HBB = word_subword (PBB:128 word) (64,64):64 word` THEN
  ABBREV_TAC `QA = word_pmul (LAA:64 word)
                             ((word 13979173243358019584):64 word):128 word` THEN
  (* --- unify the assembly / spec 2nd pmul-by-w argument, abbreviate QV --- *)
  REWRITE_TAC[VEQ2] THEN
  ABBREV_TAC `QV = word_pmul
                    (word_xor (word_xor (HAA:64 word)
                       (word_xor (word_xor (word_xor (LAA:64 word) (LBB:64 word)) LAA) LBB))
                     (word_subword (QA:128 word) (0,64):64 word))
                    ((word 13979173243358019584):64 word):128 word` THEN
  (* --- the goal is now PMUL-FREE over opaque atoms; close per 64-bit lane --- *)
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC WORD_EQ_128_LANES THEN CONJ_TAC THEN
  CONV_TAC NORM1 THEN CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* Phase 5: the H^3 & H^4 power block, PC 0x9c -> 0x134.                      *)
(*                                                                            *)
(* Precondition (the H^2 block's postcondition, GCM_INIT_V8_H2): Q20 holds    *)
(* byteswap128 h1, Q22 holds byteswap128(H^2), Q19 = Gueron's w, and the two  *)
(* Karatsuba folds Q16 = h1 (+) byteswap128 h1, Q17 = H^2 (+) byteswap128 H^2 *)
(* are live; X0 points at Htable+48.  Writing H2i := polyval_dot h1 h1, the    *)
(* block computes two powers by TWO interleaved carryless products:           *)
(*                                                                            *)
(*   H^3i = polyval_dot h1 H2i   (Q20 . Q22 : operands DIFFER, genuine mid)    *)
(*   H^4i = polyval_dot H2i H2i  (Q22 . Q22 : a SQUARE, mid = p_lo (+) p_hi)   *)
(*                                                                            *)
(* each followed by the same two-phase Gueron reduction, then stores          *)
(* byteswap128 H^3i, the packed pair word_join(kmid H^4i)(kmid H^3i), and      *)
(* byteswap128 H^4i via a single 3-register st1 (arm_STP3 at 0x130 -- the      *)
(* first proof use of the newly-modelled instruction).                        *)
(*                                                                            *)
(* The postcondition exposes every register the H^5/H^6 block (Phase 6)        *)
(* consumes at 0x134, so that block composes without re-deriving them (the     *)
(* composition-gap lesson from Phase 5's own setup): Q22 = byteswap128 H^2i,   *)
(* Q23 = byteswap128 H^3i, Q25 = byteswap128 H^4i, the H^2 fold Q18 =          *)
(* H^2i (+) byteswap128 H^2i, and the refolded Q16 = H^3i-fold, Q17 =          *)
(* H^4i-fold.  (H^5 = H^2i.H^3i uses Q22,Q23 and the folds Q18,Q16.)           *)
(*                                                                            *)
(* OPERAND-AGNOSTIC REDUCTION BRIDGE (the STATE generality mandate).  Because  *)
(* H^3 has a non-vanishing Karatsuba middle, the H^2-specific FROB64 close     *)
(* does not apply; a squaring-specialised close would have to be redone for    *)
(* every later power.  Instead the reduction is closed over the THREE opaque   *)
(* products of each power: abbreviate {PL3,PH3,PM3} for H^3 and {PL4,PH4}      *)
(* for H^4 (its middle PM4 = PL4 (+) PH4 collapses under FROB64, so the        *)
(* reconstruction middle vanishes exactly as in H^2 -- H^4 is the H^2 special  *)
(* case).  With the products opaque, the SPEC side (polyval_dot = prop3 of the *)
(* Karatsuba reconstruction, via KARA_H1H2/KARA_H2H2) and the HARDWARE side    *)
(* are XOR/lane rearrangements of the same atoms.  Only the two second-phase   *)
(* pmul-by-w arguments differ in shape; VEQ3/VEQ4 (pure WORD_BITWISE_RULE      *)
(* XOR identities) unify them so each abbreviates to a single QV3/QV4.  The    *)
(* goal is then PMUL-FREE and the SAME structure-agnostic finisher as H^2      *)
(* (WORD_EQ_128_LANES + NORM1 + WORD_BITWISE_RULE per 64-bit lane) closes all  *)
(* five conjuncts -- genuine-mid (H^3) and square (H^4) handled identically.   *)
(* This close is what Phase 6 reuses for H^5..H^8 unchanged.                   *)
(*                                                                            *)
(* The postcondition is kept in OPERAND form (H^3i = polyval_dot h1 H2i, etc.) *)
(* rather than h_power form: reconciling to htable_mem's h_power h 2/h 3 needs  *)
(* polyval_dot commutativity/associativity, deferred to Phase 7 where one      *)
(* lemma set is applied to all eight powers at once.  The internal key is the  *)
(* half-swapped byteswap128 H_mem (Phase 3 convention), carried throughout.    *)
(* ========================================================================= *)

(* Karatsuba decompositions for the two interleaved products (h2 := H^2i).     *)
let KARA_H1H2 = CONV_RULE(TOP_DEPTH_CONV let_CONV)
                  (ISPECL [`h1:int128`;`h2:int128`] PMUL_KARATSUBA);;
let KARA_H2H2 = CONV_RULE(TOP_DEPTH_CONV let_CONV)
                  (ISPECL [`h2:int128`;`h2:int128`] PMUL_KARATSUBA);;

(* VEQ3/VEQ4: the hardware vs. spec 2nd-phase pmul-by-w argument agree (XOR    *)
(* rearrangement).  VEQ3 is the genuine-mid (H^3) case; VEQ4 the square (H^4). *)
let VEQ3 = WORD_BITWISE_RULE
  `word_xor (word_xor (word_subword (PL3:128 word) (64,64):64 word)
                      (word_xor (word_xor (word_subword (PM3:128 word) (0,64))
                                          (word_subword PL3 (0,64)))
                                (word_subword (PH3:128 word) (0,64))))
            (word_subword (QA3:128 word) (0,64)) =
   word_xor (word_subword QA3 (0,64))
            (word_xor (word_xor (word_subword PH3 (0,64)) (word_subword PL3 (0,64)))
                      (word_xor (word_subword PL3 (64,64)) (word_subword PM3 (0,64))))`;;

let VEQ4 = WORD_BITWISE_RULE
  `word_xor (word_xor (word_subword (PL4:128 word) (64,64):64 word)
                      (word_xor (word_xor (word_xor (word_subword PL4 (0,64))
                                                    (word_subword (PH4:128 word) (0,64)))
                                          (word_subword PL4 (0,64)))
                                (word_subword PH4 (0,64))))
            (word_subword (QA4:128 word) (0,64)) =
   word_xor (word_subword QA4 (0,64))
            (word_xor (word_xor (word_subword PH4 (0,64)) (word_subword PL4 (0,64)))
                      (word_xor (word_subword PL4 (64,64))
                                (word_xor (word_subword PL4 (0,64)) (word_subword PH4 (0,64)))))`;;

let GCM_INIT_V8_H34 = prove
 (`!Htable h1 pc.
    nonoverlapping (word pc, LENGTH gcm_init_v8_mc) (Htable, 192)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
              read PC s = word (pc + 0x9c) /\
              read X0 s = word_add Htable (word 48) /\
              read Q19 s = word 0xC200000000000000 /\
              read Q20 s = byteswap128 h1 /\
              read Q22 s = byteswap128 (polyval_dot h1 h1) /\
              read Q16 s = word_xor h1 (byteswap128 h1) /\
              read Q17 s = word_xor (polyval_dot h1 h1)
                                    (byteswap128 (polyval_dot h1 h1)))
         (\s. read PC s = word (pc + 0x134) /\
              read X0 s = word_add Htable (word 96) /\
              read Q19 s = word 0xC200000000000000 /\
              read Q20 s = byteswap128 h1 /\
              read Q22 s = byteswap128 (polyval_dot h1 h1) /\
              read Q18 s = word_xor (polyval_dot h1 h1)
                                    (byteswap128 (polyval_dot h1 h1)) /\
              read Q23 s = byteswap128 (polyval_dot h1 (polyval_dot h1 h1)) /\
              read Q25 s = byteswap128 (polyval_dot (polyval_dot h1 h1) (polyval_dot h1 h1)) /\
              read Q16 s = word_xor (polyval_dot h1 (polyval_dot h1 h1))
                             (byteswap128 (polyval_dot h1 (polyval_dot h1 h1))) /\
              read Q17 s = word_xor (polyval_dot (polyval_dot h1 h1) (polyval_dot h1 h1))
                             (byteswap128
                               (polyval_dot (polyval_dot h1 h1) (polyval_dot h1 h1))) /\
              read (memory :> bytes128 (word_add Htable (word 48))) s =
                byteswap128 (polyval_dot h1 (polyval_dot h1 h1)) /\
              read (memory :> bytes128 (word_add Htable (word 64))) s =
                word_join (karatsuba_mid (polyval_dot (polyval_dot h1 h1) (polyval_dot h1 h1)))
                          (karatsuba_mid (polyval_dot h1 (polyval_dot h1 h1))) /\
              read (memory :> bytes128 (word_add Htable (word 80))) s =
                byteswap128 (polyval_dot (polyval_dot h1 h1) (polyval_dot h1 h1)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(Htable, 192)])`,
  MAP_EVERY X_GEN_TAC [`Htable:int64`; `h1:int128`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst GCM_INIT_V8_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SOME_FLAGS; MODIFIABLE_SIMD_REGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--38) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (* --- keep H^2 opaque (h2), unfold the two outer products' spec --- *)
  ABBREV_TAC `h2 = polyval_dot h1 h1` THEN
  REWRITE_TAC[SUBWORD_BS_LEMMAS] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid; byteswap128; KARA_H1H2; KARA_H2H2] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  (* --- normalize lanes to fixpoint, then collapse the H^4 square middle --- *)
  REWRITE_TAC(SHL_LANES @ INS_LANES) THEN CONV_TAC NORM1 THEN
  REWRITE_TAC(SHL_LANES @ INS_LANES) THEN CONV_TAC NORM1 THEN
  REWRITE_TAC(SHL_LANES @ INS_LANES) THEN CONV_TAC NORM1 THEN
  REWRITE_TAC[XOR0] THEN
  REWRITE_TAC[FROB64] THEN
  (* --- abbreviate the five base products (H^3: PL3,PH3,PM3; H^4: PL4,PH4) --- *)
  ABBREV_TAC `PL3 = word_pmul (word_subword (h1:int128) (0,64):64 word)
                             (word_subword (h2:int128) (0,64):64 word):128 word` THEN
  ABBREV_TAC `PH3 = word_pmul (word_subword (h1:int128) (64,64):64 word)
                             (word_subword (h2:int128) (64,64):64 word):128 word` THEN
  ABBREV_TAC `PM3 = word_pmul (word_xor (word_subword (h1:int128) (0,64):64 word)
                                        (word_subword h1 (64,64)))
                             (word_xor (word_subword (h2:int128) (0,64):64 word)
                                       (word_subword h2 (64,64))):128 word` THEN
  ABBREV_TAC `PL4 = word_pmul (word_subword (h2:int128) (0,64):64 word)
                             (word_subword (h2:int128) (0,64):64 word):128 word` THEN
  ABBREV_TAC `PH4 = word_pmul (word_subword (h2:int128) (64,64):64 word)
                             (word_subword (h2:int128) (64,64):64 word):128 word` THEN
  (* --- abbreviate the first-phase pmul-by-w results --- *)
  ABBREV_TAC `QA3 = word_pmul (word_subword (PL3:128 word) (0,64):64 word)
                             ((word 13979173243358019584):64 word):128 word` THEN
  ABBREV_TAC `QA4 = word_pmul (word_subword (PL4:128 word) (0,64):64 word)
                             ((word 13979173243358019584):64 word):128 word` THEN
  (* --- distribute subwords, unify the 2nd-phase pmul-by-w args, abbreviate --- *)
  CONV_TAC NORM1 THEN
  REWRITE_TAC[VEQ3; VEQ4] THEN
  ABBREV_TAC `QV3 = word_pmul
                     (word_xor (word_subword (QA3:128 word) (0,64):64 word)
                       (word_xor (word_xor (word_subword (PH3:128 word) (0,64))
                                           (word_subword (PL3:128 word) (0,64)))
                                 (word_xor (word_subword PL3 (64,64))
                                           (word_subword (PM3:128 word) (0,64)))))
                     ((word 13979173243358019584):64 word):128 word` THEN
  ABBREV_TAC `QV4 = word_pmul
                     (word_xor (word_subword (QA4:128 word) (0,64):64 word)
                       (word_xor (word_xor (word_subword (PH4:128 word) (0,64))
                                           (word_subword (PL4:128 word) (0,64)))
                                 (word_xor (word_subword PL4 (64,64))
                                           (word_xor (word_subword PL4 (0,64))
                                                     (word_subword PH4 (0,64))))))
                     ((word 13979173243358019584):64 word):128 word` THEN
  (* --- PMUL-FREE over opaque atoms; close per 64-bit lane (structure-agnostic) --- *)
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC WORD_EQ_128_LANES THEN CONJ_TAC THEN
  CONV_TAC NORM1 THEN CONV_TAC WORD_BITWISE_RULE);;
