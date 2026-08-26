(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* GHASH key-table initializer gcm_init_v8 (aarch64, PMULL/PMULL2 flavour).   *)
(*                                                                            *)
(* void gcm_init_v8(u128 Htable[16], const u64 H[2]) computes the twisted H   *)
(* and fills the 12 used slots of the 192-byte table with H^1..H^8 and their  *)
(* packed Karatsuba middle terms.  Correctness is stated against the in-tree  *)
(* POLYVAL/GHASH algebraic layer (htable_mem / h_power / ghash_twist in       *)
(* common/polyval_ghash.ml).                                                  *)
(*                                                                            *)
(* Ported from aws-lc crypto/fipsmodule/modes/asm/ghashv8-armx.pl.            *)
(* 152 instructions, 608 bytes (0x000-0x25c), leaf / no stack, straight-line. *)
(*                                                                            *)
(* Five compute blocks, each ending in the store(s) of its slots:            *)
(*   A twist   0x000-0x040  steps  1-17  ghash_twist(byteswap128 H_in)=h      *)
(*                                        slot 0,        1-reg st1             *)
(*   B H^2     0x044-0x098  steps 18-39  h_power h 1                          *)
(*                                        slots 1,2,     two 1-reg st1        *)
(*   C H^3/H^4 0x09c-0x130  steps 40-77  h_power h 2,3                        *)
(*                                        slots 3,4,5,   3-reg st1            *)
(*   D H^5/H^6 0x134-0x1c8  steps 78-115 h_power h 4,5                        *)
(*                                        slots 6,7,8,   3-reg st1            *)
(*   E H^7/H^8 0x1cc-0x258  steps 116-151 h_power h 6,7                       *)
(*                                        slots 9,10,11, 3-reg st1 (no-off)   *)
(*   ret       0x25c        step 152                                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/polyval_ghash.ml";;
needs "common/karatsuba_pmul.ml";;    (* PMUL_KARATSUBA (128x128 pmul split) *)

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                          *)
(*                                                                            *)
(* Byte list taken from `objdump -d arm/aes_gcm/gcm_init_v8.o` (objdump       *)
(* rather than print_literal_from_elf, which decodes and, pre-Phase-3, died   *)
(* on the four opcodes below).  The session-001 decode audit found FOUR       *)
(* distinct undecodable opcodes; Phase 3 has since modelled all of them       *)
(* (arm/proofs/instruction.ml + decode.ml), so a full-object ARM_MK_EXEC_RULE *)
(* now succeeds (see GCM_INIT_V8_EXEC below).  The four were:                  *)
(*                                                                            *)
(*   4e0c0631  dup v17.4s, v17.s[1]           @ 0x014  (step 6)   DUP element *)
(*   4c9f6c17  st1 {v23.2d-v25.2d},[x0],#48   @ 0x130  (step 77)  3-reg st1   *)
(*   4c9f6c1a  st1 {v26.2d-v28.2d},[x0],#48   @ 0x1c8  (step 115) 3-reg st1   *)
(*   4c006c1d  st1 {v29.2d-v31.2d},[x0]       @ 0x258  (step 151) 3-reg st1   *)
(*                                                                            *)
(* The DUP-element gap was subtle: DUP(element) `dup v.4s,v.s[1]` (opcode     *)
(* field 0b000001) is a DIFFERENT instruction from DUP(general) `dup v.4s,w0` *)
(* (0b000011 = arm_DUP_GEN, decode.ml:538, already modelled); Phase 3 added   *)
(* arm_DUP_ELEM.  The three 3-register stores are opcode field 0b0110         *)
(* (contiguous LD1/ST1-multiple) -- distinct from the modelled 1-register     *)
(* (0b0111) and 2-register (0b1010) forms, and from LD3/ST3 (0b0100, which    *)
(* de-interleaves); Phase 3 added arm_LD1_3/arm_ST1_3.  Contrast the modelled *)
(* 1-register st1 in the same object:                                         *)
(*   4c9f7c14  st1 {v20.2d},[x0],#16          @ 0x040  (step 17)  1-reg st1   *)
(* ------------------------------------------------------------------------- *)

let gcm_init_v8_mc = define_assert_from_elf "gcm_init_v8_mc" "arm/aes_gcm/gcm_init_v8.o"
[
  (* --- Block A: twist, slot 0 (0x000-0x040) --- *)
  0x4c407c31;       (* ld1 {v17.2d}, [x1] *)
  0x4f07e433;       (* movi v19.16b, #0xe1 *)
  0x4f795673;       (* shl v19.2d, v19.2d, #57 *)
  0x6e114223;       (* ext v3.16b, v17.16b, v17.16b, #8 *)
  0x6f410672;       (* ushr v18.2d, v19.2d, #63 *)
  0x4e0c0631;       (* dup v17.4s, v17.s[1] *)
  0x6e134250;       (* ext v16.16b, v18.16b, v19.16b, #8 *)
  0x6f410472;       (* ushr v18.2d, v3.2d, #63 *)
  0x4f210631;       (* sshr v17.4s, v17.4s, #31 *)
  0x4e301e52;       (* and v18.16b, v18.16b, v16.16b *)
  0x4f415463;       (* shl v3.2d, v3.2d, #1 *)
  0x6e124252;       (* ext v18.16b, v18.16b, v18.16b, #8 *)
  0x4e311e10;       (* and v16.16b, v16.16b, v17.16b *)
  0x4eb21c63;       (* orr v3.16b, v3.16b, v18.16b *)
  0x6e301c74;       (* eor v20.16b, v3.16b, v16.16b *)
  0x6e144294;       (* ext v20.16b, v20.16b, v20.16b, #8 *)
  0x4c9f7c14;       (* st1 {v20.2d}, [x0], #16 *)
  (* --- Block B: H^2, slots 1,2 (0x044-0x098) --- *)
  0x6e144290;       (* ext v16.16b, v20.16b, v20.16b, #8 *)
  0x4ef4e280;       (* pmull2 v0.1q, v20.2d, v20.2d *)
  0x6e341e10;       (* eor v16.16b, v16.16b, v20.16b *)
  0x0ef4e282;       (* pmull v2.1q, v20.1d, v20.1d *)
  0x0ef0e201;       (* pmull v1.1q, v16.1d, v16.1d *)
  0x6e024011;       (* ext v17.16b, v0.16b, v2.16b, #8 *)
  0x6e221c12;       (* eor v18.16b, v0.16b, v2.16b *)
  0x6e311c21;       (* eor v1.16b, v1.16b, v17.16b *)
  0x6e321c21;       (* eor v1.16b, v1.16b, v18.16b *)
  0x0ef3e012;       (* pmull v18.1q, v0.1d, v19.1d *)
  0x6e084422;       (* mov v2.d[0], v1.d[1] *)
  0x6e180401;       (* mov v1.d[1], v0.d[0] *)
  0x6e321c20;       (* eor v0.16b, v1.16b, v18.16b *)
  0x6e004012;       (* ext v18.16b, v0.16b, v0.16b, #8 *)
  0x0ef3e000;       (* pmull v0.1q, v0.1d, v19.1d *)
  0x6e221e52;       (* eor v18.16b, v18.16b, v2.16b *)
  0x6e321c11;       (* eor v17.16b, v0.16b, v18.16b *)
  0x6e114236;       (* ext v22.16b, v17.16b, v17.16b, #8 *)
  0x6e361e31;       (* eor v17.16b, v17.16b, v22.16b *)
  0x6e114215;       (* ext v21.16b, v16.16b, v17.16b, #8 *)
  0x4c9f7c15;       (* st1 {v21.2d}, [x0], #16 *)
  0x4c9f7c16;       (* st1 {v22.2d}, [x0], #16 *)
  (* --- Block C: H^3/H^4, slots 3,4,5 (0x09c-0x130) --- *)
  0x4ef6e280;       (* pmull2 v0.1q, v20.2d, v22.2d *)
  0x4ef6e2c5;       (* pmull2 v5.1q, v22.2d, v22.2d *)
  0x0ef6e282;       (* pmull v2.1q, v20.1d, v22.1d *)
  0x0ef6e2c7;       (* pmull v7.1q, v22.1d, v22.1d *)
  0x0ef1e201;       (* pmull v1.1q, v16.1d, v17.1d *)
  0x0ef1e226;       (* pmull v6.1q, v17.1d, v17.1d *)
  0x6e024010;       (* ext v16.16b, v0.16b, v2.16b, #8 *)
  0x6e0740b1;       (* ext v17.16b, v5.16b, v7.16b, #8 *)
  0x6e221c12;       (* eor v18.16b, v0.16b, v2.16b *)
  0x6e301c21;       (* eor v1.16b, v1.16b, v16.16b *)
  0x6e271ca4;       (* eor v4.16b, v5.16b, v7.16b *)
  0x6e311cc6;       (* eor v6.16b, v6.16b, v17.16b *)
  0x6e321c21;       (* eor v1.16b, v1.16b, v18.16b *)
  0x0ef3e012;       (* pmull v18.1q, v0.1d, v19.1d *)
  0x6e241cc6;       (* eor v6.16b, v6.16b, v4.16b *)
  0x0ef3e0a4;       (* pmull v4.1q, v5.1d, v19.1d *)
  0x6e084422;       (* mov v2.d[0], v1.d[1] *)
  0x6e0844c7;       (* mov v7.d[0], v6.d[1] *)
  0x6e180401;       (* mov v1.d[1], v0.d[0] *)
  0x6e1804a6;       (* mov v6.d[1], v5.d[0] *)
  0x6e321c20;       (* eor v0.16b, v1.16b, v18.16b *)
  0x6e241cc5;       (* eor v5.16b, v6.16b, v4.16b *)
  0x6e004012;       (* ext v18.16b, v0.16b, v0.16b, #8 *)
  0x6e0540a4;       (* ext v4.16b, v5.16b, v5.16b, #8 *)
  0x0ef3e000;       (* pmull v0.1q, v0.1d, v19.1d *)
  0x0ef3e0a5;       (* pmull v5.1q, v5.1d, v19.1d *)
  0x6e221e52;       (* eor v18.16b, v18.16b, v2.16b *)
  0x6e271c84;       (* eor v4.16b, v4.16b, v7.16b *)
  0x6e321c10;       (* eor v16.16b, v0.16b, v18.16b *)
  0x6e241cb1;       (* eor v17.16b, v5.16b, v4.16b *)
  0x6e104217;       (* ext v23.16b, v16.16b, v16.16b, #8 *)
  0x6e114239;       (* ext v25.16b, v17.16b, v17.16b, #8 *)
  0x6e1642d2;       (* ext v18.16b, v22.16b, v22.16b, #8 *)
  0x6e371e10;       (* eor v16.16b, v16.16b, v23.16b *)
  0x6e391e31;       (* eor v17.16b, v17.16b, v25.16b *)
  0x6e361e52;       (* eor v18.16b, v18.16b, v22.16b *)
  0x6e114218;       (* ext v24.16b, v16.16b, v17.16b, #8 *)
  0x4c9f6c17;       (* st1 {v23.2d-v25.2d}, [x0], #48   (3-reg, UNMODELED) *)
  (* --- Block D: H^5/H^6, slots 6,7,8 (0x134-0x1c8) --- *)
  0x4ef7e2c0;       (* pmull2 v0.1q, v22.2d, v23.2d *)
  0x4ef7e2e5;       (* pmull2 v5.1q, v23.2d, v23.2d *)
  0x0ef7e2c2;       (* pmull v2.1q, v22.1d, v23.1d *)
  0x0ef7e2e7;       (* pmull v7.1q, v23.1d, v23.1d *)
  0x0ef2e201;       (* pmull v1.1q, v16.1d, v18.1d *)
  0x0ef0e206;       (* pmull v6.1q, v16.1d, v16.1d *)
  0x6e024010;       (* ext v16.16b, v0.16b, v2.16b, #8 *)
  0x6e0740b1;       (* ext v17.16b, v5.16b, v7.16b, #8 *)
  0x6e221c12;       (* eor v18.16b, v0.16b, v2.16b *)
  0x6e301c21;       (* eor v1.16b, v1.16b, v16.16b *)
  0x6e271ca4;       (* eor v4.16b, v5.16b, v7.16b *)
  0x6e311cc6;       (* eor v6.16b, v6.16b, v17.16b *)
  0x6e321c21;       (* eor v1.16b, v1.16b, v18.16b *)
  0x0ef3e012;       (* pmull v18.1q, v0.1d, v19.1d *)
  0x6e241cc6;       (* eor v6.16b, v6.16b, v4.16b *)
  0x0ef3e0a4;       (* pmull v4.1q, v5.1d, v19.1d *)
  0x6e084422;       (* mov v2.d[0], v1.d[1] *)
  0x6e0844c7;       (* mov v7.d[0], v6.d[1] *)
  0x6e180401;       (* mov v1.d[1], v0.d[0] *)
  0x6e1804a6;       (* mov v6.d[1], v5.d[0] *)
  0x6e321c20;       (* eor v0.16b, v1.16b, v18.16b *)
  0x6e241cc5;       (* eor v5.16b, v6.16b, v4.16b *)
  0x6e004012;       (* ext v18.16b, v0.16b, v0.16b, #8 *)
  0x6e0540a4;       (* ext v4.16b, v5.16b, v5.16b, #8 *)
  0x0ef3e000;       (* pmull v0.1q, v0.1d, v19.1d *)
  0x0ef3e0a5;       (* pmull v5.1q, v5.1d, v19.1d *)
  0x6e221e52;       (* eor v18.16b, v18.16b, v2.16b *)
  0x6e271c84;       (* eor v4.16b, v4.16b, v7.16b *)
  0x6e321c10;       (* eor v16.16b, v0.16b, v18.16b *)
  0x6e241cb1;       (* eor v17.16b, v5.16b, v4.16b *)
  0x6e10421a;       (* ext v26.16b, v16.16b, v16.16b, #8 *)
  0x6e11423c;       (* ext v28.16b, v17.16b, v17.16b, #8 *)
  0x6e1642d2;       (* ext v18.16b, v22.16b, v22.16b, #8 *)
  0x6e3a1e10;       (* eor v16.16b, v16.16b, v26.16b *)
  0x6e3c1e31;       (* eor v17.16b, v17.16b, v28.16b *)
  0x6e361e52;       (* eor v18.16b, v18.16b, v22.16b *)
  0x6e11421b;       (* ext v27.16b, v16.16b, v17.16b, #8 *)
  0x4c9f6c1a;       (* st1 {v26.2d-v28.2d}, [x0], #48   (3-reg, UNMODELED) *)
  (* --- Block E: H^7/H^8, slots 9,10,11 (0x1cc-0x258) --- *)
  0x4efae2c0;       (* pmull2 v0.1q, v22.2d, v26.2d *)
  0x4efce2c5;       (* pmull2 v5.1q, v22.2d, v28.2d *)
  0x0efae2c2;       (* pmull v2.1q, v22.1d, v26.1d *)
  0x0efce2c7;       (* pmull v7.1q, v22.1d, v28.1d *)
  0x0ef2e201;       (* pmull v1.1q, v16.1d, v18.1d *)
  0x0ef2e226;       (* pmull v6.1q, v17.1d, v18.1d *)
  0x6e024010;       (* ext v16.16b, v0.16b, v2.16b, #8 *)
  0x6e0740b1;       (* ext v17.16b, v5.16b, v7.16b, #8 *)
  0x6e221c12;       (* eor v18.16b, v0.16b, v2.16b *)
  0x6e301c21;       (* eor v1.16b, v1.16b, v16.16b *)
  0x6e271ca4;       (* eor v4.16b, v5.16b, v7.16b *)
  0x6e311cc6;       (* eor v6.16b, v6.16b, v17.16b *)
  0x6e321c21;       (* eor v1.16b, v1.16b, v18.16b *)
  0x0ef3e012;       (* pmull v18.1q, v0.1d, v19.1d *)
  0x6e241cc6;       (* eor v6.16b, v6.16b, v4.16b *)
  0x0ef3e0a4;       (* pmull v4.1q, v5.1d, v19.1d *)
  0x6e084422;       (* mov v2.d[0], v1.d[1] *)
  0x6e0844c7;       (* mov v7.d[0], v6.d[1] *)
  0x6e180401;       (* mov v1.d[1], v0.d[0] *)
  0x6e1804a6;       (* mov v6.d[1], v5.d[0] *)
  0x6e321c20;       (* eor v0.16b, v1.16b, v18.16b *)
  0x6e241cc5;       (* eor v5.16b, v6.16b, v4.16b *)
  0x6e004012;       (* ext v18.16b, v0.16b, v0.16b, #8 *)
  0x6e0540a4;       (* ext v4.16b, v5.16b, v5.16b, #8 *)
  0x0ef3e000;       (* pmull v0.1q, v0.1d, v19.1d *)
  0x0ef3e0a5;       (* pmull v5.1q, v5.1d, v19.1d *)
  0x6e221e52;       (* eor v18.16b, v18.16b, v2.16b *)
  0x6e271c84;       (* eor v4.16b, v4.16b, v7.16b *)
  0x6e321c10;       (* eor v16.16b, v0.16b, v18.16b *)
  0x6e241cb1;       (* eor v17.16b, v5.16b, v4.16b *)
  0x6e10421d;       (* ext v29.16b, v16.16b, v16.16b, #8 *)
  0x6e11423f;       (* ext v31.16b, v17.16b, v17.16b, #8 *)
  0x6e3d1e10;       (* eor v16.16b, v16.16b, v29.16b *)
  0x6e3f1e31;       (* eor v17.16b, v17.16b, v31.16b *)
  0x6e11421e;       (* ext v30.16b, v16.16b, v17.16b, #8 *)
  0x4c006c1d;       (* st1 {v29.2d-v31.2d}, [x0]        (3-reg, UNMODELED) *)
  0xd65f03c0        (* ret *)
];;

(* ------------------------------------------------------------------------- *)
(* Length of the machine code (608 bytes = 152 instructions).                 *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_MC_LENGTH =
  let th1 = AP_TERM `LENGTH:byte list->num` gcm_init_v8_mc in
  TRANS th1 ((REWRITE_CONV[LENGTH] THENC NUM_REDUCE_CONV) (rhs(concl th1)));;

(* ------------------------------------------------------------------------- *)
(* Execution rule for the full object.  Phase 3 extended the ARM ISA model    *)
(* (arm/proofs/instruction.ml + decode.ml) with the two primitives the        *)
(* session-001 decode audit found missing -- DUP(element) at 0x014 and the    *)
(* contiguous 3-register LD1/ST1 (opcode 0b0110) at 0x130/0x1c8/0x258 -- so   *)
(* all 152 instructions now decode and ARM_MK_EXEC_RULE succeeds on the whole *)
(* mc.  (Before Phase 3 only a gap-free block-B sub-list, via                 *)
(* mk_sublist_of_mc "gcm_init_v8_blockB_mc" ... (68,88), could be built.)      *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_EXEC = ARM_MK_EXEC_RULE gcm_init_v8_mc;;

(* ------------------------------------------------------------------------- *)
(* Phase 4 -- the reduction bridge (the single riskiest lemma in the proof).  *)
(*                                                                            *)
(* Block B's arithmetic core (0x044-0x084, 17 straight-line instructions, no  *)
(* memory / no store) squares the 128-bit value in Q20 in GF(2^128) using the *)
(* register-split Karatsuba scheme (pmull2/pmull for the three half-products, *)
(* ext/mov/eor lane shuffles) followed by the two-phase Gueron 0xC2 reduction *)
(* (two `pmull ...,v19`).  This lemma states that the destination register    *)
(* Q17 (at 0x084, the clean H^2 before the 0x088 byteswap-and-store) holds     *)
(* exactly the spec's field square-and-reduce of the OPERAND-BYTESWAPPED input:*)
(*                                                                            *)
(*   read Q17 = polyval_reduce_prop3 (word_pmul (byteswap128 a) (byteswap128 a))*)
(*            = polyval_dot (byteswap128 a) (byteswap128 a)                    *)
(*                                                                            *)
(* The `byteswap128` on the operands is INTRINSIC to the register split (the   *)
(* pmull2/pmull lane selection + the 0x044 `ext` swap effectively feed the     *)
(* halves swapped relative to polyval_reduce_prop3's a=low/b=high lane         *)
(* convention); it is not a free choice.  This was pinned down empirically     *)
(* (concrete a: asm Q17 = prop3(pmul(swap64 a)(swap64 a)), a 128-bit match)    *)
(* and byteswap128 x = word_join(subword x(0,64))(subword x(64,64)) IS swap64. *)
(* This dovetails with the Phase-6 byteswap representation identity.           *)
(*                                                                            *)
(* Q19 carries the 0xC2 reduction constant in both 64-bit lanes (= shl #57 of  *)
(* movi 0xe1, built by block A at 0x004/0x008); only its low lane is consumed. *)
(*                                                                            *)
(* Proof: symbolically execute the 17 instructions, then discharge the         *)
(* resulting pure-word identity.  word_pmul is not bit-blastable directly (its *)
(* bit is a CARD/ODD set expression), so the three data-dependent half-product *)
(* squarings are abstracted to free 128-bit variables via PMUL_KARATSUBA       *)
(* (rewritten let-free as KARA_EQ so it fires only on the 128x128 product) and *)
(* the two constant-fold pmuls are expanded to shifts by PMUL_W_64_128.  After *)
(* a WORD_BLAST reconciliation of the lane-shuffle forms the goal is a linear  *)
(* GF(2) word identity over the three free products, closed by BITBLAST_TAC    *)
(* per 64-bit lane (LANE128).                                                  *)
(* ------------------------------------------------------------------------- *)

(* Let-free form of PMUL_KARATSUBA: matches only the 128x128 word_pmul, so it  *)
(* rewrites the reduced product without touching the 64x64 half-products.       *)
let KARA_EQ = GEN_ALL(CONV_RULE(TOP_DEPTH_CONV let_CONV)(SPEC_ALL PMUL_KARATSUBA));;

(* Split a 128-bit word equality into its two 64-bit lanes (keeps each         *)
(* BITBLAST call to 64 output bits; the full-width blast is impractical here). *)
let LANE128 = BITBLAST_RULE
 `!(x:128 word) y. x = y <=>
    (word_subword x (0,64):64 word = word_subword y (0,64)) /\
    (word_subword x (64,64):64 word = word_subword y (64,64))`;;

let GCM_INIT_V8_REDBRIDGE = prove
 (`!(a:int128) pc.
     ensures arm
      (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
           read PC s = word (pc + 0x44) /\
           read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
           read Q20 s = a)
      (\s. read PC s = word (pc + 0x88) /\
           read Q17 s =
           polyval_reduce_prop3 (word_pmul (byteswap128 a) (byteswap128 a)))
      (MAYCHANGE [PC] ,,
       MAYCHANGE [Q0; Q1; Q2; Q16; Q17; Q18] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int128`; `pc:num`] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[byteswap128] THEN
  REWRITE_TAC[KARA_EQ] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  REWRITE_TAC[WORD_BLAST
   `(word_subword (word_join (word_subword (a:int128) (0,64):64 word)
       (word_subword a (64,64):64 word) :128 word) (0,64):64 word =
     word_subword a (64,64)) /\
    (word_subword (word_join (word_subword (a:int128) (0,64):64 word)
       (word_subword a (64,64):64 word) :128 word) (64,64):64 word =
     word_subword a (0,64)) /\
    (word_subword (word_xor (a:int128)
       (word_subword (word_join a a:256 word) (64,128))) (0,64):64 word =
     word_xor (word_subword a (0,64):64 word) (word_subword a (64,64))) /\
    (word_xor (word_subword (a:int128) (64,64):64 word) (word_subword a (0,64)) =
     word_xor (word_subword a (0,64):64 word) (word_subword a (64,64)))`] THEN
  ABBREV_TAC `(qhi:(128)word) =
     word_pmul (word_subword (a:int128) (64,64) :(64)word)
               (word_subword (a:int128) (64,64) :(64)word)` THEN
  ABBREV_TAC `(qlo:(128)word) =
     word_pmul (word_subword (a:int128) (0,64) :(64)word)
               (word_subword (a:int128) (0,64) :(64)word)` THEN
  ABBREV_TAC `(qmid:(128)word) =
     word_pmul (word_xor (word_subword (a:int128) (0,64) :(64)word)
                         (word_subword (a:int128) (64,64) :(64)word))
               (word_xor (word_subword (a:int128) (0,64) :(64)word)
                         (word_subword (a:int128) (64,64) :(64)word))` THEN
  GEN_REWRITE_TAC I [LANE128] THEN CONJ_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Phase 5 -- the twist bridge (block A register core, 0x000-0x040).          *)
(*                                                                            *)
(* Block A loads H (v17 <- ld1 [x1]), builds the 0xC2 reduction constant      *)
(* (v19 = 0xC2..00 per 64-bit lane, movi 0xe1 + shl #57), byteswaps H into    *)
(* v3 (ext #8 = swap of the two 64-bit halves = byteswap128), and computes    *)
(* the GF(2^128) doubling x*H mod Q(x) as a per-lane `shl #1` plus an         *)
(* explicit cross-lane carry re-injection (the ushr/ext/and/or dance) and a   *)
(* conditional XOR of POLYVAL_TWIST_CONST (0xC2..01) selected by a mask that  *)
(* the `dup v17.s[1]` (arm_DUP_ELEM) + `sshr #31` broadcast produces from     *)
(* bit 127 of byteswap128 H.  The net register-level effect at 0x038 (v20)    *)
(* is the spec twist ghash_twist(byteswap128 H); the trailing `ext #8` at     *)
(* 0x03c byteswaps it, so at 0x040 (just before the slot-0 st1) v20 holds     *)
(*                                                                            *)
(*   read Q20 = byteswap128 (ghash_twist (byteswap128 H_in))                  *)
(*            = byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0)       *)
(*                                                                            *)
(* which is exactly the slot-0 value htable_mem demands (h_power h 0 = h).    *)
(*                                                                            *)
(* Unlike the block-B reduction bridge, block A contains NO pmul -- it is     *)
(* purely linear bit-plumbing (shifts / and / or / xor / ext / dup) -- so the *)
(* residual word identity after symbolic execution is bit-blastable directly. *)
(* The RHS orientation (which byteswap on which side) was pinned by a         *)
(* 128-bit-exact in-place BITBLAST rather than assumed (a pretty-printed-term  *)
(* round-trip invents type variables and fails spuriously; prove in place).   *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_TWISTBRIDGE = prove
 (`!hp H_in pc.
     ensures arm
      (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
           read PC s = word pc /\
           read X1 s = hp /\
           read (memory :> bytes128 hp) s = H_in)
      (\s. read PC s = word (pc + 0x40) /\
           read Q20 s = byteswap128 (ghash_twist (byteswap128 H_in)))
      (MAYCHANGE [PC] ,,
       MAYCHANGE [Q3; Q16; Q17; Q18; Q19; Q20] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`hp:int64`; `H_in:int128`; `pc:num`] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[byteswap128; ghash_twist; POLYVAL_TWIST_CONST] THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Phase 5 (cont.) -- block A including the slot-0 store (0x000-0x044).       *)
(*                                                                            *)
(* Extends the twist bridge by the single-register `st1 {v20.2d},[x0],#16` at *)
(* 0x040 (X0 = htable = Htable[0..], post-incremented by 16), landing the     *)
(* first htable_mem conjunct directly in memory:                             *)
(*                                                                            *)
(*   read (memory :> bytes128 htable) = byteswap128 (ghash_twist             *)
(*                                                     (byteswap128 H_in))    *)
(*                                    = byteswap128 (h_power h 0)              *)
(*                                                                            *)
(* (h_power h 0 = h = ghash_twist(byteswap128 H_in)).  This pins the first    *)
(* memory write + the post-increment convention every later store inherits    *)
(* (X0 advances +16 per single-register store), ready for Phase 7 to compose  *)
(* with block B.  The stored value equals the register value proved above, so *)
(* the residual identity after ENSURES_FINAL_STATE_TAC is the same word       *)
(* equality, closed by BITBLAST_TAC.  Stepping the store needs the code/table *)
(* nonoverlap and C_ARGUMENTS/exec-length rewrites BEFORE ENSURES_INIT_TAC    *)
(* (else the "updates will not modify the program code" side condition sticks).*)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_SLOT0 = prove
 (`!htable hp H_in pc.
     nonoverlapping (word pc,0x260) (htable,192)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [htable; hp] s /\
               read (memory :> bytes128 hp) s = H_in)
          (\s. read PC s = word (pc + 0x44) /\
               read X0 s = word_add htable (word 16) /\
               read (memory :> bytes128 htable) s =
                 byteswap128 (ghash_twist (byteswap128 H_in)))
          (MAYCHANGE [PC] ,,
           MAYCHANGE [X0] ,,
           MAYCHANGE [Q3; Q16; Q17; Q18; Q19; Q20] ,,
           MAYCHANGE [memory :> bytes(htable,16)] ,,
           MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; fst GCM_INIT_V8_EXEC] THEN
  STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[byteswap128; ghash_twist; POLYVAL_TWIST_CONST] THEN
  BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 6 -- algebraic power lemmas (pure word algebra, no assembly).        *)
(*                                                                            *)
(* These reconcile the assembly's balanced factorizations of the H-powers     *)
(* (verified from the disasm: H^3=H.H^2, H^4=H^2.H^2, H^5=H^2.H^3, H^6=H^3.H^3,*)
(* H^7=H^2.H^5, H^8=H^2.H^6) and its byteswapped register representation with  *)
(* the h_power recursion of common/polyval_ghash.ml.  All are stated as WORD  *)
(* equalities so blocks B-E (Phases 7-9) can apply them directly.  polyval_dot *)
(* a b = polyval_reduce_prop3 (word_pmul a b) = a*b*x^{-128} mod Q(x), so the  *)
(* dot operation is the field multiply-and-reduce the assembly computes.       *)
(*                                                                            *)
(* NOTE ON THE BYTESWAP IDENTITY (planned "hardest lemma #2").  The plan       *)
(* proposed proving  polyval_dot (byteswap128 a) (byteswap128 b) =            *)
(* polyval_dot a b  as a general identity.  IT IS FALSE: byteswap128 is a swap *)
(* of the two 64-bit HALVES (an involution), NOT a ring operation, and it does *)
(* not commute through the reduction.  Concretely (WORD_PMUL_CONV/WORD_RED_CONV*)
(* evaluation):                                                               *)
(*   polyval_dot (word 1) (word 1)                                            *)
(*      = word 194088056572031856754469952786247188481  (= x^{-128} mod Q)    *)
(*   polyval_dot (byteswap128(word 1)) (byteswap128(word 1)) = word 1          *)
(* which differ.  What blocks C/D/E actually require is NOT this identity but  *)
(* the per-operand involution below: the operand registers already hold the    *)
(* byteswapped stored powers (v20 = byteswap128 h, v22 = byteswap128(h_power   *)
(* h 1), ...), and the reduction-bridge form polyval_dot (byteswap128 u)       *)
(* (byteswap128 v) then cancels each byteswap by involution -- exactly as the  *)
(* block-B squaring did (GCM_INIT_V8_REDBRIDGE instantiated at a:=byteswap128  *)
(* h).  So no representation identity is needed; BYTESWAP128_INVOL + HPOWER_DOT *)
(* close the algebra.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Reassociation helper: swap the last two factors of a triple product.       *)
let SWAP_LAST2 = prove
 (`!a b c. a IN ring_carrier bool_poly /\ b IN ring_carrier bool_poly /\
           c IN ring_carrier bool_poly
     ==> ring_mul bool_poly (ring_mul bool_poly a b) c =
         ring_mul bool_poly (ring_mul bool_poly a c) b`,
  MESON_TAC[RING_MUL_ASSOC; RING_MUL_SYM; RING_MUL]);;

(* (a) polyval_dot is commutative (word_pmul is symmetric).                    *)
let POLYVAL_DOT_SYM = prove
 (`!a b:128 word. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC WORD_PMUL_SYM);;

(* polyval_dot is associative mod Q(x).  dot a b = a*b*x^{-128}, so            *)
(* dot a (dot b c) = a*b*c*x^{-256} = dot (dot a b) c: the x^{-128} scalars    *)
(* combine identically either way.  Proved by peeling two dots (two x^128      *)
(* cancellations via MOD_POLYVAL_CANCEL_VARPOW{,_GEN}), reducing to the ring   *)
(* associativity of poly(a)*poly(b)*poly(c).                                   *)
let POLYVAL_DOT_ASSOC = prove
 (`!a b c:128 word.
     polyval_dot a (polyval_dot b c) = polyval_dot (polyval_dot a b) c`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC `ring_mul bool_poly (poly_of_word (a:int128))
                (poly_of_word (polyval_dot b c))` THEN
  CONJ_TAC THENL [REWRITE_TAC[POLYVAL_DOT_CORRECT]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC `ring_mul bool_poly (poly_of_word (polyval_dot a b))
                (poly_of_word (c:int128))` THEN
  CONJ_TAC THENL [REWRITE_TAC[POLYVAL_DOT_CORRECT]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW_GEN) THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[RING_MUL; BOOL_POLY_OF_WORD];
    SIMP_TAC[RING_MUL; BOOL_POLY_OF_WORD];
    ALL_TAC] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC `ring_mul bool_poly (ring_mul bool_poly (poly_of_word (a:int128))
                (poly_of_word (b:int128))) (poly_of_word (c:int128))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`poly_of_word (polyval_dot a b)`; `poly_of_word (c:int128)`;
       `ring_pow bool_poly (poly_var bool_ring one) 128`] SWAP_LAST2) THEN
    ANTS_TAC THENL [SIMP_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY];
                    DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC MOD_POLYVAL_MUL THEN
    CONJ_TAC THENL [REWRITE_TAC[POLYVAL_DOT_CORRECT];
                    REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD]];
    SUBGOAL_THEN
     `ring_mul bool_poly (ring_mul bool_poly (poly_of_word (a:int128))
        (poly_of_word (b:int128))) (poly_of_word (c:int128)) =
      ring_mul bool_poly (poly_of_word (a:int128))
        (ring_mul bool_poly (poly_of_word (b:int128)) (poly_of_word (c:int128)))`
     SUBST1_TAC THENL
     [MATCH_MP_TAC(GSYM RING_MUL_ASSOC) THEN SIMP_TAC[BOOL_POLY_OF_WORD]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
    SUBGOAL_THEN
     `ring_mul bool_poly (ring_mul bool_poly (poly_of_word (a:int128))
        (poly_of_word (polyval_dot b c)))
        (ring_pow bool_poly (poly_var bool_ring one) 128) =
      ring_mul bool_poly (poly_of_word (a:int128))
        (ring_mul bool_poly (poly_of_word (polyval_dot b c))
          (ring_pow bool_poly (poly_var bool_ring one) 128))`
     SUBST1_TAC THENL
     [MATCH_MP_TAC(GSYM RING_MUL_ASSOC) THEN
      SIMP_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]; ALL_TAC] THEN
    MATCH_MP_TAC MOD_POLYVAL_MUL THEN
    CONJ_TAC THENL [REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD];
                    REWRITE_TAC[POLYVAL_DOT_CORRECT]]]);;

(* (c) exponent addition: dotting two H-powers adds their exponents.           *)
(* h_power h k = h^{k+1} * x^{-128k} mod Q, so                                 *)
(* dot(h_power h a)(h_power h b) = h^{a+b+2} x^{-128(a+b+1)} = h_power h (a+b+1).*)
(* Proved by induction on b: base is h_power's SUC clause; the step is         *)
(* POLYVAL_DOT_ASSOC + the inductive hypothesis.                              *)
let HPOWER_DOT = prove
 (`!(h:int128) a b:num.
     polyval_dot (h_power h a) (h_power h b) = h_power h (a + b + 1)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 0 + 1 = SUC a`; h_power];
    REWRITE_TAC[ARITH_RULE `a + SUC b + 1 = SUC(a + b + 1)`] THEN
    REWRITE_TAC[h_power] THEN
    ONCE_REWRITE_TAC[POLYVAL_DOT_ASSOC] THEN
    ASM_REWRITE_TAC[]]);;

(* byteswap128 is an involution (it swaps the two 64-bit halves).  This is the *)
(* fact the blocks C/D/E composition needs (see the NOTE above): the stored    *)
(* operands are byteswap128 of the powers, and the reduction bridge feeds them  *)
(* through another byteswap128, so the two cancel per operand.                 *)
let BYTESWAP128_INVOL = prove
 (`!x:int128. byteswap128 (byteswap128 x) = x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN BITBLAST_TAC);;

(* karatsuba_mid is invariant under byteswap128 (both halves get xored, and    *)
(* the swap only reorders the two halves).  Needed in the H^2 composition       *)
(* because block A leaves v20 = byteswap128 h, and slot 1's low lane is         *)
(* karatsuba_mid(v20) = karatsuba_mid h = karatsuba_mid(h_power h 0).           *)
let KARATSUBA_MID_BYTESWAP = prove
 (`!x:int128. karatsuba_mid (byteswap128 x) = karatsuba_mid x`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 7 -- block B (H^2) register core + the two 1-register stores         *)
(* (0x044-0x098, steps 18-39), stated with a SYMBOLIC input a = read Q20.     *)
(*                                                                            *)
(* Block B squares the value a (which block A leaves in Q20 = byteswap128 h)   *)
(* via the register-split Karatsuba scheme + two-phase 0xC2 reduction         *)
(* (GCM_INIT_V8_REDBRIDGE computes exactly this: Q17 at 0x088 holds            *)
(* polyval_dot (byteswap128 a) (byteswap128 a)), then packs and stores the     *)
(* two H^2 sub-table slots:                                                    *)
(*                                                                            *)
(*   slot 1 @ X0+0  (Htable[1], the packed Karatsuba middle) =                 *)
(*     word_join (karatsuba_mid (H^2)) (karatsuba_mid a)                       *)
(*     -- HIGH lane mid of the HIGHER power, LOW lane mid of the LOWER power.   *)
(*   slot 2 @ X0+16 (Htable[2]) = byteswap128 (H^2)                            *)
(*                                                                            *)
(* where H^2 = polyval_dot (byteswap128 a) (byteswap128 a) and X0 = htable+16  *)
(* (block A's post-increment).  The store then advances X0 to htable+48.       *)
(*                                                                            *)
(* IMPORTANT -- the packed-middle lane order was MEASURED on the model, not    *)
(* assumed (session-006 MEASURE_SLOT1): the assembly's                         *)
(*   ext v21,v16,v17,#8  ==>  read Q21 = word_join (karatsuba_mid Q17)         *)
(*                                                  (word_subword Q16 (64,64)) *)
(* i.e. HIGH = mid(H^2), LOW = mid(a).  This is the OPPOSITE order from what    *)
(* common/polyval_ghash.ml's htable_mem originally specified; htable_mem was   *)
(* CORRECTED (session 006) to match the aws-lc reference (producer             *)
(* `vext.8 $Hhl,$t0,$t1,#8` + consumer gcm_gmult_v8 `vpmull.p64 $Xm,$Hhl,$t1`, *)
(* which uses ONLY $Hhl's low lane against H^1, so the low lane must be         *)
(* mid(H^1)=mid(h_power h 0)).  Slot 1 is exercised by NEITHER the KAT nor the  *)
(* differential test, so this proof is its only check.                         *)
(*                                                                            *)
(* Proof: symbolically execute the 22 instructions (the stores need the        *)
(* code/table nonoverlap + exec-length rewrite BEFORE ENSURES_INIT_TAC), then  *)
(* discharge the two memory identities with the same Karatsuba-abstraction     *)
(* recipe as GCM_INIT_V8_REDBRIDGE (KARA_EQ splits the 128x128 product,        *)
(* PMUL_W_64_128 folds the 0xC2 pmuls, a WORD_BLAST reconciles the lane        *)
(* shuffles, the three half-products are ABBREV'd to free 128-bit vars, and    *)
(* LANE128 + BITBLAST closes each 64-bit lane).  PC/X0 close by WORD_RULE.      *)
(*                                                                            *)
(* The lemma also threads an UNMODIFIED slot-0 value v0 (read at htable) from  *)
(* pre to post: block B stores only to [htable+16, htable+48), disjoint from   *)
(* [htable, htable+16), so slot 0 is preserved by the frame and its post       *)
(* conjunct closes by ASM_REWRITE.  This is what lets Phase 7's composition     *)
(* (GCM_INIT_V8_H2_MEM) carry block A's slot-0 store through block B.           *)
(*                                                                            *)
(* The post ALSO exposes the block-B output registers Q19/Q20/Q22/Q16/Q17      *)
(* (a-form) -- these are exactly the inputs block C (GCM_INIT_V8_H34) reads, so *)
(* GCM_INIT_V8_H2_MEM can pass them straight through.  They close by the same   *)
(* Karatsuba+BITBLAST recipe (preserved Q19/Q20 by ASM_REWRITE, computed        *)
(* Q22/Q16/Q17 as extra per-lane blasts).  aligned_bytes_loaded is re-asserted  *)
(* (first post conjunct, ASM_REWRITE) so the lemma composes as a non-final      *)
(* block (see GCM_INIT_V8_H34_MEM).                                            *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_H2 = prove
 (`!(a:int128) v0 htable pc.
     nonoverlapping (word pc,0x260) (htable,192)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x44) /\
               read X0 s = word_add htable (word 16) /\
               read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
               read Q20 s = a /\
               read (memory :> bytes128 htable) s = v0)
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x9c) /\
               read X0 s = word_add htable (word 48) /\
               read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
               read Q20 s = a /\
               read Q22 s =
                 byteswap128 (polyval_dot (byteswap128 a) (byteswap128 a)) /\
               read Q16 s = word_xor (byteswap128 a) a /\
               read Q17 s = word_xor (polyval_dot (byteswap128 a) (byteswap128 a))
                              (byteswap128 (polyval_dot (byteswap128 a)
                                                        (byteswap128 a))) /\
               read (memory :> bytes128 htable) s = v0 /\
               read (memory :> bytes128 (word_add htable (word 16))) s =
                 word_join
                   (karatsuba_mid (polyval_dot (byteswap128 a) (byteswap128 a)))
                   (karatsuba_mid a) /\
               read (memory :> bytes128 (word_add htable (word 32))) s =
                 byteswap128 (polyval_dot (byteswap128 a) (byteswap128 a)))
          (MAYCHANGE [PC] ,,
           MAYCHANGE [X0] ,,
           MAYCHANGE [Q0; Q1; Q2; Q16; Q17; Q18; Q21; Q22] ,,
           MAYCHANGE [memory :> bytes(word_add htable (word 16),32)] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst GCM_INIT_V8_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid; byteswap128] THEN
  REWRITE_TAC[KARA_EQ] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  REWRITE_TAC[WORD_BLAST
   `(word_subword (word_join (word_subword (a:int128) (0,64):64 word)
       (word_subword a (64,64):64 word) :128 word) (0,64):64 word =
     word_subword a (64,64)) /\
    (word_subword (word_join (word_subword (a:int128) (0,64):64 word)
       (word_subword a (64,64):64 word) :128 word) (64,64):64 word =
     word_subword a (0,64)) /\
    (word_subword (word_xor (a:int128)
       (word_subword (word_join a a:256 word) (64,128))) (0,64):64 word =
     word_xor (word_subword a (0,64):64 word) (word_subword a (64,64))) /\
    (word_xor (word_subword (a:int128) (64,64):64 word) (word_subword a (0,64)) =
     word_xor (word_subword a (0,64):64 word) (word_subword a (64,64)))`] THEN
  ABBREV_TAC `(qhi:(128)word) =
     word_pmul (word_subword (a:int128) (64,64) :(64)word)
               (word_subword (a:int128) (64,64) :(64)word)` THEN
  ABBREV_TAC `(qlo:(128)word) =
     word_pmul (word_subword (a:int128) (0,64) :(64)word)
               (word_subword (a:int128) (0,64) :(64)word)` THEN
  ABBREV_TAC `(qmid:(128)word) =
     word_pmul (word_xor (word_subword (a:int128) (0,64) :(64)word)
                         (word_subword (a:int128) (64,64) :(64)word))
               (word_xor (word_subword (a:int128) (0,64) :(64)word)
                         (word_subword (a:int128) (64,64) :(64)word))` THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE) THEN
  GEN_REWRITE_TAC I [LANE128] THEN CONJ_TAC THEN BITBLAST_TAC);;

(* polyval_dot h h = h_power h 1 (specialize HPOWER_DOT at a=b=0, 0+0+1=1).    *)
(* Used to bridge block B's polyval_dot output to the h_power form htable_mem  *)
(* demands.                                                                    *)
let HDOT1 = prove
 (`!h:int128. polyval_dot h h = h_power h 1`,
  GEN_TAC THEN REWRITE_TAC[num_CONV `1`; h_power]);;

(* ========================================================================= *)
(* Phase 7 -- H^2 sub-table with memory (entry -> pc+0x9c, slots 0,1,2 +       *)
(* block-C input registers).                                                   *)
(*                                                                            *)
(* Composes block A (GCM_INIT_V8_H2 threads slot 0 via v0) with block B into   *)
(* the first three htable_mem conjuncts on the real machine code, stated in    *)
(* the h_power/karatsuba_mid/byteswap128 form htable_mem uses (h = the twisted *)
(* secret ghash_twist(byteswap128 H_in), h_power h 0 = h):                     *)
(*                                                                            *)
(*   slot 0 @ htable+0  = byteswap128 (h_power h 0)                            *)
(*   slot 1 @ htable+16 = word_join (karatsuba_mid (h_power h 1))              *)
(*                                  (karatsuba_mid (h_power h 0))              *)
(*   slot 2 @ htable+32 = byteswap128 (h_power h 1)                            *)
(*                                                                            *)
(* This is the first FULL memory proof (nonoverlapping code/table/H).  Memory  *)
(* granularity is uniformly 128-bit (H is one ld1; every slot a bytes128       *)
(* write), so no MEMORY_128_FROM_64-style restructuring is needed.             *)
(*                                                                            *)
(* Structure: ENSURES_SEQUENCE_TAC at pc+0x44 (the block A/B boundary).        *)
(*   SG1 (entry->0x44): re-run block A (steps 1-17, the twist + slot-0 st1),   *)
(*     reading off X0, the 0xC2 constant in Q19, the twist in Q20, and slot 0  *)
(*     in memory -- the exact preconditions block B needs.  Closes like        *)
(*     GCM_INIT_V8_SLOT0/TWISTBRIDGE (single BITBLAST after unfolding the       *)
(*     twist defs; X0 by WORD_RULE).                                           *)
(*   SG2 (0x44->0x9c): apply the strengthened GCM_INIT_V8_H2 at a := v0 :=      *)
(*     byteswap128 h.  The ENSURES_POSTCONDITION intermediate is H2's OWN post  *)
(*     (a-form: polyval_dot/karatsuba_mid of byteswap128 (byteswap128 h) etc.); *)
(*     the bridge rewrites it to the target form -- slots to h_power, and the   *)
(*     exposed registers to block C's INPUT form (Q20 = byteswap128 (h_power    *)
(*     h 0), Q22 = byteswap128 (h_power h 1), Q16/Q17 = word_xor (byteswap128 .)*)
(*     .) -- via BYTESWAP128_INVOL, KARATSUBA_MID_BYTESWAP, FORWARD HDOT1        *)
(*     (dot h h = h_power h 1, moving the a-form UP to h_power) and CONJUNCT1    *)
(*     h_power (h_power h 0 = h, moving the target DOWN); the two meet.          *)
(*     ENSURES_FRAME_SUBSUMED widens H2's tight frame.  No representation        *)
(*     identity is used (there is none; see the Phase-6 NOTE) -- only the        *)
(*     per-operand involution.  Stating the exposed registers in block C's      *)
(*     input form is what makes GCM_INIT_V8_H34_MEM's two MATCH_MP_TACs clean.   *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_H2_MEM = prove
 (`!htable hp H_in pc.
     nonoverlapping (word pc,0x260) (htable,192) /\
     nonoverlapping (htable,192) (hp,16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [htable; hp] s /\
               read (memory :> bytes128 hp) s = H_in)
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x9c) /\
               read X0 s = word_add htable (word 48) /\
               read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
               read Q20 s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
               read Q22 s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
               read Q16 s = word_xor
                  (byteswap128 (byteswap128
                     (h_power (ghash_twist (byteswap128 H_in)) 0)))
                  (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
               read Q17 s = word_xor
                  (byteswap128 (byteswap128
                     (h_power (ghash_twist (byteswap128 H_in)) 1)))
                  (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)) /\
               read (memory :> bytes128 htable) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
               read (memory :> bytes128 (word_add htable (word 16))) s =
                 word_join
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 1))
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
               read (memory :> bytes128 (word_add htable (word 32))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1))
          (MAYCHANGE [PC] ,,
           MAYCHANGE [X0] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q16;Q17;Q18;Q19;Q20;Q21;Q22] ,,
           MAYCHANGE [memory :> bytes(htable,48)] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; fst GCM_INIT_V8_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x44`
   `\s. read X0 s = word_add htable (word 16) /\
        read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
        read Q20 s = byteswap128 (ghash_twist (byteswap128 H_in)) /\
        read (memory :> bytes128 htable) s =
          byteswap128 (ghash_twist (byteswap128 H_in))` THEN
  CONJ_TAC THENL
   [(* --- SG1: entry -> pc+0x44 (twist + slot-0 store) --- *)
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(CONV_TAC WORD_RULE) THEN
    REWRITE_TAC[byteswap128; ghash_twist; POLYVAL_TWIST_CONST] THEN
    BITBLAST_TAC;
    (* --- SG2: pc+0x44 -> pc+0x9c (block B via strengthened GCM_INIT_V8_H2) --- *)
    (* Intermediate = strengthened GCM_INIT_V8_H2's OWN post at a := v0 :=       *)
    (* byteswap128 h (a-form registers + a-form slots); the bridge maps it to    *)
    (* the H34-input/h_power form above so H34_MEM's SG1 and SG2 are both clean   *)
    (* MATCH_MP_TAC.  Forward HDOT1 moves block B's a-form output UP to h_power.  *)
    ENSURES_POSTCONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
          read PC s = word (pc + 0x9c) /\
          read X0 s = word_add htable (word 48) /\
          read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
          read Q20 s = byteswap128 (ghash_twist (byteswap128 H_in)) /\
          read Q22 s = byteswap128 (polyval_dot
             (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in))))
             (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in))))) /\
          read Q16 s = word_xor
             (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in))))
             (byteswap128 (ghash_twist (byteswap128 H_in))) /\
          read Q17 s = word_xor (polyval_dot
             (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in))))
             (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in)))))
             (byteswap128 (polyval_dot
             (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in))))
             (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in)))))) /\
          read (memory :> bytes128 htable) s =
            byteswap128 (ghash_twist (byteswap128 H_in)) /\
          read (memory :> bytes128 (word_add htable (word 16))) s =
            word_join
              (karatsuba_mid (polyval_dot
                 (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in))))
                 (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in))))))
              (karatsuba_mid (byteswap128 (ghash_twist (byteswap128 H_in)))) /\
          read (memory :> bytes128 (word_add htable (word 32))) s =
            byteswap128 (polyval_dot
              (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in))))
              (byteswap128 (byteswap128 (ghash_twist (byteswap128 H_in)))))` THEN
    CONJ_TAC THENL
     [(* algebra bridge: block B a-form ==> H34-input/h_power form *)
      GEN_TAC THEN
      REWRITE_TAC[BYTESWAP128_INVOL; KARATSUBA_MID_BYTESWAP;
                  HDOT1; CONJUNCT1 h_power] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      (* widen H2's tight frame, then apply it at a := v0 := byteswap128 h *)
      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE [PC] ,,
        MAYCHANGE [X0] ,,
        MAYCHANGE [Q0;Q1;Q2;Q16;Q17;Q18;Q21;Q22] ,,
        MAYCHANGE [memory :> bytes(word_add htable (word 16),32)] ,,
        MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        MATCH_MP_TAC GCM_INIT_V8_H2 THEN
        ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]]]]);;

(* ========================================================================= *)
(* Phase 8 -- block C (H^3/H^4) register bridge (0x09c-0x130, steps 40-77).    *)
(*                                                                            *)
(* Block C runs TWO interleaved Karatsuba+reduction streams over the two      *)
(* register inputs a = Q20 (block A's twist output, byteswap128 h) and        *)
(* b = Q22 (block B's byteswap128 H^2), reusing the mid operands v16/v17      *)
(* carried over UNMODIFIED from block B (v16 = word_xor (byteswap128 a) a,     *)
(* v17 = word_xor (byteswap128 b) b -- both are broadcast(lo XOR hi), and     *)
(* only their low lanes are read).  Stream "0/2/1"->v16 computes the a*b       *)
(* product, "5/7/6"->v17 the b*b product; each is the same register-split      *)
(* squaring/multiply + two-phase 0xC2 reduction as GCM_INIT_V8_REDBRIDGE.      *)
(*                                                                            *)
(* MEASURED on the model (session 008, symbolic a,b, ARM_STEPS + final state): *)
(* the two pmull operands ARE independently byteswapped register values, so    *)
(* the reduction-bridge clean form is per-operand exactly as block B's squaring*)
(* -- retiring the proof's long-standing top residual risk (the operands       *)
(* separate; no new bridge shape is needed).  At 0x130 (before the store):     *)
(*                                                                            *)
(*   read Q23 = byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b))      *)
(*              (= slot 3, byteswap128 H^3)                                    *)
(*   read Q24 = word_join (karatsuba_mid (polyval_dot (byteswap128 b)          *)
(*                                                     (byteswap128 b)))       *)
(*                        (karatsuba_mid (polyval_dot (byteswap128 a)          *)
(*                                                     (byteswap128 b)))       *)
(*              (= slot 4 packed middle; HIGH lane = mid of H^4, LOW = mid H^3;*)
(*               MEASURED lane order, matching the corrected htable_mem)       *)
(*   read Q25 = byteswap128 (polyval_dot (byteswap128 b) (byteswap128 b))      *)
(*              (= slot 5, byteswap128 H^4)                                    *)
(*                                                                            *)
(* Proof: same recipe as REDBRIDGE/H2 but with SIX half-products (three per    *)
(* stream).  The reconciliation of the byteswapped-operand subword forms with  *)
(* the assembly's raw subword forms uses three generic helpers (SBW_XOR /      *)
(* SBW_BS / SBW_JOIN, push word_subword through word_xor / byteswap128 /        *)
(* word_join); the six products ABBREV to free 128-bit vars and each output    *)
(* lane closes by BITBLAST (each lane depends on only one stream's products).  *)
(* ------------------------------------------------------------------------- *)

(* Generic reconciliation: push a 64-bit word_subword through word_xor,        *)
(* byteswap128, and word_join, so KARA's subword-of-byteswapped-operand forms  *)
(* match the assembly's raw subword forms and the six products can be ABBREV'd. *)
let SBW_XOR = WORD_BLAST
 `(word_subword (word_xor (x:int128) y) (0,64):64 word =
     word_xor (word_subword x (0,64)) (word_subword y (0,64))) /\
  (word_subword (word_xor (x:int128) y) (64,64):64 word =
     word_xor (word_subword x (64,64)) (word_subword y (64,64)))`;;

let SBW_BS = prove
 (`(word_subword (byteswap128 x) (0,64):64 word = word_subword x (64,64)) /\
   (word_subword (byteswap128 x) (64,64):64 word = word_subword x (0,64))`,
  REWRITE_TAC[byteswap128] THEN CONJ_TAC THEN BITBLAST_TAC);;

let SBW_JOIN = WORD_BLAST
 `(word_subword (word_join (p:64 word) (q:64 word) :128 word) (0,64):64 word = q) /\
  (word_subword (word_join (p:64 word) (q:64 word) :128 word) (64,64):64 word = p)`;;

let GCM_INIT_V8_C_REGBRIDGE = prove
 (`!(a:int128) (b:int128) pc.
     ensures arm
      (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
           read PC s = word (pc + 0x9c) /\
           read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
           read Q20 s = a /\
           read Q22 s = b /\
           read Q16 s = word_xor (byteswap128 a) a /\
           read Q17 s = word_xor (byteswap128 b) b)
      (\s. read PC s = word (pc + 0x130) /\
           read Q23 s =
             byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b)) /\
           read Q24 s =
             word_join
               (karatsuba_mid (polyval_dot (byteswap128 b) (byteswap128 b)))
               (karatsuba_mid (polyval_dot (byteswap128 a) (byteswap128 b))) /\
           read Q25 s =
             byteswap128 (polyval_dot (byteswap128 b) (byteswap128 b)))
      (MAYCHANGE [PC] ,,
       MAYCHANGE [Q0;Q1;Q2;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q23;Q24;Q25] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int128`; `b:int128`; `pc:num`] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid] THEN
  REWRITE_TAC[KARA_EQ] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  REWRITE_TAC[SBW_XOR; SBW_BS; SBW_JOIN] THEN
  ABBREV_TAC `(pab_hi:128 word) =
     word_pmul (word_subword (a:int128) (64,64):64 word)
               (word_subword (b:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pab_lo:128 word) =
     word_pmul (word_subword (a:int128) (0,64):64 word)
               (word_subword (b:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pab_mid:128 word) =
     word_pmul (word_xor (word_subword (a:int128) (64,64):64 word)
                         (word_subword (a:int128) (0,64):64 word))
               (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))` THEN
  ABBREV_TAC `(pbb_hi:128 word) =
     word_pmul (word_subword (b:int128) (64,64):64 word)
               (word_subword (b:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pbb_lo:128 word) =
     word_pmul (word_subword (b:int128) (0,64):64 word)
               (word_subword (b:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pbb_mid:128 word) =
     word_pmul (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))
               (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))` THEN
  REWRITE_TAC[byteswap128] THEN
  REPEAT CONJ_TAC THEN GEN_REWRITE_TAC I [LANE128] THEN CONJ_TAC THEN
  BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 8 -- block C (H^3/H^4) register core + 3-register store               *)
(* (0x09c-0x134, steps 40-77 + the st1), stated with SYMBOLIC inputs           *)
(* a = Q20, b = Q22 (block B leaves a = byteswap128 h, b = byteswap128 H^2).   *)
(*                                                                            *)
(* This is the block-C analogue of GCM_INIT_V8_H2: it wraps the register       *)
(* bridge with the contiguous 3-register store `st1 {v23.2d-v25.2d},[x0],#48`  *)
(* at 0x130 -- the FIRST real exercise of the Phase-3 arm_ST1_3 primitive --   *)
(* landing the three H^3/H^4 sub-table slots (X0 = htable+48 on entry, +96 on  *)
(* exit):                                                                      *)
(*                                                                            *)
(*   slot 3 @ X0+0  (Htable[3]) = byteswap128 (H^3)                            *)
(*   slot 4 @ X0+16 (Htable[4], packed middle) =                               *)
(*     word_join (karatsuba_mid (H^4)) (karatsuba_mid (H^3))                   *)
(*     -- HIGH lane mid of the HIGHER power, LOW lane mid of the LOWER power.   *)
(*   slot 5 @ X0+32 (Htable[5]) = byteswap128 (H^4)                            *)
(*                                                                            *)
(* where H^3 = polyval_dot (byteswap128 a) (byteswap128 b) and                 *)
(* H^4 = polyval_dot (byteswap128 b) (byteswap128 b) (block-C register bridge, *)
(* MEASURED above).  Slot 4 is exercised by NEITHER the KAT nor the            *)
(* differential test, so this proof is its only check; its measured lane order *)
(* (HIGH = higher power) matches the corrected htable_mem.                     *)
(*                                                                            *)
(* Three ghost slot values g0/g1/g2 (the H^2 sub-table slots 0/1/2 that block  *)
(* A+B already stored) are threaded pre->post: block C writes only             *)
(* [htable+48, htable+96), disjoint from [htable, htable+48), so they survive  *)
(* the frame and close by ASM_REWRITE -- this is what lets Phase 8's           *)
(* composition carry slots 0-2 through block C.                                *)
(*                                                                            *)
(* Proof: step all 38 instructions (the store needs the code/table nonoverlap  *)
(* + exec-length rewrite BEFORE ENSURES_INIT_TAC), then discharge the three    *)
(* stored-slot identities with the same Karatsuba recipe as the register       *)
(* bridge (SBW_XOR/SBW_BS/SBW_JOIN reconciliation, six ABBREV'd products,      *)
(* LANE128 + BITBLAST per lane); X0 by WORD_RULE, g0/g1/g2 by ASM_REWRITE.      *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_H34 = prove
 (`!(a:int128) (b:int128) g0 g1 g2 htable pc.
     nonoverlapping (word pc,0x260) (htable,192)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x9c) /\
               read X0 s = word_add htable (word 48) /\
               read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
               read Q20 s = a /\
               read Q22 s = b /\
               read Q16 s = word_xor (byteswap128 a) a /\
               read Q17 s = word_xor (byteswap128 b) b /\
               read (memory :> bytes128 htable) s = g0 /\
               read (memory :> bytes128 (word_add htable (word 16))) s = g1 /\
               read (memory :> bytes128 (word_add htable (word 32))) s = g2)
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x134) /\
               read X0 s = word_add htable (word 96) /\
               read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
               read Q22 s = b /\
               read Q23 s =
                 byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b)) /\
               read Q18 s = word_xor (byteswap128 b) b /\
               read Q16 s = word_xor
                  (byteswap128 (byteswap128
                     (polyval_dot (byteswap128 a) (byteswap128 b))))
                  (byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b))) /\
               read (memory :> bytes128 htable) s = g0 /\
               read (memory :> bytes128 (word_add htable (word 16))) s = g1 /\
               read (memory :> bytes128 (word_add htable (word 32))) s = g2 /\
               read (memory :> bytes128 (word_add htable (word 48))) s =
                 byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b)) /\
               read (memory :> bytes128 (word_add htable (word 64))) s =
                 word_join
                   (karatsuba_mid (polyval_dot (byteswap128 b) (byteswap128 b)))
                   (karatsuba_mid (polyval_dot (byteswap128 a) (byteswap128 b))) /\
               read (memory :> bytes128 (word_add htable (word 80))) s =
                 byteswap128 (polyval_dot (byteswap128 b) (byteswap128 b)))
          (MAYCHANGE [PC] ,,
           MAYCHANGE [X0] ,,
           MAYCHANGE [Q0;Q1;Q2;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q23;Q24;Q25] ,,
           MAYCHANGE [memory :> bytes(word_add htable (word 48),48)] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst GCM_INIT_V8_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid] THEN
  REWRITE_TAC[KARA_EQ] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  REWRITE_TAC[SBW_XOR; SBW_BS; SBW_JOIN] THEN
  ABBREV_TAC `(pab_hi:128 word) =
     word_pmul (word_subword (a:int128) (64,64):64 word)
               (word_subword (b:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pab_lo:128 word) =
     word_pmul (word_subword (a:int128) (0,64):64 word)
               (word_subword (b:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pab_mid:128 word) =
     word_pmul (word_xor (word_subword (a:int128) (64,64):64 word)
                         (word_subword (a:int128) (0,64):64 word))
               (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))` THEN
  ABBREV_TAC `(pbb_hi:128 word) =
     word_pmul (word_subword (b:int128) (64,64):64 word)
               (word_subword (b:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pbb_lo:128 word) =
     word_pmul (word_subword (b:int128) (0,64):64 word)
               (word_subword (b:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pbb_mid:128 word) =
     word_pmul (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))
               (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))` THEN
  REWRITE_TAC[byteswap128] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE) THEN
  GEN_REWRITE_TAC I [LANE128] THEN CONJ_TAC THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 8 -- H^3/H^4 sub-table with memory (entry -> pc+0x134, slots 0-5).    *)
(*                                                                            *)
(* Composes GCM_INIT_V8_H2_MEM (entry->0x9c: slots 0-2 + block-C input regs)  *)
(* with block C (GCM_INIT_V8_H34, 0x9c->0x134) into the first SIX htable_mem  *)
(* conjuncts in h_power form (h = ghash_twist (byteswap128 H_in)):            *)
(*                                                                            *)
(*   slot 3 @ htable+48 = byteswap128 (h_power h 2)                           *)
(*   slot 4 @ htable+64 = word_join (km (h_power h 3)) (km (h_power h 2))      *)
(*   slot 5 @ htable+80 = byteswap128 (h_power h 3)                           *)
(*                                                                            *)
(* All composable block/memory lemmas here carry aligned_bytes_loaded in      *)
(* their post (FIRST conjunct) so any can serve as a NON-final block:         *)
(* ENSURES_SEQUENCE_TAC's intermediate always includes program_decodes        *)
(* (relational.ml:1401), so a first-block sub-lemma must reproduce it.  The   *)
(* conjunct closes for free (ASM_REWRITE after ENSURES_FINAL_STATE_TAC, or by  *)
(* the composition).  GCM_INIT_V8_H2 / H2_MEM / H34 were all strengthened      *)
(* in place to carry it (+ the block-C input registers on H2/H2_MEM).         *)
(*                                                                            *)
(* Structure: ENSURES_SEQUENCE_TAC at pc+0x9c.                                *)
(*   SG1 (entry->0x9c): GCM_INIT_V8_H2_MEM, whose post is stated in block C's  *)
(*     INPUT form (a = byteswap128 (h_power h 0), b = byteswap128 (h_power     *)
(*     h 1)), so the mid-assertion matches BOTH H2_MEM's post (SG1) and H34's  *)
(*     precondition (SG2) verbatim -- both are clean MATCH_MP_TAC, the block-B *)
(*     output -> h_power reconciliation living inside H2_MEM's own proof.      *)
(*     NB: do NOT unfold C_ARGUMENTS in the setup -- H2_MEM's pre keeps it      *)
(*     folded, so the entry precondition must too or MATCH_MP_TAC won't match. *)
(*   SG2 (0x9c->0x134): GCM_INIT_V8_H34 (block C); the ENSURES_POSTCONDITION   *)
(*     bridge maps its polyval_dot post to h_power via BYTESWAP128_INVOL       *)
(*     (byteswap128(byteswap128 (h_power h k)) = h_power h k) + HPOWER_DOT      *)
(*     (dot (h_power h i)(h_power h j) = h_power h (i+j+1)) + numeral reduction *)
(*     (0+1+1=2, 1+1+1=3).  Slots 3,5 = H^3,H^4; slot 4 the packed middle      *)
(*     (untested slot -- this proof is its only check).                       *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_H34_MEM = prove
 (`!htable hp H_in pc.
     nonoverlapping (word pc,0x260) (htable,192) /\
     nonoverlapping (htable,192) (hp,16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [htable; hp] s /\
               read (memory :> bytes128 hp) s = H_in)
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x134) /\
               read X0 s = word_add htable (word 96) /\
               read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
               read Q22 s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
               read Q23 s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2) /\
               read Q18 s = word_xor
                  (byteswap128 (byteswap128
                     (h_power (ghash_twist (byteswap128 H_in)) 1)))
                  (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)) /\
               read Q16 s = word_xor
                  (byteswap128 (byteswap128
                     (h_power (ghash_twist (byteswap128 H_in)) 2)))
                  (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2)) /\
               read (memory :> bytes128 htable) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
               read (memory :> bytes128 (word_add htable (word 16))) s =
                 word_join
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 1))
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
               read (memory :> bytes128 (word_add htable (word 32))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
               read (memory :> bytes128 (word_add htable (word 48))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2) /\
               read (memory :> bytes128 (word_add htable (word 64))) s =
                 word_join
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 3))
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 2)) /\
               read (memory :> bytes128 (word_add htable (word 80))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 3))
          (MAYCHANGE [PC] ,,
           MAYCHANGE [X0] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q19;Q20;Q21;Q22;
                      Q23;Q24;Q25] ,,
           MAYCHANGE [memory :> bytes(htable,96)] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst GCM_INIT_V8_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x9c`
   `\s. read X0 s = word_add htable (word 48) /\
        read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
        read Q20 s = byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
        read Q22 s = byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
        read Q16 s = word_xor
           (byteswap128 (byteswap128
              (h_power (ghash_twist (byteswap128 H_in)) 0)))
           (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
        read Q17 s = word_xor
           (byteswap128 (byteswap128
              (h_power (ghash_twist (byteswap128 H_in)) 1)))
           (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)) /\
        read (memory :> bytes128 htable) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
        read (memory :> bytes128 (word_add htable (word 16))) s =
          word_join
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 1))
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
        read (memory :> bytes128 (word_add htable (word 32))) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)` THEN
  CONJ_TAC THENL
   [(* --- SG1: entry -> pc+0x9c via GCM_INIT_V8_H2_MEM --- *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC] ,,
      MAYCHANGE [X0] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q16;Q17;Q18;Q19;Q20;Q21;Q22] ,,
      MAYCHANGE [memory :> bytes(htable,48)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC GCM_INIT_V8_H2_MEM THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]];
    (* --- SG2: pc+0x9c -> pc+0x134 via block C (GCM_INIT_V8_H34) --- *)
    ENSURES_POSTCONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
          read PC s = word (pc + 0x134) /\
          read X0 s = word_add htable (word 96) /\
          read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
          read Q22 s = byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
          read Q23 s = byteswap128 (polyval_dot
             (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0)))
             (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)))) /\
          read Q18 s = word_xor
             (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)))
             (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)) /\
          read Q16 s = word_xor
             (byteswap128 (byteswap128 (polyval_dot
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0)))
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1))))))
             (byteswap128 (polyval_dot
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0)))
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1))))) /\
          read (memory :> bytes128 htable) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
          read (memory :> bytes128 (word_add htable (word 16))) s =
            word_join
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 1))
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
          read (memory :> bytes128 (word_add htable (word 32))) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
          read (memory :> bytes128 (word_add htable (word 48))) s =
            byteswap128 (polyval_dot
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 0)))
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 1)))) /\
          read (memory :> bytes128 (word_add htable (word 64))) s =
            word_join
              (karatsuba_mid (polyval_dot
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 1)))
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 1)))))
              (karatsuba_mid (polyval_dot
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 0)))
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 1))))) /\
          read (memory :> bytes128 (word_add htable (word 80))) s =
            byteswap128 (polyval_dot
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 1)))
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 1))))` THEN
    CONJ_TAC THENL
     [(* bridge: block C dot form ==> h_power form (slots 3,4,5) *)
      GEN_TAC THEN
      REWRITE_TAC[BYTESWAP128_INVOL; HPOWER_DOT] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      (* apply block C (GCM_INIT_V8_H34) *)
      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE [PC] ,,
        MAYCHANGE [X0] ,,
        MAYCHANGE [Q0;Q1;Q2;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q23;Q24;Q25] ,,
        MAYCHANGE [memory :> bytes(word_add htable (word 48),48)] ,,
        MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        MATCH_MP_TAC GCM_INIT_V8_H34 THEN
        ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]]]]);;

(* ========================================================================= *)
(* Phase 9 -- block D (H^5/H^6) register bridge (0x134-0x1c8, steps 78-114).   *)
(*                                                                            *)
(* Block D is block C with the register lanes renamed: main operands          *)
(* a = Q22 (block B's byteswap128 H^2), b = Q23 (block C's byteswap128 H^3);   *)
(* mids Q18 = mid a', Q16 = mid b' (block C's tail leaves them there --        *)
(* MEASURED, see the note below).  It runs the two interleaved Karatsuba +     *)
(* 0xC2-reduction streams and computes, at 0x1c8 (before the store):           *)
(*                                                                            *)
(*   read Q26 = byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b))      *)
(*              (= slot 6, byteswap128 H^5 = byteswap128 (H^2 . H^3))          *)
(*   read Q27 = word_join (karatsuba_mid (dot (bs b)(bs b)))                   *)
(*                        (karatsuba_mid (dot (bs a)(bs b)))                   *)
(*              (= slot 7 packed middle; HIGH = mid H^6, LOW = mid H^5)         *)
(*   read Q28 = byteswap128 (polyval_dot (byteswap128 b) (byteswap128 b))      *)
(*              (= slot 8, byteswap128 H^6 = byteswap128 (H^3 . H^3))          *)
(*                                                                            *)
(* The factorization H^5 = H^2.H^3, H^6 = H^3.H^3 and slot 7's lane order were *)
(* MEASURED here (the postcondition IS the measurement -- a wrong form leaves  *)
(* a false GF(2) identity that BITBLAST_TAC rejects), not assumed.  Same       *)
(* recipe as GCM_INIT_V8_C_REGBRIDGE (block C is the same shape).  This lemma  *)
(* documents the measurement; H56 re-steps the block rather than citing it.    *)
(*                                                                            *)
(* Blocks D and E read the a*b Karatsuba MID product's operands in            *)
(* (mid b, mid a) order (D step 82: pmull v1,v16,v18 with v16 = mid b,         *)
(* v18 = mid a), swapped from block C's (mid a, mid b) and from               *)
(* PMUL_KARATSUBA's (a-mid, b-mid) convention.  word_pmul is commutative but   *)
(* the terms differ syntactically, so the pab_mid ABBREV cannot fire and a raw *)
(* word_pmul would survive into BITBLAST (huge BDD).  AB_MID_COMM is the       *)
(* targeted one-shot flip (WORD_PMUL_SYM at the block-D operand shape) that    *)
(* restores block C's (a-mid, b-mid) form after the SBW rewrites; it is inert  *)
(* on the hi/lo/square products, whose operand order block D preserves.        *)
(* ------------------------------------------------------------------------- *)

let AB_MID_COMM = prove
 (`word_pmul (word_xor (word_subword (b:int128) (64,64):64 word)
                       (word_subword b (0,64):64 word))
             (word_xor (word_subword (a:int128) (64,64):64 word)
                       (word_subword a (0,64):64 word)) =
   word_pmul (word_xor (word_subword a (64,64):64 word)
                       (word_subword a (0,64):64 word))
             (word_xor (word_subword b (64,64):64 word)
                       (word_subword b (0,64):64 word))`,
  MATCH_ACCEPT_TAC WORD_PMUL_SYM);;

let GCM_INIT_V8_D_REGBRIDGE = prove
 (`!(a:int128) (b:int128) pc.
     ensures arm
      (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
           read PC s = word (pc + 0x134) /\
           read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
           read Q22 s = a /\
           read Q23 s = b /\
           read Q18 s = word_xor (byteswap128 a) a /\
           read Q16 s = word_xor (byteswap128 b) b)
      (\s. read PC s = word (pc + 0x1c8) /\
           read Q26 s =
             byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b)) /\
           read Q27 s =
             word_join
               (karatsuba_mid (polyval_dot (byteswap128 b) (byteswap128 b)))
               (karatsuba_mid (polyval_dot (byteswap128 a) (byteswap128 b))) /\
           read Q28 s =
             byteswap128 (polyval_dot (byteswap128 b) (byteswap128 b)))
      (MAYCHANGE [PC] ,,
       MAYCHANGE [Q0;Q1;Q2;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q26;Q27;Q28] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int128`; `b:int128`; `pc:num`] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid] THEN
  REWRITE_TAC[KARA_EQ] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  REWRITE_TAC[SBW_XOR; SBW_BS; SBW_JOIN] THEN
  REWRITE_TAC[AB_MID_COMM] THEN   (* flip block D's (mid b, mid a) product *)
  ABBREV_TAC `(pab_hi:128 word) =
     word_pmul (word_subword (a:int128) (64,64):64 word)
               (word_subword (b:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pab_lo:128 word) =
     word_pmul (word_subword (a:int128) (0,64):64 word)
               (word_subword (b:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pab_mid:128 word) =
     word_pmul (word_xor (word_subword (a:int128) (64,64):64 word)
                         (word_subword (a:int128) (0,64):64 word))
               (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))` THEN
  ABBREV_TAC `(pbb_hi:128 word) =
     word_pmul (word_subword (b:int128) (64,64):64 word)
               (word_subword (b:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pbb_lo:128 word) =
     word_pmul (word_subword (b:int128) (0,64):64 word)
               (word_subword (b:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pbb_mid:128 word) =
     word_pmul (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))
               (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))` THEN
  REWRITE_TAC[byteswap128] THEN
  REPEAT CONJ_TAC THEN GEN_REWRITE_TAC I [LANE128] THEN CONJ_TAC THEN
  BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 9 -- block D (H^5/H^6) core + 3-register store (0x134-0x1cc,          *)
(* steps 78-115), stated with SYMBOLIC inputs a = Q22, b = Q23.                *)
(*                                                                            *)
(* Block-D analogue of GCM_INIT_V8_H34: wraps the register bridge with the     *)
(* contiguous 3-register store st1 {v26.2d-v28.2d},[x0],#48 at 0x1c8, landing  *)
(* the three H^5/H^6 sub-table slots (X0 = htable+96 on entry, +144 on exit):  *)
(*                                                                            *)
(*   slot 6 @ X0+0  (Htable[6])  = byteswap128 (H^5)                           *)
(*   slot 7 @ X0+16 (Htable[7], packed middle) =                               *)
(*     word_join (karatsuba_mid H^6) (karatsuba_mid H^5)  (HIGH = higher power)*)
(*   slot 8 @ X0+32 (Htable[8])  = byteswap128 (H^6)                           *)
(*                                                                            *)
(* Six ghost slot values g0..g5 (the H^2..H^4 sub-tables already stored) are   *)
(* threaded pre->post: block D writes only [htable+96, htable+144), disjoint   *)
(* from [htable, htable+96), so they survive the frame and close by ASM_REWRITE*)
(* -- this lets GCM_INIT_V8_H56_MEM carry slots 0-5 through block D.  Same      *)
(* recipe as GCM_INIT_V8_H34.                                                  *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_H56 = prove
 (`!(a:int128) (b:int128) g0 g1 g2 g3 g4 g5 htable pc.
     nonoverlapping (word pc,0x260) (htable,192)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x134) /\
               read X0 s = word_add htable (word 96) /\
               read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
               read Q22 s = a /\
               read Q23 s = b /\
               read Q18 s = word_xor (byteswap128 a) a /\
               read Q16 s = word_xor (byteswap128 b) b /\
               read (memory :> bytes128 htable) s = g0 /\
               read (memory :> bytes128 (word_add htable (word 16))) s = g1 /\
               read (memory :> bytes128 (word_add htable (word 32))) s = g2 /\
               read (memory :> bytes128 (word_add htable (word 48))) s = g3 /\
               read (memory :> bytes128 (word_add htable (word 64))) s = g4 /\
               read (memory :> bytes128 (word_add htable (word 80))) s = g5)
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x1cc) /\
               read X0 s = word_add htable (word 144) /\
               read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
               read Q22 s = a /\
               read Q26 s =
                 byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b)) /\
               read Q28 s =
                 byteswap128 (polyval_dot (byteswap128 b) (byteswap128 b)) /\
               read Q18 s = word_xor (byteswap128 a) a /\
               read Q16 s = word_xor
                  (byteswap128 (byteswap128
                     (polyval_dot (byteswap128 a) (byteswap128 b))))
                  (byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b))) /\
               read Q17 s = word_xor
                  (byteswap128 (byteswap128
                     (polyval_dot (byteswap128 b) (byteswap128 b))))
                  (byteswap128 (polyval_dot (byteswap128 b) (byteswap128 b))) /\
               read (memory :> bytes128 htable) s = g0 /\
               read (memory :> bytes128 (word_add htable (word 16))) s = g1 /\
               read (memory :> bytes128 (word_add htable (word 32))) s = g2 /\
               read (memory :> bytes128 (word_add htable (word 48))) s = g3 /\
               read (memory :> bytes128 (word_add htable (word 64))) s = g4 /\
               read (memory :> bytes128 (word_add htable (word 80))) s = g5 /\
               read (memory :> bytes128 (word_add htable (word 96))) s =
                 byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b)) /\
               read (memory :> bytes128 (word_add htable (word 112))) s =
                 word_join
                   (karatsuba_mid (polyval_dot (byteswap128 b) (byteswap128 b)))
                   (karatsuba_mid (polyval_dot (byteswap128 a) (byteswap128 b))) /\
               read (memory :> bytes128 (word_add htable (word 128))) s =
                 byteswap128 (polyval_dot (byteswap128 b) (byteswap128 b)))
          (MAYCHANGE [PC] ,,
           MAYCHANGE [X0] ,,
           MAYCHANGE [Q0;Q1;Q2;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q26;Q27;Q28] ,,
           MAYCHANGE [memory :> bytes(word_add htable (word 96),48)] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst GCM_INIT_V8_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid] THEN
  REWRITE_TAC[KARA_EQ] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  REWRITE_TAC[SBW_XOR; SBW_BS; SBW_JOIN] THEN
  REWRITE_TAC[AB_MID_COMM] THEN   (* flip block D's (mid b, mid a) product *)
  ABBREV_TAC `(pab_hi:128 word) =
     word_pmul (word_subword (a:int128) (64,64):64 word)
               (word_subword (b:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pab_lo:128 word) =
     word_pmul (word_subword (a:int128) (0,64):64 word)
               (word_subword (b:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pab_mid:128 word) =
     word_pmul (word_xor (word_subword (a:int128) (64,64):64 word)
                         (word_subword (a:int128) (0,64):64 word))
               (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))` THEN
  ABBREV_TAC `(pbb_hi:128 word) =
     word_pmul (word_subword (b:int128) (64,64):64 word)
               (word_subword (b:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pbb_lo:128 word) =
     word_pmul (word_subword (b:int128) (0,64):64 word)
               (word_subword (b:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pbb_mid:128 word) =
     word_pmul (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))
               (word_xor (word_subword (b:int128) (64,64):64 word)
                         (word_subword (b:int128) (0,64):64 word))` THEN
  REWRITE_TAC[byteswap128] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE) THEN
  GEN_REWRITE_TAC I [LANE128] THEN CONJ_TAC THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 9 -- H^5/H^6 sub-table with memory (entry -> pc+0x1cc, slots 0-8).    *)
(*                                                                            *)
(* Composes the strengthened GCM_INIT_V8_H34_MEM (entry->0x134: slots 0-5 +   *)
(* block-D input registers in block D's INPUT form) with block D              *)
(* (GCM_INIT_V8_H56, 0x134->0x1cc) into the first NINE htable_mem conjuncts    *)
(* in h_power form (h = ghash_twist (byteswap128 H_in)):                       *)
(*                                                                            *)
(*   slot 6 @ htable+96  = byteswap128 (h_power h 4)                           *)
(*   slot 7 @ htable+112 = word_join (km (h_power h 5)) (km (h_power h 4))      *)
(*   slot 8 @ htable+128 = byteswap128 (h_power h 5)                           *)
(*                                                                            *)
(* Structure mirrors GCM_INIT_V8_H34_MEM: ENSURES_SEQUENCE_TAC at pc+0x134.    *)
(*   SG1 (entry->0x134): the strengthened GCM_INIT_V8_H34_MEM, whose post is   *)
(*     stated in block D's INPUT form, so the mid-assertion matches BOTH       *)
(*     H34_MEM's post (SG1) and H56's precondition (SG2) verbatim -- both are  *)
(*     clean MATCH_MP_TAC.  (Do NOT unfold C_ARGUMENTS -- H34_MEM's pre keeps  *)
(*     it folded.)                                                            *)
(*   SG2 (0x134->0x1cc): GCM_INIT_V8_H56; the ENSURES_POSTCONDITION bridge     *)
(*     maps its polyval_dot post to h_power via BYTESWAP128_INVOL + HPOWER_DOT *)
(*     + numeral reduction (1+2+1=4 for H^5, 2+2+1=5 for H^6).  Slot 7 packed  *)
(*     middle is exercised by neither the KAT nor the differential test -- this*)
(*     proof is its only check; its measured HIGH=higher-power order matches   *)
(*     the corrected htable_mem.                                              *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_H56_MEM = prove
 (`!htable hp H_in pc.
     nonoverlapping (word pc,0x260) (htable,192) /\
     nonoverlapping (htable,192) (hp,16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [htable; hp] s /\
               read (memory :> bytes128 hp) s = H_in)
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x1cc) /\
               read X0 s = word_add htable (word 144) /\
               read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
               read Q22 s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
               read Q26 s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 4) /\
               read Q28 s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 5) /\
               read Q18 s = word_xor
                  (byteswap128 (byteswap128
                     (h_power (ghash_twist (byteswap128 H_in)) 1)))
                  (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)) /\
               read Q16 s = word_xor
                  (byteswap128 (byteswap128
                     (h_power (ghash_twist (byteswap128 H_in)) 4)))
                  (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 4)) /\
               read Q17 s = word_xor
                  (byteswap128 (byteswap128
                     (h_power (ghash_twist (byteswap128 H_in)) 5)))
                  (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 5)) /\
               read (memory :> bytes128 htable) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
               read (memory :> bytes128 (word_add htable (word 16))) s =
                 word_join
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 1))
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
               read (memory :> bytes128 (word_add htable (word 32))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
               read (memory :> bytes128 (word_add htable (word 48))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2) /\
               read (memory :> bytes128 (word_add htable (word 64))) s =
                 word_join
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 3))
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 2)) /\
               read (memory :> bytes128 (word_add htable (word 80))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 3) /\
               read (memory :> bytes128 (word_add htable (word 96))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 4) /\
               read (memory :> bytes128 (word_add htable (word 112))) s =
                 word_join
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 5))
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 4)) /\
               read (memory :> bytes128 (word_add htable (word 128))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 5))
          (MAYCHANGE [PC] ,,
           MAYCHANGE [X0] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q19;Q20;Q21;Q22;
                      Q23;Q24;Q25;Q26;Q27;Q28] ,,
           MAYCHANGE [memory :> bytes(htable,144)] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst GCM_INIT_V8_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x134`
   `\s. read X0 s = word_add htable (word 96) /\
        read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
        read Q22 s = byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
        read Q23 s = byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2) /\
        read Q18 s = word_xor
           (byteswap128 (byteswap128
              (h_power (ghash_twist (byteswap128 H_in)) 1)))
           (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)) /\
        read Q16 s = word_xor
           (byteswap128 (byteswap128
              (h_power (ghash_twist (byteswap128 H_in)) 2)))
           (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2)) /\
        read (memory :> bytes128 htable) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
        read (memory :> bytes128 (word_add htable (word 16))) s =
          word_join
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 1))
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
        read (memory :> bytes128 (word_add htable (word 32))) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
        read (memory :> bytes128 (word_add htable (word 48))) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2) /\
        read (memory :> bytes128 (word_add htable (word 64))) s =
          word_join
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 3))
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 2)) /\
        read (memory :> bytes128 (word_add htable (word 80))) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 3)` THEN
  CONJ_TAC THENL
   [(* --- SG1: entry -> pc+0x134 via strengthened GCM_INIT_V8_H34_MEM --- *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC] ,,
      MAYCHANGE [X0] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q19;Q20;Q21;Q22;
                 Q23;Q24;Q25] ,,
      MAYCHANGE [memory :> bytes(htable,96)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC GCM_INIT_V8_H34_MEM THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]];
    (* --- SG2: pc+0x134 -> pc+0x1cc via block D (GCM_INIT_V8_H56) --- *)
    ENSURES_POSTCONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
          read PC s = word (pc + 0x1cc) /\
          read X0 s = word_add htable (word 144) /\
          read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
          read Q22 s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
          read Q26 s = byteswap128 (polyval_dot
             (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)))
             (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2)))) /\
          read Q28 s = byteswap128 (polyval_dot
             (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2)))
             (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2)))) /\
          read Q18 s = word_xor
             (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)))
             (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)) /\
          read Q16 s = word_xor
             (byteswap128 (byteswap128 (polyval_dot
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)))
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2))))))
             (byteswap128 (polyval_dot
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)))
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2))))) /\
          read Q17 s = word_xor
             (byteswap128 (byteswap128 (polyval_dot
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2)))
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2))))))
             (byteswap128 (polyval_dot
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2)))
                (byteswap128 (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2))))) /\
          read (memory :> bytes128 htable) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
          read (memory :> bytes128 (word_add htable (word 16))) s =
            word_join
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 1))
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
          read (memory :> bytes128 (word_add htable (word 32))) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
          read (memory :> bytes128 (word_add htable (word 48))) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2) /\
          read (memory :> bytes128 (word_add htable (word 64))) s =
            word_join
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 3))
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 2)) /\
          read (memory :> bytes128 (word_add htable (word 80))) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 3) /\
          read (memory :> bytes128 (word_add htable (word 96))) s =
            byteswap128 (polyval_dot
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 1)))
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 2)))) /\
          read (memory :> bytes128 (word_add htable (word 112))) s =
            word_join
              (karatsuba_mid (polyval_dot
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 2)))
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 2)))))
              (karatsuba_mid (polyval_dot
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 1)))
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 2))))) /\
          read (memory :> bytes128 (word_add htable (word 128))) s =
            byteswap128 (polyval_dot
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 2)))
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 2))))` THEN
    CONJ_TAC THENL
     [(* bridge: block D dot form ==> h_power form (slots 6,7,8) *)
      GEN_TAC THEN
      REWRITE_TAC[BYTESWAP128_INVOL; HPOWER_DOT] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      (* apply block D (GCM_INIT_V8_H56) *)
      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE [PC] ,,
        MAYCHANGE [X0] ,,
        MAYCHANGE [Q0;Q1;Q2;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q26;Q27;Q28] ,,
        MAYCHANGE [memory :> bytes(word_add htable (word 96),48)] ,,
        MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        MATCH_MP_TAC GCM_INIT_V8_H56 THEN
        ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]]]]);;

(* ========================================================================= *)
(* Phase 9 -- block E (H^7/H^8) register bridge (0x1cc-0x258, steps 116-150). *)
(*                                                                            *)
(* Block E is NOT the same shape as blocks C/D.  Its two interleaved          *)
(* Karatsuba+0xC2-reduction streams SHARE the operand a = Q22 (block B's      *)
(* byteswap128 H^2, preserved through blocks C and D) and multiply it against *)
(* TWO distinct powers:                                                       *)
(*   stream 1 (v0/v2/v1 -> v16 -> v29):  a * b1,  b1 = Q26 = byteswap128 H^5  *)
(*     (block D's slot-6 output) -> H^7                                       *)
(*   stream 2 (v5/v7/v6 -> v17 -> v31):  a * b2,  b2 = Q28 = byteswap128 H^6  *)
(*     (block D's slot-8 output) -> H^8                                       *)
(* So the bridge takes THREE symbolic inputs a,b1,b2 and needs SIX ABBREV'd   *)
(* half-products (a*b1 hi/lo/mid, a*b2 hi/lo/mid) -- not the a*b + b*b pair    *)
(* of C/D.  The mids are Q18 = mid a, Q16 = mid b1, Q17 = mid b2.             *)
(*                                                                            *)
(* At 0x258 (before the no-writeback store):                                  *)
(*   read Q29 = byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b1))     *)
(*              (= slot 9,  byteswap128 H^7 = byteswap128 (H^2 . H^5))         *)
(*   read Q30 = word_join (karatsuba_mid (dot (bs a)(bs b2)))                  *)
(*                        (karatsuba_mid (dot (bs a)(bs b1)))                  *)
(*              (= slot 10 packed middle; HIGH = mid H^8, LOW = mid H^7 --      *)
(*               the LAST untested slot, MEASURED here)                        *)
(*   read Q31 = byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b2))     *)
(*              (= slot 11, byteswap128 H^8 = byteswap128 (H^2 . H^6))         *)
(*                                                                            *)
(* BOTH a*bi mid pmulls read their operands in (mid bi, mid a) order -- step   *)
(* 120 `pmull v1,v16,v18` (v16 = mid b1, v18 = mid a), step 121                *)
(* `pmull v6,v17,v18` (v17 = mid b2, v18 = mid a) -- swapped from KARA's       *)
(* (a-mid, b-mid) convention, so AB_MID_COMM must flip BOTH.  AB_MID_COMM is   *)
(* generic in a,b; REWRITE_TAC[AB_MID_COMM] canonicalizes both without looping *)
(* (verified: the prefix through the six ABBREVs leaves zero raw word_pmul).   *)
(* Same recipe as C_REGBRIDGE/D_REGBRIDGE otherwise.                          *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_E_REGBRIDGE = prove
 (`!(a:int128) (b1:int128) (b2:int128) pc.
     ensures arm
      (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
           read PC s = word (pc + 0x1cc) /\
           read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
           read Q22 s = a /\
           read Q26 s = b1 /\
           read Q28 s = b2 /\
           read Q18 s = word_xor (byteswap128 a) a /\
           read Q16 s = word_xor (byteswap128 b1) b1 /\
           read Q17 s = word_xor (byteswap128 b2) b2)
      (\s. read PC s = word (pc + 0x258) /\
           read Q29 s =
             byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b1)) /\
           read Q30 s =
             word_join
               (karatsuba_mid (polyval_dot (byteswap128 a) (byteswap128 b2)))
               (karatsuba_mid (polyval_dot (byteswap128 a) (byteswap128 b1))) /\
           read Q31 s =
             byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b2)))
      (MAYCHANGE [PC] ,,
       MAYCHANGE [Q0;Q1;Q2;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q29;Q30;Q31] ,,
       MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int128`; `b1:int128`; `b2:int128`; `pc:num`] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--35) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid] THEN
  REWRITE_TAC[KARA_EQ] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  REWRITE_TAC[SBW_XOR; SBW_BS; SBW_JOIN] THEN
  REWRITE_TAC[AB_MID_COMM] THEN   (* flip block E's two (mid bi, mid a) products *)
  ABBREV_TAC `(pab1_hi:128 word) =
     word_pmul (word_subword (a:int128) (64,64):64 word)
               (word_subword (b1:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pab1_lo:128 word) =
     word_pmul (word_subword (a:int128) (0,64):64 word)
               (word_subword (b1:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pab1_mid:128 word) =
     word_pmul (word_xor (word_subword (a:int128) (64,64):64 word)
                         (word_subword (a:int128) (0,64):64 word))
               (word_xor (word_subword (b1:int128) (64,64):64 word)
                         (word_subword (b1:int128) (0,64):64 word))` THEN
  ABBREV_TAC `(pab2_hi:128 word) =
     word_pmul (word_subword (a:int128) (64,64):64 word)
               (word_subword (b2:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pab2_lo:128 word) =
     word_pmul (word_subword (a:int128) (0,64):64 word)
               (word_subword (b2:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pab2_mid:128 word) =
     word_pmul (word_xor (word_subword (a:int128) (64,64):64 word)
                         (word_subword (a:int128) (0,64):64 word))
               (word_xor (word_subword (b2:int128) (64,64):64 word)
                         (word_subword (b2:int128) (0,64):64 word))` THEN
  REWRITE_TAC[byteswap128] THEN
  REPEAT CONJ_TAC THEN GEN_REWRITE_TAC I [LANE128] THEN CONJ_TAC THEN
  BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 9 -- block E (H^7/H^8) core + 3-register store (0x1cc-0x25c,          *)
(* steps 116-151), stated with SYMBOLIC inputs a = Q22, b1 = Q26, b2 = Q28.    *)
(*                                                                            *)
(* Block-E analogue of GCM_INIT_V8_H56: wraps the register bridge with the     *)
(* contiguous 3-register store st1 {v29.2d-v31.2d},[x0] at 0x258.  Unlike the  *)
(* C/D stores this one has NO post-increment (opcode 0x4c006c1d, Rm=31 absent),*)
(* so X0 STAYS at htable+144 and the three H^7/H^8 slots land at [x0], [x0+16],*)
(* [x0+32] = htable+144/+160/+176:                                            *)
(*                                                                            *)
(*   slot 9  @ htable+144 (Htable[9])  = byteswap128 (H^7)                     *)
(*   slot 10 @ htable+160 (Htable[10], packed middle) =                        *)
(*     word_join (karatsuba_mid H^8) (karatsuba_mid H^7)  (HIGH = higher power)*)
(*   slot 11 @ htable+176 (Htable[11]) = byteswap128 (H^8)                     *)
(*                                                                            *)
(* where H^7 = polyval_dot (byteswap128 a) (byteswap128 b1) and                *)
(* H^8 = polyval_dot (byteswap128 a) (byteswap128 b2).  Slot 10 is exercised   *)
(* by NEITHER the KAT nor the differential test -- the LAST such slot, so this *)
(* proof is its only check; its measured HIGH=higher-power order matches the   *)
(* corrected htable_mem.                                                       *)
(*                                                                            *)
(* Nine ghost slot values g0..g8 (the H^2..H^6 sub-tables already stored) are  *)
(* threaded pre->post: block E writes only [htable+144, htable+192), disjoint  *)
(* from [htable, htable+144), so they survive the frame and close by           *)
(* ASM_REWRITE -- this lets GCM_INIT_V8_H78_MEM carry slots 0-8 through block   *)
(* E.  Same recipe as GCM_INIT_V8_H56 (X0 unchanged, so no [X0] in the frame). *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_H78 = prove
 (`!(a:int128) (b1:int128) (b2:int128) g0 g1 g2 g3 g4 g5 g6 g7 g8 htable pc.
     nonoverlapping (word pc,0x260) (htable,192)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x1cc) /\
               read X0 s = word_add htable (word 144) /\
               read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
               read Q22 s = a /\
               read Q26 s = b1 /\
               read Q28 s = b2 /\
               read Q18 s = word_xor (byteswap128 a) a /\
               read Q16 s = word_xor (byteswap128 b1) b1 /\
               read Q17 s = word_xor (byteswap128 b2) b2 /\
               read (memory :> bytes128 htable) s = g0 /\
               read (memory :> bytes128 (word_add htable (word 16))) s = g1 /\
               read (memory :> bytes128 (word_add htable (word 32))) s = g2 /\
               read (memory :> bytes128 (word_add htable (word 48))) s = g3 /\
               read (memory :> bytes128 (word_add htable (word 64))) s = g4 /\
               read (memory :> bytes128 (word_add htable (word 80))) s = g5 /\
               read (memory :> bytes128 (word_add htable (word 96))) s = g6 /\
               read (memory :> bytes128 (word_add htable (word 112))) s = g7 /\
               read (memory :> bytes128 (word_add htable (word 128))) s = g8)
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x25c) /\
               read X0 s = word_add htable (word 144) /\
               read (memory :> bytes128 htable) s = g0 /\
               read (memory :> bytes128 (word_add htable (word 16))) s = g1 /\
               read (memory :> bytes128 (word_add htable (word 32))) s = g2 /\
               read (memory :> bytes128 (word_add htable (word 48))) s = g3 /\
               read (memory :> bytes128 (word_add htable (word 64))) s = g4 /\
               read (memory :> bytes128 (word_add htable (word 80))) s = g5 /\
               read (memory :> bytes128 (word_add htable (word 96))) s = g6 /\
               read (memory :> bytes128 (word_add htable (word 112))) s = g7 /\
               read (memory :> bytes128 (word_add htable (word 128))) s = g8 /\
               read (memory :> bytes128 (word_add htable (word 144))) s =
                 byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b1)) /\
               read (memory :> bytes128 (word_add htable (word 160))) s =
                 word_join
                   (karatsuba_mid (polyval_dot (byteswap128 a) (byteswap128 b2)))
                   (karatsuba_mid (polyval_dot (byteswap128 a) (byteswap128 b1))) /\
               read (memory :> bytes128 (word_add htable (word 176))) s =
                 byteswap128 (polyval_dot (byteswap128 a) (byteswap128 b2)))
          (MAYCHANGE [PC] ,,
           MAYCHANGE [Q0;Q1;Q2;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q29;Q30;Q31] ,,
           MAYCHANGE [memory :> bytes(word_add htable (word 144),48)] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst GCM_INIT_V8_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GCM_INIT_V8_EXEC (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[polyval_dot; karatsuba_mid] THEN
  REWRITE_TAC[KARA_EQ] THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  REWRITE_TAC[SBW_XOR; SBW_BS; SBW_JOIN] THEN
  REWRITE_TAC[AB_MID_COMM] THEN
  ABBREV_TAC `(pab1_hi:128 word) =
     word_pmul (word_subword (a:int128) (64,64):64 word)
               (word_subword (b1:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pab1_lo:128 word) =
     word_pmul (word_subword (a:int128) (0,64):64 word)
               (word_subword (b1:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pab1_mid:128 word) =
     word_pmul (word_xor (word_subword (a:int128) (64,64):64 word)
                         (word_subword (a:int128) (0,64):64 word))
               (word_xor (word_subword (b1:int128) (64,64):64 word)
                         (word_subword (b1:int128) (0,64):64 word))` THEN
  ABBREV_TAC `(pab2_hi:128 word) =
     word_pmul (word_subword (a:int128) (64,64):64 word)
               (word_subword (b2:int128) (64,64):64 word)` THEN
  ABBREV_TAC `(pab2_lo:128 word) =
     word_pmul (word_subword (a:int128) (0,64):64 word)
               (word_subword (b2:int128) (0,64):64 word)` THEN
  ABBREV_TAC `(pab2_mid:128 word) =
     word_pmul (word_xor (word_subword (a:int128) (64,64):64 word)
                         (word_subword (a:int128) (0,64):64 word))
               (word_xor (word_subword (b2:int128) (64,64):64 word)
                         (word_subword (b2:int128) (0,64):64 word))` THEN
  REWRITE_TAC[byteswap128] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE) THEN
  GEN_REWRITE_TAC I [LANE128] THEN CONJ_TAC THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* Phase 9/10 -- H^7/H^8 sub-table with memory (entry -> pc+0x25c, ALL 12      *)
(* slots).                                                                     *)
(*                                                                            *)
(* Composes the strengthened GCM_INIT_V8_H56_MEM (entry->0x1cc: slots 0-8 +   *)
(* block-E input registers in block E's INPUT form) with block E              *)
(* (GCM_INIT_V8_H78, 0x1cc->0x25c) into all TWELVE htable_mem conjuncts in    *)
(* h_power form (h = ghash_twist (byteswap128 H_in)):                          *)
(*                                                                            *)
(*   slot 9  @ htable+144 = byteswap128 (h_power h 6)                          *)
(*   slot 10 @ htable+160 = word_join (km (h_power h 7)) (km (h_power h 6))     *)
(*   slot 11 @ htable+176 = byteswap128 (h_power h 7)                          *)
(*                                                                            *)
(* Structure mirrors GCM_INIT_V8_H56_MEM: ENSURES_SEQUENCE_TAC at pc+0x1cc.    *)
(*   SG1 (entry->0x1cc): the strengthened GCM_INIT_V8_H56_MEM, whose post is   *)
(*     stated in block E's INPUT form (a = byteswap128 (h_power h 1),          *)
(*     b1 = byteswap128 (h_power h 4), b2 = byteswap128 (h_power h 5)), so the *)
(*     mid-assertion matches BOTH H56_MEM's post (SG1) and H78's precondition  *)
(*     (SG2) verbatim -- both clean MATCH_MP_TAC.  (Do NOT unfold C_ARGUMENTS  *)
(*     -- H56_MEM's pre keeps it folded.)                                     *)
(*   SG2 (0x1cc->0x25c): GCM_INIT_V8_H78; the ENSURES_POSTCONDITION bridge     *)
(*     maps its polyval_dot post to h_power via BYTESWAP128_INVOL + HPOWER_DOT *)
(*     + numeral reduction (1+4+1=6 for H^7, 1+5+1=7 for H^8).  Slot 10 packed *)
(*     middle -- the LAST untested slot; this proof is its only check.        *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_H78_MEM = prove
 (`!htable hp H_in pc.
     nonoverlapping (word pc,0x260) (htable,192) /\
     nonoverlapping (htable,192) (hp,16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [htable; hp] s /\
               read (memory :> bytes128 hp) s = H_in)
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word (pc + 0x25c) /\
               read X0 s = word_add htable (word 144) /\
               read (memory :> bytes128 htable) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
               read (memory :> bytes128 (word_add htable (word 16))) s =
                 word_join
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 1))
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
               read (memory :> bytes128 (word_add htable (word 32))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
               read (memory :> bytes128 (word_add htable (word 48))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2) /\
               read (memory :> bytes128 (word_add htable (word 64))) s =
                 word_join
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 3))
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 2)) /\
               read (memory :> bytes128 (word_add htable (word 80))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 3) /\
               read (memory :> bytes128 (word_add htable (word 96))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 4) /\
               read (memory :> bytes128 (word_add htable (word 112))) s =
                 word_join
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 5))
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 4)) /\
               read (memory :> bytes128 (word_add htable (word 128))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 5) /\
               read (memory :> bytes128 (word_add htable (word 144))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 6) /\
               read (memory :> bytes128 (word_add htable (word 160))) s =
                 word_join
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 7))
                   (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 6)) /\
               read (memory :> bytes128 (word_add htable (word 176))) s =
                 byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 7))
          (MAYCHANGE [PC] ,,
           MAYCHANGE [X0] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q19;Q20;Q21;Q22;
                      Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31] ,,
           MAYCHANGE [memory :> bytes(htable,192)] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst GCM_INIT_V8_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x1cc`
   `\s. read X0 s = word_add htable (word 144) /\
        read Q19 s = (word 0xC200000000000000C200000000000000:int128) /\
        read Q22 s = byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
        read Q26 s = byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 4) /\
        read Q28 s = byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 5) /\
        read Q18 s = word_xor
           (byteswap128 (byteswap128
              (h_power (ghash_twist (byteswap128 H_in)) 1)))
           (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1)) /\
        read Q16 s = word_xor
           (byteswap128 (byteswap128
              (h_power (ghash_twist (byteswap128 H_in)) 4)))
           (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 4)) /\
        read Q17 s = word_xor
           (byteswap128 (byteswap128
              (h_power (ghash_twist (byteswap128 H_in)) 5)))
           (byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 5)) /\
        read (memory :> bytes128 htable) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
        read (memory :> bytes128 (word_add htable (word 16))) s =
          word_join
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 1))
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
        read (memory :> bytes128 (word_add htable (word 32))) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
        read (memory :> bytes128 (word_add htable (word 48))) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2) /\
        read (memory :> bytes128 (word_add htable (word 64))) s =
          word_join
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 3))
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 2)) /\
        read (memory :> bytes128 (word_add htable (word 80))) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 3) /\
        read (memory :> bytes128 (word_add htable (word 96))) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 4) /\
        read (memory :> bytes128 (word_add htable (word 112))) s =
          word_join
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 5))
            (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 4)) /\
        read (memory :> bytes128 (word_add htable (word 128))) s =
          byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 5)` THEN
  CONJ_TAC THENL
   [(* --- SG1: entry -> pc+0x1cc via strengthened GCM_INIT_V8_H56_MEM --- *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC] ,,
      MAYCHANGE [X0] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q19;Q20;Q21;Q22;
                 Q23;Q24;Q25;Q26;Q27;Q28] ,,
      MAYCHANGE [memory :> bytes(htable,144)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC GCM_INIT_V8_H56_MEM THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]];
    (* --- SG2: pc+0x1cc -> pc+0x25c via block E (GCM_INIT_V8_H78) --- *)
    ENSURES_POSTCONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
          read PC s = word (pc + 0x25c) /\
          read X0 s = word_add htable (word 144) /\
          read (memory :> bytes128 htable) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 0) /\
          read (memory :> bytes128 (word_add htable (word 16))) s =
            word_join
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 1))
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 0)) /\
          read (memory :> bytes128 (word_add htable (word 32))) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 1) /\
          read (memory :> bytes128 (word_add htable (word 48))) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 2) /\
          read (memory :> bytes128 (word_add htable (word 64))) s =
            word_join
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 3))
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 2)) /\
          read (memory :> bytes128 (word_add htable (word 80))) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 3) /\
          read (memory :> bytes128 (word_add htable (word 96))) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 4) /\
          read (memory :> bytes128 (word_add htable (word 112))) s =
            word_join
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 5))
              (karatsuba_mid (h_power (ghash_twist (byteswap128 H_in)) 4)) /\
          read (memory :> bytes128 (word_add htable (word 128))) s =
            byteswap128 (h_power (ghash_twist (byteswap128 H_in)) 5) /\
          read (memory :> bytes128 (word_add htable (word 144))) s =
            byteswap128 (polyval_dot
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 1)))
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 4)))) /\
          read (memory :> bytes128 (word_add htable (word 160))) s =
            word_join
              (karatsuba_mid (polyval_dot
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 1)))
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 5)))))
              (karatsuba_mid (polyval_dot
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 1)))
                (byteswap128 (byteswap128
                   (h_power (ghash_twist (byteswap128 H_in)) 4))))) /\
          read (memory :> bytes128 (word_add htable (word 176))) s =
            byteswap128 (polyval_dot
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 1)))
              (byteswap128 (byteswap128
                 (h_power (ghash_twist (byteswap128 H_in)) 5))))` THEN
    CONJ_TAC THENL
     [(* bridge: block E dot form ==> h_power form (slots 9,10,11) *)
      GEN_TAC THEN
      REWRITE_TAC[BYTESWAP128_INVOL; HPOWER_DOT] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      (* apply block E (GCM_INIT_V8_H78) *)
      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC
       `MAYCHANGE [PC] ,,
        MAYCHANGE [Q0;Q1;Q2;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q29;Q30;Q31] ,,
        MAYCHANGE [memory :> bytes(word_add htable (word 144),48)] ,,
        MAYCHANGE [events]` THEN
      CONJ_TAC THENL
       [SUBSUMED_MAYCHANGE_TAC;
        MATCH_MP_TAC GCM_INIT_V8_H78 THEN
        ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]]]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness (core): from function entry to the ret PC, gcm_init_v8 fills   *)
(* the 12-slot Htable with the byteswapped H-powers and packed Karatsuba      *)
(* middle terms of the twisted secret ghash_twist(byteswap128 H_in).          *)
(*                                                                            *)
(* h_power h 0 = h, so the htable_mem argument is the *twisted* H (the value  *)
(* block A holds in v20 at 0x038, before its 0x03c byteswap-and-store).       *)
(*                                                                            *)
(* CHEAT-stubbed scaffold (Phase 2): this pins the exact statement everything *)
(* downstream builds toward.  Discharged in Phase 10 (needs the Phase 3       *)
(* decode extension so the full mc steps).                                    *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_CORRECT = prove
 (`!htable hp H_in pc.
     nonoverlapping (word pc,0x260) (htable,192) /\
     nonoverlapping (htable,192) (hp,16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [htable; hp] s /\
               read (memory :> bytes128 hp) s = H_in)
          (\s. read PC s = word (pc + 0x25c) /\
               htable_mem (ghash_twist (byteswap128 H_in)) htable s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(htable,192)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst GCM_INIT_V8_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_POSTCONDITION_TAC
   `\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
        read PC s = word (pc + 0x25c) /\
        read X0 s = word_add htable (word 144) /\
        htable_mem (ghash_twist (byteswap128 H_in)) htable s` THEN
  CONJ_TAC THENL
   [(* the 12 slots (folded as htable_mem) plus PC give the correctness post *)
    GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    (* unfold htable_mem into the 12 explicit slots that H78_MEM establishes *)
    REWRITE_TAC[htable_mem] THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE [PC] ,,
      MAYCHANGE [X0] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q16;Q17;Q18;Q19;Q20;Q21;Q22;
                 Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31] ,,
      MAYCHANGE [memory :> bytes(htable,192)] ,,
      MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC GCM_INIT_V8_H78_MEM THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]]]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine wrapper.  gcm_init_v8 is a leaf function with no stack frame     *)
(* (no prologue/epilogue beyond the final `ret` at 0x25c), so the standard     *)
(* ARM_ADD_RETURN_NOSTACK_TAC lifts the core theorem to a subroutine spec:     *)
(* PC starts at entry and returns to X30 (returnaddress); the MAYCHANGE frame  *)
(* is the full System-V ABI-permitted set plus the 192-byte output table.      *)
(* ------------------------------------------------------------------------- *)

let GCM_INIT_V8_SUBROUTINE_CORRECT = prove
 (`!htable hp H_in pc returnaddress.
     nonoverlapping (word pc,0x260) (htable,192) /\
     nonoverlapping (htable,192) (hp,16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) gcm_init_v8_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [htable; hp] s /\
               read (memory :> bytes128 hp) s = H_in)
          (\s. read PC s = returnaddress /\
               htable_mem (ghash_twist (byteswap128 H_in)) htable s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(htable,192)])`,
  (* htable_mem is an opaque compound memory predicate, so unfold it (in the
     goal and in the core theorem) to the 12 explicit bytes128 reads before
     ARM_ADD_RETURN_NOSTACK_TAC -- otherwise its closer cannot carry the
     predicate across the `ret` step (s1->s2) component by component. *)
  REWRITE_TAC[htable_mem] THEN
  ARM_ADD_RETURN_NOSTACK_TAC GCM_INIT_V8_EXEC
    (REWRITE_RULE[htable_mem] GCM_INIT_V8_CORRECT));;
