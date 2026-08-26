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
  CHEAT_TAC);;
