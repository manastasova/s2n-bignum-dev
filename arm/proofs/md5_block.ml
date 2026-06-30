(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correctness proof of the ARM64 MD5 compression function md5_block.        *)
(*                                                                           *)
(* The function absorbs `num` consecutive 64-byte message blocks (read as    *)
(* little-endian 32-bit words) into the four-word (A,B,C,D) state held at     *)
(* state[0..3], leaving the updated state in place.  See arm/md5/md5_block.S  *)
(* and the functional specification in arm/proofs/utils/md5_spec.ml.         *)
(*                                                                           *)
(* This file is being built up incrementally (see orchestrator STATE.md):    *)
(*   Phase 3: scaffold + smallest register-only fragment (one F-round).      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/md5_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code, as decoded from arm/md5/md5_block.o.                     *)
(* ------------------------------------------------------------------------- *)

let md5_block_mc = define_assert_from_elf "md5_block_mc" "arm/md5/md5_block.o"
[
  0xa9bb53f3;       (* stp x19, x20, [sp, #-80]! *)
  0xa9015bf5;       (* stp x21, x22, [sp, #16] *)
  0xa90263f7;       (* stp x23, x24, [sp, #32] *)
  0xa9036bf9;       (* stp x25, x26, [sp, #48] *)
  0xa90473fb;       (* stp x27, x28, [sp, #64] *)
  0x29402c0a;       (* ldp w10, w11, [x0] *)
  0x2941340c;       (* ldp w12, w13, [x0, #8] *)
  0xd503201f;       (* nop *)
  0xca0d0191;       (* eor x17, x12, x13 *)
  0x8a0b0230;       (* and x16, x17, x11 *)
  0xa9400c2f;       (* ldp x15, x3, [x1] *)
  0xca0d020e;       (* eor x14, x16, x13 *)
  0xd2948f09;       (* mov x9, #0xa478 *)
  0xf2baed49;       (* movk x9, #0xd76a, lsl #16 *)
  0x0b0f0148;       (* add w8, w10, w15 *)
  0x0b090107;       (* add w7, w8, w9 *)
  0x0b0e00e6;       (* add w6, w7, w14 *)
  0x138664c6;       (* ror w6, w6, #25 *)
  0xca0c0165;       (* eor x5, x11, x12 *)
  0x0b060164;       (* add w4, w11, w6 *)
  0x8a0400a8;       (* and x8, x5, x4 *)
  0xca0c0111;       (* eor x17, x8, x12 *)
  0xd296ead0;       (* mov x16, #0xb756 *)
  0xf2bd18f0;       (* movk x16, #0xe8c7, lsl #16 *)
  0xd360fdf4;       (* lsr x20, x15, #32 *)
  0x0b1401a9;       (* add w9, w13, w20 *)
  0x0b100127;       (* add w7, w9, w16 *)
  0x0b1100ee;       (* add w14, w7, w17 *)
  0x138e51ce;       (* ror w14, w14, #20 *)
  0xca0b0086;       (* eor x6, x4, x11 *)
  0x0b0e0085;       (* add w5, w4, w14 *)
  0x8a0500c8;       (* and x8, x6, x5 *)
  0xca0b0109;       (* eor x9, x8, x11 *)
  0xd28e1b70;       (* mov x16, #0x70db *)
  0xf2a48410;       (* movk x16, #0x2420, lsl #16 *)
  0x0b030187;       (* add w7, w12, w3 *)
  0x0b1000f1;       (* add w17, w7, w16 *)
  0x0b09022e;       (* add w14, w17, w9 *)
  0x138e3dce;       (* ror w14, w14, #15 *)
  0xca0400a6;       (* eor x6, x5, x4 *)
  0x0b0e00a8;       (* add w8, w5, w14 *)
  0x8a0800c7;       (* and x7, x6, x8 *)
  0xca0400f0;       (* eor x16, x7, x4 *)
  0xd299ddc9;       (* mov x9, #0xceee *)
  0xf2b837a9;       (* movk x9, #0xc1bd, lsl #16 *)
  0xd360fc75;       (* lsr x21, x3, #32 *)
  0x0b15016e;       (* add w14, w11, w21 *)
  0x0b0901c6;       (* add w6, w14, w9 *)
  0x0b1000c7;       (* add w7, w6, w16 *)
  0x138728e7;       (* ror w7, w7, #10 *)
  0xca050111;       (* eor x17, x8, x5 *)
  0x0b070109;       (* add w9, w8, w7 *)
  0xa9411c2e;       (* ldp x14, x7, [x1, #16] *)
  0x8a090230;       (* and x16, x17, x9 *)
  0xca050206;       (* eor x6, x16, x5 *)
  0xd281f5f0;       (* mov x16, #0xfaf *)
  0xf2beaf90;       (* movk x16, #0xf57c, lsl #16 *)
  0x0b0e0091;       (* add w17, w4, w14 *)
  0x0b100230;       (* add w16, w17, w16 *)
  0x0b060204;       (* add w4, w16, w6 *)
  0x13846484;       (* ror w4, w4, #25 *)
  0xca080130;       (* eor x16, x9, x8 *)
  0x0b040131;       (* add w17, w9, w4 *)
  0x8a110210;       (* and x16, x16, x17 *)
  0xca080206;       (* eor x6, x16, x8 *)
  0xd298c544;       (* mov x4, #0xc62a *)
  0xf2a8f0e4;       (* movk x4, #0x4787, lsl #16 *)
  0xd360fdd6;       (* lsr x22, x14, #32 *)
  0x0b1600b0;       (* add w16, w5, w22 *)
  0x0b040210;       (* add w16, w16, w4 *)
  0x0b060205;       (* add w5, w16, w6 *)
  0x138550a5;       (* ror w5, w5, #20 *)
  0xca090224;       (* eor x4, x17, x9 *)
  0x0b050233;       (* add w19, w17, w5 *)
  0x8a130086;       (* and x6, x4, x19 *)
  0xca0900c5;       (* eor x5, x6, x9 *)
  0xd288c264;       (* mov x4, #0x4613 *)
  0xf2b50604;       (* movk x4, #0xa830, lsl #16 *)
  0x0b070106;       (* add w6, w8, w7 *)
  0x0b0400c8;       (* add w8, w6, w4 *)
  0x0b050104;       (* add w4, w8, w5 *)
  0x13843c84;       (* ror w4, w4, #15 *)
  0xca110266;       (* eor x6, x19, x17 *)
  0x0b040268;       (* add w8, w19, w4 *)
  0x8a0800c5;       (* and x5, x6, x8 *)
  0xca1100a4;       (* eor x4, x5, x17 *)
  0xd292a026;       (* mov x6, #0x9501 *)
  0xf2bfa8c6;       (* movk x6, #0xfd46, lsl #16 *)
  0xd360fcf7;       (* lsr x23, x7, #32 *)
  0x0b170129;       (* add w9, w9, w23 *)
  0x0b060125;       (* add w5, w9, w6 *)
  0x0b0400a9;       (* add w9, w5, w4 *)
  0x13892929;       (* ror w9, w9, #10 *)
  0xca130106;       (* eor x6, x8, x19 *)
  0x0b090104;       (* add w4, w8, w9 *)
  0xa9424025;       (* ldp x5, x16, [x1, #32] *)
  0x8a0400c9;       (* and x9, x6, x4 *)
  0xca130126;       (* eor x6, x9, x19 *)
  0xd2931b09;       (* mov x9, #0x98d8 *)
  0xf2ad3009;       (* movk x9, #0x6980, lsl #16 *)
  0x0b050231;       (* add w17, w17, w5 *)
  0x0b090229;       (* add w9, w17, w9 *)
  0x0b060131;       (* add w17, w9, w6 *)
  0x13916631;       (* ror w17, w17, #25 *)
  0xca080089;       (* eor x9, x4, x8 *)
  0x0b110086;       (* add w6, w4, w17 *)
  0x8a060131;       (* and x17, x9, x6 *)
  0xca080229;       (* eor x9, x17, x8 *)
  0xd29ef5f1;       (* mov x17, #0xf7af *)
  0xf2b16891;       (* movk x17, #0x8b44, lsl #16 *)
  0xd360fcb8;       (* lsr x24, x5, #32 *)
  0x0b180273;       (* add w19, w19, w24 *)
  0x0b110271;       (* add w17, w19, w17 *)
  0x0b090233;       (* add w19, w17, w9 *)
  0x13935273;       (* ror w19, w19, #20 *)
  0xca0400c9;       (* eor x9, x6, x4 *)
  0x0b1300d1;       (* add w17, w6, w19 *)
  0x8a110129;       (* and x9, x9, x17 *)
  0xca040129;       (* eor x9, x9, x4 *)
  0xd28b762b;       (* mov x11, #0x5bb1 *)
  0xf2bfffeb;       (* movk x11, #0xffff, lsl #16 *)
  0x0b100108;       (* add w8, w8, w16 *)
  0x0b0b0108;       (* add w8, w8, w11 *)
  0x0b090108;       (* add w8, w8, w9 *)
  0x13883d08;       (* ror w8, w8, #15 *)
  0xca060229;       (* eor x9, x17, x6 *)
  0x0b080228;       (* add w8, w17, w8 *)
  0x8a080129;       (* and x9, x9, x8 *)
  0xca060129;       (* eor x9, x9, x6 *)
  0xd29af7cb;       (* mov x11, #0xd7be *)
  0xf2b12b8b;       (* movk x11, #0x895c, lsl #16 *)
  0xd360fe19;       (* lsr x25, x16, #32 *)
  0x0b190084;       (* add w4, w4, w25 *)
  0x0b0b0084;       (* add w4, w4, w11 *)
  0x0b090089;       (* add w9, w4, w9 *)
  0x13892929;       (* ror w9, w9, #10 *)
  0xca110104;       (* eor x4, x8, x17 *)
  0x0b090109;       (* add w9, w8, w9 *)
  0xa943302b;       (* ldp x11, x12, [x1, #48] *)
  0x8a090084;       (* and x4, x4, x9 *)
  0xca110084;       (* eor x4, x4, x17 *)
  0xd2822453;       (* mov x19, #0x1122 *)
  0xf2ad7213;       (* movk x19, #0x6b90, lsl #16 *)
  0x0b0b00c6;       (* add w6, w6, w11 *)
  0x0b1300c6;       (* add w6, w6, w19 *)
  0x0b0400c4;       (* add w4, w6, w4 *)
  0x13846484;       (* ror w4, w4, #25 *)
  0xca080126;       (* eor x6, x9, x8 *)
  0x0b040124;       (* add w4, w9, w4 *)
  0x8a0400c6;       (* and x6, x6, x4 *)
  0xca0800c6;       (* eor x6, x6, x8 *)
  0xd28e3273;       (* mov x19, #0x7193 *)
  0xf2bfb313;       (* movk x19, #0xfd98, lsl #16 *)
  0xd360fd7a;       (* lsr x26, x11, #32 *)
  0x0b1a0231;       (* add w17, w17, w26 *)
  0x0b130231;       (* add w17, w17, w19 *)
  0x0b060231;       (* add w17, w17, w6 *)
  0x13915231;       (* ror w17, w17, #20 *)
  0xca090086;       (* eor x6, x4, x9 *)
  0x0b110091;       (* add w17, w4, w17 *)
  0x8a1100c6;       (* and x6, x6, x17 *)
  0xca0900c6;       (* eor x6, x6, x9 *)
  0xd28871cd;       (* mov x13, #0x438e *)
  0xf2b4cf2d;       (* movk x13, #0xa679, lsl #16 *)
  0x0b0c0108;       (* add w8, w8, w12 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x0b060108;       (* add w8, w8, w6 *)
  0x13883d08;       (* ror w8, w8, #15 *)
  0xca040226;       (* eor x6, x17, x4 *)
  0x0b080228;       (* add w8, w17, w8 *)
  0x8a0800c6;       (* and x6, x6, x8 *)
  0xca0400c6;       (* eor x6, x6, x4 *)
  0xd281042d;       (* mov x13, #0x821 *)
  0xf2a9368d;       (* movk x13, #0x49b4, lsl #16 *)
  0xd360fd9b;       (* lsr x27, x12, #32 *)
  0x0b1b0129;       (* add w9, w9, w27 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x0b060129;       (* add w9, w9, w6 *)
  0x13892929;       (* ror w9, w9, #10 *)
  0x8a310106;       (* bic x6, x8, x17 *)
  0x0b090109;       (* add w9, w8, w9 *)
  0xd284ac4d;       (* mov x13, #0x2562 *)
  0xf2bec3cd;       (* movk x13, #0xf61e, lsl #16 *)
  0x0b140084;       (* add w4, w4, w20 *)
  0x0b0d0084;       (* add w4, w4, w13 *)
  0x8a11012d;       (* and x13, x9, x17 *)
  0x0b060084;       (* add w4, w4, w6 *)
  0x0b0d0084;       (* add w4, w4, w13 *)
  0x13846c84;       (* ror w4, w4, #27 *)
  0x8a280126;       (* bic x6, x9, x8 *)
  0x0b040124;       (* add w4, w9, w4 *)
  0xd296680d;       (* mov x13, #0xb340 *)
  0xf2b8080d;       (* movk x13, #0xc040, lsl #16 *)
  0x0b070231;       (* add w17, w17, w7 *)
  0x0b0d0231;       (* add w17, w17, w13 *)
  0x8a08008d;       (* and x13, x4, x8 *)
  0x0b060231;       (* add w17, w17, w6 *)
  0x0b0d0231;       (* add w17, w17, w13 *)
  0x13915e31;       (* ror w17, w17, #23 *)
  0x8a290086;       (* bic x6, x4, x9 *)
  0x0b110091;       (* add w17, w4, w17 *)
  0xd28b4a2d;       (* mov x13, #0x5a51 *)
  0xf2a4cbcd;       (* movk x13, #0x265e, lsl #16 *)
  0x0b190108;       (* add w8, w8, w25 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x8a09022d;       (* and x13, x17, x9 *)
  0x0b060108;       (* add w8, w8, w6 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x13884908;       (* ror w8, w8, #18 *)
  0x8a240226;       (* bic x6, x17, x4 *)
  0x0b080228;       (* add w8, w17, w8 *)
  0xd298f54d;       (* mov x13, #0xc7aa *)
  0xf2bd36cd;       (* movk x13, #0xe9b6, lsl #16 *)
  0x0b0f0129;       (* add w9, w9, w15 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x8a04010d;       (* and x13, x8, x4 *)
  0x0b060129;       (* add w9, w9, w6 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x13893129;       (* ror w9, w9, #12 *)
  0x8a310106;       (* bic x6, x8, x17 *)
  0x0b090109;       (* add w9, w8, w9 *)
  0xd2820bad;       (* mov x13, #0x105d *)
  0xf2bac5ed;       (* movk x13, #0xd62f, lsl #16 *)
  0x0b160084;       (* add w4, w4, w22 *)
  0x0b0d0084;       (* add w4, w4, w13 *)
  0x8a11012d;       (* and x13, x9, x17 *)
  0x0b060084;       (* add w4, w4, w6 *)
  0x0b0d0084;       (* add w4, w4, w13 *)
  0x13846c84;       (* ror w4, w4, #27 *)
  0x8a280126;       (* bic x6, x9, x8 *)
  0x0b040124;       (* add w4, w9, w4 *)
  0xd2828a6d;       (* mov x13, #0x1453 *)
  0xf2a0488d;       (* movk x13, #0x244, lsl #16 *)
  0x0b100231;       (* add w17, w17, w16 *)
  0x0b0d0231;       (* add w17, w17, w13 *)
  0x8a08008d;       (* and x13, x4, x8 *)
  0x0b060231;       (* add w17, w17, w6 *)
  0x0b0d0231;       (* add w17, w17, w13 *)
  0x13915e31;       (* ror w17, w17, #23 *)
  0x8a290086;       (* bic x6, x4, x9 *)
  0x0b110091;       (* add w17, w4, w17 *)
  0xd29cd02d;       (* mov x13, #0xe681 *)
  0xf2bb142d;       (* movk x13, #0xd8a1, lsl #16 *)
  0x0b1b0108;       (* add w8, w8, w27 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x8a09022d;       (* and x13, x17, x9 *)
  0x0b060108;       (* add w8, w8, w6 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x13884908;       (* ror w8, w8, #18 *)
  0x8a240226;       (* bic x6, x17, x4 *)
  0x0b080228;       (* add w8, w17, w8 *)
  0xd29f790d;       (* mov x13, #0xfbc8 *)
  0xf2bcfa6d;       (* movk x13, #0xe7d3, lsl #16 *)
  0x0b0e0129;       (* add w9, w9, w14 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x8a04010d;       (* and x13, x8, x4 *)
  0x0b060129;       (* add w9, w9, w6 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x13893129;       (* ror w9, w9, #12 *)
  0x8a310106;       (* bic x6, x8, x17 *)
  0x0b090109;       (* add w9, w8, w9 *)
  0xd299bccd;       (* mov x13, #0xcde6 *)
  0xf2a43c2d;       (* movk x13, #0x21e1, lsl #16 *)
  0x0b180084;       (* add w4, w4, w24 *)
  0x0b0d0084;       (* add w4, w4, w13 *)
  0x8a11012d;       (* and x13, x9, x17 *)
  0x0b060084;       (* add w4, w4, w6 *)
  0x0b0d0084;       (* add w4, w4, w13 *)
  0x13846c84;       (* ror w4, w4, #27 *)
  0x8a280126;       (* bic x6, x9, x8 *)
  0x0b040124;       (* add w4, w9, w4 *)
  0xd280facd;       (* mov x13, #0x7d6 *)
  0xf2b866ed;       (* movk x13, #0xc337, lsl #16 *)
  0x0b0c0231;       (* add w17, w17, w12 *)
  0x0b0d0231;       (* add w17, w17, w13 *)
  0x8a08008d;       (* and x13, x4, x8 *)
  0x0b060231;       (* add w17, w17, w6 *)
  0x0b0d0231;       (* add w17, w17, w13 *)
  0x13915e31;       (* ror w17, w17, #23 *)
  0x8a290086;       (* bic x6, x4, x9 *)
  0x0b110091;       (* add w17, w4, w17 *)
  0xd281b0ed;       (* mov x13, #0xd87 *)
  0xf2be9aad;       (* movk x13, #0xf4d5, lsl #16 *)
  0x0b150108;       (* add w8, w8, w21 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x8a09022d;       (* and x13, x17, x9 *)
  0x0b060108;       (* add w8, w8, w6 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x13884908;       (* ror w8, w8, #18 *)
  0x8a240226;       (* bic x6, x17, x4 *)
  0x0b080228;       (* add w8, w17, w8 *)
  0xd2829dad;       (* mov x13, #0x14ed *)
  0xf2a8ab4d;       (* movk x13, #0x455a, lsl #16 *)
  0x0b050129;       (* add w9, w9, w5 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x8a04010d;       (* and x13, x8, x4 *)
  0x0b060129;       (* add w9, w9, w6 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x13893129;       (* ror w9, w9, #12 *)
  0x8a310106;       (* bic x6, x8, x17 *)
  0x0b090109;       (* add w9, w8, w9 *)
  0xd29d20ad;       (* mov x13, #0xe905 *)
  0xf2b53c6d;       (* movk x13, #0xa9e3, lsl #16 *)
  0x0b1a0084;       (* add w4, w4, w26 *)
  0x0b0d0084;       (* add w4, w4, w13 *)
  0x8a11012d;       (* and x13, x9, x17 *)
  0x0b060084;       (* add w4, w4, w6 *)
  0x0b0d0084;       (* add w4, w4, w13 *)
  0x13846c84;       (* ror w4, w4, #27 *)
  0x8a280126;       (* bic x6, x9, x8 *)
  0x0b040124;       (* add w4, w9, w4 *)
  0xd2947f0d;       (* mov x13, #0xa3f8 *)
  0xf2bf9ded;       (* movk x13, #0xfcef, lsl #16 *)
  0x0b030231;       (* add w17, w17, w3 *)
  0x0b0d0231;       (* add w17, w17, w13 *)
  0x8a08008d;       (* and x13, x4, x8 *)
  0x0b060231;       (* add w17, w17, w6 *)
  0x0b0d0231;       (* add w17, w17, w13 *)
  0x13915e31;       (* ror w17, w17, #23 *)
  0x8a290086;       (* bic x6, x4, x9 *)
  0x0b110091;       (* add w17, w4, w17 *)
  0xd2805b2d;       (* mov x13, #0x2d9 *)
  0xf2aceded;       (* movk x13, #0x676f, lsl #16 *)
  0x0b170108;       (* add w8, w8, w23 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x8a09022d;       (* and x13, x17, x9 *)
  0x0b060108;       (* add w8, w8, w6 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x13884908;       (* ror w8, w8, #18 *)
  0x8a240226;       (* bic x6, x17, x4 *)
  0x0b080228;       (* add w8, w17, w8 *)
  0xd289914d;       (* mov x13, #0x4c8a *)
  0xf2b1a54d;       (* movk x13, #0x8d2a, lsl #16 *)
  0x0b0b0129;       (* add w9, w9, w11 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x8a04010d;       (* and x13, x8, x4 *)
  0x0b060129;       (* add w9, w9, w6 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0xca110106;       (* eor x6, x8, x17 *)
  0x13893129;       (* ror w9, w9, #12 *)
  0xd287284a;       (* mov x10, #0x3942 *)
  0x0b090109;       (* add w9, w8, w9 *)
  0xf2bfff4a;       (* movk x10, #0xfffa, lsl #16 *)
  0x0b160084;       (* add w4, w4, w22 *)
  0xca0900c6;       (* eor x6, x6, x9 *)
  0x0b0a0084;       (* add w4, w4, w10 *)
  0x0b060084;       (* add w4, w4, w6 *)
  0x13847084;       (* ror w4, w4, #28 *)
  0xca080126;       (* eor x6, x9, x8 *)
  0xd29ed02a;       (* mov x10, #0xf681 *)
  0x0b040124;       (* add w4, w9, w4 *)
  0xf2b0ee2a;       (* movk x10, #0x8771, lsl #16 *)
  0x0b050231;       (* add w17, w17, w5 *)
  0xca0400c6;       (* eor x6, x6, x4 *)
  0x0b0a0231;       (* add w17, w17, w10 *)
  0x0b060231;       (* add w17, w17, w6 *)
  0xca090086;       (* eor x6, x4, x9 *)
  0x13915631;       (* ror w17, w17, #21 *)
  0xd28c244d;       (* mov x13, #0x6122 *)
  0x0b110091;       (* add w17, w4, w17 *)
  0xf2adb3ad;       (* movk x13, #0x6d9d, lsl #16 *)
  0x0b190108;       (* add w8, w8, w25 *)
  0xca1100c6;       (* eor x6, x6, x17 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x0b060108;       (* add w8, w8, w6 *)
  0x13884108;       (* ror w8, w8, #16 *)
  0xca040226;       (* eor x6, x17, x4 *)
  0xd287018d;       (* mov x13, #0x380c *)
  0x0b080228;       (* add w8, w17, w8 *)
  0xf2bfbcad;       (* movk x13, #0xfde5, lsl #16 *)
  0x0b0c0129;       (* add w9, w9, w12 *)
  0xca0800c6;       (* eor x6, x6, x8 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x0b060129;       (* add w9, w9, w6 *)
  0xca110106;       (* eor x6, x8, x17 *)
  0x13892529;       (* ror w9, w9, #9 *)
  0xd29d488a;       (* mov x10, #0xea44 *)
  0x0b090109;       (* add w9, w8, w9 *)
  0xf2b497ca;       (* movk x10, #0xa4be, lsl #16 *)
  0x0b140084;       (* add w4, w4, w20 *)
  0xca0900c6;       (* eor x6, x6, x9 *)
  0x0b0a0084;       (* add w4, w4, w10 *)
  0x0b060084;       (* add w4, w4, w6 *)
  0x13847084;       (* ror w4, w4, #28 *)
  0xca080126;       (* eor x6, x9, x8 *)
  0xd299f52a;       (* mov x10, #0xcfa9 *)
  0x0b040124;       (* add w4, w9, w4 *)
  0xf2a97bca;       (* movk x10, #0x4bde, lsl #16 *)
  0x0b0e0231;       (* add w17, w17, w14 *)
  0xca0400c6;       (* eor x6, x6, x4 *)
  0x0b0a0231;       (* add w17, w17, w10 *)
  0x0b060231;       (* add w17, w17, w6 *)
  0xca090086;       (* eor x6, x4, x9 *)
  0x13915631;       (* ror w17, w17, #21 *)
  0xd2896c0d;       (* mov x13, #0x4b60 *)
  0x0b110091;       (* add w17, w4, w17 *)
  0xf2bed76d;       (* movk x13, #0xf6bb, lsl #16 *)
  0x0b170108;       (* add w8, w8, w23 *)
  0xca1100c6;       (* eor x6, x6, x17 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x0b060108;       (* add w8, w8, w6 *)
  0x13884108;       (* ror w8, w8, #16 *)
  0xca040226;       (* eor x6, x17, x4 *)
  0xd2978e0d;       (* mov x13, #0xbc70 *)
  0x0b080228;       (* add w8, w17, w8 *)
  0xf2b7d7ed;       (* movk x13, #0xbebf, lsl #16 *)
  0x0b100129;       (* add w9, w9, w16 *)
  0xca0800c6;       (* eor x6, x6, x8 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x0b060129;       (* add w9, w9, w6 *)
  0xca110106;       (* eor x6, x8, x17 *)
  0x13892529;       (* ror w9, w9, #9 *)
  0xd28fd8ca;       (* mov x10, #0x7ec6 *)
  0x0b090109;       (* add w9, w8, w9 *)
  0xf2a5136a;       (* movk x10, #0x289b, lsl #16 *)
  0x0b1a0084;       (* add w4, w4, w26 *)
  0xca0900c6;       (* eor x6, x6, x9 *)
  0x0b0a0084;       (* add w4, w4, w10 *)
  0x0b060084;       (* add w4, w4, w6 *)
  0x13847084;       (* ror w4, w4, #28 *)
  0xca080126;       (* eor x6, x9, x8 *)
  0xd284ff4a;       (* mov x10, #0x27fa *)
  0x0b040124;       (* add w4, w9, w4 *)
  0xf2bd542a;       (* movk x10, #0xeaa1, lsl #16 *)
  0x0b0f0231;       (* add w17, w17, w15 *)
  0xca0400c6;       (* eor x6, x6, x4 *)
  0x0b0a0231;       (* add w17, w17, w10 *)
  0x0b060231;       (* add w17, w17, w6 *)
  0xca090086;       (* eor x6, x4, x9 *)
  0x13915631;       (* ror w17, w17, #21 *)
  0xd28610ad;       (* mov x13, #0x3085 *)
  0x0b110091;       (* add w17, w4, w17 *)
  0xf2ba9ded;       (* movk x13, #0xd4ef, lsl #16 *)
  0x0b150108;       (* add w8, w8, w21 *)
  0xca1100c6;       (* eor x6, x6, x17 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x0b060108;       (* add w8, w8, w6 *)
  0x13884108;       (* ror w8, w8, #16 *)
  0xca040226;       (* eor x6, x17, x4 *)
  0xd283a0ad;       (* mov x13, #0x1d05 *)
  0x0b080228;       (* add w8, w17, w8 *)
  0xf2a0910d;       (* movk x13, #0x488, lsl #16 *)
  0x0b070129;       (* add w9, w9, w7 *)
  0xca0800c6;       (* eor x6, x6, x8 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x0b060129;       (* add w9, w9, w6 *)
  0xca110106;       (* eor x6, x8, x17 *)
  0x13892529;       (* ror w9, w9, #9 *)
  0xd29a072a;       (* mov x10, #0xd039 *)
  0x0b090109;       (* add w9, w8, w9 *)
  0xf2bb3a8a;       (* movk x10, #0xd9d4, lsl #16 *)
  0x0b180084;       (* add w4, w4, w24 *)
  0xca0900c6;       (* eor x6, x6, x9 *)
  0x0b0a0084;       (* add w4, w4, w10 *)
  0x0b060084;       (* add w4, w4, w6 *)
  0x13847084;       (* ror w4, w4, #28 *)
  0xca080126;       (* eor x6, x9, x8 *)
  0xd2933caa;       (* mov x10, #0x99e5 *)
  0x0b040124;       (* add w4, w9, w4 *)
  0xf2bcdb6a;       (* movk x10, #0xe6db, lsl #16 *)
  0x0b0b0231;       (* add w17, w17, w11 *)
  0xca0400c6;       (* eor x6, x6, x4 *)
  0x0b0a0231;       (* add w17, w17, w10 *)
  0x0b060231;       (* add w17, w17, w6 *)
  0xca090086;       (* eor x6, x4, x9 *)
  0x13915631;       (* ror w17, w17, #21 *)
  0xd28f9f0d;       (* mov x13, #0x7cf8 *)
  0x0b110091;       (* add w17, w4, w17 *)
  0xf2a3f44d;       (* movk x13, #0x1fa2, lsl #16 *)
  0x0b1b0108;       (* add w8, w8, w27 *)
  0xca1100c6;       (* eor x6, x6, x17 *)
  0x0b0d0108;       (* add w8, w8, w13 *)
  0x0b060108;       (* add w8, w8, w6 *)
  0x13884108;       (* ror w8, w8, #16 *)
  0xca040226;       (* eor x6, x17, x4 *)
  0xd28accad;       (* mov x13, #0x5665 *)
  0x0b080228;       (* add w8, w17, w8 *)
  0xf2b8958d;       (* movk x13, #0xc4ac, lsl #16 *)
  0x0b030129;       (* add w9, w9, w3 *)
  0xca0800c6;       (* eor x6, x6, x8 *)
  0x0b0d0129;       (* add w9, w9, w13 *)
  0x0b060129;       (* add w9, w9, w6 *)
  0x13892529;       (* ror w9, w9, #9 *)
  0xd2844886;       (* mov x6, #0x2244 *)
  0xf2be8526;       (* movk x6, #0xf429, lsl #16 *)
  0x0b090109;       (* add w9, w8, w9 *)
  0x0b0f0084;       (* add w4, w4, w15 *)
  0xaa31012d;       (* orn x13, x9, x17 *)
  0x0b060084;       (* add w4, w4, w6 *)
  0xca0d0106;       (* eor x6, x8, x13 *)
  0x0b060084;       (* add w4, w4, w6 *)
  0x13846884;       (* ror w4, w4, #26 *)
  0xd29ff2e6;       (* mov x6, #0xff97 *)
  0xf2a86546;       (* movk x6, #0x432a, lsl #16 *)
  0x0b040124;       (* add w4, w9, w4 *)
  0xaa28008a;       (* orn x10, x4, x8 *)
  0x0b170231;       (* add w17, w17, w23 *)
  0xca0a012a;       (* eor x10, x9, x10 *)
  0x0b060231;       (* add w17, w17, w6 *)
  0x0b0a0226;       (* add w6, w17, w10 *)
  0x138658c6;       (* ror w6, w6, #22 *)
  0xd28474f1;       (* mov x17, #0x23a7 *)
  0xf2b57291;       (* movk x17, #0xab94, lsl #16 *)
  0x0b060086;       (* add w6, w4, w6 *)
  0x0b0c0108;       (* add w8, w8, w12 *)
  0xaa2900ca;       (* orn x10, x6, x9 *)
  0x0b110108;       (* add w8, w8, w17 *)
  0xca0a0091;       (* eor x17, x4, x10 *)
  0x0b110108;       (* add w8, w8, w17 *)
  0x13884508;       (* ror w8, w8, #17 *)
  0xd2940731;       (* mov x17, #0xa039 *)
  0xf2bf9271;       (* movk x17, #0xfc93, lsl #16 *)
  0x0b0800c8;       (* add w8, w6, w8 *)
  0xaa24010d;       (* orn x13, x8, x4 *)
  0x0b160129;       (* add w9, w9, w22 *)
  0xca0d00cd;       (* eor x13, x6, x13 *)
  0x0b110129;       (* add w9, w9, w17 *)
  0x0b0d0131;       (* add w17, w9, w13 *)
  0x13912e31;       (* ror w17, w17, #11 *)
  0xd28b3869;       (* mov x9, #0x59c3 *)
  0xf2acab69;       (* movk x9, #0x655b, lsl #16 *)
  0x0b110111;       (* add w17, w8, w17 *)
  0x0b0b0084;       (* add w4, w4, w11 *)
  0xaa26022d;       (* orn x13, x17, x6 *)
  0x0b090089;       (* add w9, w4, w9 *)
  0xca0d0104;       (* eor x4, x8, x13 *)
  0x0b040129;       (* add w9, w9, w4 *)
  0x13896929;       (* ror w9, w9, #26 *)
  0xd2999244;       (* mov x4, #0xcc92 *)
  0xf2b1e184;       (* movk x4, #0x8f0c, lsl #16 *)
  0x0b090229;       (* add w9, w17, w9 *)
  0xaa28012a;       (* orn x10, x9, x8 *)
  0x0b1500c6;       (* add w6, w6, w21 *)
  0xca0a022a;       (* eor x10, x17, x10 *)
  0x0b0400c4;       (* add w4, w6, w4 *)
  0x0b0a0086;       (* add w6, w4, w10 *)
  0x138658c6;       (* ror w6, w6, #22 *)
  0xd29e8fa4;       (* mov x4, #0xf47d *)
  0xf2bffde4;       (* movk x4, #0xffef, lsl #16 *)
  0x0b060126;       (* add w6, w9, w6 *)
  0x0b100108;       (* add w8, w8, w16 *)
  0xaa3100ca;       (* orn x10, x6, x17 *)
  0x0b040108;       (* add w8, w8, w4 *)
  0xca0a0124;       (* eor x4, x9, x10 *)
  0x0b040108;       (* add w8, w8, w4 *)
  0x13884508;       (* ror w8, w8, #17 *)
  0xd28bba24;       (* mov x4, #0x5dd1 *)
  0xf2b0b084;       (* movk x4, #0x8584, lsl #16 *)
  0x0b0800c8;       (* add w8, w6, w8 *)
  0xaa29010a;       (* orn x10, x8, x9 *)
  0x0b14022f;       (* add w15, w17, w20 *)
  0xca0a00d1;       (* eor x17, x6, x10 *)
  0x0b0401ef;       (* add w15, w15, w4 *)
  0x0b1101e4;       (* add w4, w15, w17 *)
  0x13842c84;       (* ror w4, w4, #11 *)
  0xd28fc9ef;       (* mov x15, #0x7e4f *)
  0xf2adf50f;       (* movk x15, #0x6fa8, lsl #16 *)
  0x0b040111;       (* add w17, w8, w4 *)
  0x0b050124;       (* add w4, w9, w5 *)
  0xaa260229;       (* orn x9, x17, x6 *)
  0x0b0f008f;       (* add w15, w4, w15 *)
  0xca090104;       (* eor x4, x8, x9 *)
  0x0b0401e9;       (* add w9, w15, w4 *)
  0x13896929;       (* ror w9, w9, #26 *)
  0xd29cdc0f;       (* mov x15, #0xe6e0 *)
  0xf2bfc58f;       (* movk x15, #0xfe2c, lsl #16 *)
  0x0b090224;       (* add w4, w17, w9 *)
  0xaa280089;       (* orn x9, x4, x8 *)
  0x0b1b00c6;       (* add w6, w6, w27 *)
  0xca090229;       (* eor x9, x17, x9 *)
  0x0b0f00cf;       (* add w15, w6, w15 *)
  0x0b0901e6;       (* add w6, w15, w9 *)
  0x138658c6;       (* ror w6, w6, #22 *)
  0xd2886289;       (* mov x9, #0x4314 *)
  0xf2b46029;       (* movk x9, #0xa301, lsl #16 *)
  0x0b06008f;       (* add w15, w4, w6 *)
  0x0b070106;       (* add w6, w8, w7 *)
  0xaa3101e7;       (* orn x7, x15, x17 *)
  0x0b0900c8;       (* add w8, w6, w9 *)
  0xca070089;       (* eor x9, x4, x7 *)
  0x0b090106;       (* add w6, w8, w9 *)
  0x138644c6;       (* ror w6, w6, #17 *)
  0xd2823427;       (* mov x7, #0x11a1 *)
  0xf2a9c107;       (* movk x7, #0x4e08, lsl #16 *)
  0x0b0601e8;       (* add w8, w15, w6 *)
  0xaa240109;       (* orn x9, x8, x4 *)
  0x0b1a0226;       (* add w6, w17, w26 *)
  0xca0901f1;       (* eor x17, x15, x9 *)
  0x0b0700c9;       (* add w9, w6, w7 *)
  0x0b110127;       (* add w7, w9, w17 *)
  0x13872ce7;       (* ror w7, w7, #11 *)
  0xd28fd046;       (* mov x6, #0x7e82 *)
  0xf2beea66;       (* movk x6, #0xf753, lsl #16 *)
  0x0b070109;       (* add w9, w8, w7 *)
  0x0b0e0091;       (* add w17, w4, w14 *)
  0xaa2f0127;       (* orn x7, x9, x15 *)
  0x0b06022e;       (* add w14, w17, w6 *)
  0xca070104;       (* eor x4, x8, x7 *)
  0x0b0401d1;       (* add w17, w14, w4 *)
  0x13916a31;       (* ror w17, w17, #26 *)
  0xd29e46a6;       (* mov x6, #0xf235 *)
  0xf2b7a746;       (* movk x6, #0xbd3a, lsl #16 *)
  0x0b110127;       (* add w7, w9, w17 *)
  0xaa2800ee;       (* orn x14, x7, x8 *)
  0x0b1901e4;       (* add w4, w15, w25 *)
  0xca0e0131;       (* eor x17, x9, x14 *)
  0x0b06008f;       (* add w15, w4, w6 *)
  0x0b1101f0;       (* add w16, w15, w17 *)
  0x13905a10;       (* ror w16, w16, #22 *)
  0xd29a576e;       (* mov x14, #0xd2bb *)
  0xf2a55aee;       (* movk x14, #0x2ad7, lsl #16 *)
  0x0b1000e4;       (* add w4, w7, w16 *)
  0x0b030106;       (* add w6, w8, w3 *)
  0xaa29008f;       (* orn x15, x4, x9 *)
  0x0b0e00d1;       (* add w17, w6, w14 *)
  0xca0f00f0;       (* eor x16, x7, x15 *)
  0x0b100228;       (* add w8, w17, w16 *)
  0x13884508;       (* ror w8, w8, #17 *)
  0xd29a7223;       (* mov x3, #0xd391 *)
  0xf2bd70c3;       (* movk x3, #0xeb86, lsl #16 *)
  0x0b08008e;       (* add w14, w4, w8 *)
  0xaa2701c6;       (* orn x6, x14, x7 *)
  0x0b18012f;       (* add w15, w9, w24 *)
  0xca060091;       (* eor x17, x4, x6 *)
  0x0b0301f0;       (* add w16, w15, w3 *)
  0x0b110208;       (* add w8, w16, w17 *)
  0x13882d08;       (* ror w8, w8, #11 *)
  0x29403c06;       (* ldp w6, w15, [x0] *)
  0x29412405;       (* ldp w5, w9, [x0, #8] *)
  0x0b0801c3;       (* add w3, w14, w8 *)
  0x0b09008d;       (* add w13, w4, w9 *)
  0x0b0501cc;       (* add w12, w14, w5 *)
  0x0b0600ea;       (* add w10, w7, w6 *)
  0x0b0f006b;       (* add w11, w3, w15 *)
  0x2901340c;       (* stp w12, w13, [x0, #8] *)
  0x29002c0a;       (* stp w10, w11, [x0] *)
  0x91010021;       (* add x1, x1, #0x40 *)
  0x71000442;       (* subs w2, w2, #0x1 *)
  0x54ffb141;       (* b.ne 20 <Lmd5_block_loop> *)
  0xa9415bf5;       (* ldp x21, x22, [sp, #16] *)
  0xa94263f7;       (* ldp x23, x24, [sp, #32] *)
  0xa9436bf9;       (* ldp x25, x26, [sp, #48] *)
  0xa94473fb;       (* ldp x27, x28, [sp, #64] *)
  0xa8c553f3;       (* ldp x19, x20, [sp], #80 *)
  0xd65f03c0;       (* ret *)
];;

let MD5_BLOCK_EXEC = ARM_MK_EXEC_RULE md5_block_mc;;

(* ------------------------------------------------------------------------- *)
(* Generic chaining helper: thread a frame-preserved component read through    *)
(* both the pre- and post-condition of an already-proved `ensures`.  Given a   *)
(* group lemma `ensures arm P Q C` whose MAYCHANGE frame C does NOT touch       *)
(* component c (so `!s s'. C s s' ==> read c s' = read c s`), we may add        *)
(* `read c s = v` to BOTH P and Q for free.                                     *)
(*                                                                           *)
(* This is what lets the register-only group lemmas (g4..g14, which never       *)
(* mention X0 or the state memory) carry the state pointer X0 and the four      *)
(* original state words through to the add-back boundary, WITHOUT re-stepping:  *)
(* the add-back's precondition needs X0 = state + the four bytes32(state+4i)    *)
(* reads, and every register group preserves them (their frames list only       *)
(* registers/flags/events -- no memory, no X0).  Apply once per threaded        *)
(* component; the side condition closes with MD5_FRAME_PRESERVES_TAC below.     *)
(* ------------------------------------------------------------------------- *)

let ENSURES_THREAD_PRESERVED = prove
 (`!P Q C (c:(armstate,A)component) v.
        (!s s'. C s s' ==> read c s' = read c s) /\
        ensures arm P Q C
        ==> ensures arm (\s. P s /\ read c s = v) (\s. Q s /\ read c s = v) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN STRIP_TAC THEN
  X_GEN_TAC `s:armstate` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:armstate`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s'. ((\s'. (Q:armstate->bool) s' /\ C (s:armstate) s') s')
         ==> ((\s'. ((Q:armstate->bool) s' /\
                     read (c:(armstate,A)component) s' = v) /\
                    C (s:armstate) s') s')`
  MP_TAC THENL
   [BETA_TAC THEN X_GEN_TAC `s':armstate` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP EVENTUALLY_MONO) THEN
    DISCH_THEN(MP_TAC o SPECL [`arm`; `s:armstate`]) THEN ASM_REWRITE_TAC[]]);;

(* Discharge a `!s s'. C s s' ==> read c s' = read c s` side condition for a     *)
(* component c that the MAYCHANGE frame C does not touch (orthogonal read).      *)
(* This is the body of common/relational.ml's ENSURES_PRESERVED_TAC, lifted to   *)
(* a standalone tactic (no MESON, instant).  Works for registers and for         *)
(* memory components whose address is provably disjoint by the orthogonal conv.  *)
let MD5_FRAME_PRESERVES_TAC : tactic =
  REWRITE_TAC[SOME_FLAGS] THEN
  REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
  REWRITE_TAC[GSYM SEQ_ASSOC] THEN
  PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
  CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ASSIGNS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV
   COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV)) THEN
  REFL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Small word-level helper lemmas used to bridge the symbolic-execution       *)
(* output of one MD5 round to the spec's md5_step form.  The simulator        *)
(* models the 32-bit "ror w,w,#25" via word_subword(word_join v v)(25,32);    *)
(* on int32 this collapses to a left-rotate by 7 (= 32 - 25).  A single-      *)
(* variable WORD_BLAST proves it instantly, and -- crucially -- it folds the  *)
(* duplicated argument of word_join so the downstream term stays small.       *)
(* ------------------------------------------------------------------------- *)

let MD5_ROT_JOIN_25 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (25,32):int32) = word_rol w 7`,
  CONV_TAC WORD_BLAST);;

(* Companion rotate-join lemmas for the remaining F-round shift amounts:        *)
(* s=12 -> ror 20, s=17 -> ror 15, s=22 -> ror 10.  All instant single-var      *)
(* WORD_BLASTs; each names the rotate AND collapses the duplicated join arg.     *)
let MD5_ROT_JOIN_20 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (20,32):int32) = word_rol w 12`,
  CONV_TAC WORD_BLAST);;

let MD5_ROT_JOIN_15 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (15,32):int32) = word_rol w 17`,
  CONV_TAC WORD_BLAST);;

let MD5_ROT_JOIN_10 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (10,32):int32) = word_rol w 22`,
  CONV_TAC WORD_BLAST);;

(* Rotate-join lemmas for the G/H/I round shift amounts (Phase 5).  Same idea:    *)
(* the asm's "ror w,w,#(32-s)" appears post-step as word_subword(join v v)(32-s,32) *)
(* and equals word_rol v s.  G uses s in {5,9,14,20} (ror 27/23/18/12), H uses     *)
(* {4,11,16,23} (ror 28/21/16/9), I uses {6,10,15,21} (ror 26/22/17/11).  All      *)
(* instant single-var WORD_BLASTs.  (ror 22 = MD5_ROT_JOIN_10 above is shared by   *)
(* F's s=22 and I's s=10.)                                                         *)
let MD5_ROT_JOIN_27 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (27,32):int32) = word_rol w 5`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_23 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (23,32):int32) = word_rol w 9`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_18 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (18,32):int32) = word_rol w 14`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_12 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (12,32):int32) = word_rol w 20`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_28 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (28,32):int32) = word_rol w 4`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_21 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (21,32):int32) = word_rol w 11`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_16 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (16,32):int32) = word_rol w 16`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_9 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (9,32):int32) = word_rol w 23`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_26 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (26,32):int32) = word_rol w 6`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_22 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (22,32):int32) = word_rol w 10`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_17 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (17,32):int32) = word_rol w 15`,
  CONV_TAC WORD_BLAST);;
let MD5_ROT_JOIN_11 = prove
 (`!w:int32. (word_subword ((word_join w w):int64) (11,32):int32) = word_rol w 21`,
  CONV_TAC WORD_BLAST);;

(* The low 32 bits of a 64-bit ldp-loaded word equal its zero-extension. *)
let MD5_SUBWORD_ZX_M = prove
 (`!m:int64. word_subword m (0,32):int32 = word_zx m`,
  CONV_TAC WORD_BLAST);;

(* Message words enter via 64-bit ldp doubleword loads; ARM is little-endian,   *)
(* so the doubleword at data+8k is word_join (msg(2k+1)) (msg(2k)).  The asm     *)
(* uses the low half directly (even index, via word_zx) and the high half via   *)
(* lsr #32 (odd index, word_ushr then 32-bit truncate).                         *)
let MD5_JOIN_LO = prove
 (`!h:int32. !l:int32. word_zx ((word_join h l):int64) :int32 = l`,
  CONV_TAC WORD_BLAST);;

let MD5_JOIN_HI = prove
 (`!h:int32. !l:int32. word_zx (word_ushr ((word_join h l):int64) 32) :int32 = h`,
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Phase 5 (G/H/I) bridge helpers.  These handle two new shapes that the F      *)
(* closer never met: (a) message words that arrive in REGISTERS rather than     *)
(* fresh memory loads -- the lsr-extracted odd words sit as word_zx(msg):int64  *)
(* and round-trip via MD5_ZX_RT; (b) the `bic` (and-not) precompute, where the  *)
(* G aux's `c & ~d` is hoisted into X6 one group early and arrives through an    *)
(* int32->int64->int32 round trip.  MD5_ZX_NOT_ZX collapses that round trip and  *)
(* MD5_ZX_AND_NOT bridges the spec's zero-extended (a&~b) to the hardware's      *)
(* int64 AND-of-(zx a)-and-(NOT(zx b)) form (the AND with zx a masks the         *)
(* spurious high-1s the 64-bit NOT introduces).  All instant single-var BLASTs.  *)
let MD5_ZX_RT = prove
 (`!l:int32. word_zx (word_zx l :int64) :int32 = l`,
  CONV_TAC WORD_BLAST);;

let MD5_ZX_NOT_ZX = prove
 (`!p:int32. word_zx (word_not (word_zx p :int64)) :int32 = word_not p`,
  CONV_TAC WORD_BLAST);;

let MD5_ZX_AND_NOT = prove
 (`!a b:int32.
     word_zx (word_and a (word_not b)) :int64 =
     word_and (word_zx a) (word_not (word_zx b))`,
  CONV_TAC WORD_BLAST);;

(* G aux in the asm's two-summand add-form, in the ASM's AND-operand order:      *)
(* c&~d (the bic-precomputed first summand) + b&d (the inline `and`).  Splitting *)
(* md5_g this way lets WORD_ADD_CANON_CONV merge the aux into the round's        *)
(* add-chain exactly as the hardware does.  (Cf. MD5_G_BRIDGE, the or-form.)     *)
let MD5_G_EXPAND = prove
 (`!b c d:int32.
     md5_g b c d = word_add (word_and c (word_not d)) (word_and b d)`,
  REWRITE_TAC[md5_g] THEN CONV_TAC WORD_BLAST);;

(* H aux in the asm's precompute order: (c^d) is hoisted into X6 in the prior     *)
(* group's tail (eor x6,x8,x17), then ^b (eor x6,x6,x9) at the round head.        *)
(* md5_h b c d = b^c^d = (c^d)^b -- matching the hardware's incremental form.     *)
let MD5_H_EXPAND = prove
 (`!b c d:int32. md5_h b c d = word_xor (word_xor c d) b`,
  REWRITE_TAC[md5_h] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* A bottom-up word_add canonicaliser.  After a multi-step MD5 cut-point the   *)
(* hardware and spec sides are identical trees over word_add/word_rol/         *)
(* word_xor/word_and with the SAME leaves, differing only by word_add          *)
(* associativity/commutativity -- including inside the opaque word_rol         *)
(* arguments.  WORD_RULE alone fails: it treats `word_rol x n` as an atom and   *)
(* cannot reorder the add-chains buried inside the rotates.  This conversion    *)
(* canonicalises every word_add node bottom-up (children first), so rotate      *)
(* arguments are normalised before the enclosing adds, after which both sides   *)
(* reach a single syntactic normal form and the goal closes by REFL.           *)
let WORD_ADD_CANON_CONV =
  let rec add_summands tm =
    match tm with
    | Comb(Comb(Const("word_add",_),x),y) -> add_summands x @ add_summands y
    | _ -> [tm] in
  let rec conv tm =
    match tm with
    | Comb(Comb(Const("word_add",_) as addc, l), r) ->
        let lth = conv l and rth = conv r in
        let tm' = mk_comb(mk_comb(addc, rhs(concl lth)), rhs(concl rth)) in
        let summands = add_summands tm' in
        let sorted =
          sort (fun a b -> Stdlib.compare a b <= 0) summands in
        let rebuilt =
          match List.rev sorted with
          | [] -> failwith "WORD_ADD_CANON_CONV: empty"
          | h::t -> List.fold_left (fun acc x -> mk_comb(mk_comb(addc,x),acc))
                                   h t in
        let child_eq = MK_COMB(AP_TERM addc lth, rth) in
        if rebuilt = tm' then child_eq
        else TRANS child_eq (AC WORD_ADD_AC (mk_eq(tm',rebuilt)))
    | Comb(l,r) -> MK_COMB(conv l, conv r)
    | Abs(v,bod) -> ABS v (conv bod)
    | _ -> REFL tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Phase 4 machinery: reduce a nested md5_step spec to its word-arithmetic     *)
(* normal form, and a reusable per-register F-round closer.                    *)
(* ------------------------------------------------------------------------- *)

(* Drive a (possibly nested) `md5_step .. (md5_step .. (a,b,c,d))` term to its  *)
(* word_add/word_rol/word_xor/word_and normal form.  Interleaves the step/aux   *)
(* unfold with table lookups, NUM reduction, let-elimination and FST/SND so the *)
(* let bindings clear between successive steps (a single REWRITE_TAC[md5_step]   *)
(* cannot, because the tuple result is hidden behind two `let`s).  The aux       *)
(* functions md5_f/g/h/i are deliberately left FOLDED -- the closer unfolds      *)
(* them once, against the matching hardware form.                               *)
let MD5_SPEC_REDUCE_CONV =
  REPEATC
   (CHANGED_CONV
     (REWRITE_CONV[md5_step; md5_aux] THENC
      REWRITE_CONV[md5_msgidx; md5_T; md5_shift] THENC
      DEPTH_CONV(EL_CONV ORELSEC NUM_RED_CONV) THENC
      TOP_DEPTH_CONV let_CONV THENC
      REWRITE_CONV[FST; SND]));;

(* Close one F-round state conjunct `read Xn s = word_zx (<reduced spec>)`.      *)
(* Substitutes the matching hardware register assumption, folds the ror-as-      *)
(* left-rotate (collapsing the duplicated word_join argument), normalises the    *)
(* int32->int64->int32 word_zx round-trips, extracts the message words from the  *)
(* little-endian doubleword joins, unfolds md5_f, then canonicalises both sides' *)
(* word_add trees (bottom-up, through the opaque rotates) so the goal closes by  *)
(* REFL.  No per-round constants are baked in, so it is reused for every         *)
(* F-round and every cut-point group.                                           *)
let MD5_CLOSE_F_TAC : tactic =
  fun (asl,w) ->
    let regread = lhs w in
    (FIRST_X_ASSUM (fun th ->
        if is_eq(concl th) && lhs(concl th) = regread
        then SUBST1_TAC th else failwith "MD5_CLOSE_F_TAC") THEN
     REWRITE_TAC[MD5_ROT_JOIN_25; MD5_ROT_JOIN_20; MD5_ROT_JOIN_15;
                 MD5_ROT_JOIN_10; md5_f] THEN
     SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
              WORD_ZX_XOR; WORD_ZX_AND] THEN
     REWRITE_TAC[MD5_SUBWORD_ZX_M; MD5_JOIN_LO; MD5_JOIN_HI] THEN
     CONV_TAC(BINOP_CONV WORD_ADD_CANON_CONV) THEN REFL_TAC) (asl,w);;

(* The same reduce+canonicalise closer, but for a goal already in the form       *)
(* `<hardware> = word_zx <spec>` (register read already substituted by           *)
(* ENSURES_FINAL_STATE_TAC, as happens when the postcondition also carries       *)
(* preserved-memory conjuncts).  No assumption-substitution step.                *)
let MD5_REDUCE_CANON_TAC : tactic =
  REWRITE_TAC[MD5_ROT_JOIN_25; MD5_ROT_JOIN_20; MD5_ROT_JOIN_15;
              MD5_ROT_JOIN_10; md5_f] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
           WORD_ZX_XOR; WORD_ZX_AND] THEN
  REWRITE_TAC[MD5_SUBWORD_ZX_M; MD5_JOIN_LO; MD5_JOIN_HI] THEN
  CONV_TAC(BINOP_CONV WORD_ADD_CANON_CONV) THEN REFL_TAC;;

(* The G-round analogue of MD5_REDUCE_CANON_TAC.  Differences from the F closer:  *)
(*  - G rotate-joins (shift amounts 5/9/14/20 -> ror 27/23/18/12);                 *)
(*  - md5_g is expanded into its (c&~d)+(b&d) two-summand add-form (MD5_G_EXPAND)  *)
(*    so the aux merges into the round's add-chain like the hardware's bic+and;    *)
(*  - MD5_ZX_AND_NOT must fire BEFORE the generic WORD_ZX_AND so the X6 precompute *)
(*    conjunct `word_zx(word_and t2 (word_not t3))` matches the hardware bic form  *)
(*    (else WORD_ZX_AND leaves word_zx(word_not t3), unmatchable);                 *)
(*  - MD5_ZX_RT / MD5_ZX_NOT_ZX collapse the register-resident message and bic     *)
(*    round trips.  Otherwise identical: bottom-up word_add canon then REFL.       *)
let MD5_REDUCE_CANON_G_TAC : tactic =
  REWRITE_TAC[MD5_ROT_JOIN_27; MD5_ROT_JOIN_23; MD5_ROT_JOIN_18;
              MD5_ROT_JOIN_12; MD5_G_EXPAND] THEN
  REWRITE_TAC[MD5_ZX_AND_NOT] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
           WORD_ZX_XOR; WORD_ZX_AND] THEN
  REWRITE_TAC[MD5_SUBWORD_ZX_M; MD5_JOIN_LO; MD5_JOIN_HI;
              MD5_ZX_RT; MD5_ZX_NOT_ZX] THEN
  CONV_TAC(BINOP_CONV WORD_ADD_CANON_CONV) THEN REFL_TAC;;

(* The H-round closer: H rotate-joins (shifts 4/11/16/23 -> ror 28/21/16/9), and  *)
(* md5_h in the precompute (c^d)^b form.  No bic and no add-decomposition, so the  *)
(* AND_NOT bridge is unneeded; word_zx pushes through xor cleanly (WORD_ZX_XOR),   *)
(* then the same bottom-up word_add canon closes by REFL.  (The H-round T-constant *)
(* is pipelined a round early via mov/movk x10 across the group boundary, so each  *)
(* H cut-point must carry `read X10 = word <partial-const>` in/out -- see the      *)
(* H-group theorems below; that is a precondition-shape issue, not a closer one.)  *)
let MD5_REDUCE_CANON_H_TAC : tactic =
  REWRITE_TAC[MD5_ROT_JOIN_28; MD5_ROT_JOIN_21; MD5_ROT_JOIN_16;
              MD5_ROT_JOIN_9; MD5_H_EXPAND] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
           WORD_ZX_XOR; WORD_ZX_AND] THEN
  REWRITE_TAC[MD5_SUBWORD_ZX_M; MD5_JOIN_LO; MD5_JOIN_HI; MD5_ZX_RT] THEN
  CONV_TAC(BINOP_CONV WORD_ADD_CANON_CONV) THEN REFL_TAC;;

(* ------------------------------------------------------------------------- *)
(* F-round step-unfolding lemmas: md5_steps(4(k+1)) = the depth-4 nested       *)
(* md5_step on top of md5_steps(4k).  Used by the F16 -> G re-augmentation      *)
(* chain (MD5_BLOCK_F16_AUG_CORRECT) to line up each group's nested-md5_step    *)
(* output with the next group's md5_steps(4k) input.                            *)
(* ------------------------------------------------------------------------- *)

let MD5_STEPS_8_NEST = prove
 (`!msg st. md5_steps 8 msg st =
     md5_step 7 msg (md5_step 6 msg (md5_step 5 msg (md5_step 4 msg
       (md5_steps 4 msg st))))`,
  REWRITE_TAC[num_CONV `8`; num_CONV `7`; num_CONV `6`; num_CONV `5`; md5_steps]);;

let MD5_STEPS_12_NEST = prove
 (`!msg st. md5_steps 12 msg st =
     md5_step 11 msg (md5_step 10 msg (md5_step 9 msg (md5_step 8 msg
       (md5_steps 8 msg st))))`,
  REWRITE_TAC[num_CONV `12`; num_CONV `11`; num_CONV `10`; num_CONV `9`; md5_steps]);;

let MD5_STEPS_16_NEST = prove
 (`!msg st. md5_steps 16 msg st =
     md5_step 15 msg (md5_step 14 msg (md5_step 13 msg (md5_step 12 msg
       (md5_steps 12 msg st))))`,
  REWRITE_TAC[num_CONV `16`; num_CONV `15`; num_CONV `14`; num_CONV `13`; md5_steps]);;

(* ------------------------------------------------------------------------- *)
(* F16 -> G re-augmentation (session 010).  MD5_BLOCK_F16_CORRECT's endpoint   *)
(* emits only the 4 state words + X1, but the first G group (pc+0x2d4) needs    *)
(* the full 21-register carry set: 4 state words, the X6 = c&~d precompute      *)
(* (bic x6,x8,x17 @0x2cc), and 16 message words held in registers (8 ldp        *)
(* doublewords in X15,X3,X14,X7,X5,X16,X11,X12 + 8 lsr-#32 high halves in       *)
(* X20..X27).  These message registers are LOADED during the F section and not  *)
(* re-touched, so they cannot be threaded (threading only works for components  *)
(* the frame preserves) -- instead each F group is re-proved emitting the       *)
(* message registers it settles, carrying the earlier-settled ones forward.     *)
(*                                                                             *)
(* MACHINE-VERIFIED (objdump liveness, session 010): the 16 message-register    *)
(* values match the F-section ldp/lsr loads exactly (the spot-check open since  *)
(* session 006), and each F group's write set is DISJOINT from the message      *)
(* registers settled by earlier groups, so the carried regs survive untouched   *)
(* and close by ASM_REWRITE.  Settled sets: g0 {X15,X3,X20,X21};                 *)
(* g1 {X14,X7,X22,X23}; g2 {X5,X16,X24,X25}; g3 {X11,X12,X26,X27} + X6 (the G    *)
(* precompute).  See orchestrator/logs/phase5-liveness-notes.md (session 010).  *)
(* ------------------------------------------------------------------------- *)

(* Odd message word extracted by lsr #32 from a little-endian doubleword join,  *)
(* int64 result (matches the G-group register shape read X2k = word_zx(msg ..)).*)
let MD5_USHR_JOIN_HI = prove
 (`!(h:int32) (l:int32). word_ushr (word_join h l :int64) 32 = (word_zx h:int64)`,
  CONV_TAC WORD_BLAST);;

(* Hybrid closer for the F16->G boundary's X6 = c&~d precompute conjunct: the    *)
(* bic'd t2,t3 are F-round outputs (ror 25/20/15/10, md5_f aux) wrapped in the   *)
(* G-aux and-not form, so this combines the F rotate-joins + md5_f with the      *)
(* AND_NOT bridge.  It is a superset of MD5_REDUCE_CANON_TAC (AND_NOT is a no-op  *)
(* on the plain word_add state words), so it also closes the four ordinary F     *)
(* state conjuncts in the same group.                                           *)
let MD5_REDUCE_CANON_FANDNOT_TAC : tactic =
  REWRITE_TAC[MD5_ROT_JOIN_25; MD5_ROT_JOIN_20; MD5_ROT_JOIN_15;
              MD5_ROT_JOIN_10; md5_f] THEN
  REWRITE_TAC[MD5_ZX_AND_NOT] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
           WORD_ZX_XOR; WORD_ZX_AND] THEN
  REWRITE_TAC[MD5_SUBWORD_ZX_M; MD5_JOIN_LO; MD5_JOIN_HI;
              MD5_ZX_RT; MD5_ZX_NOT_ZX] THEN
  CONV_TAC(BINOP_CONV WORD_ADD_CANON_CONV) THEN REFL_TAC;;

(* Augmented F group 0 (pc+0x20 -> pc+0xd0): emits the 4 message regs it          *)
(* settles (X15,X3 doublewords; X20,X21 lsr halves) alongside the state.          *)
let MD5_BLOCK_F4_G0_AUG = prove
 (`!a b c d data msg pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x20) /\
            read X10 s = word_zx(a:int32) /\ read X11 s = word_zx(b:int32) /\
            read X12 s = word_zx(c:int32) /\ read X13 s = word_zx(d:int32) /\
            read X1 s = data /\
            read (memory :> bytes64 data) s = word_join (msg 1) (msg 0) /\
            read (memory :> bytes64 (word_add data (word 8))) s = word_join (msg 3) (msg 2) /\
            read (memory :> bytes64 (word_add data (word 16))) s = word_join (msg 5) (msg 4) /\
            read (memory :> bytes64 (word_add data (word 24))) s = word_join (msg 7) (msg 6) /\
            read (memory :> bytes64 (word_add data (word 32))) s = word_join (msg 9) (msg 8) /\
            read (memory :> bytes64 (word_add data (word 40))) s = word_join (msg 11) (msg 10) /\
            read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
            read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0xd0) /\
            (let (t0,t1,t2,t3) = md5_steps 4 msg (a,b,c,d) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X5 s = word_zx t3 /\
             read X17 s = word_zx(word_xor t2 t3)) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read (memory :> bytes64 (word_add data (word 16))) s = word_join (msg 5) (msg 4) /\
            read (memory :> bytes64 (word_add data (word 24))) s = word_join (msg 7) (msg 6) /\
            read (memory :> bytes64 (word_add data (word 32))) s = word_join (msg 9) (msg 8) /\
            read (memory :> bytes64 (word_add data (word 40))) s = word_join (msg 11) (msg 10) /\
            read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
            read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14))
       (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X14; X15; X16; X17; X20; X21] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (1--44) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; md5_steps] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_TAC; ASM_REWRITE_TAC[MD5_USHR_JOIN_HI]; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* Augmented F group 1 (pc+0xd0 -> pc+0x17c): carry {X15,X3,X20,X21}, settle      *)
(* {X14,X7,X22,X23}.  Tuple input st in g0-output role order (X4,X9,X8,X5)+X17.    *)
let MD5_BLOCK_F4_G1_AUG = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0xd0) /\
            (let (e0,e1,e2,e3) = st in
             read X4 s = word_zx e0 /\ read X9 s = word_zx e1 /\
             read X8 s = word_zx e2 /\ read X5 s = word_zx e3 /\
             read X17 s = word_zx(word_xor e2 e3)) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read (memory :> bytes64 (word_add data (word 16))) s = word_join (msg 5) (msg 4) /\
            read (memory :> bytes64 (word_add data (word 24))) s = word_join (msg 7) (msg 6) /\
            read (memory :> bytes64 (word_add data (word 32))) s = word_join (msg 9) (msg 8) /\
            read (memory :> bytes64 (word_add data (word 40))) s = word_join (msg 11) (msg 10) /\
            read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
            read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x17c) /\
            (let (t0,t1,t2,t3) =
                 md5_step 7 msg (md5_step 6 msg (md5_step 5 msg (md5_step 4 msg st))) in
             read X17 s = word_zx t0 /\ read X4 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X19 s = word_zx t3 /\
             read X6 s = word_zx(word_xor t2 t3)) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read (memory :> bytes64 (word_add data (word 32))) s = word_join (msg 9) (msg 8) /\
            read (memory :> bytes64 (word_add data (word 40))) s = word_join (msg 11) (msg 10) /\
            read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
            read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14))
       (MAYCHANGE [PC; X4; X5; X6; X7; X8; X9; X14; X16; X17; X19; X22; X23] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (1--43) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_TAC; ASM_REWRITE_TAC[MD5_USHR_JOIN_HI]; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* Augmented F group 2 (pc+0x17c -> pc+0x228): carry prior 8 msg regs, settle      *)
(* {X5,X16,X24,X25}.  (X11 is in the write set -- partial T-constant mov/movk.)    *)
let MD5_BLOCK_F4_G2_AUG = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x17c) /\
            (let (f0,f1,f2,f3) = st in
             read X17 s = word_zx f0 /\ read X4 s = word_zx f1 /\
             read X8 s = word_zx f2 /\ read X19 s = word_zx f3 /\
             read X6 s = word_zx(word_xor f2 f3)) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read (memory :> bytes64 (word_add data (word 32))) s = word_join (msg 9) (msg 8) /\
            read (memory :> bytes64 (word_add data (word 40))) s = word_join (msg 11) (msg 10) /\
            read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
            read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x228) /\
            (let (t0,t1,t2,t3) =
                 md5_step 11 msg (md5_step 10 msg (md5_step 9 msg (md5_step 8 msg st))) in
             read X6 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
             read X4 s = word_zx(word_xor t2 t3)) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
            read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14))
       (MAYCHANGE [PC; X4; X5; X6; X8; X9; X11; X16; X17; X19; X24; X25] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (1--43) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `11`; num_CONV `10`; num_CONV `9`; num_CONV `8`;
              num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_TAC; ASM_REWRITE_TAC[MD5_USHR_JOIN_HI]; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* Augmented F group 3 (pc+0x228 -> pc+0x2d4): carry prior 12 msg regs, settle     *)
(* {X11,X12,X26,X27}, AND emit X6 = c&~d (G round's first aux summand, hoisted by  *)
(* bic x6,x8,x17 @0x2cc).  This endpoint IS the G group-0 precondition verbatim.    *)
(* The X6 precompute conjunct needs the hybrid FANDNOT closer (F rotates inside a   *)
(* G-aux and-not form).                                                            *)
let MD5_BLOCK_F4_G3_AUG = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x228) /\
            (let (g0,g1,g2,g3) = st in
             read X6 s = word_zx g0 /\ read X9 s = word_zx g1 /\
             read X8 s = word_zx g2 /\ read X17 s = word_zx g3 /\
             read X4 s = word_zx(word_xor g2 g3)) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
            read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x2d4) /\
            (let (t0,t1,t2,t3) =
                 md5_step 15 msg (md5_step 14 msg (md5_step 13 msg (md5_step 12 msg st))) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
             read X6 s = word_zx(word_and t2 (word_not t3))) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X11; X12; X13; X17; X19; X26; X27] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (1--43) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `15`; num_CONV `14`; num_CONV `13`; num_CONV `12`;
              num_CONV `11`; num_CONV `10`; num_CONV `9`; num_CONV `8`;
              num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_FANDNOT_TAC;
             ASM_REWRITE_TAC[MD5_USHR_JOIN_HI]; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* Chain the four augmented F groups: pc+0x20 -> pc+0x2d4, endpoint = the first    *)
(* G group's precondition verbatim.  Same ENSURES_SEQUENCE + ENSURES_FRAME_SUBSUMED *)
(* recipe as MD5_BLOCK_F16_CORRECT; the seam Q's carry the full message-register    *)
(* set so each segment matches its augmented group lemma exactly.                  *)
let MD5_BLOCK_F16_AUG_CORRECT = prove
 (`!a b c d data msg pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x20) /\
            read X10 s = word_zx(a:int32) /\ read X11 s = word_zx(b:int32) /\
            read X12 s = word_zx(c:int32) /\ read X13 s = word_zx(d:int32) /\
            read X1 s = data /\
            read (memory :> bytes64 data) s = word_join (msg 1) (msg 0) /\
            read (memory :> bytes64 (word_add data (word 8))) s = word_join (msg 3) (msg 2) /\
            read (memory :> bytes64 (word_add data (word 16))) s = word_join (msg 5) (msg 4) /\
            read (memory :> bytes64 (word_add data (word 24))) s = word_join (msg 7) (msg 6) /\
            read (memory :> bytes64 (word_add data (word 32))) s = word_join (msg 9) (msg 8) /\
            read (memory :> bytes64 (word_add data (word 40))) s = word_join (msg 11) (msg 10) /\
            read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
            read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x2d4) /\
            (let (t0,t1,t2,t3) = md5_steps 16 msg (a,b,c,d) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
             read X6 s = word_zx(word_and t2 (word_not t3))) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X11; X12; X13; X14; X15;
                   X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xd0`
   `\s. (let (t0,t1,t2,t3) = md5_steps 4 msg (a:int32,b:int32,c:int32,d:int32) in
         read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
         read X8 s = word_zx t2 /\ read X5 s = word_zx t3 /\
         read X17 s = word_zx(word_xor t2 t3)) /\
        read X1 s = data /\
        read X15 s = word_join (msg 1) (msg 0) /\
        read X3 s = word_join (msg 3) (msg 2) /\
        read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
        read (memory :> bytes64 (word_add data (word 16))) s = word_join (msg 5) (msg 4) /\
        read (memory :> bytes64 (word_add data (word 24))) s = word_join (msg 7) (msg 6) /\
        read (memory :> bytes64 (word_add data (word 32))) s = word_join (msg 9) (msg 8) /\
        read (memory :> bytes64 (word_add data (word 40))) s = word_join (msg 11) (msg 10) /\
        read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
        read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X14; X15; X16; X17; X20; X21] ,,
                MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC(SPECL [`a:int32`;`b:int32`;`c:int32`;`d:int32`;
                    `data:int64`;`msg:num->int32`;`pc:num`]
                   MD5_BLOCK_F4_G0_AUG) THEN
      REWRITE_TAC[SOME_FLAGS]];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x17c`
   `\s. (let (t0,t1,t2,t3) = md5_steps 8 msg (a:int32,b:int32,c:int32,d:int32) in
         read X17 s = word_zx t0 /\ read X4 s = word_zx t1 /\
         read X8 s = word_zx t2 /\ read X19 s = word_zx t3 /\
         read X6 s = word_zx(word_xor t2 t3)) /\
        read X1 s = data /\
        read X15 s = word_join (msg 1) (msg 0) /\
        read X3 s = word_join (msg 3) (msg 2) /\
        read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
        read X14 s = word_join (msg 5) (msg 4) /\
        read X7 s = word_join (msg 7) (msg 6) /\
        read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
        read (memory :> bytes64 (word_add data (word 32))) s = word_join (msg 9) (msg 8) /\
        read (memory :> bytes64 (word_add data (word 40))) s = word_join (msg 11) (msg 10) /\
        read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
        read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14)` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV) [MD5_STEPS_8_NEST] THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE [PC; X4; X5; X6; X7; X8; X9; X14; X16; X17; X19; X22; X23] ,,
                MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC(SPECL [`md5_steps 4 msg (a:int32,b:int32,c:int32,d:int32)`;
                    `data:int64`;`msg:num->int32`;`pc:num`]
                   MD5_BLOCK_F4_G1_AUG) THEN
      REWRITE_TAC[SOME_FLAGS]];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x228`
   `\s. (let (t0,t1,t2,t3) = md5_steps 12 msg (a:int32,b:int32,c:int32,d:int32) in
         read X6 s = word_zx t0 /\ read X9 s = word_zx t1 /\
         read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
         read X4 s = word_zx(word_xor t2 t3)) /\
        read X1 s = data /\
        read X15 s = word_join (msg 1) (msg 0) /\
        read X3 s = word_join (msg 3) (msg 2) /\
        read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
        read X14 s = word_join (msg 5) (msg 4) /\
        read X7 s = word_join (msg 7) (msg 6) /\
        read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
        read X5 s = word_join (msg 9) (msg 8) /\
        read X16 s = word_join (msg 11) (msg 10) /\
        read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
        read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
        read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14)` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV) [MD5_STEPS_12_NEST] THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE [PC; X4; X5; X6; X8; X9; X11; X16; X17; X19; X24; X25] ,,
                MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC(SPECL [`md5_steps 8 msg (a:int32,b:int32,c:int32,d:int32)`;
                    `data:int64`;`msg:num->int32`;`pc:num`]
                   MD5_BLOCK_F4_G2_AUG) THEN
      REWRITE_TAC[SOME_FLAGS]];
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV) [MD5_STEPS_16_NEST] THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE [PC; X4; X6; X8; X9; X11; X12; X13; X17; X19; X26; X27] ,,
                MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MP_TAC(SPECL [`md5_steps 12 msg (a:int32,b:int32,c:int32,d:int32)`;
                    `data:int64`;`msg:num->int32`;`pc:num`]
                   MD5_BLOCK_F4_G3_AUG) THEN
      REWRITE_TAC[SOME_FLAGS]]]);;

(* ========================================================================= *)
(* Phase 5: the G/H/I rounds (16-63), register-only.                          *)
(*                                                                           *)
(* KEY STRUCTURAL DIFFERENCE FROM THE F ROUNDS (machine-verified from         *)
(* objdump register liveness -- see orchestrator/logs/phase5-liveness-notes): *)
(* the G/H/I rounds read their message words straight from REGISTERS that     *)
(* were loaded once in the F section and never reloaded.  At the F16->G        *)
(* boundary (pc+0x2d4) the live-in carry set for the register-only core       *)
(* (scanning to the add-back tail at 0x9cc) is exactly 21 registers:          *)
(*   - 4 state words: X4=t0, X9=t1, X8=t2, X17=t3 (md5_steps 16 role order);   *)
(*   - 1 software-pipelined precompute: X6 = c&~d = word_and t2 (word_not t3)  *)
(*     (the G round's first aux summand, hoisted by `bic x6,x8,x17` @0x2cc);   *)
(*   - 16 message words: the 8 little-endian doublewords (even index = low     *)
(*     half via word_zx; loaded by the F-section ldp's) in                     *)
(*     X15,X3,X14,X7,X5,X16,X11,X12, and the 8 odd-index words (lsr #32 high    *)
(*     halves, sitting as word_zx(msg):int64) in X20..X27.                     *)
(* This is the carry set the F16 endpoint must be re-augmented to re-emit so   *)
(* it chains into G (a scoped follow-up; F16's current endpoint is the minimal *)
(* 4-state+X1).  Here we prove the first G group STANDALONE, taking the carry  *)
(* as a fresh tuple-input precondition (mirrors the standalone first-F-group   *)
(* proof that bootstrapped Phase 4), which validates the entire G machinery:   *)
(* MD5_G_EXPAND, the bic round-trip bridges, the G rotate-joins, the register- *)
(* input message model, and the precompute carry across a G->G boundary.       *)
(*                                                                           *)
(* G group 0 (rounds 16-19, pc+0x2d4 -> pc+0x374, 40 instructions):            *)
(* msgidx = [1;6;11;0]; the round results (ror destinations) land in           *)
(* w4,w17,w8,w9 with outer rotate shifts 5/20/14/9, giving the role-tuple      *)
(* (t0,t1,t2,t3) -> (X4,X9,X8,X17) (same layout as F group 3).  The tail       *)
(* `bic x6,x8,x17` @0x36c precomputes the NEXT G group's c&~d, re-emitted as   *)
(* X6 = word_and t2 (word_not t3).  Write set {X4,X6,X8,X9,X13,X17}.            *)
(* ------------------------------------------------------------------------- *)

let MD5_BLOCK_G4_GROUP0_CORRECT = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x2d4) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X17 s = word_zx d /\
             read X6 s = word_zx(word_and c (word_not d))) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x374) /\
            (let (t0,t1,t2,t3) =
                 md5_step 19 msg (md5_step 18 msg (md5_step 17 msg
                   (md5_step 16 msg st))) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
             read X6 s = word_zx(word_and t2 (word_not t3))) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X13; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (182--221) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `19`; num_CONV `18`; num_CONV `17`; num_CONV `16`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_G_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* G groups 1 and 2 (rounds 20-27): identical shape to G group 0.  Each takes the *)
(* role-tuple (X4,X9,X8,X17) + X6 = c&~d precompute + the 16 register-resident     *)
(* message words, and re-emits md5_step(4k+3..4k) + the next group's X6 precompute *)
(* (tail `bic x6,x8,x17` @0x40c / @0x4ac).  Same 40-step skeleton + G closer.       *)
(* msgidx: g5 = [5;10;15;4], g6 = [9;14;3;8].                                       *)
let MD5_BLOCK_G4_GROUP1_CORRECT = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x374) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X17 s = word_zx d /\
             read X6 s = word_zx(word_and c (word_not d))) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x414) /\
            (let (t0,t1,t2,t3) =
                 md5_step 23 msg (md5_step 22 msg (md5_step 21 msg
                   (md5_step 20 msg st))) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
             read X6 s = word_zx(word_and t2 (word_not t3))) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X13; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (222--261) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `23`; num_CONV `22`; num_CONV `21`; num_CONV `20`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_G_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

let MD5_BLOCK_G4_GROUP2_CORRECT = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x414) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X17 s = word_zx d /\
             read X6 s = word_zx(word_and c (word_not d))) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x4b4) /\
            (let (t0,t1,t2,t3) =
                 md5_step 27 msg (md5_step 26 msg (md5_step 25 msg
                   (md5_step 24 msg st))) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
             read X6 s = word_zx(word_and t2 (word_not t3))) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X13; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (262--301) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `27`; num_CONV `26`; num_CONV `25`; num_CONV `24`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_G_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* ========================================================================= *)
(* Phase 5: the H rounds (32-47).  H aux = b^c^d, computed as (c^d)^b.        *)
(*                                                                           *)
(* The G->H seam is the messiest in the function: an H cut-point must carry   *)
(* THREE distinct pipelined quantities across each group boundary (all        *)
(* machine-verified from objdump; see orchestrator/logs/phase5-liveness):     *)
(*  1. X6 = c^d (word_xor) -- the H aux inner term, hoisted into X6 by the    *)
(*     prior group's tail `eor x6,x8,x17` (= t2^t3 of the H-input state) and   *)
(*     consumed at the round head `eor x6,x6,x9` (^b).  Each H group takes     *)
(*     `read X6 = word_zx(word_xor c d)` and re-emits the same for the next.   *)
(*  2. X10 = the next round's T constant, PARTIALLY loaded -- the asm splits   *)
(*     a 32-bit constant load across the boundary: `mov x10,#lo` in the prior  *)
(*     group's tail, `movk x10,#hi,lsl 16` as the next group's FIRST           *)
(*     instruction.  So at group entry X10 holds only the low 16 bits          *)
(*     (`word <lo>`).  If this is not carried, the round-0 `add w4,w4,w10`     *)
(*     reads an unconstrained X10 and DISCARD_OLDSTATE erases the entire X4    *)
(*     output chain (symptom: an output read left un-substituted, then         *)
(*     `RAND_CONV: Not a combination` from the canon).  Carry                  *)
(*     `read X10 = word <lo>` in, and re-emit the next boundary's `word <lo'>` *)
(*     out.  For g8 the constants are: in = word 14658 (=0x3942, low half of   *)
(*     T[32]=0xfffa3942), out = word 59972 (=0xea44, low half of the constant  *)
(*     hoisted for round 36).                                                  *)
(*  3. The 16 register-resident message words (unchanged from the G groups).   *)
(*                                                                           *)
(* H group 0 (rounds 32-35, pc+0x558 -> pc+0x5e8, 36 instructions): role-tuple *)
(* (X4,X9,X8,X17), msgidx = [5;8;11;14], shifts 4/11/16/23.  Closes with       *)
(* MD5_REDUCE_CANON_H_TAC, the H analogue of the G/F closers.                  *)
(* ------------------------------------------------------------------------- *)

let MD5_BLOCK_H4_GROUP0_CORRECT = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x558) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X17 s = word_zx d /\
             read X6 s = word_zx(word_xor c d)) /\
            read X10 s = word 14658 /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x5e8) /\
            (let (t0,t1,t2,t3) =
                 md5_step 35 msg (md5_step 34 msg (md5_step 33 msg
                   (md5_step 32 msg st))) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
             read X6 s = word_zx(word_xor t2 t3)) /\
            read X10 s = word 59972 /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X10; X13; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (343--378) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `35`; num_CONV `34`; num_CONV `33`; num_CONV `32`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_H_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* H groups 1 and 2 (rounds 36-43): identical shape to H group 0.  Each takes the *)
(* role-tuple (X4,X9,X8,X17) + X6 = c^d precompute + X10 = next round's partial    *)
(* T-constant + the 16 register-resident message words, and re-emits                *)
(* md5_step(4k+3..4k) + the next group's X6 = (c^d) precompute + the next group's   *)
(* X10 partial constant.  The X10 in/out values are the low halves of the round-    *)
(* (4k) T-constants, read from the `mov x10,#imm` tails (machine-verified objdump):  *)
(*   g9  in = word 59972 (=0xea44), out = word 32454 (=0x7ec6 @0x670);              *)
(*   g10 in = word 32454,           out = word 53305 (=0xd039 @0x700).              *)
(* msgidx: g9 = [1;4;7;10], g10 = [13;0;3;6].  Same 36-step skeleton + H closer.     *)
let MD5_BLOCK_H4_GROUP1_CORRECT = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x5e8) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X17 s = word_zx d /\
             read X6 s = word_zx(word_xor c d)) /\
            read X10 s = word 59972 /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x678) /\
            (let (t0,t1,t2,t3) =
                 md5_step 39 msg (md5_step 38 msg (md5_step 37 msg
                   (md5_step 36 msg st))) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
             read X6 s = word_zx(word_xor t2 t3)) /\
            read X10 s = word 32454 /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X10; X13; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (379--414) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `39`; num_CONV `38`; num_CONV `37`; num_CONV `36`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_H_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

let MD5_BLOCK_H4_GROUP2_CORRECT = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x678) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X17 s = word_zx d /\
             read X6 s = word_zx(word_xor c d)) /\
            read X10 s = word 32454 /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x708) /\
            (let (t0,t1,t2,t3) =
                 md5_step 43 msg (md5_step 42 msg (md5_step 41 msg
                   (md5_step 40 msg st))) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
             read X6 s = word_zx(word_xor t2 t3)) /\
            read X10 s = word 53305 /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X10; X13; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (415--450) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `43`; num_CONV `42`; num_CONV `41`; num_CONV `40`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_H_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* H group 3 (rounds 44-47, the LAST H group, the H->I seam, pc+0x708 -> pc+0x798): *)
(* differs from the earlier H groups (machine-verified from objdump):               *)
(*  - It spans 36 instructions (steps 451..486; round 47's a' completes at           *)
(*    `add w9,w8,w9` @0x794, and the I round begins at 0x798).  The boundary 0x798   *)
(*    was confirmed by a PC-only probe (0x708 + 36 steps -> 0x798).                  *)
(*  - It carries NO H precompute forward: the I round's aux md5_i = (~d|b)^c is       *)
(*    computed inline via `orn x13,x9,x17` @0x79c (no hoisted `eor`/`bic`), so the    *)
(*    postcondition drops both the X6 = c^d carry AND the X10 partial constant.       *)
(*  - Instead it emits X6 = word 4096336452 (= T[48] = 0xf4292244), the I round's     *)
(*    first T-constant, loaded FULLY into X6 by `mov x6,#0x2244` @0x78c + `movk       *)
(*    x6,#0xf429` @0x790 (both in g11's tail, not split across the seam).  The I       *)
(*    round-48 head `add w4,w4,w6` @0x7a0 reads it.                                   *)
(* msgidx = [9;12;15;2].  State conjuncts still close with the H closer (rounds       *)
(* 44-47 are H rounds); the X6 = constant conjunct closes by ASM_REWRITE.            *)
let MD5_BLOCK_H4_GROUP3_CORRECT = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x708) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X17 s = word_zx d /\
             read X6 s = word_zx(word_xor c d)) /\
            read X10 s = word 53305 /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x798) /\
            (let (t0,t1,t2,t3) =
                 md5_step 47 msg (md5_step 46 msg (md5_step 45 msg
                   (md5_step 44 msg st))) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3) /\
            read X6 s = word 4096336452 /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X10; X13; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (451--486) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `47`; num_CONV `46`; num_CONV `45`; num_CONV `44`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_H_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* ========================================================================= *)
(* Phase 5: the I rounds (48-63).  I aux = (~d|b)^c, computed by the asm as    *)
(* `orn x13,x_b,x_d` (= b|~d) then `eor x6,x_c,x13` (= c ^ (b|~d)).             *)
(*                                                                           *)
(* STRUCTURAL DIFFERENCES from the G/H rounds (machine-verified from objdump): *)
(*  - NON-UNIFORM register layout (like the F rounds, unlike the uniform G/H   *)
(*    role tuple).  Each I group's output role-tuple (t0,t1,t2,t3) lands in a   *)
(*    different register set, and the message-register file is progressively    *)
(*    repurposed (16 -> 12 -> 8 -> 4 live message regs) as message words are    *)
(*    consumed for the last time.  The output layouts (a,b,c,d order):          *)
(*      g12 (r48-51, 0x798->0x828): (X4,X17,X8,X6),  emits X9 = T[52]           *)
(*      g13 (r52-55, 0x828->0x8b8): (X9,X17,X8,X6),  emits X15= T[56]           *)
(*      g14 (r56-59, 0x8b8->0x948): (X4,X9,X8,X15),  emits X6 = T[60]           *)
(*    md5_steps 64 = (a60,a63,a62,a61) by the role rotation, so the output      *)
(*    register holding each ti is found by tracking which round's a' lands      *)
(*    where (e.g. for g12: t0=a48->X4, t1=a51->X17, t2=a50->X8, t3=a49->X6).     *)
(*  - The next round's T-constant is loaded FULLY (mov+movk together) in the     *)
(*    group tail -- no partial-constant split across I-group boundaries (unlike  *)
(*    the H groups).  So each I group carries `read Xn = word <full T const>`.   *)
(*  - md5_i must be expanded in the hardware's xor-operand order `word_xor c     *)
(*    (word_or b (word_not d))` (c FIRST -- matching `eor x6,x_c,x13`), since     *)
(*    the canon reorders word_add chains but NOT word_xor.                       *)
(*  - MD5_ZX_OR_NOT collapses the int64 `orn` round-trip, but it MUST fire AFTER *)
(*    the WORD_ZX SIMP normalisation (not before), else the orn shape has not    *)
(*    yet emerged and the rewrite misses.                                        *)
(* ------------------------------------------------------------------------- *)

(* md5_i in the asm's xor-operand order (c first): eor x6,x_c,(orn x_b,x_d). *)
let MD5_I_EXPAND = prove
 (`!b c d:int32. md5_i b c d = word_xor c (word_or b (word_not d))`,
  REWRITE_TAC[md5_i] THEN CONV_TAC WORD_BLAST);;

(* The asm's `orn` produces word_or (zx b) (word_not (zx d)) in int64; reading   *)
(* it back as a w-register word_zx-truncates to int32, collapsing the spurious    *)
(* high-1s the 64-bit NOT introduced.  Instant single-var BLAST.                  *)
let MD5_ZX_OR_NOT = prove
 (`!b d:int32.
     word_zx (word_or (word_zx b :int64) (word_not (word_zx d :int64))) :int32 =
     word_or b (word_not d)`,
  CONV_TAC WORD_BLAST);;

(* The I-round closer.  Like the G/H closers but: I rotate-joins 26/22/17/11      *)
(* (ror 6/10/15/21 -> rol shifts), md5_i in c-first form, and MD5_ZX_OR_NOT fired  *)
(* AFTER the WORD_ZX SIMP (alongside the other zx-collapse rules) so the int64     *)
(* orn round-trip is collapsed once it has emerged.  Then the same bottom-up       *)
(* word_add canon closes by REFL.                                                  *)
let MD5_REDUCE_CANON_I_TAC : tactic =
  REWRITE_TAC[MD5_ROT_JOIN_26; MD5_ROT_JOIN_22; MD5_ROT_JOIN_17;
              MD5_ROT_JOIN_11; MD5_I_EXPAND] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH;
           WORD_ZX_XOR; WORD_ZX_AND] THEN
  REWRITE_TAC[MD5_SUBWORD_ZX_M; MD5_JOIN_LO; MD5_JOIN_HI;
              MD5_ZX_RT; MD5_ZX_NOT_ZX; MD5_ZX_OR_NOT] THEN
  CONV_TAC(BINOP_CONV WORD_ADD_CANON_CONV) THEN REFL_TAC;;

(* I group 0 (rounds 48-51, pc+0x798 -> pc+0x828, 36 instructions).  Takes the    *)
(* H-g11 output role tuple (X4,X9,X8,X17) + X6 = T[48] (=word 4096336452, loaded   *)
(* fully into X6 in g11's tail) + the 16 register-resident message words.  Output  *)
(* role-tuple (t0,t1,t2,t3) -> (X4,X17,X8,X6); emits X9 = T[52] (=word 1700485571) *)
(* for round 52.  Drops the 4 message regs read for the last time (X11,X12,X16,X22,*)
(* X23 -> here X12/X22/X23 consumed; 12 message regs survive).  msgidx=[0;7;14;5]. *)
let MD5_BLOCK_I4_GROUP0_CORRECT = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x798) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X17 s = word_zx d) /\
            read X6 s = word 4096336452 /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x828) /\
            (let (t0,t1,t2,t3) =
                 md5_step 51 msg (md5_step 50 msg (md5_step 49 msg
                   (md5_step 48 msg st))) in
             read X4 s = word_zx t0 /\ read X17 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X6 s = word_zx t3) /\
            read X9 s = word 1700485571 /\
            read X1 s = data /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X10; X13; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (487--522) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `51`; num_CONV `50`; num_CONV `49`; num_CONV `48`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_I_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* I group 1 (rounds 52-55, pc+0x828 -> pc+0x8b8, 36 instructions).  In: g12       *)
(* output (X4,X17,X8,X6) + X9 = T[52].  Out role-tuple -> (X9,X17,X8,X6); emits     *)
(* X15 = T[56] (=word 1873313359).  4 more message regs die (X11,X16,X20,X21        *)
(* consumed for rounds 52-55: msgidx=[12;3;10;1]); 8 survive.                       *)
let MD5_BLOCK_I4_GROUP1_CORRECT = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x828) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X17 s = word_zx b /\
             read X8 s = word_zx c /\ read X6 s = word_zx d) /\
            read X9 s = word 1700485571 /\
            read X1 s = data /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x8b8) /\
            (let (t0,t1,t2,t3) =
                 md5_step 55 msg (md5_step 54 msg (md5_step 53 msg
                   (md5_step 52 msg st))) in
             read X9 s = word_zx t0 /\ read X17 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X6 s = word_zx t3) /\
            read X15 s = word 1873313359 /\
            read X1 s = data /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X10; X13; X15; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (523--558) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `55`; num_CONV `54`; num_CONV `53`; num_CONV `52`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_I_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* I group 2 (rounds 56-59, pc+0x8b8 -> pc+0x948, 36 instructions).  In: g13        *)
(* output (X9,X17,X8,X6) + X15 = T[56].  Out role-tuple -> (X4,X9,X8,X15); emits    *)
(* X6 = T[60] (=word 4149444226).  Message regs X5,X7,X26,X27 consumed              *)
(* (msgidx=[8;15;6;13]); only X3(msg2),X14(msg4),X24(msg9),X25(msg11) survive       *)
(* for g15.  NB the asm repurposes X15/X7 as scratch mid-group AFTER their message  *)
(* words are dead, so they are safely in the write set.                             *)
let MD5_BLOCK_I4_GROUP2_CORRECT = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x8b8) /\
            (let (a,b,c,d) = st in
             read X9 s = word_zx a /\ read X17 s = word_zx b /\
             read X8 s = word_zx c /\ read X6 s = word_zx d) /\
            read X15 s = word 1873313359 /\
            read X1 s = data /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x948) /\
            (let (t0,t1,t2,t3) =
                 md5_step 59 msg (md5_step 58 msg (md5_step 57 msg
                   (md5_step 56 msg st))) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X15 s = word_zx t3) /\
            read X6 s = word 4149444226 /\
            read X1 s = data /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11))
       (MAYCHANGE [PC; X4; X6; X7; X8; X9; X13; X15; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (559--594) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `59`; num_CONV `58`; num_CONV `57`; num_CONV `56`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_I_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* ========================================================================= *)
(* Phase 6: the combined round-60..63 group (g15) + the state add-back.       *)
(*                                                                           *)
(* g15 cannot end as four clean spec registers: the asm FUSES round 63's      *)
(* `+b` into the add-back.  At pc+0x9c8 (`ror w8,w8,#11`) X8 holds ONLY        *)
(* word_rol t63 21 (the rotate); the `+b` is completed at pc+0x9d4            *)
(* (`add w3,w14,w8`) inside the add-back, where w14 = a62 plays the role of    *)
(* the rotate's added `b`.  So we co-design g15 with the add-back as one       *)
(* ensures spanning pc+0x948 -> pc+0x9f0 (rounds 60-63 + the four 32-bit       *)
(* reloads/adds/stores), ending the register-only invariant.                  *)
(*                                                                           *)
(* Inputs: the g14 output role tuple st = (X4,X9,X8,X15) = md5_steps 60        *)
(* (taken opaquely as `st`), X6 = T[60] (=word 4149444226, loaded fully in     *)
(* g14's tail for round 60), the surviving message regs (X3=join(m3)(m2),      *)
(* X14=join(m5)(m4), X24=msg9, X25=msg11 -- the only message words rounds       *)
(* 60-63 read, msgidx=[4;11;2;9]), the data pointer X1, the STATE pointer X0,   *)
(* and the four ORIGINAL state words (A,B,C,D) in memory at state[0..3].        *)
(*                                                                           *)
(* Output: the four 32-bit stores back to state[0..3] equal the MD5 add-back   *)
(*   state[i] := state[i] + (md5_steps 64 msg st0)[i]                          *)
(* expressed here as (A + t0, B + t1, C + t2, D + t3) where                    *)
(*   (t0,t1,t2,t3) = md5_step 63..60 st  (= md5_steps 64 with st = md5_steps   *)
(* 60).  The role re-alignment is built into the four `add w*,...` operand      *)
(* pairings (machine-verified, RFC-faithful KAT).  The fused round-63 store     *)
(* needs NO special handling: MD5_REDUCE_CANON_I_TAC normalises the whole       *)
(* word_add tree (the leading `+A/+B/+C/+D` original and the fused `+b`         *)
(* alike), so every store conjunct closes by the same I closer.                *)
(* This is the state-memory boundary: Phase 5's register-only core ends here.  *)
(* ------------------------------------------------------------------------- *)

(* Add-back variant that ALSO emits the new state in registers w10..w13.  The    *)
(* optimized asm keeps the running MD5 state in w10..w13 across loop iterations   *)
(* (it does NOT reload from memory at the loop top -- the entry ldp's @0x18 run   *)
(* once before the loop).  At pc+0x9f0 the add-back has just computed             *)
(*   w10=A', w11=B', w12=C', w13=D'  (the new state = the four just-stored words, *)
(*   via add w10,w7,w6 @0x9e0 etc.) so re-emitting them as                        *)
(*   read X10..X13 = word_zx(word_add A/B/C/D t0/t1/t2/t3)                         *)
(* makes the loop carry state in registers.  This is the foundation for the       *)
(* Phase 7 do-while loop body, and the memory-only MD5_BLOCK_ADDBACK_CORRECT       *)
(* milestone is derived from it just below (by dropping the w10..w13 conjuncts).   *)
let MD5_BLOCK_ADDBACK_REGS = prove
 (`!st:int32#int32#int32#int32 A B C D state data (msg:num->int32) pc.
     nonoverlapping (word pc, LENGTH md5_block_mc) (state, 16)
     ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x948) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X15 s = word_zx d) /\
            read X6 s = word 4149444226 /\
            read X1 s = data /\ read X0 s = state /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read (memory :> bytes32 state) s = (A:int32) /\
            read (memory :> bytes32 (word_add state (word 4))) s = (B:int32) /\
            read (memory :> bytes32 (word_add state (word 8))) s = (C:int32) /\
            read (memory :> bytes32 (word_add state (word 12))) s = (D:int32))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x9f0) /\
            read X0 s = state /\ read X1 s = data /\
            (let (t0,t1,t2,t3) =
                 md5_step 63 msg (md5_step 62 msg (md5_step 61 msg (md5_step 60 msg st))) in
             read (memory :> bytes32 state) s = word_add A t0 /\
             read (memory :> bytes32 (word_add state (word 4))) s = word_add B t1 /\
             read (memory :> bytes32 (word_add state (word 8))) s = word_add C t2 /\
             read (memory :> bytes32 (word_add state (word 12))) s = word_add D t3 /\
             read X10 s = word_zx(word_add A t0) /\
             read X11 s = word_zx(word_add B t1) /\
             read X12 s = word_zx(word_add C t2) /\
             read X13 s = word_zx(word_add D t3)))
       (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14;
                   X15; X16; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes32 state;
                   memory :> bytes32 (word_add state (word 4));
                   memory :> bytes32 (word_add state (word 8));
                   memory :> bytes32 (word_add state (word 12))])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fst MD5_BLOCK_EXEC] THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (595--636) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[num_CONV `63`; num_CONV `62`; num_CONV `61`; num_CONV `60`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_I_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* The memory-only add-back MD5_BLOCK_ADDBACK_CORRECT is the register-emitting *)
(* MD5_BLOCK_ADDBACK_REGS above with the X10..X13 postcondition conjuncts      *)
(* dropped, so it is obtained by a one-step postcondition weakening instead of *)
(* re-running the rounds-60..63 + add-back symbolic execution a second time.   *)
(* ------------------------------------------------------------------------- *)
let MD5_BLOCK_ADDBACK_CORRECT = prove
 (`!st:int32#int32#int32#int32 A B C D state data (msg:num->int32) pc.
     nonoverlapping (word pc, LENGTH md5_block_mc) (state, 16)
     ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x948) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X15 s = word_zx d) /\
            read X6 s = word 4149444226 /\
            read X1 s = data /\ read X0 s = state /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read (memory :> bytes32 state) s = (A:int32) /\
            read (memory :> bytes32 (word_add state (word 4))) s = (B:int32) /\
            read (memory :> bytes32 (word_add state (word 8))) s = (C:int32) /\
            read (memory :> bytes32 (word_add state (word 12))) s = (D:int32))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x9f0) /\
            read X0 s = state /\ read X1 s = data /\
            (let (t0,t1,t2,t3) =
                 md5_step 63 msg (md5_step 62 msg (md5_step 61 msg
                   (md5_step 60 msg st))) in
             read (memory :> bytes32 state) s = word_add A t0 /\
             read (memory :> bytes32 (word_add state (word 4))) s = word_add B t1 /\
             read (memory :> bytes32 (word_add state (word 8))) s = word_add C t2 /\
             read (memory :> bytes32 (word_add state (word 12))) s = word_add D t3))
       (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14;
                   X15; X16; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes32 state;
                   memory :> bytes32 (word_add state (word 4));
                   memory :> bytes32 (word_add state (word 8));
                   memory :> bytes32 (word_add state (word 12))])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL MD5_BLOCK_ADDBACK_REGS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun regs ->
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl regs))) THEN
    CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC regs]) THEN
  GEN_TAC THEN BETA_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`md5_step 63 msg (md5_step 62 msg (md5_step 61 msg (md5_step 60 msg st)))`,
           `q:int32#int32#int32#int32`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* G group 3 (g7) re-augmented for the G->H seam.  The plain                   *)
(* MD5_BLOCK_G4_GROUP3_CORRECT emits only the 4 state words, but the G->H       *)
(* boundary (pc+0x558) needs TWO pipelined carries the H rounds consume:        *)
(*   - X6 = c^d (word_xor), the H aux inner term, hoisted by `eor x6,x8,x17`    *)
(*     @0x548 (within g7's span);                                               *)
(*   - X10 = word 14658, the partial T-constant `mov x10,#0x3942` @0x550,        *)
(*     completed by `movk x10,#0xfffa,lsl 16` as H group 0's first instruction. *)
(* Both are computed in g7's span (0x4b4->0x558), so re-emitting them makes      *)
(* g7's postcondition equal H group 0's precondition verbatim, letting the core  *)
(* chain cross the G->H phase boundary with no bridge.  The X6 conjunct closes   *)
(* with the G closer (WORD_ZX_XOR is already in its SIMP); X10 by ASM_REWRITE.   *)
(* ------------------------------------------------------------------------- *)
let MD5_BLOCK_G4_GROUP3_AUG = prove
 (`!st:int32#int32#int32#int32 data (msg:num->int32) pc.
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x4b4) /\
            (let (a,b,c,d) = st in
             read X4 s = word_zx a /\ read X9 s = word_zx b /\
             read X8 s = word_zx c /\ read X17 s = word_zx d /\
             read X6 s = word_zx(word_and c (word_not d))) /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x558) /\
            (let (t0,t1,t2,t3) =
                 md5_step 31 msg (md5_step 30 msg (md5_step 29 msg
                   (md5_step 28 msg st))) in
             read X4 s = word_zx t0 /\ read X9 s = word_zx t1 /\
             read X8 s = word_zx t2 /\ read X17 s = word_zx t3 /\
             read X6 s = word_zx(word_xor t2 t3)) /\
            read X10 s = word 14658 /\
            read X1 s = data /\
            read X15 s = word_join (msg 1) (msg 0) /\
            read X3 s = word_join (msg 3) (msg 2) /\
            read X14 s = word_join (msg 5) (msg 4) /\
            read X7 s = word_join (msg 7) (msg 6) /\
            read X5 s = word_join (msg 9) (msg 8) /\
            read X16 s = word_join (msg 11) (msg 10) /\
            read X11 s = word_join (msg 13) (msg 12) /\
            read X12 s = word_join (msg 15) (msg 14) /\
            read X20 s = word_zx (msg 1) /\ read X21 s = word_zx (msg 3) /\
            read X22 s = word_zx (msg 5) /\ read X23 s = word_zx (msg 7) /\
            read X24 s = word_zx (msg 9) /\ read X25 s = word_zx (msg 11) /\
            read X26 s = word_zx (msg 13) /\ read X27 s = word_zx (msg 15))
       (MAYCHANGE [PC; X4; X6; X8; X9; X10; X13; X17] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (302--342) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[num_CONV `31`; num_CONV `30`; num_CONV `29`; num_CONV `28`] THEN
  CONV_TAC(ONCE_DEPTH_CONV MD5_SPEC_REDUCE_CONV) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST [MD5_REDUCE_CANON_G_TAC; ASM_REWRITE_TAC[]]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SOME_FLAGS]) THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* ========================================================================= *)
(* Phase 5 FINAL: the complete register core + add-back, pc+0x20 -> pc+0x9f0.   *)
(* From the loop top with the four state words in X10..X13 (= the in-memory     *)
(* state A,B,C,D) and the 64-byte message block in memory, after the 64 rounds  *)
(* + the 4-word state add-back the four state words in memory equal             *)
(* md5_block_spec (A,B,C,D) msg, with X0=state and X1=data preserved.           *)
(*                                                                           *)
(* This is proved in the stronger register-emitting form first                 *)
(* (MD5_BLOCK_CORE_REGS_CORRECT below, the Phase 7 loop foundation), then the   *)
(* memory-only milestone MD5_BLOCK_CORE_CORRECT is obtained from it by simply   *)
(* dropping the X10..X13 postcondition conjuncts -- so the expensive core chain *)
(* (fold F16_AUG + 11 G/H/I groups via ENSURES_TRANS, thread X0 + the four      *)
(* bytes32(state) words, reshape + ENSURES_TRANS with the add-back, fold        *)
(* md5_steps 64 = MD5_STEPS_64_NEST + md5_block_spec) is built ONCE, not twice.  *)
(* ------------------------------------------------------------------------- *)

(* md5_steps 64 in fully-nested md5_step form (over md5_steps 16), for folding  *)
(* the chained core's deep nest back to the named spec count.                   *)
let MD5_STEPS_64_NEST =
  let st = `st:int32#int32#int32#int32` and msg = `msg:num->int32` in
  let step i t = mk_comb(mk_comb(mk_comb(`md5_step`,mk_small_numeral i),msg),t) in
  let base = `md5_steps 16 msg (st:int32#int32#int32#int32)` in
  let rhs = List.fold_left (fun acc i -> step i acc) base (16--63) in
  let lhs = `md5_steps 64 msg (st:int32#int32#int32#int32)` in
  let gtm = list_mk_forall([msg;st], mk_eq(lhs,rhs)) in
  let numconvs = map (fun i -> num_CONV (mk_small_numeral i)) (List.rev (17--64)) in
  prove(gtm, REWRITE_TAC(md5_steps :: numconvs));;

(* ------------------------------------------------------------------------- *)
(* MD5_BLOCK_CORE_REGS_CORRECT: the same complete core (pc+0x20 -> pc+0x9f0)    *)
(* but its postcondition ALSO leaves the new state in registers X10..X13        *)
(* (= word_zx of the md5_block_spec components).  Foundation for the Phase 7     *)
(* do-while loop, whose invariant carries the running state in w10..w13 across   *)
(* iterations (the asm does not reload state from memory at the loop top).       *)
(* the memory-only MD5_BLOCK_CORE_CORRECT milestone is derived from it below   *)
(* (by dropping the X10..X13 conjuncts).  This proof chains MD5_BLOCK_ADDBACK_REGS *)
(* ------------------------------------------------------------------------- *)
let MD5_BLOCK_CORE_REGS_CORRECT = prove
 (`!A B C D state data (msg:num->int32) pc.
     nonoverlapping (word pc, LENGTH md5_block_mc) (state, 16)
     ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x20) /\
            read X10 s = word_zx(A:int32) /\ read X11 s = word_zx(B:int32) /\
            read X12 s = word_zx(C:int32) /\ read X13 s = word_zx(D:int32) /\
            read X1 s = data /\ read X0 s = state /\
            read (memory :> bytes64 data) s = word_join (msg 1) (msg 0) /\
            read (memory :> bytes64 (word_add data (word 8))) s = word_join (msg 3) (msg 2) /\
            read (memory :> bytes64 (word_add data (word 16))) s = word_join (msg 5) (msg 4) /\
            read (memory :> bytes64 (word_add data (word 24))) s = word_join (msg 7) (msg 6) /\
            read (memory :> bytes64 (word_add data (word 32))) s = word_join (msg 9) (msg 8) /\
            read (memory :> bytes64 (word_add data (word 40))) s = word_join (msg 11) (msg 10) /\
            read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
            read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14) /\
            read (memory :> bytes32 state) s = A /\
            read (memory :> bytes32 (word_add state (word 4))) s = B /\
            read (memory :> bytes32 (word_add state (word 8))) s = C /\
            read (memory :> bytes32 (word_add state (word 12))) s = D)
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x9f0) /\
            read X0 s = state /\ read X1 s = data /\
            (let (a',b',c',d') = md5_block_spec (A,B,C,D) msg in
             read (memory :> bytes32 state) s = a' /\
             read (memory :> bytes32 (word_add state (word 4))) s = b' /\
             read (memory :> bytes32 (word_add state (word 8))) s = c' /\
             read (memory :> bytes32 (word_add state (word 12))) s = d' /\
             read X10 s = word_zx a' /\ read X11 s = word_zx b' /\
             read X12 s = word_zx c' /\ read X13 s = word_zx d'))
       (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14;
                   X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes32 state;
                   memory :> bytes32 (word_add state (word 4));
                   memory :> bytes32 (word_add state (word 8));
                   memory :> bytes32 (word_add state (word 12))])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  let nest4 lo st =
    let s i t = mk_comb(mk_comb(mk_comb(`md5_step`,mk_small_numeral i),`msg:num->int32`),t) in
    s (lo+3) (s (lo+2) (s (lo+1) (s lo st))) in
  let groups = [
    MD5_BLOCK_G4_GROUP0_CORRECT, 16;  MD5_BLOCK_G4_GROUP1_CORRECT, 20;
    MD5_BLOCK_G4_GROUP2_CORRECT, 24;  MD5_BLOCK_G4_GROUP3_AUG,     28;
    MD5_BLOCK_H4_GROUP0_CORRECT, 32;  MD5_BLOCK_H4_GROUP1_CORRECT, 36;
    MD5_BLOCK_H4_GROUP2_CORRECT, 40;  MD5_BLOCK_H4_GROUP3_CORRECT, 44;
    MD5_BLOCK_I4_GROUP0_CORRECT, 48;  MD5_BLOCK_I4_GROUP1_CORRECT, 52;
    MD5_BLOCK_I4_GROUP2_CORRECT, 56 ] in
  let core_reg =
    fst(List.fold_left
      (fun (acc,st_run) (grp,lo) ->
         let gi = INST [st_run, `st:int32#int32#int32#int32`] (SPEC_ALL grp) in
         (MATCH_MP ENSURES_TRANS (CONJ acc gi), nest4 lo st_run))
      (SPECL [`A:int32`;`B:int32`;`C:int32`;`D:int32`;
              `data:int64`;`msg:num->int32`;`pc:num`] MD5_BLOCK_F16_AUG_CORRECT,
       `md5_steps 16 msg (A:int32,B:int32,C:int32,D:int32)`) groups) in
  (* Collapse the deeply-nested chain frame (the 12 stacked MAYCHANGE blocks left  *)
  (* by the ENSURES_TRANS fold) to a single flat MAYCHANGE before threading.  Each  *)
  (* of the five frame-preservation side proofs below (MD5_FRAME_PRESERVES_TAC)     *)
  (* expands its frame into assignment form; against the raw nest that costs ~10s    *)
  (* each (~50s total), but against the 1-level flat frame it is ~0.01s each.  One   *)
  (* SUBSUMED_MAYCHANGE_TAC discharges the collapse; the postcondition is unchanged  *)
  (* and the goal frame is re-subsumed downstream, so the result is identical.       *)
  let flatframe =
    `MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
                X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]` in
  let core_reg =
    MATCH_MP ENSURES_FRAME_SUBSUMED
     (CONJ (prove(list_mk_icomb "subsumed" [rand(concl core_reg); flatframe],
                  REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC))
           core_reg) in
  let cframe = rand(concl core_reg) in
  let mk_pres ctm vty =
    let rd = inst (type_match `:A` vty []) `read:(armstate,A)component->armstate->A` in
    let s = `s:armstate` and s' = `s':armstate` in
    prove(list_mk_forall([s;s'],
       mk_imp(list_mk_comb(cframe,[s;s']),
              mk_eq(list_mk_comb(rd,[ctm;s']),list_mk_comb(rd,[ctm;s])))),
      MD5_FRAME_PRESERVES_TAC) in
  let thread c vty v th =
    SPEC v (MATCH_MP ENSURES_THREAD_PRESERVED (CONJ (mk_pres c vty) th)) in
  let core_thr =
    CONV_RULE(DEPTH_CONV BETA_CONV)
     (thread `memory :> bytes32 (word_add state (word 12))` `:int32` `D:int32`
      (thread `memory :> bytes32 (word_add state (word 8))` `:int32` `C:int32`
       (thread `memory :> bytes32 (word_add state (word 4))` `:int32` `B:int32`
        (thread `memory :> bytes32 state` `:int32` `A:int32`
         (thread `X0` `:int64` `state:int64` core_reg))))) in
  let deep_nest =
    List.fold_left (fun st lo -> nest4 lo st)
      `md5_steps 16 msg (A:int32,B:int32,C:int32,D:int32)`
      [16;20;24;28;32;36;40;44;48;52] in
  let i2out = nest4 56 deep_nest in
  let addback = INST [i2out, `st:int32#int32#int32#int32`] (SPEC_ALL MD5_BLOCK_ADDBACK_REGS) in
  let ab_ens = UNDISCH addback in
  let pre_ab = rand(rator(rator(concl ab_ens))) in
  let reshaped = prove
   (mk_comb(mk_comb(mk_comb(`ensures arm`, rand(rator(rator(concl core_thr)))),
                    pre_ab), rand(concl core_thr)),
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl core_thr))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN CONV_TAC TAUT;
      MP_TAC core_thr THEN MESON_TAC[]]) in
  let core_full = MATCH_MP ENSURES_TRANS (CONJ reshaped ab_ens) in
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC (rand(concl core_full)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (rand(rator(concl core_full))) THEN
  CONJ_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[md5_block_spec; GSYM MD5_STEPS_64_NEST] THEN
    SPEC_TAC(`md5_steps 64 msg (A:int32,B:int32,C:int32,D:int32)`,
             `q:int32#int32#int32#int32`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(concl core_full)))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC TAUT;
      MP_TAC core_full THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* MD5_BLOCK_CORE_CORRECT: the Phase-5/6 milestone -- the same complete core   *)
(* (pc+0x20 -> pc+0x9f0) leaving the new state in memory only.  It is the      *)
(* register-emitting MD5_BLOCK_CORE_REGS_CORRECT with the X10..X13 conjuncts   *)
(* of its postcondition dropped, so it is obtained by a one-step postcondition *)
(* weakening rather than rebuilding the 64-round core chain a second time.     *)
(* ------------------------------------------------------------------------- *)
let MD5_BLOCK_CORE_CORRECT = prove
 (`!A B C D state data (msg:num->int32) pc.
     nonoverlapping (word pc, LENGTH md5_block_mc) (state, 16)
     ==> ensures arm
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x20) /\
            read X10 s = word_zx(A:int32) /\ read X11 s = word_zx(B:int32) /\
            read X12 s = word_zx(C:int32) /\ read X13 s = word_zx(D:int32) /\
            read X1 s = data /\ read X0 s = state /\
            read (memory :> bytes64 data) s = word_join (msg 1) (msg 0) /\
            read (memory :> bytes64 (word_add data (word 8))) s = word_join (msg 3) (msg 2) /\
            read (memory :> bytes64 (word_add data (word 16))) s = word_join (msg 5) (msg 4) /\
            read (memory :> bytes64 (word_add data (word 24))) s = word_join (msg 7) (msg 6) /\
            read (memory :> bytes64 (word_add data (word 32))) s = word_join (msg 9) (msg 8) /\
            read (memory :> bytes64 (word_add data (word 40))) s = word_join (msg 11) (msg 10) /\
            read (memory :> bytes64 (word_add data (word 48))) s = word_join (msg 13) (msg 12) /\
            read (memory :> bytes64 (word_add data (word 56))) s = word_join (msg 15) (msg 14) /\
            read (memory :> bytes32 state) s = A /\
            read (memory :> bytes32 (word_add state (word 4))) s = B /\
            read (memory :> bytes32 (word_add state (word 8))) s = C /\
            read (memory :> bytes32 (word_add state (word 12))) s = D)
       (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
            read PC s = word(pc + 0x9f0) /\
            read X0 s = state /\ read X1 s = data /\
            (let (a',b',c',d') = md5_block_spec (A,B,C,D) msg in
             read (memory :> bytes32 state) s = a' /\
             read (memory :> bytes32 (word_add state (word 4))) s = b' /\
             read (memory :> bytes32 (word_add state (word 8))) s = c' /\
             read (memory :> bytes32 (word_add state (word 12))) s = d'))
       (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14;
                   X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes32 state;
                   memory :> bytes32 (word_add state (word 4));
                   memory :> bytes32 (word_add state (word 8));
                   memory :> bytes32 (word_add state (word 12))])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL MD5_BLOCK_CORE_REGS_CORRECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun regs ->
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl regs))) THEN
    CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC regs]) THEN
  GEN_TAC THEN BETA_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`md5_block_spec (A,B,C,D) msg`,`q:int32#int32#int32#int32`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* PHASE 7: the multi-block do-while loop.                                    *)
(*                                                                            *)
(* The compiled routine keeps the running MD5 state in w10..w13 across loop   *)
(* iterations (it loads the state from memory ONCE at pc+0x18, before the     *)
(* loop top pc+0x20, then threads it in registers and writes it back to       *)
(* memory each iteration via the add-back).  The loop is a do-while with no   *)
(* top guard: the body always runs at least once, the backedge is the         *)
(* flag-conditional `subs w2,#1; b.ne pc+0x20`.  Hence the final theorem      *)
(* requires `0 < val num` (at num=0 the asm would run one body and wrap the   *)
(* 32-bit counter, which does NOT match md5_blocks 0 = the identity).         *)
(* ------------------------------------------------------------------------- *)

(* Forward ("snoc") form of the md5_blocks recursion.  The spec peels the     *)
(* FIRST block (md5_blocks (SUC n) st msg = md5_blocks n (md5_block_spec ...));*)
(* the loop accumulates forward, so block i absorbs into the state after i     *)
(* blocks using the message slice starting at word 16*i.                      *)
let MD5_BLOCKS_SNOC = prove
 (`!i st (msg:num->int32).
     md5_blocks (i + 1) st msg =
     md5_block_spec (md5_blocks i st msg) (\k. msg (k + 16 * i))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; ARITH_RULE `0 + 1 = SUC 0`] THEN
    REWRITE_TAC[md5_blocks; ETA_AX];
    REWRITE_TAC[ARITH_RULE `SUC i + 1 = SUC(i + 1)`] THEN
    GEN_TAC THEN GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV) [md5_blocks] THEN
    GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [md5_blocks] THEN
    FIRST_X_ASSUM(MP_TAC o
      SPECL [`md5_block_spec st msg`; `(\k. msg (k + 16)):num->int32`]) THEN
    DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN AP_TERM_TAC THEN ARITH_TAC]);;

(* Generalization of ENSURES_THREAD_PRESERVED to an arbitrary state predicate  *)
(* R (not just a single component read).  Used to carry the loop's quantified  *)
(* read-only message-memory conjunct through the register core, whose frame    *)
(* leaves all of memory[data] untouched (it writes only memory[state], which   *)
(* is nonoverlapping with the message region).                                 *)
let ENSURES_THREAD_PRESERVED_PRED = prove
 (`!P Q C (R:armstate->bool).
        (!s s'. C s s' ==> (R s' <=> R s)) /\
        ensures arm P Q C
        ==> ensures arm (\s. P s /\ R s) (\s. Q s /\ R s) C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures] THEN STRIP_TAC THEN
  X_GEN_TAC `s:armstate` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:armstate`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s'. ((\s'. (Q:armstate->bool) s' /\ C (s:armstate) s') s')
         ==> ((\s'. ((Q:armstate->bool) s' /\ R s') /\ C (s:armstate) s') s')`
  MP_TAC THENL
   [BETA_TAC THEN X_GEN_TAC `s':armstate` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP EVENTUALLY_MONO) THEN
    DISCH_THEN(MP_TAC o SPECL [`arm`; `s:armstate`]) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7a: the do-while backedge.                                           *)
(*                                                                            *)
(* The three backedge instructions (pc+0x9f0..0x9f8) advance the data pointer *)
(* by one block (add x1,#0x40), decrement the 32-bit block counter            *)
(* (subs w2,#1), and branch back to the loop top if it is still nonzero       *)
(* (b.ne pc+0x20), else fall through to the epilogue at pc+0x9fc.             *)
(* The counter is held in W2 as `word(num - i)`; with `i < num < 2^32` the    *)
(* `subs` produces `word(num - (i+1))` and the ZF test is exactly             *)
(* `i + 1 < num`.                                                             *)
(* ------------------------------------------------------------------------- *)

(* The 32-bit decrement, narrowed back from the stepper's nested-word_zx form *)
(* to the clean `num - (i+1)` value.  Used for both the W2 result and the     *)
(* ZF/PC-conditional reasoning at the backedge.                               *)
let MD5_COUNTER_DEC = prove
 (`!num i. i < num /\ num < 2 EXP 32
   ==> val(word_sub (word_zx (word (num - i):int64):int32) (word 1)) = num - (i + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx (word (num - i):int64):int32) = num - i` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `(num - i) MOD 2 EXP 64 = num - i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1; DIMINDEX_32] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC]);;

(* The W2 result lifted through the int32->int64 zero-extension.              *)
let MD5_COUNTER_DEC_ZX = prove
 (`!num i. i < num /\ num < 2 EXP 32
   ==> word_zx (word_sub (word_zx (word (num - i):int64):int32) (word 1)):int64 =
       word (num - (i + 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`num:num`; `i:num`] MD5_COUNTER_DEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  ASM_SIMP_TAC[VAL_WORD_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`]);;

(* The backedge ensures: pc+0x9f0 -> (pc+0x20 if more blocks else pc+0x9fc).   *)
let MD5_BLOCK_BACKEDGE_CORRECT = prove
 (`!data0:int64 pc num i.
    0 < num /\ num < 2 EXP 32 /\ i < num
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
           read PC s = word(pc + 0x9f0) /\
           read X1 s = word_add data0 (word(64 * i)) /\
           read X2 s = word(num - i))
      (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
           read PC s = word(if i + 1 < num then pc + 0x20 else pc + 0x9fc) /\
           read X1 s = word_add data0 (word(64 * (i + 1))) /\
           read X2 s = word(num - (i + 1)))
      (MAYCHANGE [PC; X1; X2] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[fst MD5_BLOCK_EXEC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (637--639) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ (* PC conditional *)
    SUBGOAL_THEN
      `val(word_sub (word_zx (word (num - i):int64):int32) (word 1)) = num - (i + 1)`
      SUBST1_TAC THENL
     [ASM_SIMP_TAC[MD5_COUNTER_DEC]; ALL_TAC] THEN
    SUBGOAL_THEN `~(num - (i + 1) = 0) <=> i + 1 < num` SUBST1_TAC THENL
     [UNDISCH_TAC `i < num` THEN ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[];
    (* X1 pointer advance *)
    REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; GSYM WORD_ADD] THEN
    CONV_TAC WORD_RULE;
    (* X2 counter *)
    ASM_SIMP_TAC[MD5_COUNTER_DEC_ZX]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7a: the loop body.                                                   *)
(*                                                                            *)
(* The body runs the register-only core (MD5_BLOCK_CORE_REGS_CORRECT) for one *)
(* block i, then the three backedge instructions.  The running MD5 state is   *)
(* carried in W10..W13 (and mirrored in memory[state]); the read-only message *)
(* input is carried as a single quantified conjunct R over the whole input    *)
(* region, from which the core's eight per-block doubleword reads are derived. *)
(* The body is stated generically in the running state (a,b,c,d) and posts    *)
(* md5_block_spec; the loop theorem (Phase 7b) instantiates                    *)
(* (a,b,c,d) := md5_blocks i ... and folds via MD5_BLOCKS_SNOC.               *)
(* ------------------------------------------------------------------------- *)

(* The read-only input region is preserved across the core's MAYCHANGE frame   *)
(* (which writes only memory[state], nonoverlapping with the input region).    *)
let MD5_CORE_PRESERVES_INPUT = prove
 (`!num data0 state (msg:num->int32).
    nonoverlapping (state:int64, 16) (data0:int64, 64 * num)
    ==> !s s'.
       (MAYCHANGE
         [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X19;
          X20; X21; X22; X23; X24; X25; X26; X27] ,,
        MAYCHANGE SOME_FLAGS ,,
        MAYCHANGE [events] ,,
        MAYCHANGE
         [memory :> bytes32 state; memory :> bytes32 (word_add state (word 4));
          memory :> bytes32 (word_add state (word 8));
          memory :> bytes32 (word_add state (word 12))]) s s'
       ==> ((!m. m < 8 * num
              ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s' =
                  word_join (msg(2*m+1)) (msg(2*m))) <=>
            (!m. m < 8 * num
              ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s =
                  word_join (msg(2*m+1)) (msg(2*m))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!m. m < 8 * num
        ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s' =
            read (memory :> bytes64 (word_add data0 (word(8 * m)))) s`
   ASSUME_TAC THENL
   [FIRST_X_ASSUM MP_TAC THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID; SOME_FLAGS] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    READ_OVER_WRITE_ORTHOGONAL_TAC;
    EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    ASM_MESON_TAC[]]);;

(* The core's eight per-block doubleword reads (at data0+64i+8j, j<8) follow   *)
(* from the global read-only input conjunct R (at data0+8m, m<8*num), since    *)
(* data0+64i+8j = data0+8*(8i+j) and 8i+j < 8*num when i<num and j<8.          *)
let MD5_BLOCK_INPUT_READS = prove
 (`!num data0 (msg:num->int32) i s.
   i < num /\
   (!m. m < 8 * num
        ==> read (memory :> bytes64 (word_add (data0:int64) (word(8 * m)))) s =
            word_join (msg(2*m+1)) (msg(2*m)))
   ==> (!j. j < 8
        ==> read (memory :> bytes64 (word_add (word_add data0 (word(64*i))) (word(8*j)))) s =
            word_join (msg(16*i+(2*j+1))) (msg(16*i+2*j)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `word_add (word_add (data0:int64) (word(64*i))) (word(8*j)) =
    word_add data0 (word(8 * (8 * i + j)))` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `8 * i + j`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * (8 * i + j) = 16 * i + 2 * j`;
              ARITH_RULE `2 * (8 * i + j) + 1 = 16 * i + (2 * j + 1)`]);;

(* The read-only input region is also preserved across the backedge's frame    *)
(* (PC/X1/X2/flags/events only -- it writes no memory at all).                  *)
let MD5_BE_PRESERVES_INPUT = prove
 (`!num data0 (msg:num->int32).
    !s s'.
       (MAYCHANGE [PC; X1; X2] ,, MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events]) s s'
       ==> ((!m. m < 8 * num
              ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s' =
                  word_join (msg(2*m+1)) (msg(2*m))) <=>
            (!m. m < 8 * num
              ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s =
                  word_join (msg(2*m+1)) (msg(2*m))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!m. read (memory :> bytes64 (word_add data0 (word(8 * m)))) s' =
        read (memory :> bytes64 (word_add data0 (word(8 * m)))) s`
   (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN FIRST_X_ASSUM MP_TAC THEN
  REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
  REWRITE_TAC[GSYM SEQ_ASSOC] THEN
  PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
  CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ASSIGNS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  READ_OVER_WRITE_ORTHOGONAL_TAC);;

(* The loop body: pc+0x20 (block i) -> (pc+0x20 or pc+0x9fc) (block i+1).       *)
let MD5_BLOCK_LOOP_BODY = prove
 (`!a b c d state data0 (msg:num->int32) pc num i.
    nonoverlapping (word pc, LENGTH md5_block_mc) (state, 16) /\
    nonoverlapping (state:int64, 16) (data0:int64, 64 * num) /\
    0 < num /\ num < 2 EXP 32 /\ i < num
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
           read PC s = word(pc + 0x20) /\
           read X10 s = word_zx(a:int32) /\ read X11 s = word_zx(b:int32) /\
           read X12 s = word_zx(c:int32) /\ read X13 s = word_zx(d:int32) /\
           read X0 s = state /\ read X1 s = word_add data0 (word(64 * i)) /\
           read X2 s = word(num - i) /\
           read (memory :> bytes32 state) s = a /\
           read (memory :> bytes32 (word_add state (word 4))) s = b /\
           read (memory :> bytes32 (word_add state (word 8))) s = c /\
           read (memory :> bytes32 (word_add state (word 12))) s = d /\
           (!m. m < 8 * num
                ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s =
                    word_join (msg(2*m+1)) (msg(2*m))))
      (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
           read PC s = word(if i + 1 < num then pc + 0x20 else pc + 0x9fc) /\
           (let (a',b',c',d') = md5_block_spec (a,b,c,d) (\k. msg(16 * i + k)) in
            read X10 s = word_zx a' /\ read X11 s = word_zx b' /\
            read X12 s = word_zx c' /\ read X13 s = word_zx d' /\
            read X0 s = state /\
            read X1 s = word_add data0 (word(64 * (i + 1))) /\
            read X2 s = word(num - (i + 1)) /\
            read (memory :> bytes32 state) s = a' /\
            read (memory :> bytes32 (word_add state (word 4))) s = b' /\
            read (memory :> bytes32 (word_add state (word 8))) s = c' /\
            read (memory :> bytes32 (word_add state (word 12))) s = d') /\
           (!m. m < 8 * num
                ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s =
                    word_join (msg(2*m+1)) (msg(2*m))))
      (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14;
                  X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes32 state;
                  memory :> bytes32 (word_add state (word 4));
                  memory :> bytes32 (word_add state (word 8));
                  memory :> bytes32 (word_add state (word 12))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SOME_FLAGS] THEN
  (* Assemble the register core for block i, threaded with X2 and the           *)
  (* read-only message input R.                                                 *)
  (let core_i = SPECL [`a:int32`;`b:int32`;`c:int32`;`d:int32`;`state:int64`;
                      `word_add data0 (word(64 * i)):int64`;
                      `(\k. (msg:num->int32)(16 * i + k))`;`pc:num`]
                     MD5_BLOCK_CORE_REGS_CORRECT in
   let core_i_u = UNDISCH core_i in
   let cframe = rand(concl core_i_u) in
   let presX2 =
     let s = `s:armstate` and s' = `s':armstate` in
     prove(list_mk_forall([s;s'],
        mk_imp(list_mk_comb(cframe,[s;s']),
               mk_eq(`read X2 s':int64`,`read X2 s:int64`))),
       MD5_FRAME_PRESERVES_TAC) in
   let core_x2 = CONV_RULE(DEPTH_CONV BETA_CONV)
     (SPEC `word(num - i):int64`
      (MATCH_MP ENSURES_THREAD_PRESERVED (CONJ presX2 core_i_u))) in
   let presR = UNDISCH (SPECL [`num:num`;`data0:int64`;`state:int64`;`msg:num->int32`]
                        MD5_CORE_PRESERVES_INPUT) in
   let rfn = `\s:armstate. !m. m < 8 * num
           ==> read (memory :> bytes64 (word_add (data0:int64) (word(8 * m)))) s =
               word_join ((msg:num->int32)(2*m+1)) (msg(2*m))` in
   let pp = rand(rator(rator(concl core_x2))) in
   let qq = rand(rator(concl core_x2)) in
   let cc = rand(concl core_x2) in
   let lem = ISPECL [pp; qq; cc; rfn] ENSURES_THREAD_PRESERVED_PRED in
   let lem_b = CONV_RULE (LAND_CONV (LAND_CONV (ONCE_DEPTH_CONV BETA_CONV))) lem in
   let core_full = CONV_RULE(DEPTH_CONV BETA_CONV) (MP lem_b (CONJ presR core_x2)) in
   ENSURES_SEQUENCE_TAC `pc + 0x9f0`
    `\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
         read X0 s = state /\ read X1 s = word_add data0 (word(64 * i)) /\
         read X2 s = word(num - i) /\
         (let (a',b',c',d') = md5_block_spec (a,b,c,d) (\k. msg(16 * i + k)) in
          read (memory :> bytes32 state) s = a' /\
          read (memory :> bytes32 (word_add state (word 4))) s = b' /\
          read (memory :> bytes32 (word_add state (word 8))) s = c' /\
          read (memory :> bytes32 (word_add state (word 12))) s = d' /\
          read X10 s = word_zx a' /\ read X11 s = word_zx b' /\
          read X12 s = word_zx c' /\ read X13 s = word_zx d') /\
         (!m. m < 8 * num
              ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s =
                  word_join (msg(2*m+1)) (msg(2*m)))` THEN
   CONJ_TAC THENL
    [(* Segment 1: the register core. *)
     MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
     EXISTS_TAC (rand(concl core_full)) THEN
     CONJ_TAC THENL
      [REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
     MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
     EXISTS_TAC (rand(rator(concl core_full))) THEN
     CONJ_TAC THENL
      [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
       CONV_TAC TAUT;
       ALL_TAC] THEN
     MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
     EXISTS_TAC (rand(rator(rator(concl core_full)))) THEN
     CONJ_TAC THENL
      [(* Derive the core's eight per-block doubleword reads from R. *)
       GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
       MP_TAC(ISPECL [`num:num`; `data0:int64`; `msg:num->int32`; `i:num`;
                      `x:armstate`] MD5_BLOCK_INPUT_READS) THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[WORD_ADD_0] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[];
       MP_TAC core_full THEN REWRITE_TAC[]];
     (* Segment 2: the backedge, with the running state, X0 and R threaded     *)
     (* through its (register/flag-only) frame.                                *)
     ABBREV_TAC
       `q = md5_block_spec (a:int32,b:int32,c:int32,d:int32)
                           (\k. (msg:num->int32)(16 * i + k))` THEN
     POP_ASSUM(K ALL_TAC) THEN
     SPEC_TAC(`q:int32#int32#int32#int32`,`q:int32#int32#int32#int32`) THEN
     MATCH_MP_TAC(MESON[PAIR_SURJECTIVE]
       `(!a' b' c' d'. P(a',b',c',d')) ==> (!q. P q)`) THEN
     REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
     EXISTS_TAC `MAYCHANGE [PC; X1; X2] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
                 MAYCHANGE [events]` THEN
     CONJ_TAC THENL
      [REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
     (let hypthm =
        end_itlist CONJ [ASSUME `0 < num`; ASSUME `num < 2 EXP 32`;
                         ASSUME `i < num`] in
      let be =
        MP (SPECL [`data0:int64`;`pc:num`;`num:num`;`i:num`]
                  MD5_BLOCK_BACKEDGE_CORRECT) hypthm in
      let be = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV(REWR_CONV SOME_FLAGS))) be in
      let bf = rand(concl be) in
      let mk_pres ctm vty =
        let rd = inst (type_match `:A` vty [])
                      `read:(armstate,A)component->armstate->A` in
        let s = `s:armstate` and s' = `s':armstate` in
        prove(list_mk_forall([s;s'],
           mk_imp(list_mk_comb(bf,[s;s']),
                  mk_eq(list_mk_comb(rd,[ctm;s']),list_mk_comb(rd,[ctm;s])))),
          MD5_FRAME_PRESERVES_TAC) in
      let thread c vty v th =
        SPEC v (MATCH_MP ENSURES_THREAD_PRESERVED (CONJ (mk_pres c vty) th)) in
      let t = thread `X0` `:int64` `state:int64` be in
      let t = thread `X10` `:int64` `word_zx(a':int32):int64` t in
      let t = thread `X11` `:int64` `word_zx(b':int32):int64` t in
      let t = thread `X12` `:int64` `word_zx(c':int32):int64` t in
      let t = thread `X13` `:int64` `word_zx(d':int32):int64` t in
      let t = thread `memory :> bytes32 state` `:int32` `a':int32` t in
      let t = thread `memory :> bytes32 (word_add state (word 4))` `:int32`
                     `b':int32` t in
      let t = thread `memory :> bytes32 (word_add state (word 8))` `:int32`
                     `c':int32` t in
      let t = thread `memory :> bytes32 (word_add state (word 12))` `:int32`
                     `d':int32` t in
      let presR = SPECL [`num:num`;`data0:int64`;`msg:num->int32`]
                        MD5_BE_PRESERVES_INPUT in
      let tx = CONV_RULE(DEPTH_CONV BETA_CONV) t in
      let pp = rand(rator(rator(concl tx))) in
      let qq = rand(rator(concl tx)) in
      let cc = rand(concl tx) in
      let rfn = `\s:armstate. !m. m < 8 * num
              ==> read (memory :> bytes64 (word_add (data0:int64)
                        (word(8 * m)))) s =
                  word_join ((msg:num->int32)(2*m+1)) (msg(2*m))` in
      let lem = ISPECL [pp; qq; cc; rfn] ENSURES_THREAD_PRESERVED_PRED in
      let lem_b =
        CONV_RULE (LAND_CONV (LAND_CONV (ONCE_DEPTH_CONV BETA_CONV))) lem in
      let be_full =
        CONV_RULE(DEPTH_CONV BETA_CONV) (MP lem_b (CONJ presR tx)) in
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC (rand(rator(concl be_full))) THEN
      CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC TAUT; ALL_TAC] THEN
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl be_full)))) THEN
      CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC TAUT;
        ACCEPT_TAC be_full])]));;

(* ------------------------------------------------------------------------- *)
(* Phase 7b: the multi-block do-while loop.                                   *)
(*                                                                            *)
(* From just after the one-time state load (pc+0x14: ldp w10,w11,[x0];        *)
(* ldp w12,w13,[x0,#8]; nop; loop top pc+0x20) to the loop exit pc+0x9fc.     *)
(* ENSURES_WHILE_UP2_TAC folds the b.ne backedge; the invariant carries the   *)
(* running MD5 state md5_blocks i (A,B,C,D) msg in both W10..W13 and          *)
(* memory[state], the data pointer X1=data0+64i, the block counter            *)
(* X2=num-i, and the read-only input R.  Requires 0<num (do-while, no top     *)
(* guard) and num<2^32 (the 32-bit subs counter).  Per-block results chain    *)
(* via MD5_BLOCKS_SNOC.                                                        *)
(* ------------------------------------------------------------------------- *)

let MD5_BLOCK_LOOP_CORRECT = prove
 (`!A B C D state data0 (msg:num->int32) pc num.
    nonoverlapping (word pc, LENGTH md5_block_mc) (state, 16) /\
    nonoverlapping (state:int64, 16) (data0:int64, 64 * num) /\
    0 < num /\ num < 2 EXP 32
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
           read PC s = word(pc + 0x14) /\
           read X0 s = state /\ read X1 s = data0 /\ read X2 s = word num /\
           read (memory :> bytes32 state) s = A /\
           read (memory :> bytes32 (word_add state (word 4))) s = B /\
           read (memory :> bytes32 (word_add state (word 8))) s = C /\
           read (memory :> bytes32 (word_add state (word 12))) s = D /\
           (!m. m < 8 * num
                ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s =
                    word_join (msg(2*m+1)) (msg(2*m))))
      (\s. read PC s = word(pc + 0x9fc) /\
           (let (a,b,c,d) = md5_blocks num (A,B,C,D) msg in
            read (memory :> bytes32 state) s = a /\
            read (memory :> bytes32 (word_add state (word 4))) s = b /\
            read (memory :> bytes32 (word_add state (word 8))) s = c /\
            read (memory :> bytes32 (word_add state (word 12))) s = d))
      (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14;
                  X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes32 state;
                  memory :> bytes32 (word_add state (word 4));
                  memory :> bytes32 (word_add state (word 8));
                  memory :> bytes32 (word_add state (word 12))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SOME_FLAGS] THEN
  ENSURES_WHILE_UP2_TAC `num:num` `pc + 0x20` `pc + 0x9fc`
   `\i s. read X0 s = state /\
          read X1 s = word_add data0 (word(64 * i)) /\
          read X2 s = word(num - i) /\
          (let (a,b,c,d) = md5_blocks i (A,B,C,D) msg in
           read X10 s = word_zx a /\ read X11 s = word_zx b /\
           read X12 s = word_zx c /\ read X13 s = word_zx d /\
           read (memory :> bytes32 state) s = a /\
           read (memory :> bytes32 (word_add state (word 4))) s = b /\
           read (memory :> bytes32 (word_add state (word 8))) s = c /\
           read (memory :> bytes32 (word_add state (word 12))) s = d) /\
          (!m. m < 8 * num
               ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s =
                   word_join (msg(2*m+1)) (msg(2*m)))` THEN
  REPEAT CONJ_TAC THENL
   [(* ~(num = 0) *)
    ASM_ARITH_TAC;
    (* init: pc+0x14 -> pc+0x20, md5_blocks 0 = identity (state load only) *)
    REWRITE_TAC[md5_blocks; MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[fst MD5_BLOCK_EXEC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MD5_BLOCK_EXEC (6--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* body: MD5_BLOCK_LOOP_BODY for block i, folded via MD5_BLOCKS_SNOC *)
    GEN_TAC THEN STRIP_TAC THEN
    ABBREV_TAC `st = md5_blocks i (A:int32,B:int32,C:int32,D:int32) msg` THEN
    SUBGOAL_THEN `?a b c d. st = (a:int32,b:int32,c:int32,d:int32)`
      STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[EXISTS_PAIR_THM] THEN MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
    SUBGOAL_THEN `md5_blocks (i + 1) (A:int32,B:int32,C:int32,D:int32) msg =
                  md5_block_spec st (\k. msg(16 * i + k))` SUBST1_TAC THENL
     [REWRITE_TAC[MD5_BLOCKS_SNOC] THEN
      SUBGOAL_THEN `(\k. (msg:num->int32)(k + 16 * i)) = (\k. msg(16 * i + k))`
        SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`a:int32`;`b:int32`;`c:int32`;`d:int32`;`state:int64`;
                  `data0:int64`;`msg:num->int32`;`pc:num`;`num:num`;`i:num`]
                 MD5_BLOCK_LOOP_BODY) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC (rand(rator(concl th)))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN
      SPEC_TAC(`md5_block_spec (a:int32,b:int32,c:int32,d:int32)
                  (\k. msg(16 * i + k))`,
               `r:int32#int32#int32#int32`) THEN
      REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN CONV_TAC TAUT;
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(rator(rator(concl th)))) THEN
        CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]) THEN
      GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC TAUT];
    (* exit: weaken loopinv num to the postcondition (0 steps at pc+0x9fc) *)
    REWRITE_TAC[SUB_REFL] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC
     `\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
          read PC s = word(pc + 0x9fc) /\
          read X0 s = state /\ read X1 s = word_add data0 (word(64 * num)) /\
          read X2 s = word 0 /\
          (let (a,b,c,d) = md5_blocks num (A,B,C,D) msg in
           read X10 s = word_zx a /\ read X11 s = word_zx b /\
           read X12 s = word_zx c /\ read X13 s = word_zx d /\
           read (memory :> bytes32 state) s = a /\
           read (memory :> bytes32 (word_add state (word 4))) s = b /\
           read (memory :> bytes32 (word_add state (word 8))) s = c /\
           read (memory :> bytes32 (word_add state (word 12))) s = d) /\
          (!m. m < 8 * num
               ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s =
                   word_join (msg(2*m+1)) (msg(2*m)))` THEN
    CONJ_TAC THENL
     [GEN_TAC THEN
      SPEC_TAC(`md5_blocks num (A:int32,B:int32,C:int32,D:int32) msg`,
               `q:int32#int32#int32#int32`) THEN
      REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN CONV_TAC TAUT;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8: the subroutine wrapper.                                           *)
(*                                                                            *)
(* md5_block is a leaf function (it calls nothing, so X30 is never saved)     *)
(* that nevertheless spills the callee-saved registers X19..X28.  The         *)
(* prologue is five pre-indexed STP pairs                                      *)
(*   stp x19,x20,[sp,#-80]!  (allocates the 80-byte frame and saves x19/x20)  *)
(*   stp x21,x22,[sp,#16] ; stp x23,x24,[sp,#32];                              *)
(*   stp x25,x26,[sp,#48] ; stp x27,x28,[sp,#64]                              *)
(* and the epilogue is the matching five LDP pairs (x19/x20 post-indexed,      *)
(*   ldp x19,x20,[sp],#80, which deallocates the frame) plus the RET.         *)
(* The one-time state load (ldp w10,w11,[x0]; ldp w12,w13,[x0,#8]; nop) and    *)
(* the do-while loop sit in between; MD5_BLOCK_LOOP_CORRECT covers them        *)
(* exactly (pc+0x14 -> pc+0x9fc).  ARM_ADD_RETURN_STACK_TAC stitches the       *)
(* prologue/epilogue around that core: reglist [X19..X28] (10 regs, NO X30 -   *)
(* leaf), stack 80.  The default pre/post step counts (5,5) are correct        *)
(* (16 * (10+1)/2 = 80 = stackoff).                                            *)
(*                                                                            *)
(* This is the top-level correctness theorem for md5_block: from the function *)
(* entry, with the 4-word state at [X0], num 64-byte message blocks at [X1],   *)
(* the block count num in W2, and 0 < num < 2^32, executing the function       *)
(* leaves memory[state] = md5_blocks num (A,B,C,D) msg (the MD5 compression    *)
(* over num blocks), preserving the callee-saved registers and returning to    *)
(* the address that was in X30 on entry.                                       *)
(* ------------------------------------------------------------------------- *)

let MD5_BLOCK_SUBROUTINE_CORRECT = prove
 (`!A B C D state data0 (msg:num->int32) pc num stackpointer returnaddress.
    aligned 16 stackpointer /\
    PAIRWISE nonoverlapping
      [(state:int64,16); (word_sub stackpointer (word 80),80)] /\
    ALLPAIRS nonoverlapping
      [(state:int64,16); (word_sub stackpointer (word 80),80)]
      [(word pc,LENGTH md5_block_mc); (data0:int64,64 * num)] /\
    0 < num /\ num < 2 EXP 32
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) md5_block_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [state; data0; word num] s /\
           read (memory :> bytes32 state) s = A /\
           read (memory :> bytes32 (word_add state (word 4))) s = B /\
           read (memory :> bytes32 (word_add state (word 8))) s = C /\
           read (memory :> bytes32 (word_add state (word 12))) s = D /\
           (!m. m < 8 * num
                ==> read (memory :> bytes64 (word_add data0 (word(8 * m)))) s =
                    word_join (msg(2*m+1)) (msg(2*m))))
      (\s. read PC s = returnaddress /\
           (let (a,b,c,d) = md5_blocks num (A,B,C,D) msg in
            read (memory :> bytes32 state) s = a /\
            read (memory :> bytes32 (word_add state (word 4))) s = b /\
            read (memory :> bytes32 (word_add state (word 8))) s = c /\
            read (memory :> bytes32 (word_add state (word 12))) s = d))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes32 state;
                  memory :> bytes32 (word_add state (word 4));
                  memory :> bytes32 (word_add state (word 8));
                  memory :> bytes32 (word_add state (word 12))] ,,
       MAYCHANGE [memory :> bytes(word_sub stackpointer (word 80),80)])`,
  ARM_ADD_RETURN_STACK_TAC MD5_BLOCK_EXEC MD5_BLOCK_LOOP_CORRECT
    `[X19;X20;X21;X22;X23;X24;X25;X26;X27;X28]` 80);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(*                                                                            *)
(* md5_block has a single do-while loop (the per-block compression) wrapped   *)
(* by a callee-save stack frame (X19..X28 spilled in an 80-byte frame).  Its  *)
(* safety spec is therefore the unbounded-loop variant from the tutorial      *)
(* (arm/tutorial/safety.ml, second half) -- the same shape as the proven      *)
(* loop+stack examples bignum_emontredc_8n and bignum_copy_row_from_table_8n. *)
(* PROVE_SAFETY_SPEC_TAC cannot handle the loop; instead the f_events trace   *)
(* is scaffolded with CONCRETIZE_F_EVENTS_TAC as                              *)
(*   APPEND f_ev_end (APPEND (ENUMERATEL num f_ev_loop) f_ev_begin)           *)
(* and split with a single ENSURES_EVENTS_WHILE_UP2_TAC whose precondition    *)
(* segment absorbs the prologue + state load (pc -> pc+0x20), whose body is   *)
(* the 631-instruction compression core + 3-instruction backedge             *)
(* (pc+0x20 -> pc+0x9fc), and whose exit segment absorbs the epilogue         *)
(* (pc+0x9fc -> returnaddress).  The per-iteration counter/PC/pointer facts   *)
(* reuse the functional lemmas MD5_COUNTER_DEC / MD5_COUNTER_DEC_ZX.          *)
(*                                                                            *)
(* memaccess_inbounds reads:  [state,16; data0,64*num; stack,80]              *)
(*                   writes:  [state,16; stack,80]                            *)
(* i.e. the function reads the 16-byte state and the num 64-byte message      *)
(* blocks at data0 (plus its own 80-byte spill frame) and writes only the     *)
(* state and that frame.  Control flow / addresses depend only on the public  *)
(* values data0, state, num, pc, stackpointer, returnaddress -- never on the  *)
(* state or message contents -- so the function is constant-time.             *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "md5_block" subroutine_signatures)
    MD5_BLOCK_SUBROUTINE_CORRECT
    MD5_BLOCK_EXEC;;

let MD5_BLOCK_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e state data0 pc num stackpointer returnaddress.
           aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [state,16; word_sub stackpointer (word 80),80] /\
           ALLPAIRS nonoverlapping
           [state,16; word_sub stackpointer (word 80),80]
           [word pc,LENGTH md5_block_mc; data0,64 * num] /\
           0 < num /\
           num < 2 EXP 32
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) md5_block_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [state; data0; word num] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events data0 state num pc
                         (word_sub stackpointer (word 80))
                         returnaddress /\
                         memaccess_inbounds e2
                         [state,16; data0,(64 * val (word num:int64)) * 1;
                          word_sub stackpointer (word 80),80]
                         [state,16; word_sub stackpointer (word 80),80]))
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(data0:int64) (state:int64) (num:num) (pc:num) (sp:int64) (retaddr:int64).
      APPEND
        (f_ev_end data0 state num pc sp retaddr)
        (APPEND
          (ENUMERATEL num (\i. f_ev_loop data0 state num pc sp retaddr i))
          (f_ev_begin data0 state num pc sp retaddr))
      :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL;
              fst MD5_BLOCK_EXEC; MULT_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word num:int64) = num` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `num < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `num:num` `pc + 0x20` `pc + 0x9fc`
   `\i s. read X0 s = state /\
          read X1 s = word_add data0 (word(64 * i)) /\
          read X2 s = word(num - i) /\
          read SP s = stackpointer /\
          read X30 s = returnaddress` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* ~(num = 0) *)
    ASM_ARITH_TAC;
    (* precondition segment: prologue + state load, pc -> pc+0x20 *)
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; ENUMERATEL] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
       ~canonicalize_pc_diff:false MD5_BLOCK_EXEC (1--8) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    (* loop body, pc+0x20 -> (pc+0x20 | pc+0x9fc); handled below *)
    ALL_TAC;
    (* exit segment: epilogue, pc+0x9fc -> returnaddress *)
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
       ~canonicalize_pc_diff:false MD5_BLOCK_EXEC (1--6) THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ] THEN
    (* align the backedge EventJump target so the residual trace matches the
       accumulated-events assumption, then discharge memaccess_inbounds *)
    REWRITE_TAC[prove(`(i + 1 < num) <=> ~(num - (i + 1) = 0)`,
                      REWRITE_TAC[SUB_EQ_0] THEN ARITH_TAC)] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC] THEN
  (* loop body: one full block (631 instrs) + the 3-instruction backedge *)
  REPEAT STRIP_TAC THEN REWRITE_TAC[ENUMERATEL_ADD1] THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MD5_BLOCK_EXEC (1--631) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`num:num`;`i:num`] MD5_COUNTER_DEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_THEN `i < num` (fun ith -> LABEL_TAC "ILT" ith) THEN
  CONJ_TAC THENL
   [(* PC: backedge taken iff i+1 < num *)
    ASM_CASES_TAC `i + 1 < num` THENL
     [SUBGOAL_THEN `~(num - (i + 1) = 0)` (fun th -> REWRITE_TAC[th]) THENL
        [USE_THEN "ILT" MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `num - (i + 1) = 0` (fun th -> REWRITE_TAC[th]) THENL
        [USE_THEN "ILT" MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* X1: data pointer advances by 64 *)
    REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; GSYM WORD_ADD] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* X2: block counter decrements *)
    MP_TAC (SPECL [`num:num`;`i:num`] MD5_COUNTER_DEC_ZX) THEN
    ANTS_TAC THENL
     [USE_THEN "ILT" (fun ith -> CONJ_TAC THENL
        [ACCEPT_TAC ith; FIRST_ASSUM ACCEPT_TAC]); ALL_TAC] THEN
    DISCH_THEN (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
