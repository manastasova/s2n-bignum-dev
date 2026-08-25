(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-256-GCM encryption kernel (8x-unrolled), WHOLE-BLOCKS-ONLY variant.    *)
(*                                                                           *)
(* Correctness proof for the aws-lc-derived 8x-unrolled AES-256-GCM encrypt  *)
(* kernel aesv8_gcm_8x_enc_256.  This is the whole-blocks-only variant:    *)
(* the input bit length must be a nonzero multiple of 128 (a runtime guard   *)
(* tst x1,#127; b.ne returns 0 otherwise), and the partial-final-block        *)
(* masking machinery is removed (final block is a plain full block).  The    *)
(* proof re-anchors the aesv8_gcm_8x_enc_256 scripts to the +8-shifted PCs.   *)
(* This file freezes the machine code (via define_assert_from_elf) and builds *)
(* the execution rule.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "common/fips197.ml";;

needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

(* print_literal_from_elf "arm/aes-gcm/aesv8_gcm_8x_enc_256.o";; *)

let aesv8_gcm_8x_enc_256_mc =
  define_assert_from_elf "aesv8_gcm_8x_enc_256_mc"
                         "arm/aes-gcm/aesv8_gcm_8x_enc_256.o"
[
  0xb4009081;   (* 0 cbz x1, 1210 <L256_enc_ret> *)
  0xf240183f;   (* 4 tst x1, #0x7f *)
  0x54009041;   (* 8 b.ne 1210 <L256_enc_ret> // b.any *)
  0xd10143ff;   (* c sub sp, sp, #0x50 *)
  0x6d0027e8;   (* 10 stp d8, d9, [sp] *)
  0xd343fc29;   (* 14 lsr x9, x1, #3 *)
  0xaa0403f0;   (* 18 mov x16, x4 *)
  0xaa0503eb;   (* 1c mov x11, x5 *)
  0x6d012fea;   (* 20 stp d10, d11, [sp, #16] *)
  0x6d0237ec;   (* 24 stp d12, d13, [sp, #32] *)
  0x6d033fee;   (* 28 stp d14, d15, [sp, #48] *)
  0xd2f84005;   (* 2c mov x5, #0xc200000000000000 // #-4467570830351532032 *)
  0xa9047fe5;   (* 30 stp x5, xzr, [sp, #64] *)
  0x910103ea;   (* 34 add x10, sp, #0x40 *)
  0x4c407200;   (* 38 ld1 {v0.16b}, [x16] *)
  0xaa0903e5;   (* 3c mov x5, x9 *)
  0xd2c0002f;   (* 40 mov x15, #0x100000000 // #4294967296 *)
  0x4f00e41f;   (* 44 movi v31.16b, #0x0 *)
  0x4e181dff;   (* 48 mov v31.d[1], x15 *)
  0x4ebf87fc;   (* 4c add v28.4s, v31.4s, v31.4s *)
  0x4ebf878a;   (* 50 add v10.4s, v28.4s, v31.4s *)
  0x4ebc878b;   (* 54 add v11.4s, v28.4s, v28.4s *)
  0x4ebf856c;   (* 58 add v12.4s, v11.4s, v31.4s *)
  0x4ebc856d;   (* 5c add v13.4s, v11.4s, v28.4s *)
  0x4eaa856e;   (* 60 add v14.4s, v11.4s, v10.4s *)
  0xd10004a5;   (* 64 sub x5, x5, #0x1 *)
  0x9279e0a5;   (* 68 and x5, x5, #0xffffffffffffff80 *)
  0x8b0000a5;   (* 6c add x5, x5, x0 *)
  0x6e20081d;   (* 70 rev32 v29.16b, v0.16b *)
  0x4ebf87a8;   (* 74 add v8.4s, v29.4s, v31.4s *)
  0x4ebc87a9;   (* 78 add v9.4s, v29.4s, v28.4s *)
  0x4eaa87af;   (* 7c add v15.4s, v29.4s, v10.4s *)
  0x4eab87b0;   (* 80 add v16.4s, v29.4s, v11.4s *)
  0x4eac87b1;   (* 84 add v17.4s, v29.4s, v12.4s *)
  0x4ead87b2;   (* 88 add v18.4s, v29.4s, v13.4s *)
  0x4eae87be;   (* 8c add v30.4s, v29.4s, v14.4s *)
  0x6e200901;   (* 90 rev32 v1.16b, v8.16b *)
  0x6e200922;   (* 94 rev32 v2.16b, v9.16b *)
  0x6e2009e3;   (* 98 rev32 v3.16b, v15.16b *)
  0x6e200a04;   (* 9c rev32 v4.16b, v16.16b *)
  0x6e200a25;   (* a0 rev32 v5.16b, v17.16b *)
  0x6e200a46;   (* a4 rev32 v6.16b, v18.16b *)
  0x6e200bc7;   (* a8 rev32 v7.16b, v30.16b *)
  0xad406d7a;   (* ac ldp q26, q27, [x11] *)
  0x4c407073;   (* b0 ld1 {v19.16b}, [x3] *)
  0x6e134273;   (* b4 ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200a73;   (* b8 rev64 v19.16b, v19.16b *)
  0x4ebf87de;   (* bc add v30.4s, v30.4s, v31.4s *)
  0xf100813f;   (* c0 cmp x9, #0x20 *)
  0x5400ac20;   (* c4 b.eq 1648 <L256_enc_fast2> // b.none *)
  0xf101013f;   (* c8 cmp x9, #0x40 *)
  0x5400b560;   (* cc b.eq 1778 <L256_enc_fast4> // b.none *)
  0xf100413f;   (* d0 cmp x9, #0x10 *)
  0x5400ce00;   (* d4 b.eq 1a94 <L256_enc_fast1> // b.none *)
  0xf100c13f;   (* d8 cmp x9, #0x30 *)
  0x5400d780;   (* dc b.eq 1bcc <L256_enc_fast3> // b.none *)
  0xf101413f;   (* e0 cmp x9, #0x50 *)
  0x5400eb00;   (* e4 b.eq 1e44 <L256_enc_fast5> // b.none *)
  0xf101813f;   (* e8 cmp x9, #0x60 *)
  0x54010740;   (* ec b.eq 21d4 <L256_enc_fast6> // b.none *)
  0xf101c13f;   (* f0 cmp x9, #0x70 *)
  0x54012840;   (* f4 b.eq 25fc <L256_enc_fast7> // b.none *)
  0x4e284b40;   (* f8 aese v0.16b, v26.16b *)
  0x4e286800;   (* fc aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 100 aese v1.16b, v26.16b *)
  0x4e286821;   (* 104 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 108 aese v2.16b, v26.16b *)
  0x4e286842;   (* 10c aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 110 aese v3.16b, v26.16b *)
  0x4e286863;   (* 114 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 118 aese v4.16b, v26.16b *)
  0x4e286884;   (* 11c aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 120 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 124 aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 128 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 12c aesmc v6.16b, v6.16b *)
  0x4e284b47;   (* 130 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* 134 aesmc v7.16b, v7.16b *)
  0xad41697c;   (* 138 ldp q28, q26, [x11, #32] *)
  0x4e284b60;   (* 13c aese v0.16b, v27.16b *)
  0x4e286800;   (* 140 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 144 aese v1.16b, v27.16b *)
  0x4e286821;   (* 148 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 14c aese v2.16b, v27.16b *)
  0x4e286842;   (* 150 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 154 aese v3.16b, v27.16b *)
  0x4e286863;   (* 158 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 15c aese v4.16b, v27.16b *)
  0x4e286884;   (* 160 aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 164 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 168 aesmc v5.16b, v5.16b *)
  0x4e284b66;   (* 16c aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 170 aesmc v6.16b, v6.16b *)
  0x4e284b67;   (* 174 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* 178 aesmc v7.16b, v7.16b *)
  0x4e284b80;   (* 17c aese v0.16b, v28.16b *)
  0x4e286800;   (* 180 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 184 aese v1.16b, v28.16b *)
  0x4e286821;   (* 188 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 18c aese v2.16b, v28.16b *)
  0x4e286842;   (* 190 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 194 aese v3.16b, v28.16b *)
  0x4e286863;   (* 198 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 19c aese v4.16b, v28.16b *)
  0x4e286884;   (* 1a0 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 1a4 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 1a8 aesmc v5.16b, v5.16b *)
  0x4e284b86;   (* 1ac aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 1b0 aesmc v6.16b, v6.16b *)
  0x4e284b87;   (* 1b4 aese v7.16b, v28.16b *)
  0x4e2868e7;   (* 1b8 aesmc v7.16b, v7.16b *)
  0xad42717b;   (* 1bc ldp q27, q28, [x11, #64] *)
  0x4e284b40;   (* 1c0 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1c4 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1c8 aese v1.16b, v26.16b *)
  0x4e286821;   (* 1cc aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1d0 aese v2.16b, v26.16b *)
  0x4e286842;   (* 1d4 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 1d8 aese v3.16b, v26.16b *)
  0x4e286863;   (* 1dc aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 1e0 aese v4.16b, v26.16b *)
  0x4e286884;   (* 1e4 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 1e8 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 1ec aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 1f0 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 1f4 aesmc v6.16b, v6.16b *)
  0x4e284b47;   (* 1f8 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* 1fc aesmc v7.16b, v7.16b *)
  0x4e284b60;   (* 200 aese v0.16b, v27.16b *)
  0x4e286800;   (* 204 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 208 aese v1.16b, v27.16b *)
  0x4e286821;   (* 20c aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 210 aese v2.16b, v27.16b *)
  0x4e286842;   (* 214 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 218 aese v3.16b, v27.16b *)
  0x4e286863;   (* 21c aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 220 aese v4.16b, v27.16b *)
  0x4e286884;   (* 224 aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 228 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 22c aesmc v5.16b, v5.16b *)
  0x4e284b66;   (* 230 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 234 aesmc v6.16b, v6.16b *)
  0x4e284b67;   (* 238 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* 23c aesmc v7.16b, v7.16b *)
  0xad436d7a;   (* 240 ldp q26, q27, [x11, #96] *)
  0x4e284b80;   (* 244 aese v0.16b, v28.16b *)
  0x4e286800;   (* 248 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 24c aese v1.16b, v28.16b *)
  0x4e286821;   (* 250 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 254 aese v2.16b, v28.16b *)
  0x4e286842;   (* 258 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 25c aese v3.16b, v28.16b *)
  0x4e286863;   (* 260 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 264 aese v4.16b, v28.16b *)
  0x4e286884;   (* 268 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 26c aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 270 aesmc v5.16b, v5.16b *)
  0x4e284b86;   (* 274 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 278 aesmc v6.16b, v6.16b *)
  0x4e284b87;   (* 27c aese v7.16b, v28.16b *)
  0x4e2868e7;   (* 280 aesmc v7.16b, v7.16b *)
  0x4e284b40;   (* 284 aese v0.16b, v26.16b *)
  0x4e286800;   (* 288 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 28c aese v1.16b, v26.16b *)
  0x4e286821;   (* 290 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 294 aese v2.16b, v26.16b *)
  0x4e286842;   (* 298 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 29c aese v3.16b, v26.16b *)
  0x4e286863;   (* 2a0 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 2a4 aese v4.16b, v26.16b *)
  0x4e286884;   (* 2a8 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 2ac aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 2b0 aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 2b4 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 2b8 aesmc v6.16b, v6.16b *)
  0x4e284b47;   (* 2bc aese v7.16b, v26.16b *)
  0x4e2868e7;   (* 2c0 aesmc v7.16b, v7.16b *)
  0xad44697c;   (* 2c4 ldp q28, q26, [x11, #128] *)
  0x4e284b60;   (* 2c8 aese v0.16b, v27.16b *)
  0x4e286800;   (* 2cc aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 2d0 aese v1.16b, v27.16b *)
  0x4e286821;   (* 2d4 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 2d8 aese v2.16b, v27.16b *)
  0x4e286842;   (* 2dc aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 2e0 aese v3.16b, v27.16b *)
  0x4e286863;   (* 2e4 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 2e8 aese v4.16b, v27.16b *)
  0x4e286884;   (* 2ec aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 2f0 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 2f4 aesmc v5.16b, v5.16b *)
  0x4e284b66;   (* 2f8 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 2fc aesmc v6.16b, v6.16b *)
  0x4e284b67;   (* 300 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* 304 aesmc v7.16b, v7.16b *)
  0x4e284b80;   (* 308 aese v0.16b, v28.16b *)
  0x4e286800;   (* 30c aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 310 aese v1.16b, v28.16b *)
  0x4e286821;   (* 314 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 318 aese v2.16b, v28.16b *)
  0x4e286842;   (* 31c aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 320 aese v3.16b, v28.16b *)
  0x4e286863;   (* 324 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 328 aese v4.16b, v28.16b *)
  0x4e286884;   (* 32c aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 330 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 334 aesmc v5.16b, v5.16b *)
  0x4e284b86;   (* 338 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 33c aesmc v6.16b, v6.16b *)
  0x4e284b87;   (* 340 aese v7.16b, v28.16b *)
  0x4e2868e7;   (* 344 aesmc v7.16b, v7.16b *)
  0xad45717b;   (* 348 ldp q27, q28, [x11, #160] *)
  0x4e284b40;   (* 34c aese v0.16b, v26.16b *)
  0x4e286800;   (* 350 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 354 aese v1.16b, v26.16b *)
  0x4e286821;   (* 358 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 35c aese v2.16b, v26.16b *)
  0x4e286842;   (* 360 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 364 aese v3.16b, v26.16b *)
  0x4e286863;   (* 368 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 36c aese v4.16b, v26.16b *)
  0x4e286884;   (* 370 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 374 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 378 aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 37c aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 380 aesmc v6.16b, v6.16b *)
  0x4e284b47;   (* 384 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* 388 aesmc v7.16b, v7.16b *)
  0x4e284b60;   (* 38c aese v0.16b, v27.16b *)
  0x4e286800;   (* 390 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 394 aese v1.16b, v27.16b *)
  0x4e286821;   (* 398 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 39c aese v2.16b, v27.16b *)
  0x4e286842;   (* 3a0 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 3a4 aese v3.16b, v27.16b *)
  0x4e286863;   (* 3a8 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 3ac aese v4.16b, v27.16b *)
  0x4e286884;   (* 3b0 aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 3b4 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 3b8 aesmc v5.16b, v5.16b *)
  0x4e284b66;   (* 3bc aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 3c0 aesmc v6.16b, v6.16b *)
  0x4e284b67;   (* 3c4 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* 3c8 aesmc v7.16b, v7.16b *)
  0xad466d7a;   (* 3cc ldp q26, q27, [x11, #192] *)
  0x4e284b80;   (* 3d0 aese v0.16b, v28.16b *)
  0x4e286800;   (* 3d4 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 3d8 aese v1.16b, v28.16b *)
  0x4e286821;   (* 3dc aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 3e0 aese v2.16b, v28.16b *)
  0x4e286842;   (* 3e4 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 3e8 aese v3.16b, v28.16b *)
  0x4e286863;   (* 3ec aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 3f0 aese v4.16b, v28.16b *)
  0x4e286884;   (* 3f4 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 3f8 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 3fc aesmc v5.16b, v5.16b *)
  0x4e284b86;   (* 400 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 404 aesmc v6.16b, v6.16b *)
  0x4e284b87;   (* 408 aese v7.16b, v28.16b *)
  0x4e2868e7;   (* 40c aesmc v7.16b, v7.16b *)
  0x3dc0397c;   (* 410 ldr q28, [x11, #224] *)
  0x4e284b40;   (* 414 aese v0.16b, v26.16b *)
  0x4e286800;   (* 418 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 41c aese v1.16b, v26.16b *)
  0x4e286821;   (* 420 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 424 aese v2.16b, v26.16b *)
  0x4e286842;   (* 428 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 42c aese v3.16b, v26.16b *)
  0x4e286863;   (* 430 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 434 aese v4.16b, v26.16b *)
  0x4e286884;   (* 438 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 43c aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 440 aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 444 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 448 aesmc v6.16b, v6.16b *)
  0x4e284b47;   (* 44c aese v7.16b, v26.16b *)
  0x4e2868e7;   (* 450 aesmc v7.16b, v7.16b *)
  0x4e284b60;   (* 454 aese v0.16b, v27.16b *)
  0x4e284b61;   (* 458 aese v1.16b, v27.16b *)
  0x4e284b62;   (* 45c aese v2.16b, v27.16b *)
  0x4e284b63;   (* 460 aese v3.16b, v27.16b *)
  0x4e284b64;   (* 464 aese v4.16b, v27.16b *)
  0x4e284b65;   (* 468 aese v5.16b, v27.16b *)
  0x4e284b66;   (* 46c aese v6.16b, v27.16b *)
  0x4e284b67;   (* 470 aese v7.16b, v27.16b *)
  0x8b410c04;   (* 474 add x4, x0, x1, lsr #3 *)
  0xeb05001f;   (* 478 cmp x0, x5 *)
  0x540054aa;   (* 47c b.ge f10 <L256_enc_tail> // b.tcont *)
  0xacc12408;   (* 480 ldp q8, q9, [x0], #32 *)
  0xacc12c0a;   (* 484 ldp q10, q11, [x0], #32 *)
  0xce007108;   (* 488 eor3 v8.16b, v8.16b, v0.16b, v28.16b *)
  0x6e200bc0;   (* 48c rev32 v0.16b, v30.16b *)
  0x4ebf87de;   (* 490 add v30.4s, v30.4s, v31.4s *)
  0xce017129;   (* 494 eor3 v9.16b, v9.16b, v1.16b, v28.16b *)
  0xce03716b;   (* 498 eor3 v11.16b, v11.16b, v3.16b, v28.16b *)
  0x6e200bc1;   (* 49c rev32 v1.16b, v30.16b *)
  0x4ebf87de;   (* 4a0 add v30.4s, v30.4s, v31.4s *)
  0xacc1340c;   (* 4a4 ldp q12, q13, [x0], #32 *)
  0xacc13c0e;   (* 4a8 ldp q14, q15, [x0], #32 *)
  0xce02714a;   (* 4ac eor3 v10.16b, v10.16b, v2.16b, v28.16b *)
  0xeb05001f;   (* 4b0 cmp x0, x5 *)
  0x6e200bc2;   (* 4b4 rev32 v2.16b, v30.16b *)
  0x4ebf87de;   (* 4b8 add v30.4s, v30.4s, v31.4s *)
  0xac812448;   (* 4bc stp q8, q9, [x2], #32 *)
  0xac812c4a;   (* 4c0 stp q10, q11, [x2], #32 *)
  0x6e200bc3;   (* 4c4 rev32 v3.16b, v30.16b *)
  0x4ebf87de;   (* 4c8 add v30.4s, v30.4s, v31.4s *)
  0xce04718c;   (* 4cc eor3 v12.16b, v12.16b, v4.16b, v28.16b *)
  0xce0771ef;   (* 4d0 eor3 v15.16b, v15.16b, v7.16b, v28.16b *)
  0xce0671ce;   (* 4d4 eor3 v14.16b, v14.16b, v6.16b, v28.16b *)
  0xce0571ad;   (* 4d8 eor3 v13.16b, v13.16b, v5.16b, v28.16b *)
  0xac81344c;   (* 4dc stp q12, q13, [x2], #32 *)
  0x6e200bc4;   (* 4e0 rev32 v4.16b, v30.16b *)
  0xac813c4e;   (* 4e4 stp q14, q15, [x2], #32 *)
  0x4ebf87de;   (* 4e8 add v30.4s, v30.4s, v31.4s *)
  0x54002aaa;   (* 4ec b.ge a40 <L256_enc_prepretail> // b.tcont *)
  0xad406d7a;   (* 4f0 ldp q26, q27, [x11] *)
  0x6e200bc5;   (* 4f4 rev32 v5.16b, v30.16b *)
  0x4ebf87de;   (* 4f8 add v30.4s, v30.4s, v31.4s *)
  0x3dc01cd5;   (* 4fc ldr q21, [x6, #112] *)
  0x3dc028d8;   (* 500 ldr q24, [x6, #160] *)
  0x4e20096b;   (* 504 rev64 v11.16b, v11.16b *)
  0x3dc018d4;   (* 508 ldr q20, [x6, #96] *)
  0x3dc020d6;   (* 50c ldr q22, [x6, #128] *)
  0x4e200929;   (* 510 rev64 v9.16b, v9.16b *)
  0x6e200bc6;   (* 514 rev32 v6.16b, v30.16b *)
  0x4ebf87de;   (* 518 add v30.4s, v30.4s, v31.4s *)
  0x4e200908;   (* 51c rev64 v8.16b, v8.16b *)
  0x4e20098c;   (* 520 rev64 v12.16b, v12.16b *)
  0x6e134273;   (* 524 ext v19.16b, v19.16b, v19.16b, #8 *)
  0x3dc024d7;   (* 528 ldr q23, [x6, #144] *)
  0x3dc02cd9;   (* 52c ldr q25, [x6, #176] *)
  0x4e284b43;   (* 530 aese v3.16b, v26.16b *)
  0x4e286863;   (* 534 aesmc v3.16b, v3.16b *)
  0x4e284b45;   (* 538 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 53c aesmc v5.16b, v5.16b *)
  0x6e200bc7;   (* 540 rev32 v7.16b, v30.16b *)
  0x4e284b40;   (* 544 aese v0.16b, v26.16b *)
  0x4e286800;   (* 548 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 54c aese v1.16b, v26.16b *)
  0x4e286821;   (* 550 aesmc v1.16b, v1.16b *)
  0x4e284b46;   (* 554 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 558 aesmc v6.16b, v6.16b *)
  0x4e284b47;   (* 55c aese v7.16b, v26.16b *)
  0x4e2868e7;   (* 560 aesmc v7.16b, v7.16b *)
  0x4e284b42;   (* 564 aese v2.16b, v26.16b *)
  0x4e286842;   (* 568 aesmc v2.16b, v2.16b *)
  0x4e284b44;   (* 56c aese v4.16b, v26.16b *)
  0x4e286884;   (* 570 aesmc v4.16b, v4.16b *)
  0xad41697c;   (* 574 ldp q28, q26, [x11, #32] *)
  0x6e331d08;   (* 578 eor v8.16b, v8.16b, v19.16b *)
  0x4e284b66;   (* 57c aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 580 aesmc v6.16b, v6.16b *)
  0x4e284b62;   (* 584 aese v2.16b, v27.16b *)
  0x4e286842;   (* 588 aesmc v2.16b, v2.16b *)
  0x4e284b61;   (* 58c aese v1.16b, v27.16b *)
  0x4e286821;   (* 590 aesmc v1.16b, v1.16b *)
  0x4e284b60;   (* 594 aese v0.16b, v27.16b *)
  0x4e286800;   (* 598 aesmc v0.16b, v0.16b *)
  0x4e284b64;   (* 59c aese v4.16b, v27.16b *)
  0x4e286884;   (* 5a0 aesmc v4.16b, v4.16b *)
  0x4e284b63;   (* 5a4 aese v3.16b, v27.16b *)
  0x4e286863;   (* 5a8 aesmc v3.16b, v3.16b *)
  0x4e284b65;   (* 5ac aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 5b0 aesmc v5.16b, v5.16b *)
  0x4ef9e111;   (* 5b4 pmull2 v17.1q, v8.2d, v25.2d *)
  0x0ef9e113;   (* 5b8 pmull v19.1q, v8.1d, v25.1d *)
  0x4ef7e130;   (* 5bc pmull2 v16.1q, v9.2d, v23.2d *)
  0x4ec82932;   (* 5c0 trn1 v18.2d, v9.2d, v8.2d *)
  0x4ec86928;   (* 5c4 trn2 v8.2d, v9.2d, v8.2d *)
  0x4e284b67;   (* 5c8 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* 5cc aesmc v7.16b, v7.16b *)
  0x4e284b81;   (* 5d0 aese v1.16b, v28.16b *)
  0x4e286821;   (* 5d4 aesmc v1.16b, v1.16b *)
  0x4e284b85;   (* 5d8 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 5dc aesmc v5.16b, v5.16b *)
  0x4e284b86;   (* 5e0 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 5e4 aesmc v6.16b, v6.16b *)
  0x4e284b82;   (* 5e8 aese v2.16b, v28.16b *)
  0x4e286842;   (* 5ec aesmc v2.16b, v2.16b *)
  0x0ef7e137;   (* 5f0 pmull v23.1q, v9.1d, v23.1d *)
  0x4e284b84;   (* 5f4 aese v4.16b, v28.16b *)
  0x4e286884;   (* 5f8 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 5fc aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 600 aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 604 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 608 aesmc v6.16b, v6.16b *)
  0x4e284b80;   (* 60c aese v0.16b, v28.16b *)
  0x4e286800;   (* 610 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 614 aese v1.16b, v26.16b *)
  0x4e286821;   (* 618 aesmc v1.16b, v1.16b *)
  0x4e284b87;   (* 61c aese v7.16b, v28.16b *)
  0x4e2868e7;   (* 620 aesmc v7.16b, v7.16b *)
  0x4e284b83;   (* 624 aese v3.16b, v28.16b *)
  0x4e286863;   (* 628 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 62c aese v4.16b, v26.16b *)
  0x4e286884;   (* 630 aesmc v4.16b, v4.16b *)
  0x4e2009ce;   (* 634 rev64 v14.16b, v14.16b *)
  0x4ef4e169;   (* 638 pmull2 v9.1q, v11.2d, v20.2d *)
  0x4e284b43;   (* 63c aese v3.16b, v26.16b *)
  0x4e286863;   (* 640 aesmc v3.16b, v3.16b *)
  0xad42717b;   (* 644 ldp q27, q28, [x11, #64] *)
  0x4e20094a;   (* 648 rev64 v10.16b, v10.16b *)
  0x4e284b42;   (* 64c aese v2.16b, v26.16b *)
  0x4e286842;   (* 650 aesmc v2.16b, v2.16b *)
  0x4e284b47;   (* 654 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* 658 aesmc v7.16b, v7.16b *)
  0x4e284b40;   (* 65c aese v0.16b, v26.16b *)
  0x4e286800;   (* 660 aesmc v0.16b, v0.16b *)
  0x6e301e31;   (* 664 eor v17.16b, v17.16b, v16.16b *)
  0x4ef6e15d;   (* 668 pmull2 v29.1q, v10.2d, v22.2d *)
  0x4e2009ad;   (* 66c rev64 v13.16b, v13.16b *)
  0x0ef4e174;   (* 670 pmull v20.1q, v11.1d, v20.1d *)
  0x6e371e73;   (* 674 eor v19.16b, v19.16b, v23.16b *)
  0x3dc00cd7;   (* 678 ldr q23, [x6, #48] *)
  0x3dc014d9;   (* 67c ldr q25, [x6, #80] *)
  0x4ecc29b0;   (* 680 trn1 v16.2d, v13.2d, v12.2d *)
  0xce1d2631;   (* 684 eor3 v17.16b, v17.16b, v29.16b, v9.16b *)
  0x0ef6e156;   (* 688 pmull v22.1q, v10.1d, v22.1d *)
  0x4e284b64;   (* 68c aese v4.16b, v27.16b *)
  0x4e286884;   (* 690 aesmc v4.16b, v4.16b *)
  0x4e284b61;   (* 694 aese v1.16b, v27.16b *)
  0x4e286821;   (* 698 aesmc v1.16b, v1.16b *)
  0x4e284b65;   (* 69c aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 6a0 aesmc v5.16b, v5.16b *)
  0x4e284b67;   (* 6a4 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* 6a8 aesmc v7.16b, v7.16b *)
  0x4e284b63;   (* 6ac aese v3.16b, v27.16b *)
  0x4e286863;   (* 6b0 aesmc v3.16b, v3.16b *)
  0x4e284b62;   (* 6b4 aese v2.16b, v27.16b *)
  0x4e286842;   (* 6b8 aesmc v2.16b, v2.16b *)
  0x4eca297d;   (* 6bc trn1 v29.2d, v11.2d, v10.2d *)
  0x4e284b66;   (* 6c0 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 6c4 aesmc v6.16b, v6.16b *)
  0x4e284b60;   (* 6c8 aese v0.16b, v27.16b *)
  0x4e286800;   (* 6cc aesmc v0.16b, v0.16b *)
  0x4eca696a;   (* 6d0 trn2 v10.2d, v11.2d, v10.2d *)
  0x6e321d08;   (* 6d4 eor v8.16b, v8.16b, v18.16b *)
  0xad436d7a;   (* 6d8 ldp q26, q27, [x11, #96] *)
  0x4e284b85;   (* 6dc aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 6e0 aesmc v5.16b, v5.16b *)
  0x4e284b87;   (* 6e4 aese v7.16b, v28.16b *)
  0x4e2868e7;   (* 6e8 aesmc v7.16b, v7.16b *)
  0x4e284b84;   (* 6ec aese v4.16b, v28.16b *)
  0x4e286884;   (* 6f0 aesmc v4.16b, v4.16b *)
  0x6e3d1d4a;   (* 6f4 eor v10.16b, v10.16b, v29.16b *)
  0x4e284b82;   (* 6f8 aese v2.16b, v28.16b *)
  0x4e286842;   (* 6fc aesmc v2.16b, v2.16b *)
  0x4e2009ef;   (* 700 rev64 v15.16b, v15.16b *)
  0x4e284b83;   (* 704 aese v3.16b, v28.16b *)
  0x4e286863;   (* 708 aesmc v3.16b, v3.16b *)
  0x4e284b86;   (* 70c aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 710 aesmc v6.16b, v6.16b *)
  0x4e284b81;   (* 714 aese v1.16b, v28.16b *)
  0x4e286821;   (* 718 aesmc v1.16b, v1.16b *)
  0x4ef5e15d;   (* 71c pmull2 v29.1q, v10.2d, v21.2d *)
  0x4ef8e112;   (* 720 pmull2 v18.1q, v8.2d, v24.2d *)
  0x4e284b80;   (* 724 aese v0.16b, v28.16b *)
  0x4e286800;   (* 728 aesmc v0.16b, v0.16b *)
  0x0ef8e118;   (* 72c pmull v24.1q, v8.1d, v24.1d *)
  0x4e284b44;   (* 730 aese v4.16b, v26.16b *)
  0x4e286884;   (* 734 aesmc v4.16b, v4.16b *)
  0x4e284b42;   (* 738 aese v2.16b, v26.16b *)
  0x4e286842;   (* 73c aesmc v2.16b, v2.16b *)
  0x4e284b46;   (* 740 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 744 aesmc v6.16b, v6.16b *)
  0x4e284b41;   (* 748 aese v1.16b, v26.16b *)
  0x4e286821;   (* 74c aesmc v1.16b, v1.16b *)
  0x4e284b47;   (* 750 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* 754 aesmc v7.16b, v7.16b *)
  0x6e381e52;   (* 758 eor v18.16b, v18.16b, v24.16b *)
  0x0ef5e155;   (* 75c pmull v21.1q, v10.1d, v21.1d *)
  0x4e284b45;   (* 760 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 764 aesmc v5.16b, v5.16b *)
  0xce165273;   (* 768 eor3 v19.16b, v19.16b, v22.16b, v20.16b *)
  0x4e284b43;   (* 76c aese v3.16b, v26.16b *)
  0x4e286863;   (* 770 aesmc v3.16b, v3.16b *)
  0x4e284b40;   (* 774 aese v0.16b, v26.16b *)
  0x4e286800;   (* 778 aesmc v0.16b, v0.16b *)
  0xad44697c;   (* 77c ldp q28, q26, [x11, #128] *)
  0x4ef9e188;   (* 780 pmull2 v8.1q, v12.2d, v25.2d *)
  0x4e284b65;   (* 784 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 788 aesmc v5.16b, v5.16b *)
  0x3dc000d4;   (* 78c ldr q20, [x6] *)
  0x3dc008d6;   (* 790 ldr q22, [x6, #32] *)
  0x4e284b62;   (* 794 aese v2.16b, v27.16b *)
  0x4e286842;   (* 798 aesmc v2.16b, v2.16b *)
  0xce157652;   (* 79c eor3 v18.16b, v18.16b, v21.16b, v29.16b *)
  0x3dc004d5;   (* 7a0 ldr q21, [x6, #16] *)
  0x3dc010d8;   (* 7a4 ldr q24, [x6, #64] *)
  0x4e284b66;   (* 7a8 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 7ac aesmc v6.16b, v6.16b *)
  0x4e284b63;   (* 7b0 aese v3.16b, v27.16b *)
  0x4e286863;   (* 7b4 aesmc v3.16b, v3.16b *)
  0x4e284b60;   (* 7b8 aese v0.16b, v27.16b *)
  0x4e286800;   (* 7bc aesmc v0.16b, v0.16b *)
  0x4e284b67;   (* 7c0 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* 7c4 aesmc v7.16b, v7.16b *)
  0x0ef9e199;   (* 7c8 pmull v25.1q, v12.1d, v25.1d *)
  0x4ecc69ac;   (* 7cc trn2 v12.2d, v13.2d, v12.2d *)
  0x4e284b64;   (* 7d0 aese v4.16b, v27.16b *)
  0x4e286884;   (* 7d4 aesmc v4.16b, v4.16b *)
  0x4e284b61;   (* 7d8 aese v1.16b, v27.16b *)
  0x4e286821;   (* 7dc aesmc v1.16b, v1.16b *)
  0x4ef7e1aa;   (* 7e0 pmull2 v10.1q, v13.2d, v23.2d *)
  0x4e284b87;   (* 7e4 aese v7.16b, v28.16b *)
  0x4e2868e7;   (* 7e8 aesmc v7.16b, v7.16b *)
  0x4e284b80;   (* 7ec aese v0.16b, v28.16b *)
  0x4e286800;   (* 7f0 aesmc v0.16b, v0.16b *)
  0x0ef7e1b7;   (* 7f4 pmull v23.1q, v13.1d, v23.1d *)
  0x4ece29ed;   (* 7f8 trn1 v13.2d, v15.2d, v14.2d *)
  0x6e301d8c;   (* 7fc eor v12.16b, v12.16b, v16.16b *)
  0x4e284b83;   (* 800 aese v3.16b, v28.16b *)
  0x4e286863;   (* 804 aesmc v3.16b, v3.16b *)
  0x4e284b40;   (* 808 aese v0.16b, v26.16b *)
  0x4e286800;   (* 80c aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 810 aese v1.16b, v28.16b *)
  0x4e286821;   (* 814 aesmc v1.16b, v1.16b *)
  0x4ef8e190;   (* 818 pmull2 v16.1q, v12.2d, v24.2d *)
  0x0ef8e198;   (* 81c pmull v24.1q, v12.1d, v24.1d *)
  0x4e284b82;   (* 820 aese v2.16b, v28.16b *)
  0x4e286842;   (* 824 aesmc v2.16b, v2.16b *)
  0x4e284b85;   (* 828 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 82c aesmc v5.16b, v5.16b *)
  0x4ef6e1cb;   (* 830 pmull2 v11.1q, v14.2d, v22.2d *)
  0x0ef6e1d6;   (* 834 pmull v22.1q, v14.1d, v22.1d *)
  0x4e284b86;   (* 838 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 83c aesmc v6.16b, v6.16b *)
  0x4ece69ee;   (* 840 trn2 v14.2d, v15.2d, v14.2d *)
  0x4e284b84;   (* 844 aese v4.16b, v28.16b *)
  0x4e286884;   (* 848 aesmc v4.16b, v4.16b *)
  0xce184252;   (* 84c eor3 v18.16b, v18.16b, v24.16b, v16.16b *)
  0x4e284b47;   (* 850 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* 854 aesmc v7.16b, v7.16b *)
  0x4e284b45;   (* 858 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 85c aesmc v5.16b, v5.16b *)
  0x6e2d1dce;   (* 860 eor v14.16b, v14.16b, v13.16b *)
  0x4e284b46;   (* 864 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 868 aesmc v6.16b, v6.16b *)
  0x4e284b44;   (* 86c aese v4.16b, v26.16b *)
  0x4e286884;   (* 870 aesmc v4.16b, v4.16b *)
  0xad45717b;   (* 874 ldp q27, q28, [x11, #160] *)
  0x4e284b42;   (* 878 aese v2.16b, v26.16b *)
  0x4e286842;   (* 87c aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 880 aese v3.16b, v26.16b *)
  0x4e286863;   (* 884 aesmc v3.16b, v3.16b *)
  0x4ef4e1ec;   (* 888 pmull2 v12.1q, v15.2d, v20.2d *)
  0xce195e73;   (* 88c eor3 v19.16b, v19.16b, v25.16b, v23.16b *)
  0x0ef4e1f4;   (* 890 pmull v20.1q, v15.1d, v20.1d *)
  0xfd400150;   (* 894 ldr d16, [x10] *)
  0x4ef5e1cd;   (* 898 pmull2 v13.1q, v14.2d, v21.2d *)
  0x0ef5e1d5;   (* 89c pmull v21.1q, v14.1d, v21.1d *)
  0x4e284b41;   (* 8a0 aese v1.16b, v26.16b *)
  0x4e286821;   (* 8a4 aesmc v1.16b, v1.16b *)
  0xce153652;   (* 8a8 eor3 v18.16b, v18.16b, v21.16b, v13.16b *)
  0xce165273;   (* 8ac eor3 v19.16b, v19.16b, v22.16b, v20.16b *)
  0xce082a31;   (* 8b0 eor3 v17.16b, v17.16b, v8.16b, v10.16b *)
  0x4e284b64;   (* 8b4 aese v4.16b, v27.16b *)
  0x4e286884;   (* 8b8 aesmc v4.16b, v4.16b *)
  0x4e284b63;   (* 8bc aese v3.16b, v27.16b *)
  0x4e286863;   (* 8c0 aesmc v3.16b, v3.16b *)
  0x4e284b65;   (* 8c4 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 8c8 aesmc v5.16b, v5.16b *)
  0x4e284b60;   (* 8cc aese v0.16b, v27.16b *)
  0x4e286800;   (* 8d0 aesmc v0.16b, v0.16b *)
  0x4e284b62;   (* 8d4 aese v2.16b, v27.16b *)
  0x4e286842;   (* 8d8 aesmc v2.16b, v2.16b *)
  0x4ebf87de;   (* 8dc add v30.4s, v30.4s, v31.4s *)
  0x4e284b61;   (* 8e0 aese v1.16b, v27.16b *)
  0x4e286821;   (* 8e4 aesmc v1.16b, v1.16b *)
  0x4e284b67;   (* 8e8 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* 8ec aesmc v7.16b, v7.16b *)
  0x4e284b66;   (* 8f0 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 8f4 aesmc v6.16b, v6.16b *)
  0xce0b3231;   (* 8f8 eor3 v17.16b, v17.16b, v11.16b, v12.16b *)
  0xad466d7a;   (* 8fc ldp q26, q27, [x11, #192] *)
  0x6e200bd4;   (* 900 rev32 v20.16b, v30.16b *)
  0x6e114235;   (* 904 ext v21.16b, v17.16b, v17.16b, #8 *)
  0xacc12408;   (* 908 ldp q8, q9, [x0], #32 *)
  0x4e284b82;   (* 90c aese v2.16b, v28.16b *)
  0x4e286842;   (* 910 aesmc v2.16b, v2.16b *)
  0x4e284b86;   (* 914 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 918 aesmc v6.16b, v6.16b *)
  0x4ebf87de;   (* 91c add v30.4s, v30.4s, v31.4s *)
  0x4e284b83;   (* 920 aese v3.16b, v28.16b *)
  0x4e286863;   (* 924 aesmc v3.16b, v3.16b *)
  0x4e284b80;   (* 928 aese v0.16b, v28.16b *)
  0x4e286800;   (* 92c aesmc v0.16b, v0.16b *)
  0x4e284b87;   (* 930 aese v7.16b, v28.16b *)
  0x4e2868e7;   (* 934 aesmc v7.16b, v7.16b *)
  0x0ef0e23d;   (* 938 pmull v29.1q, v17.1d, v16.1d *)
  0x4e284b81;   (* 93c aese v1.16b, v28.16b *)
  0x4e286821;   (* 940 aesmc v1.16b, v1.16b *)
  0x4e284b47;   (* 944 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* 948 aesmc v7.16b, v7.16b *)
  0x4e284b85;   (* 94c aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 950 aesmc v5.16b, v5.16b *)
  0x4e284b43;   (* 954 aese v3.16b, v26.16b *)
  0x4e286863;   (* 958 aesmc v3.16b, v3.16b *)
  0x4e284b46;   (* 95c aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 960 aesmc v6.16b, v6.16b *)
  0x6e200bd6;   (* 964 rev32 v22.16b, v30.16b *)
  0x4ebf87de;   (* 968 add v30.4s, v30.4s, v31.4s *)
  0x4e284b84;   (* 96c aese v4.16b, v28.16b *)
  0x4e286884;   (* 970 aesmc v4.16b, v4.16b *)
  0xce114e52;   (* 974 eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x4e284b45;   (* 978 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 97c aesmc v5.16b, v5.16b *)
  0x3dc0397c;   (* 980 ldr q28, [x11, #224] *)
  0x4e284b67;   (* 984 aese v7.16b, v27.16b *)
  0xacc12c0a;   (* 988 ldp q10, q11, [x0], #32 *)
  0x4e284b42;   (* 98c aese v2.16b, v26.16b *)
  0x4e286842;   (* 990 aesmc v2.16b, v2.16b *)
  0x4e284b44;   (* 994 aese v4.16b, v26.16b *)
  0x4e286884;   (* 998 aesmc v4.16b, v4.16b *)
  0xce1d5652;   (* 99c eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x4e284b41;   (* 9a0 aese v1.16b, v26.16b *)
  0x4e286821;   (* 9a4 aesmc v1.16b, v1.16b *)
  0xacc1340c;   (* 9a8 ldp q12, q13, [x0], #32 *)
  0xacc13c0e;   (* 9ac ldp q14, q15, [x0], #32 *)
  0x4e284b62;   (* 9b0 aese v2.16b, v27.16b *)
  0x4e284b64;   (* 9b4 aese v4.16b, v27.16b *)
  0x6e200bd7;   (* 9b8 rev32 v23.16b, v30.16b *)
  0x4ebf87de;   (* 9bc add v30.4s, v30.4s, v31.4s *)
  0x4e284b65;   (* 9c0 aese v5.16b, v27.16b *)
  0x4e284b40;   (* 9c4 aese v0.16b, v26.16b *)
  0x4e286800;   (* 9c8 aesmc v0.16b, v0.16b *)
  0x4e284b63;   (* 9cc aese v3.16b, v27.16b *)
  0xeb05001f;   (* 9d0 cmp x0, x5 *)
  0xce02714a;   (* 9d4 eor3 v10.16b, v10.16b, v2.16b, v28.16b *)
  0x6e200bd9;   (* 9d8 rev32 v25.16b, v30.16b *)
  0x4ebf87de;   (* 9dc add v30.4s, v30.4s, v31.4s *)
  0x4e284b60;   (* 9e0 aese v0.16b, v27.16b *)
  0x4e284b66;   (* 9e4 aese v6.16b, v27.16b *)
  0xce0571ad;   (* 9e8 eor3 v13.16b, v13.16b, v5.16b, v28.16b *)
  0x6e124255;   (* 9ec ext v21.16b, v18.16b, v18.16b, #8 *)
  0x0ef0e251;   (* 9f0 pmull v17.1q, v18.1d, v16.1d *)
  0x4e284b61;   (* 9f4 aese v1.16b, v27.16b *)
  0xce04718c;   (* 9f8 eor3 v12.16b, v12.16b, v4.16b, v28.16b *)
  0x6e200bc4;   (* 9fc rev32 v4.16b, v30.16b *)
  0xce03716b;   (* a00 eor3 v11.16b, v11.16b, v3.16b, v28.16b *)
  0x4eb91f23;   (* a04 mov v3.16b, v25.16b *)
  0xce017129;   (* a08 eor3 v9.16b, v9.16b, v1.16b, v28.16b *)
  0xce007108;   (* a0c eor3 v8.16b, v8.16b, v0.16b, v28.16b *)
  0x4ebf87de;   (* a10 add v30.4s, v30.4s, v31.4s *)
  0xac812448;   (* a14 stp q8, q9, [x2], #32 *)
  0x4eb71ee2;   (* a18 mov v2.16b, v23.16b *)
  0xce0771ef;   (* a1c eor3 v15.16b, v15.16b, v7.16b, v28.16b *)
  0xce154673;   (* a20 eor3 v19.16b, v19.16b, v21.16b, v17.16b *)
  0xac812c4a;   (* a24 stp q10, q11, [x2], #32 *)
  0xce0671ce;   (* a28 eor3 v14.16b, v14.16b, v6.16b, v28.16b *)
  0x4eb61ec1;   (* a2c mov v1.16b, v22.16b *)
  0xac81344c;   (* a30 stp q12, q13, [x2], #32 *)
  0xac813c4e;   (* a34 stp q14, q15, [x2], #32 *)
  0x4eb41e80;   (* a38 mov v0.16b, v20.16b *)
  0x54ffd5ab;   (* a3c b.lt 4f0 <L256_enc_main_loop> // b.tstop *)
  0x6e200bc5;   (* a40 rev32 v5.16b, v30.16b *)
  0xad406d7a;   (* a44 ldp q26, q27, [x11] *)
  0x4ebf87de;   (* a48 add v30.4s, v30.4s, v31.4s *)
  0x4e20094a;   (* a4c rev64 v10.16b, v10.16b *)
  0x6e200bc6;   (* a50 rev32 v6.16b, v30.16b *)
  0x4ebf87de;   (* a54 add v30.4s, v30.4s, v31.4s *)
  0x4e2009ad;   (* a58 rev64 v13.16b, v13.16b *)
  0x3dc01cd5;   (* a5c ldr q21, [x6, #112] *)
  0x3dc028d8;   (* a60 ldr q24, [x6, #160] *)
  0x6e200bc7;   (* a64 rev32 v7.16b, v30.16b *)
  0x4e284b46;   (* a68 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* a6c aesmc v6.16b, v6.16b *)
  0x4e284b44;   (* a70 aese v4.16b, v26.16b *)
  0x4e286884;   (* a74 aesmc v4.16b, v4.16b *)
  0x4e284b41;   (* a78 aese v1.16b, v26.16b *)
  0x4e286821;   (* a7c aesmc v1.16b, v1.16b *)
  0x4e284b45;   (* a80 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* a84 aesmc v5.16b, v5.16b *)
  0x4e284b40;   (* a88 aese v0.16b, v26.16b *)
  0x4e286800;   (* a8c aesmc v0.16b, v0.16b *)
  0x4e284b42;   (* a90 aese v2.16b, v26.16b *)
  0x4e286842;   (* a94 aesmc v2.16b, v2.16b *)
  0x4e284b47;   (* a98 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* a9c aesmc v7.16b, v7.16b *)
  0x4e284b43;   (* aa0 aese v3.16b, v26.16b *)
  0x4e286863;   (* aa4 aesmc v3.16b, v3.16b *)
  0x6e134273;   (* aa8 ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200908;   (* aac rev64 v8.16b, v8.16b *)
  0x4e284b61;   (* ab0 aese v1.16b, v27.16b *)
  0x4e286821;   (* ab4 aesmc v1.16b, v1.16b *)
  0x4e200929;   (* ab8 rev64 v9.16b, v9.16b *)
  0xad41697c;   (* abc ldp q28, q26, [x11, #32] *)
  0x4e284b63;   (* ac0 aese v3.16b, v27.16b *)
  0x4e286863;   (* ac4 aesmc v3.16b, v3.16b *)
  0x3dc024d7;   (* ac8 ldr q23, [x6, #144] *)
  0x3dc02cd9;   (* acc ldr q25, [x6, #176] *)
  0x4e284b62;   (* ad0 aese v2.16b, v27.16b *)
  0x4e286842;   (* ad4 aesmc v2.16b, v2.16b *)
  0x3dc018d4;   (* ad8 ldr q20, [x6, #96] *)
  0x3dc020d6;   (* adc ldr q22, [x6, #128] *)
  0x4e284b60;   (* ae0 aese v0.16b, v27.16b *)
  0x4e286800;   (* ae4 aesmc v0.16b, v0.16b *)
  0x4e284b65;   (* ae8 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* aec aesmc v5.16b, v5.16b *)
  0x4e284b64;   (* af0 aese v4.16b, v27.16b *)
  0x4e286884;   (* af4 aesmc v4.16b, v4.16b *)
  0x6e331d08;   (* af8 eor v8.16b, v8.16b, v19.16b *)
  0x4e20096b;   (* afc rev64 v11.16b, v11.16b *)
  0x4e284b66;   (* b00 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* b04 aesmc v6.16b, v6.16b *)
  0x4e284b81;   (* b08 aese v1.16b, v28.16b *)
  0x4e286821;   (* b0c aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* b10 aese v2.16b, v28.16b *)
  0x4e286842;   (* b14 aesmc v2.16b, v2.16b *)
  0x4e284b67;   (* b18 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* b1c aesmc v7.16b, v7.16b *)
  0x4e284b84;   (* b20 aese v4.16b, v28.16b *)
  0x4e286884;   (* b24 aesmc v4.16b, v4.16b *)
  0x4e284b80;   (* b28 aese v0.16b, v28.16b *)
  0x4e286800;   (* b2c aesmc v0.16b, v0.16b *)
  0x4e284b86;   (* b30 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* b34 aesmc v6.16b, v6.16b *)
  0x4e284b85;   (* b38 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* b3c aesmc v5.16b, v5.16b *)
  0x4e284b87;   (* b40 aese v7.16b, v28.16b *)
  0x4e2868e7;   (* b44 aesmc v7.16b, v7.16b *)
  0x4e284b83;   (* b48 aese v3.16b, v28.16b *)
  0x4e286863;   (* b4c aesmc v3.16b, v3.16b *)
  0xad42717b;   (* b50 ldp q27, q28, [x11, #64] *)
  0x4ec82932;   (* b54 trn1 v18.2d, v9.2d, v8.2d *)
  0x4ef9e111;   (* b58 pmull2 v17.1q, v8.2d, v25.2d *)
  0x4e2009ce;   (* b5c rev64 v14.16b, v14.16b *)
  0x4e284b44;   (* b60 aese v4.16b, v26.16b *)
  0x4e286884;   (* b64 aesmc v4.16b, v4.16b *)
  0x4ef7e130;   (* b68 pmull2 v16.1q, v9.2d, v23.2d *)
  0x4e284b47;   (* b6c aese v7.16b, v26.16b *)
  0x4e2868e7;   (* b70 aesmc v7.16b, v7.16b *)
  0x0ef9e113;   (* b74 pmull v19.1q, v8.1d, v25.1d *)
  0x4ec86928;   (* b78 trn2 v8.2d, v9.2d, v8.2d *)
  0x4ef6e15d;   (* b7c pmull2 v29.1q, v10.2d, v22.2d *)
  0x4e284b46;   (* b80 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* b84 aesmc v6.16b, v6.16b *)
  0x4e284b42;   (* b88 aese v2.16b, v26.16b *)
  0x4e286842;   (* b8c aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* b90 aese v3.16b, v26.16b *)
  0x4e286863;   (* b94 aesmc v3.16b, v3.16b *)
  0x6e301e31;   (* b98 eor v17.16b, v17.16b, v16.16b *)
  0x0ef7e137;   (* b9c pmull v23.1q, v9.1d, v23.1d *)
  0x4ef4e169;   (* ba0 pmull2 v9.1q, v11.2d, v20.2d *)
  0x4e284b41;   (* ba4 aese v1.16b, v26.16b *)
  0x4e286821;   (* ba8 aesmc v1.16b, v1.16b *)
  0x4e284b40;   (* bac aese v0.16b, v26.16b *)
  0x4e286800;   (* bb0 aesmc v0.16b, v0.16b *)
  0x6e321d08;   (* bb4 eor v8.16b, v8.16b, v18.16b *)
  0x4e284b45;   (* bb8 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* bbc aesmc v5.16b, v5.16b *)
  0x0ef6e156;   (* bc0 pmull v22.1q, v10.1d, v22.1d *)
  0x4e284b61;   (* bc4 aese v1.16b, v27.16b *)
  0x4e286821;   (* bc8 aesmc v1.16b, v1.16b *)
  0x4e284b66;   (* bcc aese v6.16b, v27.16b *)
  0x4e2868c6;   (* bd0 aesmc v6.16b, v6.16b *)
  0x4e284b60;   (* bd4 aese v0.16b, v27.16b *)
  0x4e286800;   (* bd8 aesmc v0.16b, v0.16b *)
  0x4e284b62;   (* bdc aese v2.16b, v27.16b *)
  0x4e286842;   (* be0 aesmc v2.16b, v2.16b *)
  0x4e284b64;   (* be4 aese v4.16b, v27.16b *)
  0x4e286884;   (* be8 aesmc v4.16b, v4.16b *)
  0x4e284b86;   (* bec aese v6.16b, v28.16b *)
  0x4e2868c6;   (* bf0 aesmc v6.16b, v6.16b *)
  0x4ef8e112;   (* bf4 pmull2 v18.1q, v8.2d, v24.2d *)
  0xce1d2631;   (* bf8 eor3 v17.16b, v17.16b, v29.16b, v9.16b *)
  0x4e284b67;   (* bfc aese v7.16b, v27.16b *)
  0x4e2868e7;   (* c00 aesmc v7.16b, v7.16b *)
  0x4eca297d;   (* c04 trn1 v29.2d, v11.2d, v10.2d *)
  0x4eca696a;   (* c08 trn2 v10.2d, v11.2d, v10.2d *)
  0x4e284b65;   (* c0c aese v5.16b, v27.16b *)
  0x4e2868a5;   (* c10 aesmc v5.16b, v5.16b *)
  0x6e371e73;   (* c14 eor v19.16b, v19.16b, v23.16b *)
  0x4e284b63;   (* c18 aese v3.16b, v27.16b *)
  0x4e286863;   (* c1c aesmc v3.16b, v3.16b *)
  0x0ef4e174;   (* c20 pmull v20.1q, v11.1d, v20.1d *)
  0x0ef8e118;   (* c24 pmull v24.1q, v8.1d, v24.1d *)
  0x6e3d1d4a;   (* c28 eor v10.16b, v10.16b, v29.16b *)
  0x4e20098c;   (* c2c rev64 v12.16b, v12.16b *)
  0x4e284b81;   (* c30 aese v1.16b, v28.16b *)
  0x4e286821;   (* c34 aesmc v1.16b, v1.16b *)
  0x4e284b80;   (* c38 aese v0.16b, v28.16b *)
  0x4e286800;   (* c3c aesmc v0.16b, v0.16b *)
  0x4e284b87;   (* c40 aese v7.16b, v28.16b *)
  0x4e2868e7;   (* c44 aesmc v7.16b, v7.16b *)
  0x4e284b84;   (* c48 aese v4.16b, v28.16b *)
  0x4e286884;   (* c4c aesmc v4.16b, v4.16b *)
  0xad436d7a;   (* c50 ldp q26, q27, [x11, #96] *)
  0x3dc00cd7;   (* c54 ldr q23, [x6, #48] *)
  0x3dc014d9;   (* c58 ldr q25, [x6, #80] *)
  0x4ef5e15d;   (* c5c pmull2 v29.1q, v10.2d, v21.2d *)
  0x0ef5e155;   (* c60 pmull v21.1q, v10.1d, v21.1d *)
  0xce165273;   (* c64 eor3 v19.16b, v19.16b, v22.16b, v20.16b *)
  0x6e381e52;   (* c68 eor v18.16b, v18.16b, v24.16b *)
  0x4e284b85;   (* c6c aese v5.16b, v28.16b *)
  0x4e2868a5;   (* c70 aesmc v5.16b, v5.16b *)
  0x4e2009ef;   (* c74 rev64 v15.16b, v15.16b *)
  0x4ecc29b0;   (* c78 trn1 v16.2d, v13.2d, v12.2d *)
  0x4e284b83;   (* c7c aese v3.16b, v28.16b *)
  0x4e286863;   (* c80 aesmc v3.16b, v3.16b *)
  0x4e284b82;   (* c84 aese v2.16b, v28.16b *)
  0x4e286842;   (* c88 aesmc v2.16b, v2.16b *)
  0xce157652;   (* c8c eor3 v18.16b, v18.16b, v21.16b, v29.16b *)
  0x4e284b47;   (* c90 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* c94 aesmc v7.16b, v7.16b *)
  0x4e284b44;   (* c98 aese v4.16b, v26.16b *)
  0x4e286884;   (* c9c aesmc v4.16b, v4.16b *)
  0x4e284b46;   (* ca0 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* ca4 aesmc v6.16b, v6.16b *)
  0x3dc004d5;   (* ca8 ldr q21, [x6, #16] *)
  0x3dc010d8;   (* cac ldr q24, [x6, #64] *)
  0x4e284b45;   (* cb0 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* cb4 aesmc v5.16b, v5.16b *)
  0x4e284b43;   (* cb8 aese v3.16b, v26.16b *)
  0x4e286863;   (* cbc aesmc v3.16b, v3.16b *)
  0x4e284b40;   (* cc0 aese v0.16b, v26.16b *)
  0x4e286800;   (* cc4 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* cc8 aese v1.16b, v26.16b *)
  0x4e286821;   (* ccc aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* cd0 aese v2.16b, v26.16b *)
  0x4e286842;   (* cd4 aesmc v2.16b, v2.16b *)
  0x4ef9e188;   (* cd8 pmull2 v8.1q, v12.2d, v25.2d *)
  0x0ef9e199;   (* cdc pmull v25.1q, v12.1d, v25.1d *)
  0x3dc000d4;   (* ce0 ldr q20, [x6] *)
  0x3dc008d6;   (* ce4 ldr q22, [x6, #32] *)
  0xad44697c;   (* ce8 ldp q28, q26, [x11, #128] *)
  0x4e284b61;   (* cec aese v1.16b, v27.16b *)
  0x4e286821;   (* cf0 aesmc v1.16b, v1.16b *)
  0x4e284b64;   (* cf4 aese v4.16b, v27.16b *)
  0x4e286884;   (* cf8 aesmc v4.16b, v4.16b *)
  0x4ef7e1aa;   (* cfc pmull2 v10.1q, v13.2d, v23.2d *)
  0x4ecc69ac;   (* d00 trn2 v12.2d, v13.2d, v12.2d *)
  0x4e284b65;   (* d04 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* d08 aesmc v5.16b, v5.16b *)
  0x4e284b66;   (* d0c aese v6.16b, v27.16b *)
  0x4e2868c6;   (* d10 aesmc v6.16b, v6.16b *)
  0x0ef7e1b7;   (* d14 pmull v23.1q, v13.1d, v23.1d *)
  0x4e284b67;   (* d18 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* d1c aesmc v7.16b, v7.16b *)
  0x4e284b63;   (* d20 aese v3.16b, v27.16b *)
  0x4e286863;   (* d24 aesmc v3.16b, v3.16b *)
  0x6e301d8c;   (* d28 eor v12.16b, v12.16b, v16.16b *)
  0x4ef6e1cb;   (* d2c pmull2 v11.1q, v14.2d, v22.2d *)
  0x0ef6e1d6;   (* d30 pmull v22.1q, v14.1d, v22.1d *)
  0x4e284b62;   (* d34 aese v2.16b, v27.16b *)
  0x4e286842;   (* d38 aesmc v2.16b, v2.16b *)
  0x4ece29ed;   (* d3c trn1 v13.2d, v15.2d, v14.2d *)
  0x4ece69ee;   (* d40 trn2 v14.2d, v15.2d, v14.2d *)
  0x4e284b60;   (* d44 aese v0.16b, v27.16b *)
  0x4e286800;   (* d48 aesmc v0.16b, v0.16b *)
  0x4e284b87;   (* d4c aese v7.16b, v28.16b *)
  0x4e2868e7;   (* d50 aesmc v7.16b, v7.16b *)
  0xce195e73;   (* d54 eor3 v19.16b, v19.16b, v25.16b, v23.16b *)
  0x4e284b82;   (* d58 aese v2.16b, v28.16b *)
  0x4e286842;   (* d5c aesmc v2.16b, v2.16b *)
  0x4e284b86;   (* d60 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* d64 aesmc v6.16b, v6.16b *)
  0x4e284b84;   (* d68 aese v4.16b, v28.16b *)
  0x4e286884;   (* d6c aesmc v4.16b, v4.16b *)
  0x4e284b83;   (* d70 aese v3.16b, v28.16b *)
  0x4e286863;   (* d74 aesmc v3.16b, v3.16b *)
  0x4e284b85;   (* d78 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* d7c aesmc v5.16b, v5.16b *)
  0x6e2d1dce;   (* d80 eor v14.16b, v14.16b, v13.16b *)
  0x4e284b80;   (* d84 aese v0.16b, v28.16b *)
  0x4e286800;   (* d88 aesmc v0.16b, v0.16b *)
  0x4ef8e190;   (* d8c pmull2 v16.1q, v12.2d, v24.2d *)
  0x0ef8e198;   (* d90 pmull v24.1q, v12.1d, v24.1d *)
  0x4e284b81;   (* d94 aese v1.16b, v28.16b *)
  0x4e286821;   (* d98 aesmc v1.16b, v1.16b *)
  0x4ef4e1ec;   (* d9c pmull2 v12.1q, v15.2d, v20.2d *)
  0x4ef5e1cd;   (* da0 pmull2 v13.1q, v14.2d, v21.2d *)
  0x0ef5e1d5;   (* da4 pmull v21.1q, v14.1d, v21.1d *)
  0x0ef4e1f4;   (* da8 pmull v20.1q, v15.1d, v20.1d *)
  0xce184252;   (* dac eor3 v18.16b, v18.16b, v24.16b, v16.16b *)
  0xce082a31;   (* db0 eor3 v17.16b, v17.16b, v8.16b, v10.16b *)
  0xad45717b;   (* db4 ldp q27, q28, [x11, #160] *)
  0x4e284b41;   (* db8 aese v1.16b, v26.16b *)
  0x4e286821;   (* dbc aesmc v1.16b, v1.16b *)
  0x4e284b40;   (* dc0 aese v0.16b, v26.16b *)
  0x4e286800;   (* dc4 aesmc v0.16b, v0.16b *)
  0xce0b3231;   (* dc8 eor3 v17.16b, v17.16b, v11.16b, v12.16b *)
  0xce153652;   (* dcc eor3 v18.16b, v18.16b, v21.16b, v13.16b *)
  0xfd400150;   (* dd0 ldr d16, [x10] *)
  0xce165273;   (* dd4 eor3 v19.16b, v19.16b, v22.16b, v20.16b *)
  0x4e284b43;   (* dd8 aese v3.16b, v26.16b *)
  0x4e286863;   (* ddc aesmc v3.16b, v3.16b *)
  0x4e284b47;   (* de0 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* de4 aesmc v7.16b, v7.16b *)
  0x4e284b45;   (* de8 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* dec aesmc v5.16b, v5.16b *)
  0x4e284b42;   (* df0 aese v2.16b, v26.16b *)
  0x4e286842;   (* df4 aesmc v2.16b, v2.16b *)
  0x4e284b46;   (* df8 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* dfc aesmc v6.16b, v6.16b *)
  0x4e284b65;   (* e00 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* e04 aesmc v5.16b, v5.16b *)
  0x4e284b61;   (* e08 aese v1.16b, v27.16b *)
  0x4e286821;   (* e0c aesmc v1.16b, v1.16b *)
  0x4e284b44;   (* e10 aese v4.16b, v26.16b *)
  0x4e286884;   (* e14 aesmc v4.16b, v4.16b *)
  0x4e284b67;   (* e18 aese v7.16b, v27.16b *)
  0x4e2868e7;   (* e1c aesmc v7.16b, v7.16b *)
  0x4e284b66;   (* e20 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* e24 aesmc v6.16b, v6.16b *)
  0x4e284b63;   (* e28 aese v3.16b, v27.16b *)
  0x4e286863;   (* e2c aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* e30 aese v4.16b, v27.16b *)
  0x4e286884;   (* e34 aesmc v4.16b, v4.16b *)
  0x4e284b60;   (* e38 aese v0.16b, v27.16b *)
  0x4e286800;   (* e3c aesmc v0.16b, v0.16b *)
  0x4e284b62;   (* e40 aese v2.16b, v27.16b *)
  0x4e286842;   (* e44 aesmc v2.16b, v2.16b *)
  0x0ef0e23d;   (* e48 pmull v29.1q, v17.1d, v16.1d *)
  0xce114e52;   (* e4c eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x4e284b87;   (* e50 aese v7.16b, v28.16b *)
  0x4e2868e7;   (* e54 aesmc v7.16b, v7.16b *)
  0xad466d7a;   (* e58 ldp q26, q27, [x11, #192] *)
  0x6e114235;   (* e5c ext v21.16b, v17.16b, v17.16b, #8 *)
  0x4e284b82;   (* e60 aese v2.16b, v28.16b *)
  0x4e286842;   (* e64 aesmc v2.16b, v2.16b *)
  0xce1d5652;   (* e68 eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x4e284b81;   (* e6c aese v1.16b, v28.16b *)
  0x4e286821;   (* e70 aesmc v1.16b, v1.16b *)
  0x4e284b86;   (* e74 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* e78 aesmc v6.16b, v6.16b *)
  0x4e284b80;   (* e7c aese v0.16b, v28.16b *)
  0x4e286800;   (* e80 aesmc v0.16b, v0.16b *)
  0x4e284b84;   (* e84 aese v4.16b, v28.16b *)
  0x4e286884;   (* e88 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* e8c aese v5.16b, v28.16b *)
  0x4e2868a5;   (* e90 aesmc v5.16b, v5.16b *)
  0x0ef0e251;   (* e94 pmull v17.1q, v18.1d, v16.1d *)
  0x4e284b83;   (* e98 aese v3.16b, v28.16b *)
  0x4e286863;   (* e9c aesmc v3.16b, v3.16b *)
  0x3dc0397c;   (* ea0 ldr q28, [x11, #224] *)
  0x4e284b41;   (* ea4 aese v1.16b, v26.16b *)
  0x4e286821;   (* ea8 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* eac aese v2.16b, v26.16b *)
  0x4e286842;   (* eb0 aesmc v2.16b, v2.16b *)
  0x4e284b40;   (* eb4 aese v0.16b, v26.16b *)
  0x4e286800;   (* eb8 aesmc v0.16b, v0.16b *)
  0x4e284b46;   (* ebc aese v6.16b, v26.16b *)
  0x4e2868c6;   (* ec0 aesmc v6.16b, v6.16b *)
  0x4e284b45;   (* ec4 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* ec8 aesmc v5.16b, v5.16b *)
  0x6e124255;   (* ecc ext v21.16b, v18.16b, v18.16b, #8 *)
  0x4e284b44;   (* ed0 aese v4.16b, v26.16b *)
  0x4e286884;   (* ed4 aesmc v4.16b, v4.16b *)
  0x4ebf87de;   (* ed8 add v30.4s, v30.4s, v31.4s *)
  0x4e284b43;   (* edc aese v3.16b, v26.16b *)
  0x4e286863;   (* ee0 aesmc v3.16b, v3.16b *)
  0x4e284b47;   (* ee4 aese v7.16b, v26.16b *)
  0x4e2868e7;   (* ee8 aesmc v7.16b, v7.16b *)
  0x4e284b60;   (* eec aese v0.16b, v27.16b *)
  0xce154673;   (* ef0 eor3 v19.16b, v19.16b, v21.16b, v17.16b *)
  0x4e284b65;   (* ef4 aese v5.16b, v27.16b *)
  0x4e284b61;   (* ef8 aese v1.16b, v27.16b *)
  0x4e284b63;   (* efc aese v3.16b, v27.16b *)
  0x4e284b64;   (* f00 aese v4.16b, v27.16b *)
  0x4e284b67;   (* f04 aese v7.16b, v27.16b *)
  0x4e284b62;   (* f08 aese v2.16b, v27.16b *)
  0x4e284b66;   (* f0c aese v6.16b, v27.16b *)
  0xad4564d8;   (* f10 ldp q24, q25, [x6, #160] *)
  0xcb000085;   (* f14 sub x5, x4, x0 *)
  0x3cc10408;   (* f18 ldr q8, [x0], #16 *)
  0xad4354d4;   (* f1c ldp q20, q21, [x6, #96] *)
  0x6e134270;   (* f20 ext v16.16b, v19.16b, v19.16b, #8 *)
  0xad445cd6;   (* f24 ldp q22, q23, [x6, #128] *)
  0x4ebc1f9d;   (* f28 mov v29.16b, v28.16b *)
  0xf101c0bf;   (* f2c cmp x5, #0x70 *)
  0xce007509;   (* f30 eor3 v9.16b, v8.16b, v0.16b, v29.16b *)
  0x1400016a;   (* f34 b 14dc <L256_enc_tail_dispatch> *)
  0x0f00e413;   (* f38 movi v19.8b, #0x0 *)
  0x4ea61cc7;   (* f3c mov v7.16b, v6.16b *)
  0x0f00e411;   (* f40 movi v17.8b, #0x0 *)
  0x4ea51ca6;   (* f44 mov v6.16b, v5.16b *)
  0x4ea41c85;   (* f48 mov v5.16b, v4.16b *)
  0x4ea31c64;   (* f4c mov v4.16b, v3.16b *)
  0x4ea21c43;   (* f50 mov v3.16b, v2.16b *)
  0x6ebf87de;   (* f54 sub v30.4s, v30.4s, v31.4s *)
  0x4ea11c22;   (* f58 mov v2.16b, v1.16b *)
  0x0f00e412;   (* f5c movi v18.8b, #0x0 *)
  0xf10180bf;   (* f60 cmp x5, #0x60 *)
  0x540005ec;   (* f64 b.gt 1020 <L256_enc_blocks_more_than_6> *)
  0x4ea61cc7;   (* f68 mov v7.16b, v6.16b *)
  0x4ea51ca6;   (* f6c mov v6.16b, v5.16b *)
  0xf10140bf;   (* f70 cmp x5, #0x50 *)
  0x4ea41c85;   (* f74 mov v5.16b, v4.16b *)
  0x4ea31c64;   (* f78 mov v4.16b, v3.16b *)
  0x4ea11c23;   (* f7c mov v3.16b, v1.16b *)
  0x6ebf87de;   (* f80 sub v30.4s, v30.4s, v31.4s *)
  0x540006ac;   (* f84 b.gt 1058 <L256_enc_blocks_more_than_5> *)
  0x4ea61cc7;   (* f88 mov v7.16b, v6.16b *)
  0x6ebf87de;   (* f8c sub v30.4s, v30.4s, v31.4s *)
  0x4ea51ca6;   (* f90 mov v6.16b, v5.16b *)
  0x4ea41c85;   (* f94 mov v5.16b, v4.16b *)
  0xf10100bf;   (* f98 cmp x5, #0x40 *)
  0x4ea11c24;   (* f9c mov v4.16b, v1.16b *)
  0x540007ac;   (* fa0 b.gt 1094 <L256_enc_blocks_more_than_4> *)
  0xf100c0bf;   (* fa4 cmp x5, #0x30 *)
  0x4ea61cc7;   (* fa8 mov v7.16b, v6.16b *)
  0x4ea51ca6;   (* fac mov v6.16b, v5.16b *)
  0x4ea11c25;   (* fb0 mov v5.16b, v1.16b *)
  0x6ebf87de;   (* fb4 sub v30.4s, v30.4s, v31.4s *)
  0x5400208c;   (* fb8 b.gt 13c8 <L256_enc_rem4_drain> *)
  0xf10080bf;   (* fbc cmp x5, #0x20 *)
  0x4ea61cc7;   (* fc0 mov v7.16b, v6.16b *)
  0x3dc010d8;   (* fc4 ldr q24, [x6, #64] *)
  0x4ea11c26;   (* fc8 mov v6.16b, v1.16b *)
  0x6ebf87de;   (* fcc sub v30.4s, v30.4s, v31.4s *)
  0x54000a0c;   (* fd0 b.gt 1110 <L256_enc_blocks_more_than_2> *)
  0x4ea11c27;   (* fd4 mov v7.16b, v1.16b *)
  0x6ebf87de;   (* fd8 sub v30.4s, v30.4s, v31.4s *)
  0xf10040bf;   (* fdc cmp x5, #0x10 *)
  0x54000b6c;   (* fe0 b.gt 114c <L256_enc_blocks_more_than_1> *)
  0x6ebf87de;   (* fe4 sub v30.4s, v30.4s, v31.4s *)
  0x3dc004d5;   (* fe8 ldr q21, [x6, #16] *)
  0x14000069;   (* fec b 1190 <L256_enc_blocks_less_than_1> *)
  0x4c9f7049;   (* ff0 st1 {v9.16b}, [x2], #16 *)
  0x4e200928;   (* ff4 rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* ff8 eor v8.16b, v8.16b, v16.16b *)
  0x3cc10409;   (* ffc ldr q9, [x0], #16 *)
  0x4ef9e111;   (* 1000 pmull2 v17.1q, v8.2d, v25.2d *)
  0x6e08411b;   (* 1004 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x6e084712;   (* 1008 mov v18.d[0], v24.d[1] *)
  0x0f00e410;   (* 100c movi v16.8b, #0x0 *)
  0x2e281f7b;   (* 1010 eor v27.8b, v27.8b, v8.8b *)
  0xce017529;   (* 1014 eor3 v9.16b, v9.16b, v1.16b, v29.16b *)
  0x0ef2e372;   (* 1018 pmull v18.1q, v27.1d, v18.1d *)
  0x0ef9e113;   (* 101c pmull v19.1q, v8.1d, v25.1d *)
  0x4c9f7049;   (* 1020 st1 {v9.16b}, [x2], #16 *)
  0x4e200928;   (* 1024 rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* 1028 eor v8.16b, v8.16b, v16.16b *)
  0x0ef7e11a;   (* 102c pmull v26.1q, v8.1d, v23.1d *)
  0x6e08411b;   (* 1030 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef7e11c;   (* 1034 pmull2 v28.1q, v8.2d, v23.2d *)
  0x3cc10409;   (* 1038 ldr q9, [x0], #16 *)
  0x6e3a1e73;   (* 103c eor v19.16b, v19.16b, v26.16b *)
  0x2e281f7b;   (* 1040 eor v27.8b, v27.8b, v8.8b *)
  0x0ef8e37b;   (* 1044 pmull v27.1q, v27.1d, v24.1d *)
  0xce027529;   (* 1048 eor3 v9.16b, v9.16b, v2.16b, v29.16b *)
  0x0f00e410;   (* 104c movi v16.8b, #0x0 *)
  0x6e3b1e52;   (* 1050 eor v18.16b, v18.16b, v27.16b *)
  0x6e3c1e31;   (* 1054 eor v17.16b, v17.16b, v28.16b *)
  0x4c9f7049;   (* 1058 st1 {v9.16b}, [x2], #16 *)
  0x4e200928;   (* 105c rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* 1060 eor v8.16b, v8.16b, v16.16b *)
  0x6e08411b;   (* 1064 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef6e11c;   (* 1068 pmull2 v28.1q, v8.2d, v22.2d *)
  0x6e3c1e31;   (* 106c eor v17.16b, v17.16b, v28.16b *)
  0x2e281f7b;   (* 1070 eor v27.8b, v27.8b, v8.8b *)
  0x6e1542ac;   (* 1074 ext v12.16b, v21.16b, v21.16b, #8 *)
  0x3cc10409;   (* 1078 ldr q9, [x0], #16 *)
  0x0ef6e11a;   (* 107c pmull v26.1q, v8.1d, v22.1d *)
  0x0eece37b;   (* 1080 pmull v27.1q, v27.1d, v12.1d *)
  0x0f00e410;   (* 1084 movi v16.8b, #0x0 *)
  0x6e3a1e73;   (* 1088 eor v19.16b, v19.16b, v26.16b *)
  0x6e3b1e52;   (* 108c eor v18.16b, v18.16b, v27.16b *)
  0xce037529;   (* 1090 eor3 v9.16b, v9.16b, v3.16b, v29.16b *)
  0x4c9f7049;   (* 1094 st1 {v9.16b}, [x2], #16 *)
  0x4e200928;   (* 1098 rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 109c ldr q9, [x0], #16 *)
  0x6e301d08;   (* 10a0 eor v8.16b, v8.16b, v16.16b *)
  0x6e08411b;   (* 10a4 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef4e11c;   (* 10a8 pmull2 v28.1q, v8.2d, v20.2d *)
  0xce047529;   (* 10ac eor3 v9.16b, v9.16b, v4.16b, v29.16b *)
  0x0ef4e11a;   (* 10b0 pmull v26.1q, v8.1d, v20.1d *)
  0x2e281f7b;   (* 10b4 eor v27.8b, v27.8b, v8.8b *)
  0x6e3a1e73;   (* 10b8 eor v19.16b, v19.16b, v26.16b *)
  0x0ef5e37b;   (* 10bc pmull v27.1q, v27.1d, v21.1d *)
  0x0f00e410;   (* 10c0 movi v16.8b, #0x0 *)
  0x6e3b1e52;   (* 10c4 eor v18.16b, v18.16b, v27.16b *)
  0x6e3c1e31;   (* 10c8 eor v17.16b, v17.16b, v28.16b *)
  0x4c9f7049;   (* 10cc st1 {v9.16b}, [x2], #16 *)
  0x3dc014d9;   (* 10d0 ldr q25, [x6, #80] *)
  0x4e200928;   (* 10d4 rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* 10d8 eor v8.16b, v8.16b, v16.16b *)
  0x6e08411b;   (* 10dc ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef9e11c;   (* 10e0 pmull2 v28.1q, v8.2d, v25.2d *)
  0x6e3c1e31;   (* 10e4 eor v17.16b, v17.16b, v28.16b *)
  0x2e281f7b;   (* 10e8 eor v27.8b, v27.8b, v8.8b *)
  0x3dc010d8;   (* 10ec ldr q24, [x6, #64] *)
  0x6e18430b;   (* 10f0 ext v11.16b, v24.16b, v24.16b, #8 *)
  0x3cc10409;   (* 10f4 ldr q9, [x0], #16 *)
  0x0eebe37b;   (* 10f8 pmull v27.1q, v27.1d, v11.1d *)
  0x0ef9e11a;   (* 10fc pmull v26.1q, v8.1d, v25.1d *)
  0xce057529;   (* 1100 eor3 v9.16b, v9.16b, v5.16b, v29.16b *)
  0x0f00e410;   (* 1104 movi v16.8b, #0x0 *)
  0x6e3b1e52;   (* 1108 eor v18.16b, v18.16b, v27.16b *)
  0x6e3a1e73;   (* 110c eor v19.16b, v19.16b, v26.16b *)
  0x3dc00cd7;   (* 1110 ldr q23, [x6, #48] *)
  0x4c9f7049;   (* 1114 st1 {v9.16b}, [x2], #16 *)
  0x4e200928;   (* 1118 rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 111c ldr q9, [x0], #16 *)
  0x6e301d08;   (* 1120 eor v8.16b, v8.16b, v16.16b *)
  0x6e08411b;   (* 1124 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x0f00e410;   (* 1128 movi v16.8b, #0x0 *)
  0x4ef7e11c;   (* 112c pmull2 v28.1q, v8.2d, v23.2d *)
  0xce067529;   (* 1130 eor3 v9.16b, v9.16b, v6.16b, v29.16b *)
  0x2e281f7b;   (* 1134 eor v27.8b, v27.8b, v8.8b *)
  0x6e3c1e31;   (* 1138 eor v17.16b, v17.16b, v28.16b *)
  0x0ef8e37b;   (* 113c pmull v27.1q, v27.1d, v24.1d *)
  0x0ef7e11a;   (* 1140 pmull v26.1q, v8.1d, v23.1d *)
  0x6e3b1e52;   (* 1144 eor v18.16b, v18.16b, v27.16b *)
  0x6e3a1e73;   (* 1148 eor v19.16b, v19.16b, v26.16b *)
  0x4c9f7049;   (* 114c st1 {v9.16b}, [x2], #16 *)
  0x3dc008d6;   (* 1150 ldr q22, [x6, #32] *)
  0x4e200928;   (* 1154 rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 1158 ldr q9, [x0], #16 *)
  0x6e301d08;   (* 115c eor v8.16b, v8.16b, v16.16b *)
  0x0f00e410;   (* 1160 movi v16.8b, #0x0 *)
  0x6e08411b;   (* 1164 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef6e11c;   (* 1168 pmull2 v28.1q, v8.2d, v22.2d *)
  0xce077529;   (* 116c eor3 v9.16b, v9.16b, v7.16b, v29.16b *)
  0x6e3c1e31;   (* 1170 eor v17.16b, v17.16b, v28.16b *)
  0x0ef6e11a;   (* 1174 pmull v26.1q, v8.1d, v22.1d *)
  0x2e281f7b;   (* 1178 eor v27.8b, v27.8b, v8.8b *)
  0x3dc004d5;   (* 117c ldr q21, [x6, #16] *)
  0x6e1542aa;   (* 1180 ext v10.16b, v21.16b, v21.16b, #8 *)
  0x6e3a1e73;   (* 1184 eor v19.16b, v19.16b, v26.16b *)
  0x0eeae37b;   (* 1188 pmull v27.1q, v27.1d, v10.1d *)
  0x6e3b1e52;   (* 118c eor v18.16b, v18.16b, v27.16b *)
  0x3dc000d4;   (* 1190 ldr q20, [x6] *)
  0x4e200928;   (* 1194 rev64 v8.16b, v9.16b *)
  0x6e200bde;   (* 1198 rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 119c str q30, [x16] *)
  0x6e301d08;   (* 11a0 eor v8.16b, v8.16b, v16.16b *)
  0x4c007049;   (* 11a4 st1 {v9.16b}, [x2] *)
  0x6e084510;   (* 11a8 mov v16.d[0], v8.d[1] *)
  0x4ef4e11c;   (* 11ac pmull2 v28.1q, v8.2d, v20.2d *)
  0x0ef4e11a;   (* 11b0 pmull v26.1q, v8.1d, v20.1d *)
  0x6e3c1e31;   (* 11b4 eor v17.16b, v17.16b, v28.16b *)
  0x6e3a1e73;   (* 11b8 eor v19.16b, v19.16b, v26.16b *)
  0x2e281e10;   (* 11bc eor v16.8b, v16.8b, v8.8b *)
  0x0ef5e210;   (* 11c0 pmull v16.1q, v16.1d, v21.1d *)
  0x6e301e52;   (* 11c4 eor v18.16b, v18.16b, v16.16b *)
  0xfd400150;   (* 11c8 ldr d16, [x10] *)
  0x6e114235;   (* 11cc ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 11d0 eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 11d4 pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 11d8 eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 11dc pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 11e0 ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 11e4 eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x6e134273;   (* 11e8 ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200a73;   (* 11ec rev64 v19.16b, v19.16b *)
  0x4c007073;   (* 11f0 st1 {v19.16b}, [x3] *)
  0xaa0903e0;   (* 11f4 mov x0, x9 *)
  0x6d412fea;   (* 11f8 ldp d10, d11, [sp, #16] *)
  0x6d4237ec;   (* 11fc ldp d12, d13, [sp, #32] *)
  0x6d433fee;   (* 1200 ldp d14, d15, [sp, #48] *)
  0x6d4027e8;   (* 1204 ldp d8, d9, [sp] *)
  0x910143ff;   (* 1208 add sp, sp, #0x50 *)
  0xd65f03c0;   (* 120c ret *)
  0x52800000;   (* 1210 mov w0, #0x0 // #0 *)
  0xd65f03c0;   (* 1214 ret *)
  0x4c9f7049;   (* 1218 st1 {v9.16b}, [x2], #16 *)
  0x4e200928;   (* 121c rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* 1220 eor v8.16b, v8.16b, v16.16b *)
  0x3cc10409;   (* 1224 ldr q9, [x0], #16 *)
  0x4ef9e111;   (* 1228 pmull2 v17.1q, v8.2d, v25.2d *)
  0x6e08411b;   (* 122c ext v27.16b, v8.16b, v8.16b, #8 *)
  0x6e084712;   (* 1230 mov v18.d[0], v24.d[1] *)
  0x0f00e410;   (* 1234 movi v16.8b, #0x0 *)
  0x2e281f7b;   (* 1238 eor v27.8b, v27.8b, v8.8b *)
  0xce017529;   (* 123c eor3 v9.16b, v9.16b, v1.16b, v29.16b *)
  0x0ef2e372;   (* 1240 pmull v18.1q, v27.1d, v18.1d *)
  0x0ef9e113;   (* 1244 pmull v19.1q, v8.1d, v25.1d *)
  0x4c9f7049;   (* 1248 st1 {v9.16b}, [x2], #16 *)
  0x4e200928;   (* 124c rev64 v8.16b, v9.16b *)
  0x0ef7e10e;   (* 1250 pmull v14.1q, v8.1d, v23.1d *)
  0x6e08411b;   (* 1254 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef7e10d;   (* 1258 pmull2 v13.1q, v8.2d, v23.2d *)
  0x3cc10409;   (* 125c ldr q9, [x0], #16 *)
  0x2e281f7b;   (* 1260 eor v27.8b, v27.8b, v8.8b *)
  0x0ef8e36f;   (* 1264 pmull v15.1q, v27.1d, v24.1d *)
  0xce027529;   (* 1268 eor3 v9.16b, v9.16b, v2.16b, v29.16b *)
  0x4c9f7049;   (* 126c st1 {v9.16b}, [x2], #16 *)
  0x4e200928;   (* 1270 rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 1274 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef6e11c;   (* 1278 pmull2 v28.1q, v8.2d, v22.2d *)
  0xce1c3631;   (* 127c eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0x2e281f7b;   (* 1280 eor v27.8b, v27.8b, v8.8b *)
  0x6e1542ac;   (* 1284 ext v12.16b, v21.16b, v21.16b, #8 *)
  0x3cc10409;   (* 1288 ldr q9, [x0], #16 *)
  0x0ef6e11a;   (* 128c pmull v26.1q, v8.1d, v22.1d *)
  0x0eece37b;   (* 1290 pmull v27.1q, v27.1d, v12.1d *)
  0xce1a3a73;   (* 1294 eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0xce1b3e52;   (* 1298 eor3 v18.16b, v18.16b, v27.16b, v15.16b *)
  0xce037529;   (* 129c eor3 v9.16b, v9.16b, v3.16b, v29.16b *)
  0x4c9f7049;   (* 12a0 st1 {v9.16b}, [x2], #16 *)
  0x4e200928;   (* 12a4 rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 12a8 ldr q9, [x0], #16 *)
  0x6e08411b;   (* 12ac ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef4e10d;   (* 12b0 pmull2 v13.1q, v8.2d, v20.2d *)
  0xce047529;   (* 12b4 eor3 v9.16b, v9.16b, v4.16b, v29.16b *)
  0x0ef4e10e;   (* 12b8 pmull v14.1q, v8.1d, v20.1d *)
  0x2e281f7b;   (* 12bc eor v27.8b, v27.8b, v8.8b *)
  0x0ef5e36f;   (* 12c0 pmull v15.1q, v27.1d, v21.1d *)
  0x4c9f7049;   (* 12c4 st1 {v9.16b}, [x2], #16 *)
  0x3dc014d9;   (* 12c8 ldr q25, [x6, #80] *)
  0x4e200928;   (* 12cc rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 12d0 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef9e11c;   (* 12d4 pmull2 v28.1q, v8.2d, v25.2d *)
  0xce1c3631;   (* 12d8 eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0x2e281f7b;   (* 12dc eor v27.8b, v27.8b, v8.8b *)
  0x3dc010d8;   (* 12e0 ldr q24, [x6, #64] *)
  0x6e18430b;   (* 12e4 ext v11.16b, v24.16b, v24.16b, #8 *)
  0x3cc10409;   (* 12e8 ldr q9, [x0], #16 *)
  0x0eebe37b;   (* 12ec pmull v27.1q, v27.1d, v11.1d *)
  0x0ef9e11a;   (* 12f0 pmull v26.1q, v8.1d, v25.1d *)
  0xce057529;   (* 12f4 eor3 v9.16b, v9.16b, v5.16b, v29.16b *)
  0xce1b3e52;   (* 12f8 eor3 v18.16b, v18.16b, v27.16b, v15.16b *)
  0xce1a3a73;   (* 12fc eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0x3dc00cd7;   (* 1300 ldr q23, [x6, #48] *)
  0x4c9f7049;   (* 1304 st1 {v9.16b}, [x2], #16 *)
  0x4e200928;   (* 1308 rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 130c ldr q9, [x0], #16 *)
  0x6e08411b;   (* 1310 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef7e10d;   (* 1314 pmull2 v13.1q, v8.2d, v23.2d *)
  0xce067529;   (* 1318 eor3 v9.16b, v9.16b, v6.16b, v29.16b *)
  0x2e281f7b;   (* 131c eor v27.8b, v27.8b, v8.8b *)
  0x0ef8e36f;   (* 1320 pmull v15.1q, v27.1d, v24.1d *)
  0x0ef7e10e;   (* 1324 pmull v14.1q, v8.1d, v23.1d *)
  0x4c9f7049;   (* 1328 st1 {v9.16b}, [x2], #16 *)
  0x3dc008d6;   (* 132c ldr q22, [x6, #32] *)
  0x4e200928;   (* 1330 rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 1334 ldr q9, [x0], #16 *)
  0x6e08411b;   (* 1338 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef6e11c;   (* 133c pmull2 v28.1q, v8.2d, v22.2d *)
  0xce077529;   (* 1340 eor3 v9.16b, v9.16b, v7.16b, v29.16b *)
  0xce1c3631;   (* 1344 eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0x0ef6e11a;   (* 1348 pmull v26.1q, v8.1d, v22.1d *)
  0x2e281f7b;   (* 134c eor v27.8b, v27.8b, v8.8b *)
  0x3dc004d5;   (* 1350 ldr q21, [x6, #16] *)
  0x6e1542aa;   (* 1354 ext v10.16b, v21.16b, v21.16b, #8 *)
  0xce1a3a73;   (* 1358 eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0x0eeae37b;   (* 135c pmull v27.1q, v27.1d, v10.1d *)
  0xce1b3e52;   (* 1360 eor3 v18.16b, v18.16b, v27.16b, v15.16b *)
  0x3dc000d4;   (* 1364 ldr q20, [x6] *)
  0x4e200928;   (* 1368 rev64 v8.16b, v9.16b *)
  0x6e200bde;   (* 136c rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 1370 str q30, [x16] *)
  0x4c007049;   (* 1374 st1 {v9.16b}, [x2] *)
  0x6e084510;   (* 1378 mov v16.d[0], v8.d[1] *)
  0x4ef4e11c;   (* 137c pmull2 v28.1q, v8.2d, v20.2d *)
  0x0ef4e11a;   (* 1380 pmull v26.1q, v8.1d, v20.1d *)
  0x6e3c1e31;   (* 1384 eor v17.16b, v17.16b, v28.16b *)
  0x6e3a1e73;   (* 1388 eor v19.16b, v19.16b, v26.16b *)
  0x2e281e10;   (* 138c eor v16.8b, v16.8b, v8.8b *)
  0x0ef5e210;   (* 1390 pmull v16.1q, v16.1d, v21.1d *)
  0x6e301e52;   (* 1394 eor v18.16b, v18.16b, v16.16b *)
  0xfd400150;   (* 1398 ldr d16, [x10] *)
  0x6e114235;   (* 139c ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 13a0 eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 13a4 pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 13a8 eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 13ac pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 13b0 ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 13b4 eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x6e134273;   (* 13b8 ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200a73;   (* 13bc rev64 v19.16b, v19.16b *)
  0x4c007073;   (* 13c0 st1 {v19.16b}, [x3] *)
  0x17ffff8c;   (* 13c4 b 11f4 <L256_enc_epilogue> *)
  0x4c9f7049;   (* 13c8 st1 {v9.16b}, [x2], #16 *)
  0x3dc014d9;   (* 13cc ldr q25, [x6, #80] *)
  0x4e200928;   (* 13d0 rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* 13d4 eor v8.16b, v8.16b, v16.16b *)
  0x6e08411b;   (* 13d8 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef9e10d;   (* 13dc pmull2 v13.1q, v8.2d, v25.2d *)
  0x3dc010d8;   (* 13e0 ldr q24, [x6, #64] *)
  0x6e18430b;   (* 13e4 ext v11.16b, v24.16b, v24.16b, #8 *)
  0x2e281f7b;   (* 13e8 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 13ec ldr q9, [x0], #16 *)
  0x0eebe36f;   (* 13f0 pmull v15.1q, v27.1d, v11.1d *)
  0x0ef9e10e;   (* 13f4 pmull v14.1q, v8.1d, v25.1d *)
  0xce057529;   (* 13f8 eor3 v9.16b, v9.16b, v5.16b, v29.16b *)
  0x0f00e410;   (* 13fc movi v16.8b, #0x0 *)
  0x4c9f7049;   (* 1400 st1 {v9.16b}, [x2], #16 *)
  0x3dc00cd7;   (* 1404 ldr q23, [x6, #48] *)
  0x4e200928;   (* 1408 rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 140c ldr q9, [x0], #16 *)
  0x6e301d08;   (* 1410 eor v8.16b, v8.16b, v16.16b *)
  0x6e08411b;   (* 1414 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x0f00e410;   (* 1418 movi v16.8b, #0x0 *)
  0x4ef7e11c;   (* 141c pmull2 v28.1q, v8.2d, v23.2d *)
  0xce067529;   (* 1420 eor3 v9.16b, v9.16b, v6.16b, v29.16b *)
  0x2e281f7b;   (* 1424 eor v27.8b, v27.8b, v8.8b *)
  0x0ef7e11a;   (* 1428 pmull v26.1q, v8.1d, v23.1d *)
  0x0ef8e37b;   (* 142c pmull v27.1q, v27.1d, v24.1d *)
  0xce1c3631;   (* 1430 eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0xce1a3a73;   (* 1434 eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0xce1b3e52;   (* 1438 eor3 v18.16b, v18.16b, v27.16b, v15.16b *)
  0x4c9f7049;   (* 143c st1 {v9.16b}, [x2], #16 *)
  0x3dc008d6;   (* 1440 ldr q22, [x6, #32] *)
  0x4e200928;   (* 1444 rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 1448 ldr q9, [x0], #16 *)
  0x6e301d08;   (* 144c eor v8.16b, v8.16b, v16.16b *)
  0x0f00e410;   (* 1450 movi v16.8b, #0x0 *)
  0x6e08411b;   (* 1454 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef6e10d;   (* 1458 pmull2 v13.1q, v8.2d, v22.2d *)
  0xce077529;   (* 145c eor3 v9.16b, v9.16b, v7.16b, v29.16b *)
  0x0ef6e10e;   (* 1460 pmull v14.1q, v8.1d, v22.1d *)
  0x2e281f7b;   (* 1464 eor v27.8b, v27.8b, v8.8b *)
  0x3dc004d5;   (* 1468 ldr q21, [x6, #16] *)
  0x6e1542aa;   (* 146c ext v10.16b, v21.16b, v21.16b, #8 *)
  0x0eeae36f;   (* 1470 pmull v15.1q, v27.1d, v10.1d *)
  0x3dc000d4;   (* 1474 ldr q20, [x6] *)
  0x4e200928;   (* 1478 rev64 v8.16b, v9.16b *)
  0x6e200bde;   (* 147c rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 1480 str q30, [x16] *)
  0x6e301d08;   (* 1484 eor v8.16b, v8.16b, v16.16b *)
  0x4c007049;   (* 1488 st1 {v9.16b}, [x2] *)
  0x6e084510;   (* 148c mov v16.d[0], v8.d[1] *)
  0x4ef4e11c;   (* 1490 pmull2 v28.1q, v8.2d, v20.2d *)
  0x0ef4e11a;   (* 1494 pmull v26.1q, v8.1d, v20.1d *)
  0x2e281e10;   (* 1498 eor v16.8b, v16.8b, v8.8b *)
  0x0ef5e210;   (* 149c pmull v16.1q, v16.1d, v21.1d *)
  0xce1c3631;   (* 14a0 eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0xce1a3a73;   (* 14a4 eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0xce103e52;   (* 14a8 eor3 v18.16b, v18.16b, v16.16b, v15.16b *)
  0xfd400150;   (* 14ac ldr d16, [x10] *)
  0x6e114235;   (* 14b0 ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 14b4 eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 14b8 pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 14bc eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 14c0 pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 14c4 ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 14c8 eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x6e134273;   (* 14cc ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200a73;   (* 14d0 rev64 v19.16b, v19.16b *)
  0x4c007073;   (* 14d4 st1 {v19.16b}, [x3] *)
  0x17ffff47;   (* 14d8 b 11f4 <L256_enc_epilogue> *)
  0x54ffe9ec;   (* 14dc b.gt 1218 <L256_enc_exact8_drain> *)
  0xf10080bf;   (* 14e0 cmp x5, #0x20 *)
  0x54000040;   (* 14e4 b.eq 14ec <L256_enc_rem2_drain> // b.none *)
  0x17fffe94;   (* 14e8 b f38 <L256_enc_tail_slides> *)
  0x6ebf87de;   (* 14ec sub v30.4s, v30.4s, v31.4s *)
  0x3dc008d6;   (* 14f0 ldr q22, [x6, #32] *)
  0x6ebf87de;   (* 14f4 sub v30.4s, v30.4s, v31.4s *)
  0x3dc004d5;   (* 14f8 ldr q21, [x6, #16] *)
  0x6ebf87de;   (* 14fc sub v30.4s, v30.4s, v31.4s *)
  0x3dc000d4;   (* 1500 ldr q20, [x6] *)
  0x6ebf87de;   (* 1504 sub v30.4s, v30.4s, v31.4s *)
  0x4c9f7049;   (* 1508 st1 {v9.16b}, [x2], #16 *)
  0x6ebf87de;   (* 150c sub v30.4s, v30.4s, v31.4s *)
  0x4e200928;   (* 1510 rev64 v8.16b, v9.16b *)
  0x6ebf87de;   (* 1514 sub v30.4s, v30.4s, v31.4s *)
  0x6e301d08;   (* 1518 eor v8.16b, v8.16b, v16.16b *)
  0x3cc10409;   (* 151c ldr q9, [x0], #16 *)
  0x6e08411b;   (* 1520 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x6e1542aa;   (* 1524 ext v10.16b, v21.16b, v21.16b, #8 *)
  0x4ef6e10d;   (* 1528 pmull2 v13.1q, v8.2d, v22.2d *)
  0x2e281f7b;   (* 152c eor v27.8b, v27.8b, v8.8b *)
  0x0ef6e10e;   (* 1530 pmull v14.1q, v8.1d, v22.1d *)
  0xce017529;   (* 1534 eor3 v9.16b, v9.16b, v1.16b, v29.16b *)
  0x0eeae36f;   (* 1538 pmull v15.1q, v27.1d, v10.1d *)
  0x4c007049;   (* 153c st1 {v9.16b}, [x2] *)
  0x4e200928;   (* 1540 rev64 v8.16b, v9.16b *)
  0x6e084510;   (* 1544 mov v16.d[0], v8.d[1] *)
  0x4ef4e11c;   (* 1548 pmull2 v28.1q, v8.2d, v20.2d *)
  0x0ef4e11a;   (* 154c pmull v26.1q, v8.1d, v20.1d *)
  0x2e281e10;   (* 1550 eor v16.8b, v16.8b, v8.8b *)
  0x0ef5e210;   (* 1554 pmull v16.1q, v16.1d, v21.1d *)
  0x6e3c1db1;   (* 1558 eor v17.16b, v13.16b, v28.16b *)
  0x6e3a1dd3;   (* 155c eor v19.16b, v14.16b, v26.16b *)
  0x6e301df2;   (* 1560 eor v18.16b, v15.16b, v16.16b *)
  0x6e200bde;   (* 1564 rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 1568 str q30, [x16] *)
  0xfd400150;   (* 156c ldr d16, [x10] *)
  0x6e114235;   (* 1570 ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 1574 eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 1578 pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 157c eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 1580 pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 1584 ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 1588 eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x6e134273;   (* 158c ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200a73;   (* 1590 rev64 v19.16b, v19.16b *)
  0x4c007073;   (* 1594 st1 {v19.16b}, [x3] *)
  0x17ffff17;   (* 1598 b 11f4 <L256_enc_epilogue> *)
  0x6ebf87de;   (* 159c sub v30.4s, v30.4s, v31.4s *)
  0x3dc008d6;   (* 15a0 ldr q22, [x6, #32] *)
  0x6ebf87de;   (* 15a4 sub v30.4s, v30.4s, v31.4s *)
  0x3dc004d5;   (* 15a8 ldr q21, [x6, #16] *)
  0x6ebf87de;   (* 15ac sub v30.4s, v30.4s, v31.4s *)
  0x3dc000d4;   (* 15b0 ldr q20, [x6] *)
  0x6ebf87de;   (* 15b4 sub v30.4s, v30.4s, v31.4s *)
  0x4c9f7049;   (* 15b8 st1 {v9.16b}, [x2], #16 *)
  0x6ebf87de;   (* 15bc sub v30.4s, v30.4s, v31.4s *)
  0x4e200928;   (* 15c0 rev64 v8.16b, v9.16b *)
  0x6ebf87de;   (* 15c4 sub v30.4s, v30.4s, v31.4s *)
  0x6e301d08;   (* 15c8 eor v8.16b, v8.16b, v16.16b *)
  0x3cc10409;   (* 15cc ldr q9, [x0], #16 *)
  0x6e08411b;   (* 15d0 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x6e1542aa;   (* 15d4 ext v10.16b, v21.16b, v21.16b, #8 *)
  0x4ef6e10d;   (* 15d8 pmull2 v13.1q, v8.2d, v22.2d *)
  0x2e281f7b;   (* 15dc eor v27.8b, v27.8b, v8.8b *)
  0x0ef6e10e;   (* 15e0 pmull v14.1q, v8.1d, v22.1d *)
  0xce017529;   (* 15e4 eor3 v9.16b, v9.16b, v1.16b, v29.16b *)
  0x0eeae36f;   (* 15e8 pmull v15.1q, v27.1d, v10.1d *)
  0x4c007049;   (* 15ec st1 {v9.16b}, [x2] *)
  0x4e200928;   (* 15f0 rev64 v8.16b, v9.16b *)
  0x6e084510;   (* 15f4 mov v16.d[0], v8.d[1] *)
  0x4ef4e11c;   (* 15f8 pmull2 v28.1q, v8.2d, v20.2d *)
  0x0ef4e11a;   (* 15fc pmull v26.1q, v8.1d, v20.1d *)
  0x2e281e10;   (* 1600 eor v16.8b, v16.8b, v8.8b *)
  0x0ef5e210;   (* 1604 pmull v16.1q, v16.1d, v21.1d *)
  0x6e3c1db1;   (* 1608 eor v17.16b, v13.16b, v28.16b *)
  0x6e3a1dd3;   (* 160c eor v19.16b, v14.16b, v26.16b *)
  0x6e301df2;   (* 1610 eor v18.16b, v15.16b, v16.16b *)
  0x6e200bde;   (* 1614 rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 1618 str q30, [x16] *)
  0xfd400150;   (* 161c ldr d16, [x10] *)
  0x6e114235;   (* 1620 ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 1624 eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 1628 pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 162c eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 1630 pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 1634 ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 1638 eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x4e190273;   (* 163c tbl v19.16b, {v19.16b}, v25.16b *)
  0x4c007073;   (* 1640 st1 {v19.16b}, [x3] *)
  0x17fffeec;   (* 1644 b 11f4 <L256_enc_epilogue> *)
  0xd281c1e7;   (* 1648 mov x7, #0xe0f // #3599 *)
  0xf2a181a7;   (* 164c movk x7, #0xc0d, lsl #16 *)
  0xf2c14167;   (* 1650 movk x7, #0xa0b, lsl #32 *)
  0xf2e10127;   (* 1654 movk x7, #0x809, lsl #48 *)
  0xd280c0e8;   (* 1658 mov x8, #0x607 // #1543 *)
  0xf2a080a8;   (* 165c movk x8, #0x405, lsl #16 *)
  0xf2c04068;   (* 1660 movk x8, #0x203, lsl #32 *)
  0xf2e00028;   (* 1664 movk x8, #0x1, lsl #48 *)
  0x9e6700f9;   (* 1668 fmov d25, x7 *)
  0x4e181d19;   (* 166c mov v25.d[1], x8 *)
  0x4e284b40;   (* 1670 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1674 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1678 aese v1.16b, v26.16b *)
  0x4e286821;   (* 167c aesmc v1.16b, v1.16b *)
  0xad41697c;   (* 1680 ldp q28, q26, [x11, #32] *)
  0x4e284b60;   (* 1684 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1688 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 168c aese v1.16b, v27.16b *)
  0x4e286821;   (* 1690 aesmc v1.16b, v1.16b *)
  0x4e284b80;   (* 1694 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1698 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 169c aese v1.16b, v28.16b *)
  0x4e286821;   (* 16a0 aesmc v1.16b, v1.16b *)
  0xad42717b;   (* 16a4 ldp q27, q28, [x11, #64] *)
  0x4e284b40;   (* 16a8 aese v0.16b, v26.16b *)
  0x4e286800;   (* 16ac aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 16b0 aese v1.16b, v26.16b *)
  0x4e286821;   (* 16b4 aesmc v1.16b, v1.16b *)
  0x4e284b60;   (* 16b8 aese v0.16b, v27.16b *)
  0x4e286800;   (* 16bc aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 16c0 aese v1.16b, v27.16b *)
  0x4e286821;   (* 16c4 aesmc v1.16b, v1.16b *)
  0xad436d7a;   (* 16c8 ldp q26, q27, [x11, #96] *)
  0x4e284b80;   (* 16cc aese v0.16b, v28.16b *)
  0x4e286800;   (* 16d0 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 16d4 aese v1.16b, v28.16b *)
  0x4e286821;   (* 16d8 aesmc v1.16b, v1.16b *)
  0x4e284b40;   (* 16dc aese v0.16b, v26.16b *)
  0x4e286800;   (* 16e0 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 16e4 aese v1.16b, v26.16b *)
  0x4e286821;   (* 16e8 aesmc v1.16b, v1.16b *)
  0xad44697c;   (* 16ec ldp q28, q26, [x11, #128] *)
  0x4e284b60;   (* 16f0 aese v0.16b, v27.16b *)
  0x4e286800;   (* 16f4 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 16f8 aese v1.16b, v27.16b *)
  0x4e286821;   (* 16fc aesmc v1.16b, v1.16b *)
  0x4e284b80;   (* 1700 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1704 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1708 aese v1.16b, v28.16b *)
  0x4e286821;   (* 170c aesmc v1.16b, v1.16b *)
  0xad45717b;   (* 1710 ldp q27, q28, [x11, #160] *)
  0x4e284b40;   (* 1714 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1718 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 171c aese v1.16b, v26.16b *)
  0x4e286821;   (* 1720 aesmc v1.16b, v1.16b *)
  0x4e284b60;   (* 1724 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1728 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 172c aese v1.16b, v27.16b *)
  0x4e286821;   (* 1730 aesmc v1.16b, v1.16b *)
  0xad466d7a;   (* 1734 ldp q26, q27, [x11, #192] *)
  0x4e284b80;   (* 1738 aese v0.16b, v28.16b *)
  0x4e286800;   (* 173c aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1740 aese v1.16b, v28.16b *)
  0x4e286821;   (* 1744 aesmc v1.16b, v1.16b *)
  0x3dc0397c;   (* 1748 ldr q28, [x11, #224] *)
  0x4e284b40;   (* 174c aese v0.16b, v26.16b *)
  0x4e286800;   (* 1750 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1754 aese v1.16b, v26.16b *)
  0x4e286821;   (* 1758 aesmc v1.16b, v1.16b *)
  0x4e284b60;   (* 175c aese v0.16b, v27.16b *)
  0x4e284b61;   (* 1760 aese v1.16b, v27.16b *)
  0x3cc10408;   (* 1764 ldr q8, [x0], #16 *)
  0x6e134270;   (* 1768 ext v16.16b, v19.16b, v19.16b, #8 *)
  0x4ebc1f9d;   (* 176c mov v29.16b, v28.16b *)
  0xce007509;   (* 1770 eor3 v9.16b, v8.16b, v0.16b, v29.16b *)
  0x17ffff8a;   (* 1774 b 159c <L256_enc_fast2_drain> *)
  0xd281c1e7;   (* 1778 mov x7, #0xe0f // #3599 *)
  0xf2a181a7;   (* 177c movk x7, #0xc0d, lsl #16 *)
  0xf2c14167;   (* 1780 movk x7, #0xa0b, lsl #32 *)
  0xf2e10127;   (* 1784 movk x7, #0x809, lsl #48 *)
  0xd280c0e8;   (* 1788 mov x8, #0x607 // #1543 *)
  0xf2a080a8;   (* 178c movk x8, #0x405, lsl #16 *)
  0xf2c04068;   (* 1790 movk x8, #0x203, lsl #32 *)
  0xf2e00028;   (* 1794 movk x8, #0x1, lsl #48 *)
  0x9e6700ec;   (* 1798 fmov d12, x7 *)
  0x4e181d0c;   (* 179c mov v12.d[1], x8 *)
  0x4e284b40;   (* 17a0 aese v0.16b, v26.16b *)
  0x4e286800;   (* 17a4 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 17a8 aese v1.16b, v26.16b *)
  0x4e286821;   (* 17ac aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 17b0 aese v2.16b, v26.16b *)
  0x4e286842;   (* 17b4 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 17b8 aese v3.16b, v26.16b *)
  0x4e286863;   (* 17bc aesmc v3.16b, v3.16b *)
  0xad41697c;   (* 17c0 ldp q28, q26, [x11, #32] *)
  0x4e284b60;   (* 17c4 aese v0.16b, v27.16b *)
  0x4e286800;   (* 17c8 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 17cc aese v1.16b, v27.16b *)
  0x4e286821;   (* 17d0 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 17d4 aese v2.16b, v27.16b *)
  0x4e286842;   (* 17d8 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 17dc aese v3.16b, v27.16b *)
  0x4e286863;   (* 17e0 aesmc v3.16b, v3.16b *)
  0x4e284b80;   (* 17e4 aese v0.16b, v28.16b *)
  0x4e286800;   (* 17e8 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 17ec aese v1.16b, v28.16b *)
  0x4e286821;   (* 17f0 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 17f4 aese v2.16b, v28.16b *)
  0x4e286842;   (* 17f8 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 17fc aese v3.16b, v28.16b *)
  0x4e286863;   (* 1800 aesmc v3.16b, v3.16b *)
  0xad42717b;   (* 1804 ldp q27, q28, [x11, #64] *)
  0x4e284b40;   (* 1808 aese v0.16b, v26.16b *)
  0x4e286800;   (* 180c aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1810 aese v1.16b, v26.16b *)
  0x4e286821;   (* 1814 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1818 aese v2.16b, v26.16b *)
  0x4e286842;   (* 181c aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 1820 aese v3.16b, v26.16b *)
  0x4e286863;   (* 1824 aesmc v3.16b, v3.16b *)
  0x4e284b60;   (* 1828 aese v0.16b, v27.16b *)
  0x4e286800;   (* 182c aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 1830 aese v1.16b, v27.16b *)
  0x4e286821;   (* 1834 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 1838 aese v2.16b, v27.16b *)
  0x4e286842;   (* 183c aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 1840 aese v3.16b, v27.16b *)
  0x4e286863;   (* 1844 aesmc v3.16b, v3.16b *)
  0xad436d7a;   (* 1848 ldp q26, q27, [x11, #96] *)
  0x4e284b80;   (* 184c aese v0.16b, v28.16b *)
  0x4e286800;   (* 1850 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1854 aese v1.16b, v28.16b *)
  0x4e286821;   (* 1858 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 185c aese v2.16b, v28.16b *)
  0x4e286842;   (* 1860 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 1864 aese v3.16b, v28.16b *)
  0x4e286863;   (* 1868 aesmc v3.16b, v3.16b *)
  0x4e284b40;   (* 186c aese v0.16b, v26.16b *)
  0x4e286800;   (* 1870 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1874 aese v1.16b, v26.16b *)
  0x4e286821;   (* 1878 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 187c aese v2.16b, v26.16b *)
  0x4e286842;   (* 1880 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 1884 aese v3.16b, v26.16b *)
  0x4e286863;   (* 1888 aesmc v3.16b, v3.16b *)
  0xad44697c;   (* 188c ldp q28, q26, [x11, #128] *)
  0x4e284b60;   (* 1890 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1894 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 1898 aese v1.16b, v27.16b *)
  0x4e286821;   (* 189c aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 18a0 aese v2.16b, v27.16b *)
  0x4e286842;   (* 18a4 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 18a8 aese v3.16b, v27.16b *)
  0x4e286863;   (* 18ac aesmc v3.16b, v3.16b *)
  0x4e284b80;   (* 18b0 aese v0.16b, v28.16b *)
  0x4e286800;   (* 18b4 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 18b8 aese v1.16b, v28.16b *)
  0x4e286821;   (* 18bc aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 18c0 aese v2.16b, v28.16b *)
  0x4e286842;   (* 18c4 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 18c8 aese v3.16b, v28.16b *)
  0x4e286863;   (* 18cc aesmc v3.16b, v3.16b *)
  0xad45717b;   (* 18d0 ldp q27, q28, [x11, #160] *)
  0x4e284b40;   (* 18d4 aese v0.16b, v26.16b *)
  0x4e286800;   (* 18d8 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 18dc aese v1.16b, v26.16b *)
  0x4e286821;   (* 18e0 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 18e4 aese v2.16b, v26.16b *)
  0x4e286842;   (* 18e8 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 18ec aese v3.16b, v26.16b *)
  0x4e286863;   (* 18f0 aesmc v3.16b, v3.16b *)
  0x4e284b60;   (* 18f4 aese v0.16b, v27.16b *)
  0x4e286800;   (* 18f8 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 18fc aese v1.16b, v27.16b *)
  0x4e286821;   (* 1900 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 1904 aese v2.16b, v27.16b *)
  0x4e286842;   (* 1908 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 190c aese v3.16b, v27.16b *)
  0x4e286863;   (* 1910 aesmc v3.16b, v3.16b *)
  0xad466d7a;   (* 1914 ldp q26, q27, [x11, #192] *)
  0x4e284b80;   (* 1918 aese v0.16b, v28.16b *)
  0x4e286800;   (* 191c aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1920 aese v1.16b, v28.16b *)
  0x4e286821;   (* 1924 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 1928 aese v2.16b, v28.16b *)
  0x4e286842;   (* 192c aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 1930 aese v3.16b, v28.16b *)
  0x4e286863;   (* 1934 aesmc v3.16b, v3.16b *)
  0x3dc0397c;   (* 1938 ldr q28, [x11, #224] *)
  0x4e284b40;   (* 193c aese v0.16b, v26.16b *)
  0x4e286800;   (* 1940 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1944 aese v1.16b, v26.16b *)
  0x4e286821;   (* 1948 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 194c aese v2.16b, v26.16b *)
  0x4e286842;   (* 1950 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 1954 aese v3.16b, v26.16b *)
  0x4e286863;   (* 1958 aesmc v3.16b, v3.16b *)
  0x4e284b60;   (* 195c aese v0.16b, v27.16b *)
  0x4e284b61;   (* 1960 aese v1.16b, v27.16b *)
  0x4e284b62;   (* 1964 aese v2.16b, v27.16b *)
  0x4e284b63;   (* 1968 aese v3.16b, v27.16b *)
  0x3cc10408;   (* 196c ldr q8, [x0], #16 *)
  0x6e134270;   (* 1970 ext v16.16b, v19.16b, v19.16b, #8 *)
  0x4ebc1f9d;   (* 1974 mov v29.16b, v28.16b *)
  0x6ebf87de;   (* 1978 sub v30.4s, v30.4s, v31.4s *)
  0x6ebf87de;   (* 197c sub v30.4s, v30.4s, v31.4s *)
  0x6ebf87de;   (* 1980 sub v30.4s, v30.4s, v31.4s *)
  0x6ebf87de;   (* 1984 sub v30.4s, v30.4s, v31.4s *)
  0x0f00e411;   (* 1988 movi v17.8b, #0x0 *)
  0x0f00e412;   (* 198c movi v18.8b, #0x0 *)
  0x0f00e413;   (* 1990 movi v19.8b, #0x0 *)
  0xce007509;   (* 1994 eor3 v9.16b, v8.16b, v0.16b, v29.16b *)
  0x14000001;   (* 1998 b 199c <L256_enc_fast4_drain> *)
  0x4c9f7049;   (* 199c st1 {v9.16b}, [x2], #16 *)
  0x3dc014d9;   (* 19a0 ldr q25, [x6, #80] *)
  0x4e200928;   (* 19a4 rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* 19a8 eor v8.16b, v8.16b, v16.16b *)
  0x6e08411b;   (* 19ac ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef9e10d;   (* 19b0 pmull2 v13.1q, v8.2d, v25.2d *)
  0x3dc010d8;   (* 19b4 ldr q24, [x6, #64] *)
  0x6e18430b;   (* 19b8 ext v11.16b, v24.16b, v24.16b, #8 *)
  0x2e281f7b;   (* 19bc eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 19c0 ldr q9, [x0], #16 *)
  0x0eebe36f;   (* 19c4 pmull v15.1q, v27.1d, v11.1d *)
  0x0ef9e10e;   (* 19c8 pmull v14.1q, v8.1d, v25.1d *)
  0xce017529;   (* 19cc eor3 v9.16b, v9.16b, v1.16b, v29.16b *)
  0x4c9f7049;   (* 19d0 st1 {v9.16b}, [x2], #16 *)
  0x3dc00cd7;   (* 19d4 ldr q23, [x6, #48] *)
  0x4e200928;   (* 19d8 rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 19dc ldr q9, [x0], #16 *)
  0x6e08411b;   (* 19e0 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef7e11c;   (* 19e4 pmull2 v28.1q, v8.2d, v23.2d *)
  0xce027529;   (* 19e8 eor3 v9.16b, v9.16b, v2.16b, v29.16b *)
  0x2e281f7b;   (* 19ec eor v27.8b, v27.8b, v8.8b *)
  0x0ef7e11a;   (* 19f0 pmull v26.1q, v8.1d, v23.1d *)
  0x0ef8e37b;   (* 19f4 pmull v27.1q, v27.1d, v24.1d *)
  0xce1c3631;   (* 19f8 eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0xce1a3a73;   (* 19fc eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0xce1b3e52;   (* 1a00 eor3 v18.16b, v18.16b, v27.16b, v15.16b *)
  0x4c9f7049;   (* 1a04 st1 {v9.16b}, [x2], #16 *)
  0x3dc008d6;   (* 1a08 ldr q22, [x6, #32] *)
  0x4e200928;   (* 1a0c rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 1a10 ldr q9, [x0], #16 *)
  0x6e08411b;   (* 1a14 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef6e10d;   (* 1a18 pmull2 v13.1q, v8.2d, v22.2d *)
  0xce037529;   (* 1a1c eor3 v9.16b, v9.16b, v3.16b, v29.16b *)
  0x0ef6e10e;   (* 1a20 pmull v14.1q, v8.1d, v22.1d *)
  0x2e281f7b;   (* 1a24 eor v27.8b, v27.8b, v8.8b *)
  0x3dc004d5;   (* 1a28 ldr q21, [x6, #16] *)
  0x6e1542aa;   (* 1a2c ext v10.16b, v21.16b, v21.16b, #8 *)
  0x0eeae36f;   (* 1a30 pmull v15.1q, v27.1d, v10.1d *)
  0x3dc000d4;   (* 1a34 ldr q20, [x6] *)
  0x4e200928;   (* 1a38 rev64 v8.16b, v9.16b *)
  0x6e200bde;   (* 1a3c rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 1a40 str q30, [x16] *)
  0x4c007049;   (* 1a44 st1 {v9.16b}, [x2] *)
  0x6e084510;   (* 1a48 mov v16.d[0], v8.d[1] *)
  0x4ef4e11c;   (* 1a4c pmull2 v28.1q, v8.2d, v20.2d *)
  0x0ef4e11a;   (* 1a50 pmull v26.1q, v8.1d, v20.1d *)
  0x2e281e10;   (* 1a54 eor v16.8b, v16.8b, v8.8b *)
  0x0ef5e210;   (* 1a58 pmull v16.1q, v16.1d, v21.1d *)
  0xce1c3631;   (* 1a5c eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0xce1a3a73;   (* 1a60 eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0xce103e52;   (* 1a64 eor3 v18.16b, v18.16b, v16.16b, v15.16b *)
  0xfd400150;   (* 1a68 ldr d16, [x10] *)
  0x6e114235;   (* 1a6c ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 1a70 eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 1a74 pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 1a78 eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 1a7c pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 1a80 ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 1a84 eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x4e0c0273;   (* 1a88 tbl v19.16b, {v19.16b}, v12.16b *)
  0x4c007073;   (* 1a8c st1 {v19.16b}, [x3] *)
  0x17fffdd9;   (* 1a90 b 11f4 <L256_enc_epilogue> *)
  0xd281c1e7;   (* 1a94 mov x7, #0xe0f // #3599 *)
  0xf2a181a7;   (* 1a98 movk x7, #0xc0d, lsl #16 *)
  0xf2c14167;   (* 1a9c movk x7, #0xa0b, lsl #32 *)
  0xf2e10127;   (* 1aa0 movk x7, #0x809, lsl #48 *)
  0xd280c0e8;   (* 1aa4 mov x8, #0x607 // #1543 *)
  0xf2a080a8;   (* 1aa8 movk x8, #0x405, lsl #16 *)
  0xf2c04068;   (* 1aac movk x8, #0x203, lsl #32 *)
  0xf2e00028;   (* 1ab0 movk x8, #0x1, lsl #48 *)
  0x9e6700f9;   (* 1ab4 fmov d25, x7 *)
  0x4e181d19;   (* 1ab8 mov v25.d[1], x8 *)
  0x4e284b40;   (* 1abc aese v0.16b, v26.16b *)
  0x4e286800;   (* 1ac0 aesmc v0.16b, v0.16b *)
  0xad41697c;   (* 1ac4 ldp q28, q26, [x11, #32] *)
  0x4e284b60;   (* 1ac8 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1acc aesmc v0.16b, v0.16b *)
  0x4e284b80;   (* 1ad0 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1ad4 aesmc v0.16b, v0.16b *)
  0xad42717b;   (* 1ad8 ldp q27, q28, [x11, #64] *)
  0x4e284b40;   (* 1adc aese v0.16b, v26.16b *)
  0x4e286800;   (* 1ae0 aesmc v0.16b, v0.16b *)
  0x4e284b60;   (* 1ae4 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1ae8 aesmc v0.16b, v0.16b *)
  0xad436d7a;   (* 1aec ldp q26, q27, [x11, #96] *)
  0x4e284b80;   (* 1af0 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1af4 aesmc v0.16b, v0.16b *)
  0x4e284b40;   (* 1af8 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1afc aesmc v0.16b, v0.16b *)
  0xad44697c;   (* 1b00 ldp q28, q26, [x11, #128] *)
  0x4e284b60;   (* 1b04 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1b08 aesmc v0.16b, v0.16b *)
  0x4e284b80;   (* 1b0c aese v0.16b, v28.16b *)
  0x4e286800;   (* 1b10 aesmc v0.16b, v0.16b *)
  0xad45717b;   (* 1b14 ldp q27, q28, [x11, #160] *)
  0x4e284b40;   (* 1b18 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1b1c aesmc v0.16b, v0.16b *)
  0x4e284b60;   (* 1b20 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1b24 aesmc v0.16b, v0.16b *)
  0xad466d7a;   (* 1b28 ldp q26, q27, [x11, #192] *)
  0x4e284b80;   (* 1b2c aese v0.16b, v28.16b *)
  0x4e286800;   (* 1b30 aesmc v0.16b, v0.16b *)
  0x3dc0397c;   (* 1b34 ldr q28, [x11, #224] *)
  0x4e284b40;   (* 1b38 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1b3c aesmc v0.16b, v0.16b *)
  0x4e284b60;   (* 1b40 aese v0.16b, v27.16b *)
  0x3dc00008;   (* 1b44 ldr q8, [x0] *)
  0x6e134270;   (* 1b48 ext v16.16b, v19.16b, v19.16b, #8 *)
  0x4ebc1f9d;   (* 1b4c mov v29.16b, v28.16b *)
  0xce007509;   (* 1b50 eor3 v9.16b, v8.16b, v0.16b, v29.16b *)
  0x6ebf87de;   (* 1b54 sub v30.4s, v30.4s, v31.4s *)
  0x3dc000d4;   (* 1b58 ldr q20, [x6] *)
  0x6ebf87de;   (* 1b5c sub v30.4s, v30.4s, v31.4s *)
  0x3dc004d5;   (* 1b60 ldr q21, [x6, #16] *)
  0x6ebf87de;   (* 1b64 sub v30.4s, v30.4s, v31.4s *)
  0x4e200928;   (* 1b68 rev64 v8.16b, v9.16b *)
  0x6ebf87de;   (* 1b6c sub v30.4s, v30.4s, v31.4s *)
  0x6e301d08;   (* 1b70 eor v8.16b, v8.16b, v16.16b *)
  0x6ebf87de;   (* 1b74 sub v30.4s, v30.4s, v31.4s *)
  0x4c007049;   (* 1b78 st1 {v9.16b}, [x2] *)
  0x6ebf87de;   (* 1b7c sub v30.4s, v30.4s, v31.4s *)
  0x6e084510;   (* 1b80 mov v16.d[0], v8.d[1] *)
  0x6ebf87de;   (* 1b84 sub v30.4s, v30.4s, v31.4s *)
  0x4ef4e111;   (* 1b88 pmull2 v17.1q, v8.2d, v20.2d *)
  0x0ef4e113;   (* 1b8c pmull v19.1q, v8.1d, v20.1d *)
  0x2e281e10;   (* 1b90 eor v16.8b, v16.8b, v8.8b *)
  0x0ef5e212;   (* 1b94 pmull v18.1q, v16.1d, v21.1d *)
  0x6e200bde;   (* 1b98 rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 1b9c str q30, [x16] *)
  0xfd400150;   (* 1ba0 ldr d16, [x10] *)
  0x6e114235;   (* 1ba4 ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 1ba8 eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 1bac pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 1bb0 eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 1bb4 pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 1bb8 ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 1bbc eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x4e190273;   (* 1bc0 tbl v19.16b, {v19.16b}, v25.16b *)
  0x4c007073;   (* 1bc4 st1 {v19.16b}, [x3] *)
  0x17fffd8b;   (* 1bc8 b 11f4 <L256_enc_epilogue> *)
  0xd281c1e7;   (* 1bcc mov x7, #0xe0f // #3599 *)
  0xf2a181a7;   (* 1bd0 movk x7, #0xc0d, lsl #16 *)
  0xf2c14167;   (* 1bd4 movk x7, #0xa0b, lsl #32 *)
  0xf2e10127;   (* 1bd8 movk x7, #0x809, lsl #48 *)
  0xd280c0e8;   (* 1bdc mov x8, #0x607 // #1543 *)
  0xf2a080a8;   (* 1be0 movk x8, #0x405, lsl #16 *)
  0xf2c04068;   (* 1be4 movk x8, #0x203, lsl #32 *)
  0xf2e00028;   (* 1be8 movk x8, #0x1, lsl #48 *)
  0x9e6700f9;   (* 1bec fmov d25, x7 *)
  0x4e181d19;   (* 1bf0 mov v25.d[1], x8 *)
  0x4e284b40;   (* 1bf4 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1bf8 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1bfc aese v1.16b, v26.16b *)
  0x4e286821;   (* 1c00 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1c04 aese v2.16b, v26.16b *)
  0x4e286842;   (* 1c08 aesmc v2.16b, v2.16b *)
  0xad41697c;   (* 1c0c ldp q28, q26, [x11, #32] *)
  0x4e284b60;   (* 1c10 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1c14 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 1c18 aese v1.16b, v27.16b *)
  0x4e286821;   (* 1c1c aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 1c20 aese v2.16b, v27.16b *)
  0x4e286842;   (* 1c24 aesmc v2.16b, v2.16b *)
  0x4e284b80;   (* 1c28 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1c2c aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1c30 aese v1.16b, v28.16b *)
  0x4e286821;   (* 1c34 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 1c38 aese v2.16b, v28.16b *)
  0x4e286842;   (* 1c3c aesmc v2.16b, v2.16b *)
  0xad42717b;   (* 1c40 ldp q27, q28, [x11, #64] *)
  0x4e284b40;   (* 1c44 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1c48 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1c4c aese v1.16b, v26.16b *)
  0x4e286821;   (* 1c50 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1c54 aese v2.16b, v26.16b *)
  0x4e286842;   (* 1c58 aesmc v2.16b, v2.16b *)
  0x4e284b60;   (* 1c5c aese v0.16b, v27.16b *)
  0x4e286800;   (* 1c60 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 1c64 aese v1.16b, v27.16b *)
  0x4e286821;   (* 1c68 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 1c6c aese v2.16b, v27.16b *)
  0x4e286842;   (* 1c70 aesmc v2.16b, v2.16b *)
  0xad436d7a;   (* 1c74 ldp q26, q27, [x11, #96] *)
  0x4e284b80;   (* 1c78 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1c7c aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1c80 aese v1.16b, v28.16b *)
  0x4e286821;   (* 1c84 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 1c88 aese v2.16b, v28.16b *)
  0x4e286842;   (* 1c8c aesmc v2.16b, v2.16b *)
  0x4e284b40;   (* 1c90 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1c94 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1c98 aese v1.16b, v26.16b *)
  0x4e286821;   (* 1c9c aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1ca0 aese v2.16b, v26.16b *)
  0x4e286842;   (* 1ca4 aesmc v2.16b, v2.16b *)
  0xad44697c;   (* 1ca8 ldp q28, q26, [x11, #128] *)
  0x4e284b60;   (* 1cac aese v0.16b, v27.16b *)
  0x4e286800;   (* 1cb0 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 1cb4 aese v1.16b, v27.16b *)
  0x4e286821;   (* 1cb8 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 1cbc aese v2.16b, v27.16b *)
  0x4e286842;   (* 1cc0 aesmc v2.16b, v2.16b *)
  0x4e284b80;   (* 1cc4 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1cc8 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1ccc aese v1.16b, v28.16b *)
  0x4e286821;   (* 1cd0 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 1cd4 aese v2.16b, v28.16b *)
  0x4e286842;   (* 1cd8 aesmc v2.16b, v2.16b *)
  0xad45717b;   (* 1cdc ldp q27, q28, [x11, #160] *)
  0x4e284b40;   (* 1ce0 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1ce4 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1ce8 aese v1.16b, v26.16b *)
  0x4e286821;   (* 1cec aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1cf0 aese v2.16b, v26.16b *)
  0x4e286842;   (* 1cf4 aesmc v2.16b, v2.16b *)
  0x4e284b60;   (* 1cf8 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1cfc aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 1d00 aese v1.16b, v27.16b *)
  0x4e286821;   (* 1d04 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 1d08 aese v2.16b, v27.16b *)
  0x4e286842;   (* 1d0c aesmc v2.16b, v2.16b *)
  0xad466d7a;   (* 1d10 ldp q26, q27, [x11, #192] *)
  0x4e284b80;   (* 1d14 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1d18 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1d1c aese v1.16b, v28.16b *)
  0x4e286821;   (* 1d20 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 1d24 aese v2.16b, v28.16b *)
  0x4e286842;   (* 1d28 aesmc v2.16b, v2.16b *)
  0x3dc0397c;   (* 1d2c ldr q28, [x11, #224] *)
  0x4e284b40;   (* 1d30 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1d34 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1d38 aese v1.16b, v26.16b *)
  0x4e286821;   (* 1d3c aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1d40 aese v2.16b, v26.16b *)
  0x4e286842;   (* 1d44 aesmc v2.16b, v2.16b *)
  0x4e284b60;   (* 1d48 aese v0.16b, v27.16b *)
  0x4e284b61;   (* 1d4c aese v1.16b, v27.16b *)
  0x4e284b62;   (* 1d50 aese v2.16b, v27.16b *)
  0x3cc10408;   (* 1d54 ldr q8, [x0], #16 *)
  0x6e134270;   (* 1d58 ext v16.16b, v19.16b, v19.16b, #8 *)
  0x4ebc1f9d;   (* 1d5c mov v29.16b, v28.16b *)
  0x6ebf87de;   (* 1d60 sub v30.4s, v30.4s, v31.4s *)
  0x6ebf87de;   (* 1d64 sub v30.4s, v30.4s, v31.4s *)
  0x6ebf87de;   (* 1d68 sub v30.4s, v30.4s, v31.4s *)
  0x6ebf87de;   (* 1d6c sub v30.4s, v30.4s, v31.4s *)
  0x6ebf87de;   (* 1d70 sub v30.4s, v30.4s, v31.4s *)
  0xce007509;   (* 1d74 eor3 v9.16b, v8.16b, v0.16b, v29.16b *)
  0x4c9f7049;   (* 1d78 st1 {v9.16b}, [x2], #16 *)
  0x3dc00cd7;   (* 1d7c ldr q23, [x6, #48] *)
  0x4e200928;   (* 1d80 rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* 1d84 eor v8.16b, v8.16b, v16.16b *)
  0x3dc010d8;   (* 1d88 ldr q24, [x6, #64] *)
  0x6e08411b;   (* 1d8c ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef7e10d;   (* 1d90 pmull2 v13.1q, v8.2d, v23.2d *)
  0x2e281f7b;   (* 1d94 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 1d98 ldr q9, [x0], #16 *)
  0x0ef7e10e;   (* 1d9c pmull v14.1q, v8.1d, v23.1d *)
  0x0ef8e36f;   (* 1da0 pmull v15.1q, v27.1d, v24.1d *)
  0xce017529;   (* 1da4 eor3 v9.16b, v9.16b, v1.16b, v29.16b *)
  0x4c9f7049;   (* 1da8 st1 {v9.16b}, [x2], #16 *)
  0x3dc008d6;   (* 1dac ldr q22, [x6, #32] *)
  0x4e200928;   (* 1db0 rev64 v8.16b, v9.16b *)
  0x3cc10409;   (* 1db4 ldr q9, [x0], #16 *)
  0x6e08411b;   (* 1db8 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x4ef6e11c;   (* 1dbc pmull2 v28.1q, v8.2d, v22.2d *)
  0xce027529;   (* 1dc0 eor3 v9.16b, v9.16b, v2.16b, v29.16b *)
  0x2e281f7b;   (* 1dc4 eor v27.8b, v27.8b, v8.8b *)
  0x0ef6e11a;   (* 1dc8 pmull v26.1q, v8.1d, v22.1d *)
  0x3dc004d5;   (* 1dcc ldr q21, [x6, #16] *)
  0x6e1542aa;   (* 1dd0 ext v10.16b, v21.16b, v21.16b, #8 *)
  0x0eeae37b;   (* 1dd4 pmull v27.1q, v27.1d, v10.1d *)
  0x6e2d1f91;   (* 1dd8 eor v17.16b, v28.16b, v13.16b *)
  0x6e2e1f53;   (* 1ddc eor v19.16b, v26.16b, v14.16b *)
  0x6e2f1f72;   (* 1de0 eor v18.16b, v27.16b, v15.16b *)
  0x3dc000d4;   (* 1de4 ldr q20, [x6] *)
  0x4e200928;   (* 1de8 rev64 v8.16b, v9.16b *)
  0x6e200bde;   (* 1dec rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 1df0 str q30, [x16] *)
  0x4c007049;   (* 1df4 st1 {v9.16b}, [x2] *)
  0x6e084510;   (* 1df8 mov v16.d[0], v8.d[1] *)
  0x4ef4e11c;   (* 1dfc pmull2 v28.1q, v8.2d, v20.2d *)
  0x0ef4e11a;   (* 1e00 pmull v26.1q, v8.1d, v20.1d *)
  0x2e281e10;   (* 1e04 eor v16.8b, v16.8b, v8.8b *)
  0x0ef5e210;   (* 1e08 pmull v16.1q, v16.1d, v21.1d *)
  0x6e3c1e31;   (* 1e0c eor v17.16b, v17.16b, v28.16b *)
  0x6e3a1e73;   (* 1e10 eor v19.16b, v19.16b, v26.16b *)
  0x6e301e52;   (* 1e14 eor v18.16b, v18.16b, v16.16b *)
  0xfd400150;   (* 1e18 ldr d16, [x10] *)
  0x6e114235;   (* 1e1c ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 1e20 eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 1e24 pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 1e28 eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 1e2c pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 1e30 ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 1e34 eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x4e190273;   (* 1e38 tbl v19.16b, {v19.16b}, v25.16b *)
  0x4c007073;   (* 1e3c st1 {v19.16b}, [x3] *)
  0x17fffced;   (* 1e40 b 11f4 <L256_enc_epilogue> *)
  0x4e284b40;   (* 1e44 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1e48 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1e4c aese v1.16b, v26.16b *)
  0x4e286821;   (* 1e50 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1e54 aese v2.16b, v26.16b *)
  0x4e286842;   (* 1e58 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 1e5c aese v3.16b, v26.16b *)
  0x4e286863;   (* 1e60 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 1e64 aese v4.16b, v26.16b *)
  0x4e286884;   (* 1e68 aesmc v4.16b, v4.16b *)
  0xad41697c;   (* 1e6c ldp q28, q26, [x11, #32] *)
  0x4e284b60;   (* 1e70 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1e74 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 1e78 aese v1.16b, v27.16b *)
  0x4e286821;   (* 1e7c aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 1e80 aese v2.16b, v27.16b *)
  0x4e286842;   (* 1e84 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 1e88 aese v3.16b, v27.16b *)
  0x4e286863;   (* 1e8c aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 1e90 aese v4.16b, v27.16b *)
  0x4e286884;   (* 1e94 aesmc v4.16b, v4.16b *)
  0x4e284b80;   (* 1e98 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1e9c aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1ea0 aese v1.16b, v28.16b *)
  0x4e286821;   (* 1ea4 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 1ea8 aese v2.16b, v28.16b *)
  0x4e286842;   (* 1eac aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 1eb0 aese v3.16b, v28.16b *)
  0x4e286863;   (* 1eb4 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 1eb8 aese v4.16b, v28.16b *)
  0x4e286884;   (* 1ebc aesmc v4.16b, v4.16b *)
  0xad42717b;   (* 1ec0 ldp q27, q28, [x11, #64] *)
  0x4e284b40;   (* 1ec4 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1ec8 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1ecc aese v1.16b, v26.16b *)
  0x4e286821;   (* 1ed0 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1ed4 aese v2.16b, v26.16b *)
  0x4e286842;   (* 1ed8 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 1edc aese v3.16b, v26.16b *)
  0x4e286863;   (* 1ee0 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 1ee4 aese v4.16b, v26.16b *)
  0x4e286884;   (* 1ee8 aesmc v4.16b, v4.16b *)
  0x4e284b60;   (* 1eec aese v0.16b, v27.16b *)
  0x4e286800;   (* 1ef0 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 1ef4 aese v1.16b, v27.16b *)
  0x4e286821;   (* 1ef8 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 1efc aese v2.16b, v27.16b *)
  0x4e286842;   (* 1f00 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 1f04 aese v3.16b, v27.16b *)
  0x4e286863;   (* 1f08 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 1f0c aese v4.16b, v27.16b *)
  0x4e286884;   (* 1f10 aesmc v4.16b, v4.16b *)
  0xad436d7a;   (* 1f14 ldp q26, q27, [x11, #96] *)
  0x4e284b80;   (* 1f18 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1f1c aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1f20 aese v1.16b, v28.16b *)
  0x4e286821;   (* 1f24 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 1f28 aese v2.16b, v28.16b *)
  0x4e286842;   (* 1f2c aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 1f30 aese v3.16b, v28.16b *)
  0x4e286863;   (* 1f34 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 1f38 aese v4.16b, v28.16b *)
  0x4e286884;   (* 1f3c aesmc v4.16b, v4.16b *)
  0x4e284b40;   (* 1f40 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1f44 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1f48 aese v1.16b, v26.16b *)
  0x4e286821;   (* 1f4c aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1f50 aese v2.16b, v26.16b *)
  0x4e286842;   (* 1f54 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 1f58 aese v3.16b, v26.16b *)
  0x4e286863;   (* 1f5c aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 1f60 aese v4.16b, v26.16b *)
  0x4e286884;   (* 1f64 aesmc v4.16b, v4.16b *)
  0xad44697c;   (* 1f68 ldp q28, q26, [x11, #128] *)
  0x4e284b60;   (* 1f6c aese v0.16b, v27.16b *)
  0x4e286800;   (* 1f70 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 1f74 aese v1.16b, v27.16b *)
  0x4e286821;   (* 1f78 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 1f7c aese v2.16b, v27.16b *)
  0x4e286842;   (* 1f80 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 1f84 aese v3.16b, v27.16b *)
  0x4e286863;   (* 1f88 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 1f8c aese v4.16b, v27.16b *)
  0x4e286884;   (* 1f90 aesmc v4.16b, v4.16b *)
  0x4e284b80;   (* 1f94 aese v0.16b, v28.16b *)
  0x4e286800;   (* 1f98 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 1f9c aese v1.16b, v28.16b *)
  0x4e286821;   (* 1fa0 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 1fa4 aese v2.16b, v28.16b *)
  0x4e286842;   (* 1fa8 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 1fac aese v3.16b, v28.16b *)
  0x4e286863;   (* 1fb0 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 1fb4 aese v4.16b, v28.16b *)
  0x4e286884;   (* 1fb8 aesmc v4.16b, v4.16b *)
  0xad45717b;   (* 1fbc ldp q27, q28, [x11, #160] *)
  0x4e284b40;   (* 1fc0 aese v0.16b, v26.16b *)
  0x4e286800;   (* 1fc4 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 1fc8 aese v1.16b, v26.16b *)
  0x4e286821;   (* 1fcc aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 1fd0 aese v2.16b, v26.16b *)
  0x4e286842;   (* 1fd4 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 1fd8 aese v3.16b, v26.16b *)
  0x4e286863;   (* 1fdc aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 1fe0 aese v4.16b, v26.16b *)
  0x4e286884;   (* 1fe4 aesmc v4.16b, v4.16b *)
  0x4e284b60;   (* 1fe8 aese v0.16b, v27.16b *)
  0x4e286800;   (* 1fec aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 1ff0 aese v1.16b, v27.16b *)
  0x4e286821;   (* 1ff4 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 1ff8 aese v2.16b, v27.16b *)
  0x4e286842;   (* 1ffc aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 2000 aese v3.16b, v27.16b *)
  0x4e286863;   (* 2004 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 2008 aese v4.16b, v27.16b *)
  0x4e286884;   (* 200c aesmc v4.16b, v4.16b *)
  0xad466d7a;   (* 2010 ldp q26, q27, [x11, #192] *)
  0x4e284b80;   (* 2014 aese v0.16b, v28.16b *)
  0x4e286800;   (* 2018 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 201c aese v1.16b, v28.16b *)
  0x4e286821;   (* 2020 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 2024 aese v2.16b, v28.16b *)
  0x4e286842;   (* 2028 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 202c aese v3.16b, v28.16b *)
  0x4e286863;   (* 2030 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 2034 aese v4.16b, v28.16b *)
  0x4e286884;   (* 2038 aesmc v4.16b, v4.16b *)
  0x4e284b40;   (* 203c aese v0.16b, v26.16b *)
  0x4e286800;   (* 2040 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 2044 aese v1.16b, v26.16b *)
  0x4e286821;   (* 2048 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 204c aese v2.16b, v26.16b *)
  0x4e286842;   (* 2050 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 2054 aese v3.16b, v26.16b *)
  0x4e286863;   (* 2058 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 205c aese v4.16b, v26.16b *)
  0x4e286884;   (* 2060 aesmc v4.16b, v4.16b *)
  0x3dc0397c;   (* 2064 ldr q28, [x11, #224] *)
  0x4e284b60;   (* 2068 aese v0.16b, v27.16b *)
  0x4e284b61;   (* 206c aese v1.16b, v27.16b *)
  0x4e284b62;   (* 2070 aese v2.16b, v27.16b *)
  0x4e284b63;   (* 2074 aese v3.16b, v27.16b *)
  0x4e284b64;   (* 2078 aese v4.16b, v27.16b *)
  0x3cc10408;   (* 207c ldr q8, [x0], #16 *)
  0x6e134270;   (* 2080 ext v16.16b, v19.16b, v19.16b, #8 *)
  0x4ebc1f9d;   (* 2084 mov v29.16b, v28.16b *)
  0x6ebf87de;   (* 2088 sub v30.4s, v30.4s, v31.4s *)
  0x6ebf87de;   (* 208c sub v30.4s, v30.4s, v31.4s *)
  0x6ebf87de;   (* 2090 sub v30.4s, v30.4s, v31.4s *)
  0xce007509;   (* 2094 eor3 v9.16b, v8.16b, v0.16b, v29.16b *)
  0x4c9f7049;   (* 2098 st1 {v9.16b}, [x2], #16 *)
  0x3dc018d9;   (* 209c ldr q25, [x6, #96] *)
  0x4e200928;   (* 20a0 rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* 20a4 eor v8.16b, v8.16b, v16.16b *)
  0x6e08411b;   (* 20a8 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc01cd8;   (* 20ac ldr q24, [x6, #112] *)
  0x2e281f7b;   (* 20b0 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 20b4 ldr q9, [x0], #16 *)
  0x4ef9e10d;   (* 20b8 pmull2 v13.1q, v8.2d, v25.2d *)
  0x0ef9e10e;   (* 20bc pmull v14.1q, v8.1d, v25.1d *)
  0x0ef8e36f;   (* 20c0 pmull v15.1q, v27.1d, v24.1d *)
  0xce017529;   (* 20c4 eor3 v9.16b, v9.16b, v1.16b, v29.16b *)
  0x4c9f7049;   (* 20c8 st1 {v9.16b}, [x2], #16 *)
  0x3dc014d9;   (* 20cc ldr q25, [x6, #80] *)
  0x4e200928;   (* 20d0 rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 20d4 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc010d8;   (* 20d8 ldr q24, [x6, #64] *)
  0x6e18430b;   (* 20dc ext v11.16b, v24.16b, v24.16b, #8 *)
  0x2e281f7b;   (* 20e0 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 20e4 ldr q9, [x0], #16 *)
  0x4ef9e11c;   (* 20e8 pmull2 v28.1q, v8.2d, v25.2d *)
  0x0ef9e11a;   (* 20ec pmull v26.1q, v8.1d, v25.1d *)
  0x0eebe37b;   (* 20f0 pmull v27.1q, v27.1d, v11.1d *)
  0xce027529;   (* 20f4 eor3 v9.16b, v9.16b, v2.16b, v29.16b *)
  0x6e2d1f91;   (* 20f8 eor v17.16b, v28.16b, v13.16b *)
  0x6e2e1f53;   (* 20fc eor v19.16b, v26.16b, v14.16b *)
  0x6e2f1f72;   (* 2100 eor v18.16b, v27.16b, v15.16b *)
  0x4c9f7049;   (* 2104 st1 {v9.16b}, [x2], #16 *)
  0x3dc00cd9;   (* 2108 ldr q25, [x6, #48] *)
  0x4e200928;   (* 210c rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 2110 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc010d8;   (* 2114 ldr q24, [x6, #64] *)
  0x2e281f7b;   (* 2118 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 211c ldr q9, [x0], #16 *)
  0x4ef9e10d;   (* 2120 pmull2 v13.1q, v8.2d, v25.2d *)
  0x0ef9e10e;   (* 2124 pmull v14.1q, v8.1d, v25.1d *)
  0x0ef8e36f;   (* 2128 pmull v15.1q, v27.1d, v24.1d *)
  0xce037529;   (* 212c eor3 v9.16b, v9.16b, v3.16b, v29.16b *)
  0x4c9f7049;   (* 2130 st1 {v9.16b}, [x2], #16 *)
  0x3dc008d9;   (* 2134 ldr q25, [x6, #32] *)
  0x4e200928;   (* 2138 rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 213c ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc004d8;   (* 2140 ldr q24, [x6, #16] *)
  0x6e18430b;   (* 2144 ext v11.16b, v24.16b, v24.16b, #8 *)
  0x2e281f7b;   (* 2148 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 214c ldr q9, [x0], #16 *)
  0x4ef9e11c;   (* 2150 pmull2 v28.1q, v8.2d, v25.2d *)
  0x0ef9e11a;   (* 2154 pmull v26.1q, v8.1d, v25.1d *)
  0x0eebe37b;   (* 2158 pmull v27.1q, v27.1d, v11.1d *)
  0xce047529;   (* 215c eor3 v9.16b, v9.16b, v4.16b, v29.16b *)
  0xce1c3631;   (* 2160 eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0xce1a3a73;   (* 2164 eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0xce1b3e52;   (* 2168 eor3 v18.16b, v18.16b, v27.16b, v15.16b *)
  0x3dc000d4;   (* 216c ldr q20, [x6] *)
  0x4e200928;   (* 2170 rev64 v8.16b, v9.16b *)
  0x6e200bde;   (* 2174 rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 2178 str q30, [x16] *)
  0x4c007049;   (* 217c st1 {v9.16b}, [x2] *)
  0x6e084510;   (* 2180 mov v16.d[0], v8.d[1] *)
  0x4ef4e11c;   (* 2184 pmull2 v28.1q, v8.2d, v20.2d *)
  0x0ef4e11a;   (* 2188 pmull v26.1q, v8.1d, v20.1d *)
  0x2e281e10;   (* 218c eor v16.8b, v16.8b, v8.8b *)
  0x3dc004d5;   (* 2190 ldr q21, [x6, #16] *)
  0x0ef5e210;   (* 2194 pmull v16.1q, v16.1d, v21.1d *)
  0x6e3c1e31;   (* 2198 eor v17.16b, v17.16b, v28.16b *)
  0x6e3a1e73;   (* 219c eor v19.16b, v19.16b, v26.16b *)
  0x6e301e52;   (* 21a0 eor v18.16b, v18.16b, v16.16b *)
  0xfd400150;   (* 21a4 ldr d16, [x10] *)
  0x6e114235;   (* 21a8 ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 21ac eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 21b0 pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 21b4 eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 21b8 pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 21bc ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 21c0 eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x6e134273;   (* 21c4 ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200a73;   (* 21c8 rev64 v19.16b, v19.16b *)
  0x4c007073;   (* 21cc st1 {v19.16b}, [x3] *)
  0x17fffc09;   (* 21d0 b 11f4 <L256_enc_epilogue> *)
  0x4e284b40;   (* 21d4 aese v0.16b, v26.16b *)
  0x4e286800;   (* 21d8 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 21dc aese v1.16b, v26.16b *)
  0x4e286821;   (* 21e0 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 21e4 aese v2.16b, v26.16b *)
  0x4e286842;   (* 21e8 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 21ec aese v3.16b, v26.16b *)
  0x4e286863;   (* 21f0 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 21f4 aese v4.16b, v26.16b *)
  0x4e286884;   (* 21f8 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 21fc aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 2200 aesmc v5.16b, v5.16b *)
  0xad41697c;   (* 2204 ldp q28, q26, [x11, #32] *)
  0x4e284b60;   (* 2208 aese v0.16b, v27.16b *)
  0x4e286800;   (* 220c aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 2210 aese v1.16b, v27.16b *)
  0x4e286821;   (* 2214 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 2218 aese v2.16b, v27.16b *)
  0x4e286842;   (* 221c aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 2220 aese v3.16b, v27.16b *)
  0x4e286863;   (* 2224 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 2228 aese v4.16b, v27.16b *)
  0x4e286884;   (* 222c aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 2230 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 2234 aesmc v5.16b, v5.16b *)
  0x4e284b80;   (* 2238 aese v0.16b, v28.16b *)
  0x4e286800;   (* 223c aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 2240 aese v1.16b, v28.16b *)
  0x4e286821;   (* 2244 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 2248 aese v2.16b, v28.16b *)
  0x4e286842;   (* 224c aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 2250 aese v3.16b, v28.16b *)
  0x4e286863;   (* 2254 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 2258 aese v4.16b, v28.16b *)
  0x4e286884;   (* 225c aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 2260 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 2264 aesmc v5.16b, v5.16b *)
  0xad42717b;   (* 2268 ldp q27, q28, [x11, #64] *)
  0x4e284b40;   (* 226c aese v0.16b, v26.16b *)
  0x4e286800;   (* 2270 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 2274 aese v1.16b, v26.16b *)
  0x4e286821;   (* 2278 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 227c aese v2.16b, v26.16b *)
  0x4e286842;   (* 2280 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 2284 aese v3.16b, v26.16b *)
  0x4e286863;   (* 2288 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 228c aese v4.16b, v26.16b *)
  0x4e286884;   (* 2290 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 2294 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 2298 aesmc v5.16b, v5.16b *)
  0x4e284b60;   (* 229c aese v0.16b, v27.16b *)
  0x4e286800;   (* 22a0 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 22a4 aese v1.16b, v27.16b *)
  0x4e286821;   (* 22a8 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 22ac aese v2.16b, v27.16b *)
  0x4e286842;   (* 22b0 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 22b4 aese v3.16b, v27.16b *)
  0x4e286863;   (* 22b8 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 22bc aese v4.16b, v27.16b *)
  0x4e286884;   (* 22c0 aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 22c4 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 22c8 aesmc v5.16b, v5.16b *)
  0xad436d7a;   (* 22cc ldp q26, q27, [x11, #96] *)
  0x4e284b80;   (* 22d0 aese v0.16b, v28.16b *)
  0x4e286800;   (* 22d4 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 22d8 aese v1.16b, v28.16b *)
  0x4e286821;   (* 22dc aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 22e0 aese v2.16b, v28.16b *)
  0x4e286842;   (* 22e4 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 22e8 aese v3.16b, v28.16b *)
  0x4e286863;   (* 22ec aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 22f0 aese v4.16b, v28.16b *)
  0x4e286884;   (* 22f4 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 22f8 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 22fc aesmc v5.16b, v5.16b *)
  0x4e284b40;   (* 2300 aese v0.16b, v26.16b *)
  0x4e286800;   (* 2304 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 2308 aese v1.16b, v26.16b *)
  0x4e286821;   (* 230c aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 2310 aese v2.16b, v26.16b *)
  0x4e286842;   (* 2314 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 2318 aese v3.16b, v26.16b *)
  0x4e286863;   (* 231c aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 2320 aese v4.16b, v26.16b *)
  0x4e286884;   (* 2324 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 2328 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 232c aesmc v5.16b, v5.16b *)
  0xad44697c;   (* 2330 ldp q28, q26, [x11, #128] *)
  0x4e284b60;   (* 2334 aese v0.16b, v27.16b *)
  0x4e286800;   (* 2338 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 233c aese v1.16b, v27.16b *)
  0x4e286821;   (* 2340 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 2344 aese v2.16b, v27.16b *)
  0x4e286842;   (* 2348 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 234c aese v3.16b, v27.16b *)
  0x4e286863;   (* 2350 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 2354 aese v4.16b, v27.16b *)
  0x4e286884;   (* 2358 aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 235c aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 2360 aesmc v5.16b, v5.16b *)
  0x4e284b80;   (* 2364 aese v0.16b, v28.16b *)
  0x4e286800;   (* 2368 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 236c aese v1.16b, v28.16b *)
  0x4e286821;   (* 2370 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 2374 aese v2.16b, v28.16b *)
  0x4e286842;   (* 2378 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 237c aese v3.16b, v28.16b *)
  0x4e286863;   (* 2380 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 2384 aese v4.16b, v28.16b *)
  0x4e286884;   (* 2388 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 238c aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 2390 aesmc v5.16b, v5.16b *)
  0xad45717b;   (* 2394 ldp q27, q28, [x11, #160] *)
  0x4e284b40;   (* 2398 aese v0.16b, v26.16b *)
  0x4e286800;   (* 239c aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 23a0 aese v1.16b, v26.16b *)
  0x4e286821;   (* 23a4 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 23a8 aese v2.16b, v26.16b *)
  0x4e286842;   (* 23ac aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 23b0 aese v3.16b, v26.16b *)
  0x4e286863;   (* 23b4 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 23b8 aese v4.16b, v26.16b *)
  0x4e286884;   (* 23bc aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 23c0 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 23c4 aesmc v5.16b, v5.16b *)
  0x4e284b60;   (* 23c8 aese v0.16b, v27.16b *)
  0x4e286800;   (* 23cc aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 23d0 aese v1.16b, v27.16b *)
  0x4e286821;   (* 23d4 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 23d8 aese v2.16b, v27.16b *)
  0x4e286842;   (* 23dc aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 23e0 aese v3.16b, v27.16b *)
  0x4e286863;   (* 23e4 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 23e8 aese v4.16b, v27.16b *)
  0x4e286884;   (* 23ec aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 23f0 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 23f4 aesmc v5.16b, v5.16b *)
  0xad466d7a;   (* 23f8 ldp q26, q27, [x11, #192] *)
  0x4e284b80;   (* 23fc aese v0.16b, v28.16b *)
  0x4e286800;   (* 2400 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 2404 aese v1.16b, v28.16b *)
  0x4e286821;   (* 2408 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 240c aese v2.16b, v28.16b *)
  0x4e286842;   (* 2410 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 2414 aese v3.16b, v28.16b *)
  0x4e286863;   (* 2418 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 241c aese v4.16b, v28.16b *)
  0x4e286884;   (* 2420 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 2424 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 2428 aesmc v5.16b, v5.16b *)
  0x4e284b40;   (* 242c aese v0.16b, v26.16b *)
  0x4e286800;   (* 2430 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 2434 aese v1.16b, v26.16b *)
  0x4e286821;   (* 2438 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 243c aese v2.16b, v26.16b *)
  0x4e286842;   (* 2440 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 2444 aese v3.16b, v26.16b *)
  0x4e286863;   (* 2448 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 244c aese v4.16b, v26.16b *)
  0x4e286884;   (* 2450 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 2454 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 2458 aesmc v5.16b, v5.16b *)
  0x3dc0397c;   (* 245c ldr q28, [x11, #224] *)
  0x4e284b60;   (* 2460 aese v0.16b, v27.16b *)
  0x4e284b61;   (* 2464 aese v1.16b, v27.16b *)
  0x4e284b62;   (* 2468 aese v2.16b, v27.16b *)
  0x4e284b63;   (* 246c aese v3.16b, v27.16b *)
  0x4e284b64;   (* 2470 aese v4.16b, v27.16b *)
  0x4e284b65;   (* 2474 aese v5.16b, v27.16b *)
  0x3cc10408;   (* 2478 ldr q8, [x0], #16 *)
  0x6e134270;   (* 247c ext v16.16b, v19.16b, v19.16b, #8 *)
  0x4ebc1f9d;   (* 2480 mov v29.16b, v28.16b *)
  0x6ebf87de;   (* 2484 sub v30.4s, v30.4s, v31.4s *)
  0x6ebf87de;   (* 2488 sub v30.4s, v30.4s, v31.4s *)
  0xce007509;   (* 248c eor3 v9.16b, v8.16b, v0.16b, v29.16b *)
  0x4c9f7049;   (* 2490 st1 {v9.16b}, [x2], #16 *)
  0x3dc020d9;   (* 2494 ldr q25, [x6, #128] *)
  0x4e200928;   (* 2498 rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* 249c eor v8.16b, v8.16b, v16.16b *)
  0x6e08411b;   (* 24a0 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc01cd8;   (* 24a4 ldr q24, [x6, #112] *)
  0x6e18430b;   (* 24a8 ext v11.16b, v24.16b, v24.16b, #8 *)
  0x2e281f7b;   (* 24ac eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 24b0 ldr q9, [x0], #16 *)
  0x4ef9e10d;   (* 24b4 pmull2 v13.1q, v8.2d, v25.2d *)
  0x0ef9e10e;   (* 24b8 pmull v14.1q, v8.1d, v25.1d *)
  0x0eebe36f;   (* 24bc pmull v15.1q, v27.1d, v11.1d *)
  0xce017529;   (* 24c0 eor3 v9.16b, v9.16b, v1.16b, v29.16b *)
  0x4c9f7049;   (* 24c4 st1 {v9.16b}, [x2], #16 *)
  0x3dc018d9;   (* 24c8 ldr q25, [x6, #96] *)
  0x4e200928;   (* 24cc rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 24d0 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc01cd8;   (* 24d4 ldr q24, [x6, #112] *)
  0x2e281f7b;   (* 24d8 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 24dc ldr q9, [x0], #16 *)
  0x4ef9e11c;   (* 24e0 pmull2 v28.1q, v8.2d, v25.2d *)
  0x0ef9e11a;   (* 24e4 pmull v26.1q, v8.1d, v25.1d *)
  0x0ef8e37b;   (* 24e8 pmull v27.1q, v27.1d, v24.1d *)
  0xce027529;   (* 24ec eor3 v9.16b, v9.16b, v2.16b, v29.16b *)
  0x6e2d1f91;   (* 24f0 eor v17.16b, v28.16b, v13.16b *)
  0x6e2e1f53;   (* 24f4 eor v19.16b, v26.16b, v14.16b *)
  0x6e2f1f72;   (* 24f8 eor v18.16b, v27.16b, v15.16b *)
  0x4c9f7049;   (* 24fc st1 {v9.16b}, [x2], #16 *)
  0x3dc014d9;   (* 2500 ldr q25, [x6, #80] *)
  0x4e200928;   (* 2504 rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 2508 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc010d8;   (* 250c ldr q24, [x6, #64] *)
  0x6e18430b;   (* 2510 ext v11.16b, v24.16b, v24.16b, #8 *)
  0x2e281f7b;   (* 2514 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 2518 ldr q9, [x0], #16 *)
  0x4ef9e10d;   (* 251c pmull2 v13.1q, v8.2d, v25.2d *)
  0x0ef9e10e;   (* 2520 pmull v14.1q, v8.1d, v25.1d *)
  0x0eebe36f;   (* 2524 pmull v15.1q, v27.1d, v11.1d *)
  0xce037529;   (* 2528 eor3 v9.16b, v9.16b, v3.16b, v29.16b *)
  0x4c9f7049;   (* 252c st1 {v9.16b}, [x2], #16 *)
  0x3dc00cd9;   (* 2530 ldr q25, [x6, #48] *)
  0x4e200928;   (* 2534 rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 2538 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc010d8;   (* 253c ldr q24, [x6, #64] *)
  0x2e281f7b;   (* 2540 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 2544 ldr q9, [x0], #16 *)
  0x4ef9e11c;   (* 2548 pmull2 v28.1q, v8.2d, v25.2d *)
  0x0ef9e11a;   (* 254c pmull v26.1q, v8.1d, v25.1d *)
  0x0ef8e37b;   (* 2550 pmull v27.1q, v27.1d, v24.1d *)
  0xce047529;   (* 2554 eor3 v9.16b, v9.16b, v4.16b, v29.16b *)
  0xce1c3631;   (* 2558 eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0xce1a3a73;   (* 255c eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0xce1b3e52;   (* 2560 eor3 v18.16b, v18.16b, v27.16b, v15.16b *)
  0x4c9f7049;   (* 2564 st1 {v9.16b}, [x2], #16 *)
  0x3dc008d9;   (* 2568 ldr q25, [x6, #32] *)
  0x4e200928;   (* 256c rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 2570 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc004d8;   (* 2574 ldr q24, [x6, #16] *)
  0x6e18430b;   (* 2578 ext v11.16b, v24.16b, v24.16b, #8 *)
  0x2e281f7b;   (* 257c eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 2580 ldr q9, [x0], #16 *)
  0x4ef9e10d;   (* 2584 pmull2 v13.1q, v8.2d, v25.2d *)
  0x0ef9e10e;   (* 2588 pmull v14.1q, v8.1d, v25.1d *)
  0x0eebe36f;   (* 258c pmull v15.1q, v27.1d, v11.1d *)
  0xce057529;   (* 2590 eor3 v9.16b, v9.16b, v5.16b, v29.16b *)
  0x3dc000d4;   (* 2594 ldr q20, [x6] *)
  0x4e200928;   (* 2598 rev64 v8.16b, v9.16b *)
  0x6e200bde;   (* 259c rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 25a0 str q30, [x16] *)
  0x4c007049;   (* 25a4 st1 {v9.16b}, [x2] *)
  0x6e084510;   (* 25a8 mov v16.d[0], v8.d[1] *)
  0x4ef4e11c;   (* 25ac pmull2 v28.1q, v8.2d, v20.2d *)
  0x0ef4e11a;   (* 25b0 pmull v26.1q, v8.1d, v20.1d *)
  0x2e281e10;   (* 25b4 eor v16.8b, v16.8b, v8.8b *)
  0x3dc004d5;   (* 25b8 ldr q21, [x6, #16] *)
  0x0ef5e210;   (* 25bc pmull v16.1q, v16.1d, v21.1d *)
  0xce1c3631;   (* 25c0 eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0xce1a3a73;   (* 25c4 eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0xce103e52;   (* 25c8 eor3 v18.16b, v18.16b, v16.16b, v15.16b *)
  0xfd400150;   (* 25cc ldr d16, [x10] *)
  0x6e114235;   (* 25d0 ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 25d4 eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 25d8 pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 25dc eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 25e0 pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 25e4 ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 25e8 eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x6e134273;   (* 25ec ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200a73;   (* 25f0 rev64 v19.16b, v19.16b *)
  0x4c007073;   (* 25f4 st1 {v19.16b}, [x3] *)
  0x17fffaff;   (* 25f8 b 11f4 <L256_enc_epilogue> *)
  0x4e284b40;   (* 25fc aese v0.16b, v26.16b *)
  0x4e286800;   (* 2600 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 2604 aese v1.16b, v26.16b *)
  0x4e286821;   (* 2608 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 260c aese v2.16b, v26.16b *)
  0x4e286842;   (* 2610 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 2614 aese v3.16b, v26.16b *)
  0x4e286863;   (* 2618 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 261c aese v4.16b, v26.16b *)
  0x4e286884;   (* 2620 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 2624 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 2628 aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 262c aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 2630 aesmc v6.16b, v6.16b *)
  0xad41697c;   (* 2634 ldp q28, q26, [x11, #32] *)
  0x4e284b60;   (* 2638 aese v0.16b, v27.16b *)
  0x4e286800;   (* 263c aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 2640 aese v1.16b, v27.16b *)
  0x4e286821;   (* 2644 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 2648 aese v2.16b, v27.16b *)
  0x4e286842;   (* 264c aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 2650 aese v3.16b, v27.16b *)
  0x4e286863;   (* 2654 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 2658 aese v4.16b, v27.16b *)
  0x4e286884;   (* 265c aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 2660 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 2664 aesmc v5.16b, v5.16b *)
  0x4e284b66;   (* 2668 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 266c aesmc v6.16b, v6.16b *)
  0x4e284b80;   (* 2670 aese v0.16b, v28.16b *)
  0x4e286800;   (* 2674 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 2678 aese v1.16b, v28.16b *)
  0x4e286821;   (* 267c aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 2680 aese v2.16b, v28.16b *)
  0x4e286842;   (* 2684 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 2688 aese v3.16b, v28.16b *)
  0x4e286863;   (* 268c aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 2690 aese v4.16b, v28.16b *)
  0x4e286884;   (* 2694 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 2698 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 269c aesmc v5.16b, v5.16b *)
  0x4e284b86;   (* 26a0 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 26a4 aesmc v6.16b, v6.16b *)
  0xad42717b;   (* 26a8 ldp q27, q28, [x11, #64] *)
  0x4e284b40;   (* 26ac aese v0.16b, v26.16b *)
  0x4e286800;   (* 26b0 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 26b4 aese v1.16b, v26.16b *)
  0x4e286821;   (* 26b8 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 26bc aese v2.16b, v26.16b *)
  0x4e286842;   (* 26c0 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 26c4 aese v3.16b, v26.16b *)
  0x4e286863;   (* 26c8 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 26cc aese v4.16b, v26.16b *)
  0x4e286884;   (* 26d0 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 26d4 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 26d8 aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 26dc aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 26e0 aesmc v6.16b, v6.16b *)
  0x4e284b60;   (* 26e4 aese v0.16b, v27.16b *)
  0x4e286800;   (* 26e8 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 26ec aese v1.16b, v27.16b *)
  0x4e286821;   (* 26f0 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 26f4 aese v2.16b, v27.16b *)
  0x4e286842;   (* 26f8 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 26fc aese v3.16b, v27.16b *)
  0x4e286863;   (* 2700 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 2704 aese v4.16b, v27.16b *)
  0x4e286884;   (* 2708 aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 270c aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 2710 aesmc v5.16b, v5.16b *)
  0x4e284b66;   (* 2714 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 2718 aesmc v6.16b, v6.16b *)
  0xad436d7a;   (* 271c ldp q26, q27, [x11, #96] *)
  0x4e284b80;   (* 2720 aese v0.16b, v28.16b *)
  0x4e286800;   (* 2724 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 2728 aese v1.16b, v28.16b *)
  0x4e286821;   (* 272c aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 2730 aese v2.16b, v28.16b *)
  0x4e286842;   (* 2734 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 2738 aese v3.16b, v28.16b *)
  0x4e286863;   (* 273c aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 2740 aese v4.16b, v28.16b *)
  0x4e286884;   (* 2744 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 2748 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 274c aesmc v5.16b, v5.16b *)
  0x4e284b86;   (* 2750 aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 2754 aesmc v6.16b, v6.16b *)
  0x4e284b40;   (* 2758 aese v0.16b, v26.16b *)
  0x4e286800;   (* 275c aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 2760 aese v1.16b, v26.16b *)
  0x4e286821;   (* 2764 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 2768 aese v2.16b, v26.16b *)
  0x4e286842;   (* 276c aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 2770 aese v3.16b, v26.16b *)
  0x4e286863;   (* 2774 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 2778 aese v4.16b, v26.16b *)
  0x4e286884;   (* 277c aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 2780 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 2784 aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 2788 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 278c aesmc v6.16b, v6.16b *)
  0xad44697c;   (* 2790 ldp q28, q26, [x11, #128] *)
  0x4e284b60;   (* 2794 aese v0.16b, v27.16b *)
  0x4e286800;   (* 2798 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 279c aese v1.16b, v27.16b *)
  0x4e286821;   (* 27a0 aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 27a4 aese v2.16b, v27.16b *)
  0x4e286842;   (* 27a8 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 27ac aese v3.16b, v27.16b *)
  0x4e286863;   (* 27b0 aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 27b4 aese v4.16b, v27.16b *)
  0x4e286884;   (* 27b8 aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 27bc aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 27c0 aesmc v5.16b, v5.16b *)
  0x4e284b66;   (* 27c4 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 27c8 aesmc v6.16b, v6.16b *)
  0x4e284b80;   (* 27cc aese v0.16b, v28.16b *)
  0x4e286800;   (* 27d0 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 27d4 aese v1.16b, v28.16b *)
  0x4e286821;   (* 27d8 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 27dc aese v2.16b, v28.16b *)
  0x4e286842;   (* 27e0 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 27e4 aese v3.16b, v28.16b *)
  0x4e286863;   (* 27e8 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 27ec aese v4.16b, v28.16b *)
  0x4e286884;   (* 27f0 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 27f4 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 27f8 aesmc v5.16b, v5.16b *)
  0x4e284b86;   (* 27fc aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 2800 aesmc v6.16b, v6.16b *)
  0xad45717b;   (* 2804 ldp q27, q28, [x11, #160] *)
  0x4e284b40;   (* 2808 aese v0.16b, v26.16b *)
  0x4e286800;   (* 280c aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 2810 aese v1.16b, v26.16b *)
  0x4e286821;   (* 2814 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 2818 aese v2.16b, v26.16b *)
  0x4e286842;   (* 281c aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 2820 aese v3.16b, v26.16b *)
  0x4e286863;   (* 2824 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 2828 aese v4.16b, v26.16b *)
  0x4e286884;   (* 282c aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 2830 aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 2834 aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 2838 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 283c aesmc v6.16b, v6.16b *)
  0x4e284b60;   (* 2840 aese v0.16b, v27.16b *)
  0x4e286800;   (* 2844 aesmc v0.16b, v0.16b *)
  0x4e284b61;   (* 2848 aese v1.16b, v27.16b *)
  0x4e286821;   (* 284c aesmc v1.16b, v1.16b *)
  0x4e284b62;   (* 2850 aese v2.16b, v27.16b *)
  0x4e286842;   (* 2854 aesmc v2.16b, v2.16b *)
  0x4e284b63;   (* 2858 aese v3.16b, v27.16b *)
  0x4e286863;   (* 285c aesmc v3.16b, v3.16b *)
  0x4e284b64;   (* 2860 aese v4.16b, v27.16b *)
  0x4e286884;   (* 2864 aesmc v4.16b, v4.16b *)
  0x4e284b65;   (* 2868 aese v5.16b, v27.16b *)
  0x4e2868a5;   (* 286c aesmc v5.16b, v5.16b *)
  0x4e284b66;   (* 2870 aese v6.16b, v27.16b *)
  0x4e2868c6;   (* 2874 aesmc v6.16b, v6.16b *)
  0xad466d7a;   (* 2878 ldp q26, q27, [x11, #192] *)
  0x4e284b80;   (* 287c aese v0.16b, v28.16b *)
  0x4e286800;   (* 2880 aesmc v0.16b, v0.16b *)
  0x4e284b81;   (* 2884 aese v1.16b, v28.16b *)
  0x4e286821;   (* 2888 aesmc v1.16b, v1.16b *)
  0x4e284b82;   (* 288c aese v2.16b, v28.16b *)
  0x4e286842;   (* 2890 aesmc v2.16b, v2.16b *)
  0x4e284b83;   (* 2894 aese v3.16b, v28.16b *)
  0x4e286863;   (* 2898 aesmc v3.16b, v3.16b *)
  0x4e284b84;   (* 289c aese v4.16b, v28.16b *)
  0x4e286884;   (* 28a0 aesmc v4.16b, v4.16b *)
  0x4e284b85;   (* 28a4 aese v5.16b, v28.16b *)
  0x4e2868a5;   (* 28a8 aesmc v5.16b, v5.16b *)
  0x4e284b86;   (* 28ac aese v6.16b, v28.16b *)
  0x4e2868c6;   (* 28b0 aesmc v6.16b, v6.16b *)
  0x4e284b40;   (* 28b4 aese v0.16b, v26.16b *)
  0x4e286800;   (* 28b8 aesmc v0.16b, v0.16b *)
  0x4e284b41;   (* 28bc aese v1.16b, v26.16b *)
  0x4e286821;   (* 28c0 aesmc v1.16b, v1.16b *)
  0x4e284b42;   (* 28c4 aese v2.16b, v26.16b *)
  0x4e286842;   (* 28c8 aesmc v2.16b, v2.16b *)
  0x4e284b43;   (* 28cc aese v3.16b, v26.16b *)
  0x4e286863;   (* 28d0 aesmc v3.16b, v3.16b *)
  0x4e284b44;   (* 28d4 aese v4.16b, v26.16b *)
  0x4e286884;   (* 28d8 aesmc v4.16b, v4.16b *)
  0x4e284b45;   (* 28dc aese v5.16b, v26.16b *)
  0x4e2868a5;   (* 28e0 aesmc v5.16b, v5.16b *)
  0x4e284b46;   (* 28e4 aese v6.16b, v26.16b *)
  0x4e2868c6;   (* 28e8 aesmc v6.16b, v6.16b *)
  0x3dc0397c;   (* 28ec ldr q28, [x11, #224] *)
  0x4e284b60;   (* 28f0 aese v0.16b, v27.16b *)
  0x4e284b61;   (* 28f4 aese v1.16b, v27.16b *)
  0x4e284b62;   (* 28f8 aese v2.16b, v27.16b *)
  0x4e284b63;   (* 28fc aese v3.16b, v27.16b *)
  0x4e284b64;   (* 2900 aese v4.16b, v27.16b *)
  0x4e284b65;   (* 2904 aese v5.16b, v27.16b *)
  0x4e284b66;   (* 2908 aese v6.16b, v27.16b *)
  0x3cc10408;   (* 290c ldr q8, [x0], #16 *)
  0x6e134270;   (* 2910 ext v16.16b, v19.16b, v19.16b, #8 *)
  0x4ebc1f9d;   (* 2914 mov v29.16b, v28.16b *)
  0x6ebf87de;   (* 2918 sub v30.4s, v30.4s, v31.4s *)
  0xce007509;   (* 291c eor3 v9.16b, v8.16b, v0.16b, v29.16b *)
  0x4c9f7049;   (* 2920 st1 {v9.16b}, [x2], #16 *)
  0x3dc024d9;   (* 2924 ldr q25, [x6, #144] *)
  0x4e200928;   (* 2928 rev64 v8.16b, v9.16b *)
  0x6e301d08;   (* 292c eor v8.16b, v8.16b, v16.16b *)
  0x6e08411b;   (* 2930 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc028d8;   (* 2934 ldr q24, [x6, #160] *)
  0x2e281f7b;   (* 2938 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 293c ldr q9, [x0], #16 *)
  0x4ef9e10d;   (* 2940 pmull2 v13.1q, v8.2d, v25.2d *)
  0x0ef9e10e;   (* 2944 pmull v14.1q, v8.1d, v25.1d *)
  0x0ef8e36f;   (* 2948 pmull v15.1q, v27.1d, v24.1d *)
  0xce017529;   (* 294c eor3 v9.16b, v9.16b, v1.16b, v29.16b *)
  0x4c9f7049;   (* 2950 st1 {v9.16b}, [x2], #16 *)
  0x3dc020d9;   (* 2954 ldr q25, [x6, #128] *)
  0x4e200928;   (* 2958 rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 295c ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc01cd8;   (* 2960 ldr q24, [x6, #112] *)
  0x6e18430b;   (* 2964 ext v11.16b, v24.16b, v24.16b, #8 *)
  0x2e281f7b;   (* 2968 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 296c ldr q9, [x0], #16 *)
  0x4ef9e11c;   (* 2970 pmull2 v28.1q, v8.2d, v25.2d *)
  0x0ef9e11a;   (* 2974 pmull v26.1q, v8.1d, v25.1d *)
  0x0eebe37b;   (* 2978 pmull v27.1q, v27.1d, v11.1d *)
  0xce027529;   (* 297c eor3 v9.16b, v9.16b, v2.16b, v29.16b *)
  0x6e2d1f91;   (* 2980 eor v17.16b, v28.16b, v13.16b *)
  0x6e2e1f53;   (* 2984 eor v19.16b, v26.16b, v14.16b *)
  0x6e2f1f72;   (* 2988 eor v18.16b, v27.16b, v15.16b *)
  0x4c9f7049;   (* 298c st1 {v9.16b}, [x2], #16 *)
  0x3dc018d9;   (* 2990 ldr q25, [x6, #96] *)
  0x4e200928;   (* 2994 rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 2998 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc01cd8;   (* 299c ldr q24, [x6, #112] *)
  0x2e281f7b;   (* 29a0 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 29a4 ldr q9, [x0], #16 *)
  0x4ef9e10d;   (* 29a8 pmull2 v13.1q, v8.2d, v25.2d *)
  0x0ef9e10e;   (* 29ac pmull v14.1q, v8.1d, v25.1d *)
  0x0ef8e36f;   (* 29b0 pmull v15.1q, v27.1d, v24.1d *)
  0xce037529;   (* 29b4 eor3 v9.16b, v9.16b, v3.16b, v29.16b *)
  0x4c9f7049;   (* 29b8 st1 {v9.16b}, [x2], #16 *)
  0x3dc014d9;   (* 29bc ldr q25, [x6, #80] *)
  0x4e200928;   (* 29c0 rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 29c4 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc010d8;   (* 29c8 ldr q24, [x6, #64] *)
  0x6e18430b;   (* 29cc ext v11.16b, v24.16b, v24.16b, #8 *)
  0x2e281f7b;   (* 29d0 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 29d4 ldr q9, [x0], #16 *)
  0x4ef9e11c;   (* 29d8 pmull2 v28.1q, v8.2d, v25.2d *)
  0x0ef9e11a;   (* 29dc pmull v26.1q, v8.1d, v25.1d *)
  0x0eebe37b;   (* 29e0 pmull v27.1q, v27.1d, v11.1d *)
  0xce047529;   (* 29e4 eor3 v9.16b, v9.16b, v4.16b, v29.16b *)
  0xce1c3631;   (* 29e8 eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0xce1a3a73;   (* 29ec eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0xce1b3e52;   (* 29f0 eor3 v18.16b, v18.16b, v27.16b, v15.16b *)
  0x4c9f7049;   (* 29f4 st1 {v9.16b}, [x2], #16 *)
  0x3dc00cd9;   (* 29f8 ldr q25, [x6, #48] *)
  0x4e200928;   (* 29fc rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 2a00 ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc010d8;   (* 2a04 ldr q24, [x6, #64] *)
  0x2e281f7b;   (* 2a08 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 2a0c ldr q9, [x0], #16 *)
  0x4ef9e10d;   (* 2a10 pmull2 v13.1q, v8.2d, v25.2d *)
  0x0ef9e10e;   (* 2a14 pmull v14.1q, v8.1d, v25.1d *)
  0x0ef8e36f;   (* 2a18 pmull v15.1q, v27.1d, v24.1d *)
  0xce057529;   (* 2a1c eor3 v9.16b, v9.16b, v5.16b, v29.16b *)
  0x4c9f7049;   (* 2a20 st1 {v9.16b}, [x2], #16 *)
  0x3dc008d9;   (* 2a24 ldr q25, [x6, #32] *)
  0x4e200928;   (* 2a28 rev64 v8.16b, v9.16b *)
  0x6e08411b;   (* 2a2c ext v27.16b, v8.16b, v8.16b, #8 *)
  0x3dc004d8;   (* 2a30 ldr q24, [x6, #16] *)
  0x6e18430b;   (* 2a34 ext v11.16b, v24.16b, v24.16b, #8 *)
  0x2e281f7b;   (* 2a38 eor v27.8b, v27.8b, v8.8b *)
  0x3cc10409;   (* 2a3c ldr q9, [x0], #16 *)
  0x4ef9e11c;   (* 2a40 pmull2 v28.1q, v8.2d, v25.2d *)
  0x0ef9e11a;   (* 2a44 pmull v26.1q, v8.1d, v25.1d *)
  0x0eebe37b;   (* 2a48 pmull v27.1q, v27.1d, v11.1d *)
  0xce067529;   (* 2a4c eor3 v9.16b, v9.16b, v6.16b, v29.16b *)
  0xce1c3631;   (* 2a50 eor3 v17.16b, v17.16b, v28.16b, v13.16b *)
  0xce1a3a73;   (* 2a54 eor3 v19.16b, v19.16b, v26.16b, v14.16b *)
  0xce1b3e52;   (* 2a58 eor3 v18.16b, v18.16b, v27.16b, v15.16b *)
  0x3dc000d4;   (* 2a5c ldr q20, [x6] *)
  0x4e200928;   (* 2a60 rev64 v8.16b, v9.16b *)
  0x6e200bde;   (* 2a64 rev32 v30.16b, v30.16b *)
  0x3d80021e;   (* 2a68 str q30, [x16] *)
  0x4c007049;   (* 2a6c st1 {v9.16b}, [x2] *)
  0x6e084510;   (* 2a70 mov v16.d[0], v8.d[1] *)
  0x4ef4e11c;   (* 2a74 pmull2 v28.1q, v8.2d, v20.2d *)
  0x0ef4e11a;   (* 2a78 pmull v26.1q, v8.1d, v20.1d *)
  0x2e281e10;   (* 2a7c eor v16.8b, v16.8b, v8.8b *)
  0x3dc004d5;   (* 2a80 ldr q21, [x6, #16] *)
  0x0ef5e210;   (* 2a84 pmull v16.1q, v16.1d, v21.1d *)
  0x6e3c1e31;   (* 2a88 eor v17.16b, v17.16b, v28.16b *)
  0x6e3a1e73;   (* 2a8c eor v19.16b, v19.16b, v26.16b *)
  0x6e301e52;   (* 2a90 eor v18.16b, v18.16b, v16.16b *)
  0xfd400150;   (* 2a94 ldr d16, [x10] *)
  0x6e114235;   (* 2a98 ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;   (* 2a9c eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;   (* 2aa0 pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;   (* 2aa4 eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;   (* 2aa8 pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;   (* 2aac ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;   (* 2ab0 eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x6e134273;   (* 2ab4 ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200a73;   (* 2ab8 rev64 v19.16b, v19.16b *)
  0x4c007073;   (* 2abc st1 {v19.16b}, [x3] *)
  0x17fff9cd;   (* 2ac0 b 11f4 <L256_enc_epilogue> *)
];;

let AESV8_GCM_8X_ENC_256_EXEC = ARM_MK_EXEC_RULE aesv8_gcm_8x_enc_256_mc;;

(* ========================================================================= *)
(* P2 - Layer-1 specification glue for AES-256 CTR + GHASH.                   *)
(*                                                                           *)
(* These are the local CTR wrappers, Htable predicate, reversefields         *)
(* equivalences, hardware-primitive reconstruction lemmas and Karatsuba      *)
(* reduction lemmas needed by the correctness proof.  They mirror the x4     *)
(* AES-128-GCM kernel proofs (s2n-bignum-dev branch `gcm`,                    *)
(* arm/proofs/aes_gcm_enc_kernel_x4_reload_round_keys_full.ml), retargeted   *)
(* to AES-256 (15-entry key schedule / 14 aese/aesmc rounds) and to the 8x   *)
(* Htable layout (H^1..H^8, offsets 0..176).  Cipher-agnostic lemmas are     *)
(* ported verbatim.                                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Some specification concepts.                                              *)
(* ------------------------------------------------------------------------- *)

let ctr_block = new_definition
 `ctr_block nonce ctr :int128 = word_join (nonce:96 word) (word ctr:int32)`;;

(**** This is the form that we actually XOR little-endian bytes with
 **** in the algorithm, so we switch back out of NIST big-endian
 ****)

let aes_ctr_block = new_definition
 `aes_ctr_block nonce rk i =
    word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 2)) rk)`;;

(* The i-th ciphertext block: keystream XOR plaintext - little-endian *)

let cipher_block = new_definition
 `cipher_block nonce rk inblock i =
    word_xor (aes_ctr_block nonce rk i) (inblock i)`;;

(* The NIST convention is big-endian, however *)

let nist_cipher_block = new_definition
 `nist_cipher_block nonce rk inblock i =
        word_reversefields 8 (cipher_block nonce rk inblock i)`;;

(* Restricted Htable predicate for the 8x-unrolled kernel: the main loop
   uses H^1..H^8 and their Karatsuba mid terms (12 entries, offsets 0..176).
   This extends the x4 kernel's htable_mem_4 with the H^5..H^8 slots.
   NB the karatsuba_mid join order (high power in the high 64-bit lane)
   follows the x4 htable_mem_4 convention; it is reconciled against the
   actual x8 Htable loads in the main-loop phase (P5). *)

let htable_mem_8 = new_definition
 `htable_mem_8 (h:int128) (ptr:int64) (s:armstate) <=>
  read (memory :> bytes128 ptr) s =
    byteswap128(h_power h 0) /\
  read (memory :> bytes128 (word_add ptr (word 16))) s =
    word_join (karatsuba_mid(h_power h 1) : 64 word)
              (karatsuba_mid(h_power h 0) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 32))) s =
    byteswap128(h_power h 1) /\
  read (memory :> bytes128 (word_add ptr (word 48))) s =
    byteswap128(h_power h 2) /\
  read (memory :> bytes128 (word_add ptr (word 64))) s =
    word_join (karatsuba_mid(h_power h 3) : 64 word)
              (karatsuba_mid(h_power h 2) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 80))) s =
    byteswap128(h_power h 3) /\
  read (memory :> bytes128 (word_add ptr (word 96))) s =
    byteswap128(h_power h 4) /\
  read (memory :> bytes128 (word_add ptr (word 112))) s =
    word_join (karatsuba_mid(h_power h 5) : 64 word)
              (karatsuba_mid(h_power h 4) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 128))) s =
    byteswap128(h_power h 5) /\
  read (memory :> bytes128 (word_add ptr (word 144))) s =
    byteswap128(h_power h 6) /\
  read (memory :> bytes128 (word_add ptr (word 160))) s =
    word_join (karatsuba_mid(h_power h 7) : 64 word)
              (karatsuba_mid(h_power h 6) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 176))) s =
    byteswap128(h_power h 7)`;;

(* ------------------------------------------------------------------------- *)
(* Equivalences between the FIPS197 specs and the ARM hardware specs.        *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_REVERSEFIELDS = prove
 (`word_subword (word_reversefields 8 x) (0,8):byte = word_subword x (120,8) /\
   word_subword (word_reversefields 8 x) (8,8):byte = word_subword x (112,8) /\
   word_subword (word_reversefields 8 x) (16,8):byte = word_subword x (104,8) /\
   word_subword (word_reversefields 8 x) (24,8):byte = word_subword x (96,8) /\
   word_subword (word_reversefields 8 x) (32,8):byte = word_subword x (88,8) /\
   word_subword (word_reversefields 8 x) (40,8):byte = word_subword x (80,8) /\
   word_subword (word_reversefields 8 x) (48,8):byte = word_subword x (72,8) /\
   word_subword (word_reversefields 8 x) (56,8):byte = word_subword x (64,8) /\
   word_subword (word_reversefields 8 x) (64,8):byte = word_subword x (56,8) /\
   word_subword (word_reversefields 8 x) (72,8):byte = word_subword x (48,8) /\
   word_subword (word_reversefields 8 x) (80,8):byte = word_subword x (40,8) /\
   word_subword (word_reversefields 8 x) (88,8):byte = word_subword x (32,8) /\
   word_subword (word_reversefields 8 x) (96,8):byte = word_subword x (24,8) /\
   word_subword (word_reversefields 8 x) (104,8):byte = word_subword x (16,8) /\
   word_subword (word_reversefields 8 x) (112,8):byte = word_subword x (8,8) /\
   word_subword (word_reversefields 8 x:int128) (120,8):byte =
   word_subword x (0,8)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_SHIFT_ROWS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (aes_shift_rows x) =
              aes_shift_rows (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[aes_sub_bytes_select; LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let WORD_XOR_REVERSEFIELDS = prove
 (`!x y:int128.
        word_xor (word_reversefields 8 x) (word_reversefields 8 y) =
        word_reversefields 8 (word_xor x y)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_REVERSEFIELDS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (word_reversefields 8 x) =
              word_reversefields 8 (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_sub_bytes_select; word_join_list_16_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  CONV_TAC WORD_BLAST);;

let FIPS197_EQ_SHIFT_ROWS = prove
 (`!x:int128.
        fips197_shift_rows x =
        word_reversefields 8 (aes_shift_rows (word_reversefields 8 x))`,
  REWRITE_TAC[fips197_shift_rows; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

let FIPS197_EQ_MIX_COLUMNS = prove
 (`!x:int128.
        fips197_mix_columns x =
        word_reversefields 8 (aes_mix_columns  (word_reversefields 8 x))`,
  REWRITE_TAC[aes_mix_columns; fips197_mix_columns;
              word_join_list_16_8; aes_mix_word] THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Reconstruction of high-level concepts from the computed expressions.      *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN_COMBINE_LEMMA = prove
 (`(!(x:N word) pos1 pos2.
        pos1 + 8 = pos2
        ==> word_join (word_subword x (pos2,8):byte)
                      (word_subword x (pos1,8):byte):int16 =
            word_subword x (pos1,16)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 16 = pos2
        ==> word_join (word_subword x (pos2,16):int16)
                      (word_subword x (pos1,16):int16):int32 =
            word_subword x (pos1,32)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 32 = pos2
        ==> word_join (word_subword x (pos2,32):int32)
                      (word_subword x (pos1,32):int32):int64 =
            word_subword x (pos1,64)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 64 = pos2
        ==> word_join (word_subword x (pos2,64):int64)
                      (word_subword x (pos1,64):int64):int128 =
            word_subword x (pos1,128)) /\
   (!x:int128. word_subword x (0,128) = x)`,
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_BLAST] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_16; DIMINDEX_32;
              DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_SUBWORD;
        DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_SUBWORD_REVERSEFIELDS_32 = prove
 (`word_subword (word_reversefields 32 x:int128) (0,32):int32 =
   word_subword x (96,32) /\
   word_subword (word_reversefields 32 x:int128) (32,32):int32 =
   word_subword x (64,32) /\
   word_subword (word_reversefields 32 x:int128) (64,32):int32 =
   word_subword x (32,32) /\
   word_subword (word_reversefields 32 x:int128) (96,32):int32 =
   word_subword x (0,32)`,
  CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_BYTESWAP128 = prove
 (`(!x. word_subword (byteswap128 x) (0,64):int64 = word_subword x (64,64)) /\
   (!x. word_subword (byteswap128 x) (64,64):int64 = word_subword x (0,64))`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* [Removed, session 092 elegance] The session 019-021 byteswap-flip toolkit  *)
(* (BS_INVOL / BS_EXT / BS_INVOL2 / BS_INJ / EXT_TO_JOIN) that moved the RHS   *)
(* byteswap onto the LHS to fold the x8 Q19 reduce was SUPERSEDED by the s029  *)
(* plain-invariant route (Q19 stated WITHOUT the byteswap128 wrapper), which   *)
(* folds via GHASH_REDUCE_RAW_DIST8_PLAIN + KARATSUBA_IS_DOT_HW.  Those five    *)
(* lemmas were unreferenced and are deleted; see Q19_FOLD_TAC / TAIL_Q19_FOLD. *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_CTR_BLOCK_32 = prove
 (`word_subword (ctr_block nonce cnt) (0,32):int32 = word cnt /\
   word_subword (ctr_block nonce cnt) (32,32):int32 =
     word_subword nonce (0,32) /\
   word_subword (ctr_block nonce cnt) (64,32):int32 =
     word_subword nonce (32,32) /\
   word_subword (ctr_block nonce cnt) (96,32):int32 =
     word_subword nonce (64,32)`,
  REWRITE_TAC[ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let CTR_BLOCK_RECONSTRUCT_REV8 = prove
 (`word_join
    (word_join (word_reversefields 8 (word ctr):int32)
               (word_reversefields 8 (word_subword nonce (0,32):int32)):int64)
    (word_join (word_reversefields 8 (word_subword nonce (32,32):int32))
               (word_reversefields 8 (word_subword nonce (64,32):int32)):int64)
    = word_reversefields 8 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

let CTR_BLOCK_RECONSTRUCT_REV32 = prove
 (`word_join
    (word_join (word ctr:int32)
               (word_subword nonce (0,32):int32):int64)
    (word_join (word_subword nonce (32,32):int32)
               (word_subword nonce (64,32):int32):int64) =
  word_reversefields 32 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

let AES_CTR_BLOCK_RECONSTRUCT = prove
 (`word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 2)) rk) =
   aes_ctr_block nonce rk i /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 3)) rk) =
   aes_ctr_block nonce rk (i + 1) /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 4)) rk) =
   aes_ctr_block nonce rk (i + 2) /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 5)) rk) =
   aes_ctr_block nonce rk (i + 3)`,
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CIPHER_BLOCK_NIST = prove
 (`cipher_block nonce rk inblock i =
        word_reversefields 8 (nist_cipher_block nonce rk inblock i)`,
  REWRITE_TAC[nist_cipher_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

(*** Direct implementation of AES256 using the hardware primitives.
 *** 14 aese (rk0..rk13), 13 interleaved aesmc, and a final word_xor rk14. ***)

let AES256_CIPHER_RECONSTRUCT = prove
 (`word_xor (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
    (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
    (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2)) rk3))
    rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13) rk14 =
   word_reversefields 8
    (aes256_cipher (word_reversefields 8 plaintext)
        (MAP (word_reversefields 8)
             [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10;
              rk11; rk12; rk13; rk14]))`,
  REWRITE_TAC[aes256_cipher; LET_DEF; LET_END_DEF; MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[aesmc; aese; fips197_final_round; fips197_round] THEN
  REWRITE_TAC[AES_SUB_BYTES_SHIFT_ROWS] THEN
  REWRITE_TAC[FIPS197_EQ_SHIFT_ROWS; FIPS197_EQ_MIX_COLUMNS; fips197_sub_bytes;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GSYM WORD_XOR_REVERSEFIELDS; WORD_REVERSEFIELDS_REVERSEFIELDS;
              GSYM AES_SUB_BYTES_REVERSEFIELDS]);;

(*** This is the sequence in the code, folding an XOR in sooner ***)

let XOR_AES256_CIPHER_RECONSTRUCT = prove
 (`word_xor (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
    (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
    (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2)) rk3))
    rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13)
   (word_xor rk14 inblock) =
   word_xor
    (word_reversefields 8
      (aes256_cipher (word_reversefields 8 plaintext)
         (MAP (word_reversefields 8)
              [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10;
               rk11; rk12; rk13; rk14])))
    inblock`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REWRITE_TAC[AES256_CIPHER_RECONSTRUCT]);;

(* aes256_cipher reads only EL 0..14 of its key list (see common/fips197.ml),  *)
(* so replacing the key argument by its explicit first-15 EL-projection is a    *)
(* no-op.  UNCONDITIONAL (no `LENGTH rk = 15` needed).  This closes the final   *)
(* residual left on each ciphertext out-block conjunct after                    *)
(* XOR_AES256_CIPHER_RECONSTRUCT + MAP + WORD_REVERSEFIELDS_REVERSEFIELDS: those *)
(* rewrites collapse the per-element `word_reversefields`, but leave the key as  *)
(* the explicit list `[EL 0 rk; ...; EL 14 rk]` rather than `rk`.  The x4 proof  *)
(* sidesteps this by `ASM_CASES_TAC \`LENGTH rk = 11\`` + `EXPAND_TAC "rk"` at    *)
(* the top of its _CORRECT (making `rk` a concrete cons-list); this lemma is     *)
(* the cleaner route for the x8 statement, which keeps `rk` a free variable.     *)
let AES256_CIPHER_KEYLIST = prove
 (`aes256_cipher p
     [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk] =
   aes256_cipher p rk`,
  REWRITE_TAC[aes256_cipher] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The reduction pattern that is used in the code (p1, p2, p3 are the        *)
(* Karatsuba subcomponents of an implicit 256-bit result).                   *)
(* ------------------------------------------------------------------------- *)

let polyval_reduce_g2 = new_definition
 `polyval_reduce_g2 p1 p2 p3 =
        let (HI:int128->int64) = \x. word_subword x (64,64)
        and (LO:int128->int64) = \x. word_subword x (0,64) in
        let ks = word_xor (word_xor p1 p2) p3 in
        let w1 = word_pmul (LO p1) (word 13979173243358019584 : int64) in
        let w2 = word_pmul
                 (word_xor (word_xor (LO w1) (HI p1))
                           (LO(word_xor (word_xor p1 p2) p3)))
                 (word 13979173243358019584 : int64) in
        word_xor
           (word_join
              (LO (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              (HI (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              : int128)
           (word_xor w2 p2 : int128)`;;

let POLYVAL_REDUCE_G2 = prove
 (`polyval_reduce_g2 p1 p2 p3 =
    polyval_reduce_prop3
      ((word_join : int128 -> int128 -> (256)word)
         (word_join (word_subword p2 (64,64):int64)
                    (word_xor (word_subword (word_xor (word_xor p1 p2) p3)
                                            (64,64):int64)
                              (word_subword p2 (0,64):int64)): int128)
         (word_join (word_xor (word_subword
          (word_xor (word_xor p1 p2) p3) (0,64):int64)
                    (word_subword p1 (64,64):int64))
                    (word_subword p1 (0,64):int64): int128))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_reduce_g2; polyval_reduce_prop3;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w1 =  (word_pmul:int64->int64->int128)
      (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
  ABBREV_TAC `ks:int128 = word_xor (word_xor p1 p2) p3` THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w2:int128 = word_pmul
     (word_xor (word_xor (word_subword (w1:int128) (0,64):int64)
                     (word_subword (p1:int128) (64,64):int64))
           (word_subword (ks:int128) (0,64):int64))
     (word 13979173243358019584:int64)` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE (LAND_CONV o LAND_CONV)
   [WORD_BITWISE_RULE
    `word_xor (word_xor w1 p1) ks = word_xor (word_xor ks p1) w1`]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Variants of the existing Karatsuba lemmas better fitting the code.        *)
(* ------------------------------------------------------------------------- *)

let PMUL_KARATSUBA_JOIN = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (0,64):int64)
                                 (word_subword a (64,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC WORD_BLAST);;

(* [Removed, session 092 elegance] PMUL_KARATSUBA_JOIN_ALT and                *)
(* BYTESWAP128_G2_PROP3 belonged to the superseded byteswap-flip Q19 fold     *)
(* route (see the note above POLYVAL_REDUCE_G2's neighbours); both were       *)
(* unreferenced under the live s029 plain-invariant route.                    *)

(* ========================================================================= *)
(* P3 - First register-only AES-256 block bridge.                            *)
(*                                                                           *)
(* Smallest meaningful contiguous computational unit of the kernel: the      *)
(* eight interleaved 14-round aese/aesmc chains that form the first AES-256  *)
(* counter-mode pass in the setup region (pc+0x90 .. pc+0x41c).  This is     *)
(* register-only: the eight counter blocks are taken as opaque inputs in     *)
(* Q0..Q7, the fifteen round keys rk0,rk1 come in Q26,Q27 and rk2..rk14 are  *)
(* reloaded in-region from the key schedule in memory at key_p (offsets      *)
(* 32..224).  The region ends at the round-13 aese of every block, just      *)
(* before the data-dependent tail branch; the final rk14 xor is folded into  *)
(* the subsequent eor3 with plaintext, so the raw Qi value here is exactly   *)
(* the pre-rk14-xor AES chain.  Each output therefore satisfies              *)
(* `word_xor (read Qi s) rk14 = word_reversefields 8 (aes256_cipher ...)`,   *)
(* i.e. AES256_CIPHER_RECONSTRUCT (proved in P2) applied verbatim.           *)
(*                                                                           *)
(* NB the eight blocks are FULLY INTERLEAVED instruction-by-instruction in   *)
(* the machine code (block3-r0, block4-r0, block2-r0, block0-r0, ...), so    *)
(* there is no shorter contiguous single-block range to carve out; the whole *)
(* 227-instruction region is the atomic AES unit.  It validates the AES      *)
(* bridge (14 aese / 13 aesmc + in-memory key reload) before any GHASH or    *)
(* ciphertext-memory complexity is added in later phases.                    *)
(* ========================================================================= *)

let AESV8_GCM_8X_ENC_256_AES_SETUP = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7
     k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 key_p pc.
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xb0) /\
           read X11 s = key_p /\
           read X9 s = word 33 /\
           read Q0 s = b0 /\ read Q1 s = b1 /\ read Q2 s = b2 /\
           read Q3 s = b3 /\ read Q4 s = b4 /\ read Q5 s = b5 /\
           read Q6 s = b6 /\ read Q7 s = b7 /\
           read Q26 s = k0 /\ read Q27 s = k1 /\
           read (memory :> bytes128 (word_add key_p (word 32)))  s = k2 /\
           read (memory :> bytes128 (word_add key_p (word 48)))  s = k3 /\
           read (memory :> bytes128 (word_add key_p (word 64)))  s = k4 /\
           read (memory :> bytes128 (word_add key_p (word 80)))  s = k5 /\
           read (memory :> bytes128 (word_add key_p (word 96)))  s = k6 /\
           read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
           read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
           read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
           read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
           read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
           read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
           read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
           read (memory :> bytes128 (word_add key_p (word 224))) s = k14)
      (\s. read PC s = word (pc + 0x474) /\
           word_xor (read Q0 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b0)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q1 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b1)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q2 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b2)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q3 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b3)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q4 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b4)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q5 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b5)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q6 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b6)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q7 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b7)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])))
      (MAYCHANGE [PC] ,,
       MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q19;Q26;Q27;Q28;Q30] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,,
       MAYCHANGE [events])`,
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (1--241) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AES256_CIPHER_RECONSTRUCT]);;

(* ========================================================================= *)
(* P4 - GHASH single-fold / reduction bridge.                                *)
(*                                                                           *)
(* Structural finding (session 005, from objdump of the frozen .o):          *)
(* The x8 kernel is FULLY SOFTWARE-PIPELINED, exactly like its AES region:   *)
(* the GHASH pmull/pmull2/eor3/rev64 instructions are interleaved            *)
(* instruction-by-instruction with the AES aese/aesmc chain throughout the   *)
(* main loop (pc 0x498..0x9e4) AND the prepretail (0x9e8..0xeb4).  There is  *)
(* NO contiguous "one ghash block" PC range in those regions - the fold of   *)
(* the previous 8 blocks shares the same PC span as the AES of the next 8.   *)
(* The single-block GHASH folds do appear standalone in the TAIL cascade     *)
(* (.L256_enc_blocks_more_than_{7..1}), and the GF(2^128) MODULO reduction    *)
(* (Gueron prop-3, two pmull-by-0xC2..0) is a clean, contiguous, AES-free,    *)
(* register-in/register-out sequence that EVERY ghash path funnels through:  *)
(*                                                                           *)
(*   pc 0x11ac  ldr  d16,[x10]          ; load modulo const 0xC200..00        *)
(*   pc 0x11b0  ext  v21,v17,v17,#8                                           *)
(*   pc 0x11b4  eor3 v18,v18,v17,v19    ; MODULO - karatsuba tidy up          *)
(*   pc 0x11b8  pmull v29,v17.1d,v16.1d ; MODULO - top 64b align with mid     *)
(*   pc 0x11bc  eor3 v18,v18,v29,v21    ; MODULO - fold into mid              *)
(*   pc 0x11c0  pmull v17,v18.1d,v16.1d ; MODULO - mid 64b align with low     *)
(*   pc 0x11c4  ext  v21,v18,v18,#8                                           *)
(*   pc 0x11c8  eor3 v19,v19,v17,v21    ; MODULO - fold into low              *)
(*  (pc 0x11cc  ext  v19,v19,#8   +  0x11d0 rev64 v19  == byteswap128, the    *)
(*   store-order swap; excluded so the postcondition is reflection-free.)     *)
(*                                                                           *)
(* VERIFIED this session on server gcm8x: `ARM_STEPS_TAC EXEC (1--8)` over    *)
(* pc+0x11ac..pc+0x11cc runs clean in ~2s and yields, for accumulators       *)
(* p1=Q17(hi) p2=Q18(mid) p3=Q19(lo):                                        *)
(*   read Q19 = word_xor (word_xor p3 (word_pmul (LO Q18') w))               *)
(*                       (ext Q18')                                          *)
(*   where Q18' = p2 ^ p1 ^ p3 ^ word_pmul(LO p1) w ^ ext(p1),  w=0xC2..0,   *)
(*         ext x = word_subword (word_join x x) (64,128),                    *)
(*         LO x  = word_subword x (0,64).                                    *)
(* eor3 divergence handled transparently (opcode 0xce0.....; the stepper      *)
(* models it as a 3-way xor, no special tactic needed).                      *)
(*                                                                           *)
(* OPEN (deferred to P5/P6 with the loaded byteswap lemmas): this raw Q19 is  *)
(* NOT equal to `polyval_reduce_g2 p1 p2 p3` for ANY of the 6 argument        *)
(* permutations - CONFIRMED by a concrete-value BITBLAST oracle over all 6.   *)
(* Reason: the hardware Karatsuba accumulators entering the reduce are        *)
(* byte-reflected relative to the polyval convention (in x4 the operands are  *)
(* rev64'd GHASH blocks and the whole tag lives under `byteswap128`).  The    *)
(* clean identity therefore needs the reflection layer (byteswap128 /         *)
(* word_reversefields) threaded through, matching x4                          *)
(* aes_gcm_enc_kernel_x4_*.ml:1236-1291 where POLYVAL_REDUCE_G2 fires only    *)
(* after RECONSTRUCT_POLYVAL_REDUCE_G2 + a byteswap128 WORD_BLAST normaliser. *)
(* Once the reflection is pinned, close via                                  *)
(*   REWRITE_TAC[<swap-norm WORD_BLAST>] THEN                                 *)
(*   REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] (after WORD_SUBWORD_XOR +     *)
(*     WORD_SIMPLE_SUBWORD_CONV normalisation) THEN REWRITE_TAC[POLYVAL_...]  *)
(* or, as a fallback, a single `CONV_TAC BITBLAST_RULE` on the reflection-    *)
(* corrected goal (x4 uses exactly this at reload_full.ml:1291; on the        *)
(* normalised 2KB goal it ran in ~4s this session).                          *)
(*                                                                           *)
(* The reduce region itself is proved outright below against ghash_reduce_raw; *)
(* only the ghash_reduce_raw -> polyval_reduce_g2 spec bridge (needing the      *)
(* reflection layer) is deferred to P5/P6.                                      *)
(* ========================================================================= *)

(* The exact register-out value the 8-step symbolic execution produces for    *)
(* Q19 (VERIFIED clean this session, before the store-order byteswap).  Stated *)
(* as its own definition so the ensures postcondition stays legible; p1/p2/p3  *)
(* are the incoming Q17(hi)/Q18(mid)/Q19(lo) Karatsuba accumulators, w=0xC2..0.*)
let ghash_reduce_raw = new_definition
 `ghash_reduce_raw p1 p2 p3 =
    let (LO:int128->int64) = \x. word_subword x (0,64) in
    let (ext:int128->int128) = \x. word_subword (word_join x x : int256) (64,128) in
    let w = word 13979173243358019584 : int64 in
    let q18 = word_xor (word_xor (word_xor (word_xor p2 p1) p3)
                                 (word_pmul (LO p1) w))
                       (ext p1) in
    word_xor (word_xor p3 (word_pmul (LO q18) w)) (ext q18) : int128`;;

(* The reduce region proved GENUINELY (no CHEAT) against its raw output          *)
(* `ghash_reduce_raw`, which is exactly what ARM_STEPS_TAC (1--8) emits for Q19.  *)
(* P5/P6 will bridge `ghash_reduce_raw p1 p2 p3` to `polyval_reduce_g2` under the *)
(* reflection layer (see the OPEN note above) once the byteswap relationship of   *)
(* the incoming accumulators is threaded in.                                      *)
let AESV8_GCM_8X_ENC_256_GHASH_REDUCE = prove
 (`!p1 p2 p3 const_p pc.
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x11c8) /\
           read X10 s = const_p /\
           read (memory :> bytes64 const_p) s = word 13979173243358019584 /\
           read Q17 s = p1 /\ read Q18 s = p2 /\ read Q19 s = p3)
      (\s. read PC s = word (pc + 0x11e8) /\
           read Q19 s = ghash_reduce_raw p1 p2 p3)
      (MAYCHANGE [PC] ,,
       MAYCHANGE [Q16;Q17;Q18;Q19;Q21;Q29] ,,
       MAYCHANGE [events])`,
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ghash_reduce_raw] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* P4 bridge (a): the reduce region's raw output IS the polyval reduction.   *)
(*                                                                           *)
(* CORRECTS the session-005 note above: `ghash_reduce_raw p1 p2 p3` is NOT   *)
(* reflection-entangled at the reduce boundary.  It equals the polyval       *)
(* reduction of the SAME accumulators with p2/p3 swapped:                    *)
(*                                                                           *)
(*     ghash_reduce_raw p1 p2 p3 = polyval_reduce_g2 p1 p3 p2                 *)
(*                                                                           *)
(* No byteswap128 / word_reversefields layer is required HERE (the store-    *)
(* order byteswap that session-005's oracle saw lives in the ext+rev64 at    *)
(* pc 0x11cc/0x11d0, which ghash_reduce_raw deliberately excludes).  The      *)
(* argument swap arises because the reduce loads Q17=hi, Q18=mid, Q19=lo,     *)
(* whereas polyval_reduce_g2's convention takes (p1,p2,p3) = (hi,lo,mid).     *)
(*                                                                           *)
(* A symbolic `CONV_TAC BITBLAST_RULE` on the bare identity FAILS because     *)
(* BITBLAST treats `word_pmul` opaquely and cannot see that the two outer     *)
(* pmul arguments are XOR-equal (they differ only by the associativity/order  *)
(* of a 5-term int64 XOR).  The fix is exactly POLYVAL_REDUCE_G2's own:       *)
(* abbreviate the inner pmul w1, push subwords through the XORs, then align   *)
(* the outer pmul argument with a WORD_BITWISE_RULE rewrite so it becomes a   *)
(* common subterm on both sides; WORD_BLAST then closes the rest.            *)
(* ------------------------------------------------------------------------- *)

let GHASH_REDUCE_RAW_IS_POLYVAL_G2 = prove
 (`!p1 p2 p3. ghash_reduce_raw p1 p2 p3 = polyval_reduce_g2 p1 p3 p2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_reduce_raw; polyval_reduce_g2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w1 = (word_pmul:int64->int64->int128)
      (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
   `word_xor (word_xor (word_xor (word_xor (a:int64) b) c) d) e =
    word_xor (word_xor d e) (word_xor (word_xor b c) a)`] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* P4 bridge (b): the Karatsuba multiply-accumulate fold.                    *)
(*                                                                           *)
(* Given the three Karatsuba partial products of a single 128x128 carryless  *)
(* multiply  a * b  --  lo*lo, the cross term (a_lo^a_hi)*(b_lo^b_hi), and    *)
(* hi*hi -- feeding the reduce region in the Q17(hi)/Q18(mid)/Q19(lo) order   *)
(* the hardware uses (pmull -> lo lane, pmull2 -> hi lane, pmull of the       *)
(* eor'd halves -> cross/mid lane), the reduce computes exactly the polyval   *)
(* "dot" product  polyval_dot a b = prop3(pmul a b).                          *)
(*                                                                           *)
(*     ghash_reduce_raw <lo*lo> <cross> <hi*hi>  =  polyval_dot a b           *)
(*                                                                           *)
(* Proof chain: bridge (a) turns ghash_reduce_raw into polyval_reduce_g2      *)
(* (with the p2<->p3 swap that reorders cross/hi into g2's hi,lo,mid slots),  *)
(* POLYVAL_REDUCE_G2 rewrites that to polyval_reduce_prop3 of the reassembled *)
(* 256-bit product, and GSYM PMUL_KARATSUBA_JOIN collapses the three partial  *)
(* products back into the single word_pmul a b inside polyval_dot.  NB the    *)
(* two REWRITE_TAC calls must stay SEPARATE: folding POLYVAL_REDUCE_G2 into    *)
(* the bridge-(a) rewrite list makes it fire before the swap settles and the  *)
(* proof diverges.                                                           *)
(*                                                                           *)
(* This is the per-block fold primitive the main-loop / prepretail / tail     *)
(* bodies compose (P6): each GHASH block is `word_pmul (acc_xor_block)        *)
(* (h_power ...)`; the batched multi-block accumulation over v8..v15 then      *)
(* closes with the existing common/ lemma GHASH_POLYVAL_ACC_BATCHED (which    *)
(* already reduces `ghash_polyval_acc h a (CONS b bs)` to a prop3 of the      *)
(* pmul + ghash_wide sum), and NIST_DOT_IS_POLYVAL_DOT / nist_ghash bridge    *)
(* the polyval accumulator to the nist_ghash tag - exactly the x4 loop-body   *)
(* composition at reload_full.ml:1256-1275.                                   *)
(* ------------------------------------------------------------------------- *)

let GHASH_REDUCE_RAW_KARATSUBA_IS_DOT = prove
 (`!a b:int128.
    ghash_reduce_raw
      (word_pmul (word_subword a (0,64):int64)
                 (word_subword b (0,64):int64):int128)
      (word_pmul (word_xor (word_subword a (0,64):int64)
                           (word_subword a (64,64):int64))
                 (word_xor (word_subword b (0,64):int64)
                           (word_subword b (64,64):int64)):int128)
      (word_pmul (word_subword a (64,64):int64)
                 (word_subword b (64,64):int64):int128)
    = polyval_dot a b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_IS_POLYVAL_G2] THEN
  REWRITE_TAC[POLYVAL_REDUCE_G2; polyval_dot] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[LET_DEF;LET_END_DEF] PMUL_KARATSUBA_JOIN)]);;

(* ========================================================================= *)
(* P5 - Main-loop invariant (the software-pipelined core).                    *)
(*                                                                           *)
(* The x8 main loop (pc+0x498 .. back-edge b.lt pc+0x9e4 -> 0x498) is         *)
(* software-pipelined: iteration i GHASH-folds the PREVIOUS group of 8        *)
(* ciphertext blocks (blocks 8i..8i+7, held in v8..v15) while AES-producing   *)
(* and storing the NEXT group (blocks 8(i+1)..8(i+1)+7).  So at the loop TOP  *)
(* of iteration i the machine has STORED 8*(i+1) ciphertext blocks but only   *)
(* GHASHED 8*i of them - the lag the invariant must encode.                  *)
(*                                                                           *)
(* DIVERGENCE FROM x4 (session 007 direction call): the back-edge is a        *)
(* FLAG-CONDITIONAL pointer compare - `cmp x0,x5` (pc+0x978) sets the flags,  *)
(* `b.lt` (pc+0x9e4) branches back while x0 < x5 (signed).  x4 instead uses a *)
(* countdown register + `cbnz`, so it uses ENSURES_WHILE_UP_TAC.  Here we     *)
(* MUST use ENSURES_WHILE_PUP_TAC (the post-test "P" variant) and carry a     *)
(* flag-fact conjunct `q i s`.  On ARM `b.lt` is taken iff ~(NF <=> VF)       *)
(* (instruction.ml:568, Condition_LT), so the flag fact is                    *)
(*   (read NF s <=> read VF s) <=> (i = k)                                    *)
(* i.e. GE (fall through) exactly on the last iteration.  This is the ARM     *)
(* analogue of the x86 `(read ZF s <=> i = k)` PUP flag fact.                *)
(*                                                                           *)
(* This session (P5) proves init + back-edge + exit and CHEATs the 340-instr *)
(* body (P6).  Because this is a standalone loop lemma whose precondition IS  *)
(* the invariant at i=0 (at pc+0x498), the init subgoal is a reflexive        *)
(* 0-step ensures; the back-edge/exit subgoals only step the single b.lt      *)
(* (register/memory preserving) so every state conjunct passes through.       *)
(*                                                                           *)
(* SESSION 008 (P6, partial): stepped the full 339-instr body on server gcm8x  *)
(* with ghost values for v0..v15 and confirmed the invariant was INCOMPLETE.   *)
(* The loop is software-pipelined, so the SIMD blocks are loop-carried across  *)
(* the b.lt back-edge and MUST be pinned:                                      *)
(*   - v8..v15 = the PREVIOUS group's ciphertext (blocks 8i..8i+7), GHASH-folded *)
(*     this iteration; each is `word_xor (aes_ctr_block nonce rk (8i+j))         *)
(*     (inblock (8i+j))` (identical to the out-memory store form; store order    *)
(*     confirmed: stp q8,q9,[x2] puts q8 at 8(i+1)+0, ..., q15 at 8(i+1)+7).    *)
(*     Without these, `read Q19 s339` (the fold result the postcondition must    *)
(*     equal) is a word_pmul/word_xor over the UNPINNED ghosts q8,q9,... and the *)
(*     goal is unprovable.  NOW ADDED below (24 conjuncts: pre/inv/post).        *)
(*   - `8 * (k + 1) <= nb` antecedent ADDED: the 4 ciphertext stores            *)
(*     (stp q8..q15,[x2],#32 at 0x9bc..0x9dc) FAIL the stepper's                 *)
(*     "updates will not modify program code" check without a bound tying the   *)
(*     block count nb to the loop count k (max store byte = 128k+128 = 16*nb).  *)
(*     (This is the P9 nb-vs-k tie surfacing early.)                            *)
(* CONFIRMED-CORRECT invariant-at-(i+1) forms (goal conclusion matched verbatim *)
(* after stepping): X0/X2 128*((i+1)+1), Q30 index 8*(i+1)+13, Q19 byteswap128  *)
(* nist_ghash..(8*(i+1)), Q31, all key/htable/tag/ivec mem, out-forall bound,   *)
(* flag fact (NF<=>VF)<=>(i+1=k), PC pc+0x9e4.                                   *)
(* STILL TODO for the body (P6, next session): v0,v1,v2,v3,v4 are ALSO          *)
(* loop-carried (first body use is `aese vN,v26`, a READ) = pre-AES CTR         *)
(* keystream blocks for the group AES'd this iteration; v5,v6,v7 are computed   *)
(* fresh inside (first use `rev32 vN,v30`).  Their exact counter-index forms    *)
(* must be pinned (derive via XOR_AES256_CIPHER_RECONSTRUCT + the setup counter *)
(* bookkeeping) before the body's AES side can close.  init stays reflexive so  *)
(* adding them will not break it.                                              *)
(* ------------------------------------------------------------------------- *)
(* SESSION 011 body-stepping helpers.                                          *)
(*                                                                             *)
(* The main-loop body reloads 8 plaintext blocks with `ldp q_even,q_odd,       *)
(* [x0],#32` (steps 263/295/303/304).  Because X0 post-increments, the SECOND  *)
(* element of each later pair is read at `word_add (word_add in_p (word ...))  *)
(* (word 16)` where the offset arithmetic (e.g. `(128*(i+1)+64)+48`) is NOT    *)
(* reduced to the literal `128*(i+1)+112` that the input-block reads use.  The  *)
(* stepper's memory resolution needs a syntactic address match, so the load    *)
(* stays opaque (`read(memory..) s_prev`) and DISCARD_OLDSTATE drops the        *)
(* ciphertext-register fact.  (The very first ldp, blocks 0/1, resolves        *)
(* natively because X0 is the un-incremented base there.)                      *)
(*                                                                             *)
(* Fix, applied only at the incremented ldps (LDP_STEP4_TAC): re-derive the 8  *)
(* plaintext reads at the CURRENT state from the persistent quantified         *)
(* in-memory forall (INBLOCKS_TAC — the specific s0 facts get dropped, the     *)
(* forall does not), verbose-step (no auto-discard), FLATTEN the nested         *)
(* word_adds, NORMOFF the offset arithmetic to the literal form, resolve the   *)
(* now-matching memory reads, then discard old state.  NORMOFF_RULE reduces    *)
(* `word (a + c1 + c2 + ...)` offsets; is_inp_memfact selects the memory       *)
(* equations used to substitute the loads.  NSTEP is the ordinary per-step     *)
(* chain (flatten + NORMOFF + subword) for all other instructions.             *)
(* ------------------------------------------------------------------------- *)

let NORMOFF_RULE =
  CONV_RULE(ONCE_DEPTH_CONV(fun tm -> match tm with
      Comb(Const("word",_),_) ->
        (RAND_CONV(REWRITE_CONV[GSYM ADD_ASSOC] THENC DEPTH_CONV NUM_ADD_CONV)) tm
    | _ -> failwith "NORMOFF"));;

(* Selects ONLY the freshly re-derived input-block reads                       *)
(* (`read (memory :> bytesN ..) s = inblock <idx>`), which LDP_STEP4_TAC        *)
(* substitutes into the ldp 2nd-element load.  The RHS-variable-headed guard    *)
(* `is_var(fst(strip_comb rhs))` is essential: WITHOUT it this matched EVERY    *)
(* `read(memory..) s = v` fact, so REWRITE_RULE memfacts rewrote each READ-ONLY *)
(* key/mod/tag/ivec/htable fact BY ITSELF -> `v = v` -> `T`, silently deleting  *)
(* the ~30 read-only memory facts the postcondition needs (they are never       *)
(* regenerated, unlike the input reads which INBLOCKS_TAC re-asserts each call). *)
(* Input reads carry the abstract value `inblock j` (a var applied to args);    *)
(* all read-only facts carry constant-headed values (word_reversefields/word/…).*)
let is_inp_memfact th =
  match concl th with
    Comb(Comb(Const("=",_), Comb(Comb(Const("read",_),
      Comb(Comb(Const(":>",_),Const("memory",_)),_)), _)), rhs) ->
        is_var(fst(strip_comb rhs))
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* REPLAY-PERFORMANCE (session 057): the per-step subword normalisation is     *)
(* O(n^2).  ASSUMPTION_STATE_UPDATE_TAC (common/components.ml:3341) re-stamps   *)
(* EVERY surviving assumption from s(n-1) to sN each step with its RHS          *)
(* UNCHANGED, so a fact already put in subword-normal form last step comes back *)
(* still-normal — yet the bare CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_    *)
(* CONV) below re-traverses all ~140 carried facts every step, rebuilding each  *)
(* as theorems, a redundant no-op.  Over a 139-step drive that is ~19k          *)
(* redundant deep-conv passes (the TAIL was ~2h; s057 STATE.md profiling).      *)
(*                                                                             *)
(* WORD_SIMPLE_SUBWORD_CONV (hol-light Library/words.ml:4566) can ONLY fire on  *)
(* a `word_subword _ (NUMERAL,NUMERAL)` subterm — its outer match failwith's    *)
(* otherwise.  So TOP_DEPTH_CONV of it on a term WITHOUT that shape returns      *)
(* REFL (CONV_RULE is then the identity).  SUBWORD_NORM_RULE guards the conv     *)
(* with a cheap short-circuiting find_term for exactly that shape: it is        *)
(* PROOF-PRESERVING — for every theorem `th` it returns exactly what            *)
(* `CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th` returns (identical    *)
(* when the redex is present; th unchanged, = the conv's own no-op, when        *)
(* absent) — but it skips the expensive multi-rule traversal on the stable      *)
(* carried facts, restoring O(n).  Used by NSTEP / NSTEP_G / NSTEP_GP below.     *)
let has_word_subword_numpair =
  can (find_term (fun t -> match t with
      Comb(Comb(Const("word_subword",_),_),
           Comb(Comb(Const(",",_),Comb(Const("NUMERAL",_),_)),
                Comb(Const("NUMERAL",_),_))) -> true
    | _ -> false));;

let SUBWORD_NORM_RULE th =
  if has_word_subword_numpair (concl th)
  then CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th
  else th;;

(* PERF (session 068): the same short-circuit idea as SUBWORD_NORM_RULE, applied to  *)
(* the word_add-nest flatten (WB_WADD_RULE / NSTEP_GP_WADD_RULE).  That REWRITE_RULE   *)
(* rewrites `word_add (word_add b (word m)) (word nn) -> word_add b (word(m+nn))`,     *)
(* which fires ONLY on a register-pointer fact carrying the doubly-nested word_add    *)
(* shape (produced by a post-increment ldr/str advancing X0/X2).  On EVERY other       *)
(* carried fact — the Q-register reads, the read-only key/mod/ivec/htable memory        *)
(* facts, the non-incrementing state facts — the redex is absent, so REWRITE_RULE       *)
(* still builds its net and TOP_DEPTH-traverses the whole term only to return it         *)
(* unchanged.  Guarding with a cheap short-circuiting find_term for exactly that redex   *)
(* is PROOF-PRESERVING (identical to the bare rule: unchanged when the shape is absent,  *)
(* the rule's own no-op; identical rewrite when present) yet skips the net-walk on the   *)
(* facts that can never match.  In the WB_TAIL drive the doubly-nested shape is present  *)
(* on ~0 of ~110 carried facts at any given step (X0/X2 offsets are normalised away by   *)
(* NORMOFF the same step), so this is nearly a full skip.  VALIDATED (session 068, warm   *)
(* s2n-wbtail): over the full WB_TAIL drive MAP_EVERY NSTEP_GP (10--136) from the SAME    *)
(* s9 set-point, old vs guarded give a BIT-IDENTICAL goal (sig len=4522863 hash=          *)
(* 151882239 both) and 127.3s->121.9s / 127.2s->122.1s (~4.2% / ~4.0%, ~5.2s), reproduced *)
(* twice.  Used by the guarded steppers below.                                            *)
let has_wadd_nest =
  can (find_term (fun t -> match t with
      Comb(Comb(Const("word_add",_),
             Comb(Comb(Const("word_add",_),_),
                  Comb(Const("word",_),_))),
           Comb(Const("word",_),_)) -> true
    | _ -> false));;

(* PERF (session 068): companion guard for NORMOFF_RULE, which is                        *)
(* CONV_RULE(ONCE_DEPTH_CONV ..) firing only on a `word (t)` subterm whose argument t is  *)
(* a sum (`_ + _`) it can renormalise — i.e. a not-yet-collapsed offset like              *)
(* `word (128 * (k+1) + 16 + 32)`.  On every fact WITHOUT such a `word(sum)` the           *)
(* ONCE_DEPTH_CONV still descends the whole term to find nothing.  has_word_of_sum is a    *)
(* cheap short-circuiting find_term for `word (_ + _)`; guarding NORMOFF with it is         *)
(* PROOF-PRESERVING (NORMOFF is a no-op on facts lacking `word(sum)`, exactly what the      *)
(* guard skips) and stacks on top of the has_wadd_nest guard.  VALIDATED (session 068,       *)
(* warm s2n-wbtail): guarding BOTH passes over the full (10--136) drive from the same s9     *)
(* set-point gives a BIT-IDENTICAL goal (sig len=4522863 hash=151882239) and 127.3s->121.2s /*)
(* 127.4s->121.4s (~4.8% / ~4.7%, ~6.1s), reproduced twice — ~0.9s beyond the WADD guard.   *)
let has_word_of_sum =
  can (find_term (fun t -> match t with
      Comb(Const("word",_), Comb(Comb(Const("+",_),_),_)) -> true
    | _ -> false));;

(* The word_add-nest flatten used by every per-step stepper (NSTEP/NSTEP_G/NSTEP_GP). *)
(* Lifted out so the guarded steppers can compose it with NORMOFF/SUBWORD in ONE       *)
(* RULE_ASSUM_TAC pass and skip it on the giant GHASH accumulators (see NSTEP_G).       *)
let WB_WADD_RULE = REWRITE_RULE[WORD_RULE
  `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`];;

(* PERF (session 061): fold the three per-step RULE_ASSUM_TAC passes (word_add flatten,  *)
(* NORMOFF, SUBWORD_NORM) into ONE assumption-list traversal.  This is a pure refactor —  *)
(* the composed rule applied per fact is bit-identical to running the three rules in       *)
(* sequence — but it walks the assumption list once per step instead of three times.  No   *)
(* is_ghash_acc guard here: NSTEP drives SETUP, which carries NO large GHASH accumulators   *)
(* (measured: max fact ~1900 chars, <=2 Q19 facts through step 253), so there is nothing    *)
(* to skip; the win is purely the single traversal.  VALIDATED (session 061, warm           *)
(* s2n-wbtail): on the SAME SETUP state, old vs new NSTEP give a BIT-IDENTICAL goal over a   *)
(* block (41--120 hash=951408941 both), and block 41--200 21.9s->18.9s (~13.5%, ~3.0s),      *)
(* reproduced twice.                                                                         *)
let NSTEP n =
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th -> SUBWORD_NORM_RULE (NORMOFF_RULE (WB_WADD_RULE th)));;

(* ------------------------------------------------------------------------- *)
(* GUARDED body stepper (session 021/022 — the Q19-fold breakthrough).        *)
(*                                                                           *)
(* NSTEP applies WORD_SIMPLE_SUBWORD_CONV after EVERY step.  The GHASH        *)
(* accumulators Q17/Q18/Q19 are word_join-headed Karatsuba lane sums, and     *)
(* that conv pushes word_subword INTO the joins, collapsing                   *)
(* `word_subword(word_join a b)(0,64)`->b etc.  This destroys the `LO p1` /   *)
(* `ext p1` structure `ghash_reduce_raw`'s definition needs, so the body-end  *)
(* Q19 residual can no longer be folded back to ghash_reduce_raw (the         *)
(* 5-session Q19 dead-end, sessions 017-021).                                 *)
(*                                                                           *)
(* NSTEP_G is NSTEP with the per-step subword conv SKIPPED on any assumption  *)
(* whose read-component is Q17/Q18/Q19, preserving the accumulators' ext/LO   *)
(* structure so the final Q19 stays ghash_reduce_raw-foldable.  The v0..v15   *)
(* counter/ciphertext facts (all other registers) are still normalised as     *)
(* before, so the cheap-close is unaffected.                                  *)
let is_ghash_acc th =
  let c = concl th in
  can (find_term (fun t -> match t with
      Comb(Const("read",_), r) ->
        (match r with
         | Const("Q17",_) | Const("Q18",_) | Const("Q19",_) -> true
         | _ -> false)
    | _ -> false)) c;;

(* PERF (session 061): same optimisation as NSTEP_GP — fold the three per-step        *)
(* RULE_ASSUM_TAC passes (word_add flatten, NORMOFF, SUBWORD_NORM) into ONE, and        *)
(* extend the is_ghash_acc (Q17/18/19) guard — previously on the subword pass only —    *)
(* to ALSO skip the word_add flatten and NORMOFF on the giant GHASH accumulators. Those *)
(* two passes are identity on the word_join/word_subword accumulator terms (word_add    *)
(* rule fires only on register-pointer shape; NORMOFF only on word(c1+c2+..) offsets),  *)
(* so skipping them there is proof-preserving while avoiding an O(term-size) traversal  *)
(* of the accumulator every step.  VALIDATED (session 061, warm s2n-wbtail): on the     *)
(* SAME MAIN_LOOP-body state, old vs new NSTEP_G give a BIT-IDENTICAL goal over a drive  *)
(* block (early block 41--55 hash=980081400 both; heavy block 260--274 hash=191483695   *)
(* both), and it is measurably faster — early block 41--70 7.42s->5.85s (~21%),          *)
(* heavy-accumulator block 260--289 14.35s->11.58s (~19%, 2.8s), each reproduced twice.  *)
(* MAIN_LOOP is the file's largest drive (1--339), so the whole-body speedup is ~19%.    *)
let NSTEP_G n =
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_ghash_acc th then th
    else SUBWORD_NORM_RULE (NORMOFF_RULE (WB_WADD_RULE th)));;

let INBLOCKS_TAC sname =
  let sv = mk_var(sname,`:armstate`) in
  let concl_tm = subst[sv,`s:armstate`]
   `read (memory :> bytes128 (word_add in_p (word (128 * (i + 1))))) s =
    inblock (8 * (i + 1)) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 16)))) s =
    inblock (8 * (i + 1) + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 32)))) s =
    inblock (8 * (i + 1) + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 48)))) s =
    inblock (8 * (i + 1) + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 64)))) s =
    inblock (8 * (i + 1) + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 80)))) s =
    inblock (8 * (i + 1) + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 96)))) s =
    inblock (8 * (i + 1) + 6) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 112)))) s =
    inblock (8 * (i + 1) + 7)` in
  SUBGOAL_THEN concl_tm STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE
     `128 * (i + 1) + 16 = 16 * (8 * (i + 1) + 1) /\
      128 * (i + 1) + 32 = 16 * (8 * (i + 1) + 2) /\
      128 * (i + 1) + 48 = 16 * (8 * (i + 1) + 3) /\
      128 * (i + 1) + 64 = 16 * (8 * (i + 1) + 4) /\
      128 * (i + 1) + 80 = 16 * (8 * (i + 1) + 5) /\
      128 * (i + 1) + 96 = 16 * (8 * (i + 1) + 6) /\
      128 * (i + 1) + 112 = 16 * (8 * (i + 1) + 7)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * a = 16 * 8 * a`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    (* PERF (session 074): the block-index obligation is `8*(i+1)+b < nb`, closed  *)
    (* by just {i < k, 8*(k+1) <= nb}.  ASM_ARITH_TAC here MP_TAC'd EVERY hyp into  *)
    (* the goal — at the LDP store steps (295/303/304) the assumption list carries  *)
    (* the ~163k-char Q17/Q18/Q19 GHASH accumulators, so each INBLOCKS call spent    *)
    (* ~24s dragging+scanning the giants (3 calls = ~76s, 36% of the body drive).    *)
    (* Targeted UNDISCH of exactly the two needed hyps + bare ARITH_TAC is the same  *)
    (* idiom the body's flag-close already uses (see the flag_arith note below); it  *)
    (* closes in ~1.2s (proof-preserving: goal signature bit-identical).  Whole      *)
    (* MAIN_LOOP 342s->270s (-21%), measured twice on warm s2n-wbtail.               *)
    UNDISCH_TAC `8 * (k + 1) <= nb` THEN UNDISCH_TAC `(i:num) < k` THEN ARITH_TAC;
    ALL_TAC];;

let LDP_STEP4_TAC n =
  let sprev = "s"^string_of_int (n-1) in
  let sn = "s"^string_of_int n in
  INBLOCKS_TAC sprev THEN
  ARM_VERBOSE_STEP_TAC AESV8_GCM_8X_ENC_256_EXEC sn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`]) THEN
  RULE_ASSUM_TAC NORMOFF_RULE THEN
  (fun (asl,w as gl) ->
     let memfacts = filter is_inp_memfact (map snd asl) in
     RULE_ASSUM_TAC(REWRITE_RULE memfacts) gl) THEN
  RULE_ASSUM_TAC SUBWORD_NORM_RULE THEN
  DISCARD_OLDSTATE_TAC sn;;

(* ------------------------------------------------------------------------- *)
(* Flag-close lemmas for the main-loop body (blocker C, session 017).        *)
(*                                                                           *)
(* The loop back-edge is a signed pointer compare `cmp x0,x5; b.lt` at       *)
(* pc 0x978/0x9e4: X0 = in_p + 128*(i+2) (four `ldp [x0],#32` past the loop  *)
(* top), X5 = end_p.  After the cheap-close ASM_REWRITE, the invariant's     *)
(* flag conjunct q(i+1) has been reduced to the raw NF!=VF biconditional     *)
(* over `word_sub X0 end_p`.  BRIDGE_GE recognises that biconditional as the *)
(* signed GE `ival end_p <= ival X0`; IV_ADD linearises each additive ival   *)
(* under the buffer-end no-wrap bound `val in_p + 128*(k+1) < 2^63`; FLAG_LEM *)
(* then reduces the whole thing to `i + 1 = k` using the body hyp `i < k`.   *)
(* The no-wrap bound is supplied by MAIN_LOOP's new end_p antecedent.        *)

let BRIDGE_GE = prove
 (`!a c:int64.
     ((ival (word_sub a c) < &0) <=>
      ~(ival a - ival c = ival (word_sub a c))) <=> ival c <= ival a`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let IV_ADD = prove
 (`!(in_p:int64) off.
     val in_p + off < 2 EXP 63
     ==> ival(word_add in_p (word off)) = &(val in_p + off)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add (in_p:int64) (word off)) = val in_p + off`
    ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_IVAL; DIMINDEX_64] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* [Removed, session 092 elegance] FLAG_LEM (an i+1=k branch-flag biconditional
   for the main-loop back-edge) was unreferenced — the live proofs discharge
   that flag via BRIDGE_GE / IV_ADD directly. *)

(* ------------------------------------------------------------------------- *)
(* SETUP branch-discharge lemmas (P7, session 032).                          *)
(*                                                                           *)
(* The pipeline-fill setup has two `cmp x0,x5; b.ge` guards — the tail check *)
(* at 0x420/0x424 and the prepretail check at 0x458/0x494 — both comparing   *)
(* the running input pointer X0 against the loop-end pointer                  *)
(*   X5 = ((byte_len DIV 8) - 1) & ~127  +  in_p                             *)
(* (hardware: sub x5,x5,#1; and x5,x5,#0xffffffffffffff80; add x5,x5,x0 at    *)
(* 0x44/0x48/0x4c, with x5 initialised to x9 = word(byte_len DIV 8)).  Both   *)
(* guards must fall through (b.ge NOT taken) when k >= 1, i.e. when more than *)
(* one 8-block group remains.                                                 *)
(*                                                                           *)
(* X5_END_PTR: under block-aligned byte_len = 128*nb with nb = 8*(k+2), the   *)
(* round-down-to-128 mask collapses X5 to the loop-end pointer end_p =        *)
(* in_p + 128*(k+1) — the SAME end_p MAIN_LOOP's antecedent pins.  The key    *)
(* arithmetic: (16*nb - 1) & ~127 = 128*(k+1) because 16*nb = 128*(k+2) =     *)
(* 128*(k+1) + 128, so (128*(k+1)+127) rounds down to 128*(k+1).  This        *)
(* CONFIRMS the k = nb DIV 8 - 2 accounting (the last 8-group is drained by   *)
(* prepretail, hence -2 not -1). Proof via WORD_AND_NOT_MASK_WORD (the        *)
(* clear-low-7-bits lemma) + VAL_WORD_SUB_CASES.                              *)
let X5_END_PTR = prove
 (`!(in_p:int64) k.
     16 * (8 * (k + 2)) < 2 EXP 64
     ==> word_add
           (word_and (word_sub (word (16 * (8 * (k + 2)))) (word 1))
                     (word 18446744073709551488))
           in_p =
         word_add in_p (word (128 * (k + 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `val(word_sub (word (16 * (8 * (k + 2)))) (word 1):int64) = 128 * (k + 1) + 127`
   ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word (16 * (8 * (k + 2))):int64) = 16 * (8 * (k + 2))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_SYM] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_and (word_sub (word (16 * (8 * (k + 2)))) (word 1))
             (word 18446744073709551488):int64 =
    word(2 EXP 7 * (val(word_sub (word (16 * (8 * (k + 2)))) (word 1):int64)
                    DIV 2 EXP 7))`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `word 18446744073709551488:int64 = word_not(word(2 EXP 7 - 1))`
      SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    REWRITE_TAC[WORD_AND_NOT_MASK_WORD];
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `128 * (k + 1) + 127 = (k + 1) * 2 EXP 7 + 127`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

(* X5_END_PTR_GEN (session 082): the g-general round-down lemma.  For ANY     *)
(* nb>=1 the mask-off-low-7-bits of (16*nb - 1) yields 128 * groups where      *)
(* groups = (nb-1) DIV 8 — the last-full-8-group pointer.  Subsumes X5_END_PTR *)
(* (nb = 8*(k+2) => (nb-1) DIV 8 = k+1) and WB_X5_GROUPS0 (nb<=8 => groups=0).  *)
(* Needed by the loop_count>=1 reassembly leg where rem may be 1..8 (not just 8).*)
let X5_END_PTR_GEN = prove
 (`!(in_p:int64) nb.
     1 <= nb /\ 16 * nb < 2 EXP 64
     ==> word_add
           (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                     (word 18446744073709551488))
           in_p =
         word_add in_p (word (128 * ((nb - 1) DIV 8)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word_sub (word (16 * nb)) (word 1):int64) = 16 * nb - 1`
   ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word (16 * nb):int64) = 16 * nb` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_SYM] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_and (word_sub (word (16 * nb)) (word 1))
             (word 18446744073709551488):int64 =
    word(2 EXP 7 * (val(word_sub (word (16 * nb)) (word 1):int64)
                    DIV 2 EXP 7))`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `word 18446744073709551488:int64 = word_not(word(2 EXP 7 - 1))`
      SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    REWRITE_TAC[WORD_AND_NOT_MASK_WORD];
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`] THEN
    SUBGOAL_THEN `16 * nb - 1 = 128 * ((nb-1) DIV 8) + (16 * ((nb-1) MOD 8) + 15)`
      SUBST1_TAC THENL
     [MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `128 * ((nb-1) DIV 8) = ((nb-1) DIV 8) * 128` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    SUBGOAL_THEN `(16 * ((nb-1) MOD 8) + 15) DIV 128 = 0` SUBST1_TAC THENL
     [REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN
      MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN ARITH_TAC;
      ARITH_TAC]]);;

(* end_p = in_p + 128*(k+1) is strictly ABOVE in_p (signed), since 128*(k+1)  *)
(* >= 128 > 0 and there is no signed wrap.  So the `cmp x0,x5; b.ge` with     *)
(* X0 = in_p (or in_p+128) at the guards does NOT take the branch.            *)
let SETUP_GE_FALSE = prove
 (`!(in_p:int64) k.
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ~(ival (word_add in_p (word (128 * (k + 1)))) <= ival in_p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `128 * (k + 1)`] IV_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival(in_p:int64) = &(val in_p)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_IVAL; DIMINDEX_64] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LE]) THEN ASM_ARITH_TAC);;

(* Collapse the first-guard conditional (the exact NF!=VF biconditional the   *)
(* stepper emits for `cmp x0,x5; b.ge` with X0 = in_p) to F, so the           *)
(* conditional PC resolves to the fall-through.  X5 here is the raw hardware  *)
(* form ((128*nb DIV 8) - 1) & ~127 + in_p; the lemma normalises it to end_p  *)
(* via X5_END_PTR and finishes with BRIDGE_GE + SETUP_GE_FALSE.               *)
let SETUP_BRANCH_COND_FALSE = prove
 (`!(in_p:int64) k nb.
     8 * (k + 2) = nb /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub in_p
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival in_p -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub in_p
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `word_add
      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                (word 18446744073709551488))
      in_p =
    word_add in_p (word (128 * (k + 1))):int64`
   SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ARITH_RULE `(128 * (8 * (k + 2))) DIV 8 = 16 * 8 * (k + 2)`] THEN
    MATCH_MP_TAC X5_END_PTR THEN
    MP_TAC(SPEC `in_p:int64` VAL_BOUND_64) THEN
    UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN ARITH_TAC;
    REWRITE_TAC[BRIDGE_GE] THEN
    REWRITE_TAC[MATCH_MP SETUP_GE_FALSE (ASSUME
      `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`)]]);;

(* [s113] fast2 32B dispatch (`cmp x9,#32; b.eq L256_enc_fast2` inserted after the *)
(* counter build @pc+0xc0).  Resolves the b.eq as NOT-taken for nb != 2 (all SETUP  *)
(* legs + SETUP0 restricted to nb!=2).  x9 = word((128*nb) DIV 8).  Stepper emits   *)
(* PC = if val(word_sub (word((128*nb) DIV 8)) (word 32)) = 0 then fast2 else next.  *)
(* PROVEN 0-CHEAT on the s113 EXEC server; see optimize-113-fast2-PROOF-RECIPE.md.   *)
let DISPATCH_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 2)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 32)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 32 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 32) = word 0) <=> (word (16*nb):int64 = word 32)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

(* s115: TAKEN twin of DISPATCH_NOT_TAKEN — for nb=2 the fast2 dispatch        *)
(* `cmp x9,#32; b.eq L256_enc_fast2` branches TAKEN (x9 = (128*2)DIV8 = 32).   *)
let DISPATCH_TAKEN = prove
 (`!nb:num. nb = 2
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 32)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 32` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 32:int64) (word 32) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* [s121] fast4 64B dispatch (`cmp x9,#64; b.eq L256_enc_fast4` inserted right   *)
(* after the fast2 dispatch @pc+0xc8).  NOT-taken twin for nb != 4 (the SETUP     *)
(* legs + SETUP0/_TAIL, all reached only when nb!=2 already).  x9 = word(16*nb).  *)
let DISPATCH4_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 4)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 64 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 64) = word 0) <=> (word (16*nb):int64 = word 64)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

(* s121: TAKEN twin — for nb=4 the fast4 dispatch branches TAKEN (x9=(128*4)DIV8=64). *)
let DISPATCH4_TAKEN = prove
 (`!nb:num. nb = 4
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 64` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 64:int64) (word 64) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* [s126] fast1 16B dispatch (`cmp x9,#16; b.eq L256_enc_fast1` inserted after the   *)
(* fast4 dispatch @pc+0xd0).  NOT-taken twin for nb != 1; x9 = word(16*nb).          *)
let DISPATCH1_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 1)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 16)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 16 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 16) = word 0) <=> (word (16*nb):int64 = word 16)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

let DISPATCH1_TAKEN = prove
 (`!nb:num. nb = 1
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 16)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 16:int64) (word 16) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* [s126] fast3 48B dispatch (`cmp x9,#48; b.eq L256_enc_fast3` @pc+0xd8).           *)
let DISPATCH3_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 3)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 48)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 48 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 48) = word 0) <=> (word (16*nb):int64 = word 48)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

let DISPATCH3_TAKEN = prove
 (`!nb:num. nb = 3
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 48)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 48` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 48:int64) (word 48) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* [s127] fast5 80B dispatch (`cmp x9,#80; b.eq L256_enc_fast5` @pc+0xe0).           *)
let DISPATCH5_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 5)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 80)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 80 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 80) = word 0) <=> (word (16*nb):int64 = word 80)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

let DISPATCH5_TAKEN = prove
 (`!nb:num. nb = 5
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 80)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 80` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 80:int64) (word 80) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* [s127] fast6 96B dispatch (`cmp x9,#96; b.eq L256_enc_fast6` @pc+0xe8).           *)
let DISPATCH6_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 6)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 96)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 96 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 96) = word 0) <=> (word (16*nb):int64 = word 96)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

let DISPATCH6_TAKEN = prove
 (`!nb:num. nb = 6
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 96)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 96` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 96:int64) (word 96) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* [s127] fast7 112B dispatch (`cmp x9,#112; b.eq L256_enc_fast7` @pc+0xf0).         *)
let DISPATCH7_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 7)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 112)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 112 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 112) = word 0) <=> (word (16*nb):int64 = word 112)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

let DISPATCH7_TAKEN = prove
 (`!nb:num. nb = 7
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 112)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 112` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 112:int64) (word 112) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* Second-guard variant (session 033): the prepretail-check b.ge@0x494 fires   *)
(* AFTER the 4 ldp[x0],#32 plaintext loads, so the running pointer is          *)
(* X0 = in_p + 128 (one 8-block group consumed) — NOT in_p.  end_p is strictly *)
(* above in_p+128 (signed) since 128*(k+1) > 128 for k>=1, so the branch again *)
(* falls through.  SETUP_GE_FALSE_2 is the in_p+128 analogue of SETUP_GE_FALSE;*)
(* SETUP_BRANCH_COND_FALSE_2 collapses the exact NF!=VF biconditional the       *)
(* stepper emits at step 282 to F.                                             *)
let SETUP_GE_FALSE_2 = prove
 (`!(in_p:int64) k.
     ~(k = 0) /\ val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ~(ival (word_add in_p (word (128 * (k + 1)))) <=
           ival (word_add in_p (word 128)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `128 * (k + 1)`] IV_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`in_p:int64`; `128`] IV_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LE]) THEN ASM_ARITH_TAC);;

let SETUP_BRANCH_COND_FALSE_2 = prove
 (`!(in_p:int64) k nb.
     ~(k = 0) /\ 8 * (k + 2) = nb /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub (word_add in_p (word 128))
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival (word_add in_p (word 128)) -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub (word_add in_p (word 128))
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `word_add
      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                (word 18446744073709551488))
      in_p =
    word_add in_p (word (128 * (k + 1))):int64`
   SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ARITH_RULE `(128 * (8 * (k + 2))) DIV 8 = 16 * 8 * (k + 2)`] THEN
    MATCH_MP_TAC X5_END_PTR THEN
    MP_TAC(SPEC `in_p:int64` VAL_BOUND_64) THEN
    UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN ARITH_TAC;
    REWRITE_TAC[BRIDGE_GE] THEN
    REWRITE_TAC[MATCH_MP SETUP_GE_FALSE_2 (CONJ (ASSUME `~(k = 0)`) (ASSUME
      `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`))]]);;

(* ------ g-general SETUP branch discharges (session 082) --------------------- *)
(* The g>=2 reassembly sub-leg reuses WB_SETUP's drive but with rem in 1..8      *)
(* (8*(k+1) < nb <= 8*(k+2)) instead of the rem=8-only 8*(k+2)=nb.  The two      *)
(* main-loop-skip guard discharges must then use groups=(nb-1)DIV8=k+1 (via      *)
(* X5_END_PTR_GEN) rather than the exact-multiple X5_END_PTR.  SETUP_X5_END_GEN   *)
(* is the round-down=end_p reduction; BRANCH_COND_FALSE{,_2}_GEN collapse the     *)
(* two b.ge biconditionals to F for the fall-through (groups>=2).                 *)
(* The generalized round-down = end_p reduction (verified interactively s082). *)
let SETUP_X5_END_GEN = prove
 (`!(in_p:int64) k nb.
     8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> word_add
           (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                     (word 18446744073709551488)) in_p =
         word_add in_p (word (128 * (k + 1)):int64)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `nb:num`] X5_END_PTR_GEN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_ARITH_TAC;
      UNDISCH_TAC `nb <= 8 * (k + 2)` THEN
      UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(nb - 1) DIV 8 = k + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]);;

let SETUP_BRANCH_COND_FALSE_GEN = prove
 (`!(in_p:int64) k nb.
     8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub in_p
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival in_p -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub in_p
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SETUP_X5_END_GEN] THEN
  REWRITE_TAC[BRIDGE_GE] THEN
  REWRITE_TAC[MATCH_MP SETUP_GE_FALSE (ASSUME
    `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`)]);;

let SETUP_BRANCH_COND_FALSE_2_GEN = prove
 (`!(in_p:int64) k nb.
     ~(k = 0) /\ 8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub (word_add in_p (word 128))
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival (word_add in_p (word 128)) -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub (word_add in_p (word 128))
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SETUP_X5_END_GEN] THEN
  REWRITE_TAC[BRIDGE_GE] THEN
  REWRITE_TAC[MATCH_MP SETUP_GE_FALSE_2 (CONJ (ASSUME `~(k = 0)`) (ASSUME
    `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`))]);;

(* SETUP_BRANCH_COND_TRUE_2: the 2nd setup guard (b.ge@0x49c, cmp with        *)
(* X0 = word_add in_p (word 128) after consuming one 8-group) is TAKEN for    *)
(* groups=1 (k=0): round-down end_p = word_add in_p (word(128*(k+1))) =         *)
(* in_p+128 at k=0, so X0 = end_p and b.ge collapses to T -> PC = 0x9f0        *)
(* (PREPRETAIL).  Mirror of WB_BRANCH_COND_TRUE (1st guard) for the 2nd guard.  *)
let SETUP_BRANCH_COND_TRUE_2 = prove
 (`!(in_p:int64) k nb.
     k = 0 /\ 8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub (word_add in_p (word 128))
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival (word_add in_p (word 128)) -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub (word_add in_p (word 128))
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> T)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SETUP_X5_END_GEN] THEN
  ASM_REWRITE_TAC[ARITH_RULE `128 * (0 + 1) = 128`] THEN
  REWRITE_TAC[WORD_SUB_REFL; INT_SUB_REFL; IVAL_WORD_0] THEN
  INT_ARITH_TAC);;


(* SETUP-specific input-block re-derivation and ldp stepper.  In the setup    *)
(* the 8 plaintext blocks live at in_p + 16*j (j=0..7) — NOT the loop body's  *)
(* 128*(i+1)+off.  SETUP_INBLOCKS_TAC re-asserts all 8 reads at state `sname` *)
(* from the persistent quantified input-forall; LDP_SETUP_TAC is LDP_STEP4    *)
(* with that variant (needed for the post-incremented ldp [x0],#32 2nd loads).*)
let SETUP_INBLOCKS_TAC sname =
  let sv = mk_var(sname,`:armstate`) in
  let concl_tm = subst[sv,`s:armstate`]
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s = inblock 3 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 4)))) s = inblock 4 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 5)))) s = inblock 5 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 6)))) s = inblock 6 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 7)))) s = inblock 7` in
  SUBGOAL_THEN concl_tm STRIP_ASSUME_TAC THENL
   [(* PERF (session 090): after FIRST_ASSUM MATCH_MP_TAC each of the 8       *)
    (* obligations is the trivial `b < nb` (b = literal 0..7), closed by      *)
    (* just the bound `8 * (k + 1) <= nb` (b < 8 <= 8*(k+1) <= nb).  The old  *)
    (* ASM_ARITH_TAC dragged ALL ~67 carried facts into the arith decision    *)
    (* procedure, spending ~17.7s PER conjunct = ~142s per SETUP_INBLOCKS     *)
    (* call; with 4 LDP_SETUP_TAC calls (255/256/264/265) that was ~570s =     *)
    (* 83% of the whole WB_SETUP proof.  Targeted UNDISCH of exactly the one   *)
    (* needed hyp + bare ARITH_TAC (the same idiom the body's INBLOCKS_TAC     *)
    (* uses, session 074) closes each in ~0.005s — proof-preserving (the       *)
    (* resulting STRIP_ASSUME_TAC state is bit-identical: goal signature       *)
    (* len=26063 hash=312405345 old vs new, warm s2n-wbtail).  142.7s->0.04s   *)
    (* per call, measured twice.  All three callers (WB_SETUP/_GEN/_G1) carry  *)
    (* `8 * (k + 1) <= nb` verbatim.                                          *)
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `8 * (k + 1) <= nb` THEN ARITH_TAC;
    ALL_TAC];;

let LDP_SETUP_TAC n =
  let sprev = "s"^string_of_int (n-1) in
  let sn = "s"^string_of_int n in
  SETUP_INBLOCKS_TAC sprev THEN
  ARM_VERBOSE_STEP_TAC AESV8_GCM_8X_ENC_256_EXEC sn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`]) THEN
  RULE_ASSUM_TAC NORMOFF_RULE THEN
  (fun (asl,w as gl) ->
     (* Normalize the SETUP input memfacts so their addresses MATCH the ldp     *)
     (* reads: reduce `16*j`->literal (NUM_MULT_CONV) and collapse              *)
     (* `word_add in_p (word 0)`->in_p (WORD_ADD_0).  Without this the block-0  *)
     (* ldp read (at BARE `in_p`) fails to match SETUP_INBLOCKS_TAC's memfact   *)
     (* address `word_add in_p (word (16*0))`, so that load stays opaque        *)
     (* (`read Q8 s = read(memory:>bytes128 in_p) s_prev`) and DISCARD_OLDSTATE *)
     (* drops the register fact.  SESSION 035: this LOAD-side mismatch (NOT the *)
     (* stp store, as s034 wrongly diagnosed) is why Q8..Q15 were lost — Q8 is  *)
     (* already absent at s255 (right after the first ldp@0x428), BEFORE any    *)
     (* store.  With the norm, all 8 ciphertext regs survive to s282 (validated *)
     (* /tmp/s035_probe4).                                                      *)
     let norm th =
       REWRITE_RULE[WORD_ADD_0]
         (try CONV_RULE(TOP_DEPTH_CONV NUM_MULT_CONV) th with _ -> th) in
     let memfacts = map norm (filter is_inp_memfact (map snd asl)) in
     RULE_ASSUM_TAC(REWRITE_RULE memfacts) gl) THEN
  RULE_ASSUM_TAC SUBWORD_NORM_RULE THEN
  DISCARD_OLDSTATE_TAC sn;;

(* ------------------------------------------------------------------------- *)
(* GF(2)-linearity (additivity over word_xor) of the reduction primitives.    *)
(*                                                                           *)
(* Both polyval_reduce_prop3 and ghash_reduce_raw are compositions of         *)
(* GF(2)-linear word ops (word_subword, word_pmul BY A CONSTANT, word_xor,    *)
(* word_join), hence additive.  These are the KEY lemmas (session 025,        *)
(* advisor-directed route) that let the pipelined-GHASH Q19 fold DISTRIBUTE   *)
(* the summed-lane hardware reduce over the 8 in-flight blocks, so each block *)
(* individually fires GHASH_REDUCE_RAW_KARATSUBA_IS_DOT — replacing the       *)
(* dead-end byteswap128(prop3 A) = prop3 B lane-match (sessions 020-024).      *)
(*                                                                           *)
(* PROOF RECIPE (the crux — prior sessions failed because WORD_BITWISE_RULE   *)
(* cannot crack opaque `word_pmul a w`): first distribute the opaque pmuls    *)
(* with `WORD_PMUL_XOR` (hol-light Library/words.ml) so every pmul atom is    *)
(* SHARED across both sides, then push word_xor into the word_join lanes and  *)
(* split into 64-bit lanes closed by WORD_BITWISE_RULE (pure XOR ring, NO     *)
(* bit-blasting of pmul).  A whole-goal WORD_BLAST does NOT terminate in      *)
(* practical time (it bit-blasts the pmuls); the lane-split is essential.     *)
(* ------------------------------------------------------------------------- *)

(* word_xor of two word_joins is the join of the xored lanes (64- and         *)
(* 128-bit-lane variants) + lane-split helpers.                               *)
let JOIN_XOR_LANE = WORD_BLAST
  `word_xor (word_join (a:int64) (b:int64):int128) (word_join c d) =
   word_join (word_xor a c) (word_xor b d)`;;

let JOIN_XOR_128 = WORD_BLAST
  `word_xor (word_join (a:int128) (b:int128):int256) (word_join c d) =
   word_join (word_xor a c) (word_xor b d)`;;

let JOIN_EQ_LANE = MESON[]
  `(a:int64) = c /\ (b:int64) = d ==> word_join a b:int128 = word_join c d`;;

let JOIN_EQ_128 = MESON[]
  `(a:int128) = c /\ (b:int128) = d ==> word_join a b:int256 = word_join c d`;;

(* polyval_reduce_prop3 distributes over word_xor. *)
let PROP3_XOR = prove
 (`!s t:256 word.
     polyval_reduce_prop3 (word_xor s t) =
     word_xor (polyval_reduce_prop3 s) (polyval_reduce_prop3 t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_PMUL_XOR; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_XOR_LANE] THEN
  MATCH_MP_TAC JOIN_EQ_LANE THEN CONJ_TAC THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ghash_reduce_raw is jointly additive in its three arguments.  Proved via   *)
(* the polyval_reduce_g2 bridge (so its two nested pmul layers become a single *)
(* prop3 of a linear argument) + PROP3_XOR + a 4-lane split.                   *)
let GHASH_REDUCE_RAW_XOR = prove
 (`!a1 a2 b1 b2 c1 c2:int128.
     ghash_reduce_raw (word_xor a1 a2) (word_xor b1 b2) (word_xor c1 c2) =
     word_xor (ghash_reduce_raw a1 b1 c1) (ghash_reduce_raw a2 b2 c2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_IS_POLYVAL_G2; POLYVAL_REDUCE_G2] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[JOIN_XOR_128; JOIN_XOR_LANE] THEN
  MATCH_MP_TAC JOIN_EQ_128 THEN CONJ_TAC THEN
  MATCH_MP_TAC JOIN_EQ_LANE THEN CONJ_TAC THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* [Removed, session 092 elegance] The session-026 algebraic-fold building     *)
(* blocks EXT_BS / GHASH_REDUCE_RAW_DIST8 / DOTSUM_IS_PROP3SUM (canonical-order *)
(* lane reduce) were superseded by the s029 plain route and left unreferenced. *)
(* The live per-block reduce is KARATSUBA_IS_DOT_HW + REORD_CROSS +            *)
(* GHASH_REDUCE_RAW_DIST8_PLAIN below.                                         *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Session 027: obstruction-3 building blocks — reduce the summed lanes in the *)
(* EXACT hardware lane order the body-end residual presents.                  *)
(*                                                                           *)
(* The reassembled body-end reduce is `ghash_reduce_raw P0 P1 P2` where each   *)
(* Pl is an 8-term LEFT-associated word_xor sum of per-block Karatsuba pieces, *)
(* but the three lanes DISAGREE on block order:                               *)
(*   P0 (lo.lo)  block order [1;0;2;3;4;5;6;7], b-lane = subword(h^p)(0,64)   *)
(*   P1 (cross)  block order [1;0;3;2;5;4;7;6], b-lane = karatsuba_mid(h^p)   *)
(*   P2 (hi.hi)  block order [1;0;2;3;4;5;6;7], b-lane = subword(h^p)(64,64)  *)
(* (block j is paired with h-power h^{7-j}).  KARATSUBA_IS_DOT_HW handles the  *)
(* per-block cross-lane form, and REORD_CROSS AC-reorders the cross lane       *)
(* [1;0;3;2..] -> [1;0;2;3..] so the shared-order reduce fires — both consumed *)
(* by GHASH_REDUCE_RAW_DIST8_PLAIN (the live s029 route).                      *)
(* ------------------------------------------------------------------------- *)

(* Per-block: the cross lane in the body uses `karatsuba_mid b` and an a-arg   *)
(* subword order (64,64),(0,64); normalise both to KARATSUBA_IS_DOT's form.    *)
let KARATSUBA_IS_DOT_HW = prove
 (`!a b:int128.
    ghash_reduce_raw
      (word_pmul (word_subword a (0,64):int64) (word_subword b (0,64):int64):int128)
      (word_pmul (word_xor (word_subword a (64,64):int64) (word_subword a (0,64):int64))
                 (karatsuba_mid b):int128)
      (word_pmul (word_subword a (64,64):int64) (word_subword b (64,64):int64):int128)
    = polyval_dot a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[karatsuba_mid] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_subword (a:int128) (64,64):int64) (word_subword a (0,64))
     = word_xor (word_subword a (0,64):int64) (word_subword a (64,64))`] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_KARATSUBA_IS_DOT]);;

(* AC-reorder a LEFT-associated 8-term int128 word_xor from the cross-lane     *)
(* block order [1;0;3;2;5;4;7;6] to the shared order [1;0;2;3;4;5;6;7].        *)
let REORD_CROSS = prove
 (`word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
      (x1:int128) x0) x3) x2) x5) x4) x7) x6 =
   word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
      x1 x0) x2) x3) x4) x5) x6) x7`,
  CONV_TAC WORD_BITWISE_RULE);;

(* Per-block-0 reduce, in the EXACT raw swapped-lane form the body produces      *)
(* (sofar's two 64-bit halves crossed with cb0's — the store-order byteswap):    *)
(*   lo.lo  = word_xor (subword sofar (64,64)) (subword cb0 (0,64))              *)
(*   hi.hi  = word_xor (subword sofar (0,64))  (subword cb0 (64,64))             *)
(*   cross  = word_xor <hi-shape> <lo-shape>                                     *)
(* This reduces to polyval_dot (byteswap128 sofar (x) cb0) b.  The block-0       *)
(* accumulator byteswap is absorbed INSIDE this lemma (ABBREV byteswap128 sofar  *)
(* so the swap-lane rewrites do not re-fire on their own output): a global       *)
(* subword fold cannot be used directly on the body residual.                    *)
let KDOT_B0 = prove
 (`!s c b:int128.
    ghash_reduce_raw
      (word_pmul (word_xor (word_subword s (64,64):int64) (word_subword c (0,64):int64))
                 (word_subword b (0,64):int64):int128)
      (word_pmul (word_xor (word_xor (word_subword s (0,64):int64) (word_subword c (64,64):int64))
                           (word_xor (word_subword s (64,64):int64) (word_subword c (0,64):int64)))
                 (karatsuba_mid b):int128)
      (word_pmul (word_xor (word_subword s (0,64):int64) (word_subword c (64,64):int64))
                 (word_subword b (64,64):int64):int128)
    = polyval_dot (word_xor (byteswap128 s) c) b`,
  REPEAT GEN_TAC THEN ABBREV_TAC `bs = byteswap128 (s:int128)` THEN
  SUBGOAL_THEN `word_subword (s:int128) (64,64):int64 = word_subword (bs:int128) (0,64) /\
                word_subword (s:int128) (0,64):int64 = word_subword (bs:int128) (64,64)`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "bs" THEN REWRITE_TAC[byteswap128] THEN CONJ_TAC THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[KARATSUBA_IS_DOT_HW]);;

(* SESSION 029 (route c — HUMAN-directed re-examination of the x8 Q19 invariant): *)
(* the body-order 8-block distribution with ALL blocks in the CLEAN (non-crossed) *)
(* form — block order [1;0;2;3;4;5;6;7] on lo.lo/hi.hi, [1;0;3;2;5;4;7;6] on the *)
(* cross lane — reduces to the canonical XOR-sum of the eight per-block           *)
(* polyval_dots.  It FIRES on the body-end Q19 residual once the Q19 loop-        *)
(* invariant conjunct is stated WITHOUT the `byteswap128` wrapper                  *)
(* (`read Q19 s = nist_ghash..8i`, not `byteswap128(nist_ghash..8i)`).  Session   *)
(* 029 established EMPIRICALLY (via a faithful re-derivation of the H2 body        *)
(* residual) that under the plain invariant block 0 enters the reduce as the      *)
(* ordinary `nist_cipher_block (x) sofar` (NO store-order byteswap), so no block-0 *)
(* crossing is needed — this clean flat-sum form is what matches.                  *)
let GHASH_REDUCE_RAW_DIST8_PLAIN = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7:int128.
    ghash_reduce_raw
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_subword a1 (0,64):int64) (word_subword b1 (0,64):int64):int128)
        (word_pmul (word_subword a0 (0,64):int64) (word_subword b0 (0,64):int64):int128))
        (word_pmul (word_subword a2 (0,64):int64) (word_subword b2 (0,64):int64):int128))
        (word_pmul (word_subword a3 (0,64):int64) (word_subword b3 (0,64):int64):int128))
        (word_pmul (word_subword a4 (0,64):int64) (word_subword b4 (0,64):int64):int128))
        (word_pmul (word_subword a5 (0,64):int64) (word_subword b5 (0,64):int64):int128))
        (word_pmul (word_subword a6 (0,64):int64) (word_subword b6 (0,64):int64):int128))
        (word_pmul (word_subword a7 (0,64):int64) (word_subword b7 (0,64):int64):int128))
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_xor (word_subword a1 (64,64):int64) (word_subword a1 (0,64):int64)) (karatsuba_mid b1):int128)
        (word_pmul (word_xor (word_subword a0 (64,64):int64) (word_subword a0 (0,64):int64)) (karatsuba_mid b0):int128))
        (word_pmul (word_xor (word_subword a3 (64,64):int64) (word_subword a3 (0,64):int64)) (karatsuba_mid b3):int128))
        (word_pmul (word_xor (word_subword a2 (64,64):int64) (word_subword a2 (0,64):int64)) (karatsuba_mid b2):int128))
        (word_pmul (word_xor (word_subword a5 (64,64):int64) (word_subword a5 (0,64):int64)) (karatsuba_mid b5):int128))
        (word_pmul (word_xor (word_subword a4 (64,64):int64) (word_subword a4 (0,64):int64)) (karatsuba_mid b4):int128))
        (word_pmul (word_xor (word_subword a7 (64,64):int64) (word_subword a7 (0,64):int64)) (karatsuba_mid b7):int128))
        (word_pmul (word_xor (word_subword a6 (64,64):int64) (word_subword a6 (0,64):int64)) (karatsuba_mid b6):int128))
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_subword a1 (64,64):int64) (word_subword b1 (64,64):int64):int128)
        (word_pmul (word_subword a0 (64,64):int64) (word_subword b0 (64,64):int64):int128))
        (word_pmul (word_subword a2 (64,64):int64) (word_subword b2 (64,64):int64):int128))
        (word_pmul (word_subword a3 (64,64):int64) (word_subword b3 (64,64):int64):int128))
        (word_pmul (word_subword a4 (64,64):int64) (word_subword b4 (64,64):int64):int128))
        (word_pmul (word_subword a5 (64,64):int64) (word_subword b5 (64,64):int64):int128))
        (word_pmul (word_subword a6 (64,64):int64) (word_subword b6 (64,64):int64):int128))
        (word_pmul (word_subword a7 (64,64):int64) (word_subword b7 (64,64):int64):int128))
    = word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (polyval_dot a0 b0) (polyval_dot a1 b1)) (polyval_dot a2 b2))
        (polyval_dot a3 b3)) (polyval_dot a4 b4)) (polyval_dot a5 b5))
        (polyval_dot a6 b6)) (polyval_dot a7 b7)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [REORD_CROSS] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* Q19 GHASH-fold tactic (blocker A — sessions 017-022).                      *)
(*                                                                           *)
(* Applied to the body-end Q19 residual conjunct                              *)
(*   `<raw ghash reduce of the 8 in-flight ciphertext blocks> =              *)
(*    byteswap128(nist_ghash H tag0 (list_of_seq nist_cipher_block (8i+8)))`  *)
(* AFTER splitting it off the raw post-FINAL_STATE conjunction but BEFORE the *)
(* cheap-close (whose WORD_SIMPLE_SUBWORD_CONV would destroy the foldable     *)
(* ext/LO structure — session 022 confirmed the fold FAILS post-cheap-close). *)
(* NSTEP_G (guarded stepper) is what keeps the accumulator foldable through   *)
(* the 339 body steps.                                                        *)
(*                                                                           *)
(* Chain (session 021/022, validated live end-to-end):                        *)
(*  1. AC-swap the eor3 top XOR into ghash_reduce_raw's grouping;             *)
(*  2. GSYM ghash_reduce_raw (RECON_GRR) — FIRES (LHS 186k->67k);             *)
(*  3. GHASH_REDUCE_RAW_IS_POLYVAL_G2 (-> polyval_reduce_g2 P1 P3 P2);        *)
(*  4. MATCH_MP_TAC BS_INVOL (flip the RHS byteswap onto the LHS);            *)
(*  5. fold the RHS nist_ghash to a prop3 chain: NIST_GHASH_IS_POLYVAL +      *)
(*     8(i+1)=SUC^8(8i) + list_of_seq + APPEND + GHASH_ACC_APPEND, then       *)
(*     normalise the CONS SUC-form indices to +n (ADD1;GSYM ADD_ASSOC;        *)
(*     NUM_ADD_CONV) so the batched ISPECL matches, then                      *)
(*     GHASH_POLYVAL_ACC_BATCHED collapses it to prop3 B.                     *)
(* The residual is the final lane-match                                       *)
(*   `byteswap128(polyval_reduce_prop3 A) = polyval_reduce_prop3 B`           *)
(* (A = the g2-Karatsuba lanes, B = the clean cipherblock (x) h_power chain,  *)
(* differing by the store-order byteswap).  That lane-identity is CHEAT'd     *)
(* here (the ONE remaining piece of blocker A — see the Q19_LANE_MATCH note   *)
(* in the body-close comment); everything ABOVE it is genuinely proved.       *)
let RECON_GRR = REWRITE_RULE[LET_DEF; LET_END_DEF] (GSYM ghash_reduce_raw);;

(* SESSION 029 — ROUTE (c), blocker A CLOSED (no CHEAT).  The 5-session Q19    *)
(* dead-end (s018-028) was caused by the P5 invariant stating the Q19          *)
(* accumulator conjunct WITH a `byteswap128` wrapper                            *)
(*   read Q19 s = byteswap128(nist_ghash..8i)                                   *)
(* whereas the x8 body PRESERVES the PLAIN form                                 *)
(*   read Q19 s = nist_ghash..8i.                                               *)
(* ROOT CAUSE of the divergence from x4: x4 has BOTH a leading `ext v17`        *)
(* AND a TRAILING `ext v11` at body-end (byteswap-parity 1); x8 has ONLY the    *)
(* leading `ext v19`@0x4cc and NO trailing ext (byteswap-parity 0).  Under the  *)
(* byteswapped invariant the body-end reduce (parity 0) could never match the   *)
(* byteswap-wrapped RHS (parity 1) — the odd-parity gap that BS_INVOL/BS_INJ    *)
(* only move side-to-side (s028).  With the PLAIN invariant the body-end reduce *)
(* (parity 0) matches the plain RHS (parity 0) and the fold closes cleanly via  *)
(* the flat 8-`polyval_dot`-sum route.  Established empirically (session 029)    *)
(* by re-deriving the H2 body residual: block 0 enters the reduce as the        *)
(* ordinary clean `nist_cipher_block (x) sofar` (no store-order byteswap), so    *)
(* the fold uses GHASH_REDUCE_RAW_DIST8_PLAIN (all blocks clean), NOT DIST8_B0.  *)
let Q19_FOLD_TAC =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (x:int128) e) p = word_xor (word_xor x p) e`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  (* Reassemble the 8 cipherblocks (no EXT_BS: the plain invariant leaves no    *)
  (* store-order byteswap on the accumulator to cancel).                        *)
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  (* Re-fold the block-accumulator's distributed subwords                        *)
  (* (subword X (x) subword Y -> subword(X (x) Y)) so DIST8_PLAIN's lo.lo/hi.hi  *)
  (* lanes match, then distribute the reduce over the 8 clean blocks.            *)
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_DIST8_PLAIN] THEN
  (* RHS: fold nist_ghash..8(i+1) to prop3(pmul chain) — plain, no BS_INVOL.     *)
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * (i + 1) = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * i))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8*i+1);
       nist_cipher_block nonce rk inblock (8*i+2);
       nist_cipher_block nonce rk inblock (8*i+3);
       nist_cipher_block nonce rk inblock (8*i+4);
       nist_cipher_block nonce rk inblock (8*i+5);
       nist_cipher_block nonce rk inblock (8*i+6);
       nist_cipher_block nonce rk inblock (8*i+7)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8*i))`;
     `nist_cipher_block nonce rk inblock (8*i)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  (* Both sides are now the SAME 8-block field element, byteswap-free: collapse *)
  (* the LHS XOR-of-polyval_dot to a single prop3 (GF(2)-linearity, PROP3_XOR)  *)
  (* and match the pmul-sums by GF(2) XOR-AC.                                    *)
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* ---- historical note (blocker A resolution, sessions 018-029) --------------- *)
(* The comment below documents the DEAD routes so future sessions don't retry    *)
(* them.  Route (c) [drop the byteswap128 invariant wrapper] closed the fold.     *)
(* OLD (superseded) tactic tail, kept for the diagnosis it records:              *)
(*   ... MATCH_MP_TAC BS_INVOL ... then CHEAT'd the lane-match                    *)
(*   Final lane-match `byteswap128(prop3 A) = prop3 B` — CHEAT'd (the ONE      *)
  (* remaining piece of blocker A).  A = g2 Karatsuba lanes over the 8 in-     *)
  (* flight cipherblocks; B = the clean cipherblock (x) h_power chain; they    *)
  (* differ by the store-order byteswap.                                       *)
  (*                                                                           *)
  (* SESSION 023 DIAGNOSIS (decisive; redirects the s020-022 lane-split idea): *)
  (* the reduction to a "pure word_join/subword/xor identity over ~40 int128   *)
  (* vars" is NOT closable by BITBLAST after abstracting the pmul atoms to      *)
  (* fresh vars.  Verified end-to-end on the warm server (goal captured, all   *)
  (* stages measured):                                                         *)
  (*  - Reassemble the 8 cipherblocks (69329->7443 chars), strip the outer     *)
  (*    byteswap via GSYM BS_INVOL2+AP_TERM, ABBREV cb0..7/h0..7/sofar         *)
  (*    (-> 3060), REWRITE karatsuba_mid + align the mid-pmul arg order with   *)
  (*    the x4 WORD_XOR_SYM MESON rule (reload_full 1083-1085).                 *)
  (*  - Result: 24 pmul atoms per side; 21 of 24 MATCH; exactly 3 GENUINELY    *)
  (*    MISMATCH — the accumulator (cb0) block: LHS uses `byteswap128 sofar`   *)
  (*    (the hardware Q19 is stored byteswapped, invariant Q19 =               *)
  (*    byteswap128(nist_ghash..8i)) so its lo/hi lanes pair sofar_hi with     *)
  (*    cb0_lo; RHS uses plain `word_xor sofar cb0` (sofar_lo with cb0_lo).    *)
  (*  - Abstracting all pmul atoms then BITBLAST => `EQT_ELIM` (goal FALSE      *)
  (*    under free sofar): the accumulator's store-order byteswap is           *)
  (*    load-bearing, it is NOT a term-by-term pmul match.                     *)
  (*  - CONFIRMED prop3 does NOT commute with byteswap under ANY lane          *)
  (*    permutation of its 256-bit arg (half-swap and lane-reverse both        *)
  (*    disproved by a 0.3s BITBLAST over a free `t:256 word`).  So there is   *)
  (*    no `byteswap128(prop3 t) = prop3(perm t)` shortcut — the identity is   *)
  (*    a GF(2^128) REDUCTION fact (both sides = the same field element), not  *)
  (*    a lane shuffle.                                                        *)
  (* NEXT-SESSION ROUTE (algebraic, avoids the byteswap-vs-reduce BITBLAST):   *)
  (* DON'T reduce to a lane-match.  Compose at the polyval_dot / nist_ghash    *)
  (* level like x4 reload_full 1256-1275: bridge each per-block hardware       *)
  (* reduce to `polyval_dot (acc_block) (h_power)` via                         *)
  (* GHASH_REDUCE_RAW_KARATSUBA_IS_DOT (@~2017), accumulate via                *)
  (* GHASH_POLYVAL_ACC_BATCHED, and match the RHS byteswap128(nist_ghash)      *)
  (* through NIST_GHASH_IS_POLYVAL (accumulator passes UNCHANGED — verified).  *)
  (* CAVEAT: after RECON_GRR the LHS is `ghash_reduce_raw P0 P1 P2` where       *)
  (* P0/P1/P2 are word_xor SUMS of all 8 blocks' Karatsuba pieces, so          *)
  (* GHASH_REDUCE_RAW_KARATSUBA_IS_DOT (single a.b product) does NOT fire      *)
  (* directly on the summed lanes — the per-block dot must be established      *)
  (* BEFORE the lanes are summed (i.e. reorganise the fold so each block's     *)
  (* reduce is folded individually), OR find/prove the batched analogue        *)
  (* `ghash_reduce_raw <Sum lo.lo> <Sum cross> <Sum hi.hi> = Sum polyval_dot`. *)
  (*                                                                           *)
  (* SESSION 028 (advisor#2-directed two-sided-strip route) — FALSIFIED, and   *)
  (* the falsification is DECISIVE about the true residual.  Verified LIVE on  *)
  (* the real q19_raw (drivers /tmp/s028_probe.ml, s028_advisor_route.ml,      *)
  (* s028_parity_check.ml):                                                    *)
  (*  * After RECON_GRR + GHASH_REDUCE_RAW_IS_POLYVAL_G2 the goal is           *)
  (*      polyval_reduce_g2 P0 P2 P1  =  byteswap128(nist_ghash ..8(i+1))       *)
  (*    LHS outer head = polyval_reduce_g2 (byteswap-PARITY 0, NO outer        *)
  (*    byteswap); RHS outer head = byteswap128 (parity 1).                    *)
  (*  * Advisor's RHS fold (NIST_GHASH_IS_POLYVAL + GHASH_POLYVAL_ACC_BATCHED, *)
  (*    keeping the byteswap) gives RHS = byteswap128(polyval_reduce_prop3 W_R)*)
  (*    as predicted, BUT the LHS stays bare polyval_reduce_g2 (parity 0);     *)
  (*    BYTESWAP128_G2_PROP3 does NOT fire (its pattern needs                  *)
  (*    byteswap128(polyval_reduce_g2 ..)).  POLYVAL_REDUCE_G2 then gives      *)
  (*      polyval_reduce_prop3 W_L = byteswap128(polyval_reduce_prop3 W_R)      *)
  (*    = EXACTLY the s023 asymmetric "wound" prop3 A = byteswap128(prop3 B).   *)
  (*  * ROOT CAUSE of the parity gap: x4's LHS is byteswap-wrapped (parity 1)  *)
  (*    because x4 has a TRAILING `ext v11` at body-end; x8 has NO trailing    *)
  (*    `ext v19` (objdump s018/019).  x4's two-sided strip (reload_full       *)
  (*    1236-1245 / 1043-1052) REQUIRES both sides byteswap128(..) before      *)
  (*    REWRITE_TAC[byteswap128;..].  x8 cannot reach that: the odd            *)
  (*    byteswap-parity gap is not removable by BS_INVOL/BS_INJ/BS_INVOL2.     *)
  (*  * The true residual `prop3 W_L = byteswap128(prop3 W_R)` is NOT the naive *)
  (*    free-sofar shape: block-0 on the LHS carries (byteswap128 sofar (x)cb0) *)
  (*    while the RHS carries plain (sofar (x) cb0) (s027/s023).  It should be  *)
  (*    TRUE (invariant self-consistent: init/back-edge/exit close; advisor    *)
  (*    verified the invariant is char-identical to x4's working one; KATs     *)
  (*    pass) — the block-0 half-swap must compensate the outer byteswap.      *)
  (*  * BUT: unfolding polyval_reduce_prop3 + BITBLAST is INTRACTABLE (churns   *)
  (*    even on ONE free 256-word — the word_pmul-by-0xC2.. constant is opaque *)
  (*    to BITBLAST; confirmed s028, had to `holctl interrupt`).  And s023     *)
  (*    proved prop3 does NOT commute with byteswap128 under ANY lane perm.    *)
  (*    So neither a lane shuffle (s023 dead) nor a bit-blast closes it.       *)
  (*  * THIS IS THE 3rd advisor/route to hit the SAME byteswap-parity wall     *)
  (*    (lane-shuffle s020-023; flat-sum s025-027; two-sided-strip s028).      *)
  (*    ESCALATED to human (session-028 summary "Questions for human"): the    *)
  (*    remaining obligation is a GF(2^128) field identity                     *)
  (*      prop3(A[block0 = word_xor(byteswap128 sofar) cb0])                    *)
  (*        = byteswap128(prop3(B[block0 = word_xor sofar cb0]))                *)
  (*    where byteswap128 = 64-bit HALF-SWAP (def @polyval_ghash.ml:416, NOT   *)
  (*    a byte reversal).  Likely needs a NEW field-level lemma via            *)
  (*    POLYVAL_REDUCE_PROP3_CORRECT (prop3 t * x^128 == poly_of_word t mod Q) *)
  (*    giving byteswap128 (half-swap) a polynomial meaning — real math, not   *)
  (*    plumbing.  Do NOT open a 4th shortcut route without human direction.   *)
  (* SESSION 029 RESOLUTION (route c, human-directed): the human's diagnosis   *)
  (* was correct — the parity gap was NOT intrinsic; it was the invariant's    *)
  (* byteswap128 wrapper.  Dropping it (plain `read Q19 = nist_ghash..8i` in    *)
  (* pre/inv/post) makes the body-end reduce (parity 0) match the plain RHS     *)
  (* (parity 0), and the fold closes via GHASH_REDUCE_RAW_DIST8_PLAIN + the     *)
  (* flat-sum route with NO byteswap crossing.  See the new Q19_FOLD_TAC above. *)

(* PERF (session 088): the body cheap-close dispatcher rewrites the out-forall  *)
(* bound `j < 8*((i+1)+1)` into its 9-way disjunction split via an INLINE       *)
(* `ARITH_RULE`.  That ARITH_RULE costs ~5.85s to PROVE, and the dispatcher is  *)
(* run under `REPEAT CONJ_TAC` over ~19 residual goals — so the SAME lemma was  *)
(* re-proven ~18 times (~105s), i.e. essentially the ENTIRE post-drive close    *)
(* cost (profiled: every other sub-tactic in the cheap-close is ~0.02s).  Hoist *)
(* it to a single top-level theorem computed ONCE and REWRITE_TAC[..] with it   *)
(* per goal — byte-identical rewrite, hence proof-preserving.  MEASURED (warm    *)
(* s2n-wbtail, shared drive+FINAL_STATE setpoint, interleaved A/B, twice): the   *)
(* whole post-drive closer 113.34s/109.95s -> 12.44s/12.41s (NEW closes hyps=0), *)
(* i.e. whole MAIN_LOOP ~270s -> ~171s (~-37%).                                  *)
let MAIN_LOOP_OUT_DISJSPLIT = ARITH_RULE
  `j < 8 * ((i + 1) + 1) <=>
   j < 8 * (i+1) \/ j = 8*(i+1) \/ j = 8*(i+1) + 1 \/
   j = 8*(i+1) + 2 \/ j = 8*(i+1) + 3 \/ j = 8*(i+1) + 4 \/
   j = 8*(i+1) + 5 \/ j = 8*(i+1) + 6 \/ j = 8*(i+1) + 7`;;

let AESV8_GCM_8X_ENC_256_MAIN_LOOP = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (mod_p, 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x4f0) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 15)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 0)) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 1)) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 2)) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 3)) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 4)) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 5)) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 6)) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 7)) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 10)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 11)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 12)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 13)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 14)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)) /\
           ((read NF s <=> read VF s) <=> (0 = k)))
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xa40) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 15)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * k)) /\
           read Q8 s = word_xor (aes_ctr_block nonce rk (8 * k + 0)) (inblock (8 * k + 0)) /\
           read Q9 s = word_xor (aes_ctr_block nonce rk (8 * k + 1)) (inblock (8 * k + 1)) /\
           read Q10 s = word_xor (aes_ctr_block nonce rk (8 * k + 2)) (inblock (8 * k + 2)) /\
           read Q11 s = word_xor (aes_ctr_block nonce rk (8 * k + 3)) (inblock (8 * k + 3)) /\
           read Q12 s = word_xor (aes_ctr_block nonce rk (8 * k + 4)) (inblock (8 * k + 4)) /\
           read Q13 s = word_xor (aes_ctr_block nonce rk (8 * k + 5)) (inblock (8 * k + 5)) /\
           read Q14 s = word_xor (aes_ctr_block nonce rk (8 * k + 6)) (inblock (8 * k + 6)) /\
           read Q15 s = word_xor (aes_ctr_block nonce rk (8 * k + 7)) (inblock (8 * k + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + 10)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + 11)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + 12)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + 13)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + 14)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x4f0` `pc + 0xa3c`
    `\i s. (read X0 s = word_add in_p (word (128 * (i + 1))) /\
            read X2 s = word_add out_p (word (128 * (i + 1))) /\
            read X3 s = tag_p /\
            read X4 s = word_add in_p (word (16 * nb)) /\
            read X16 s = ivec_p /\
            read X5 s = end_p /\
            read X6 s = htable_p /\
            read X10 s = mod_p /\
            read X11 s = key_p /\
            read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
            read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
            read (memory :> bytes128 (word_add key_p (word 16))) s =
              word_reversefields 8 (EL 1 rk) /\
            read (memory :> bytes128 (word_add key_p (word 32))) s =
              word_reversefields 8 (EL 2 rk) /\
            read (memory :> bytes128 (word_add key_p (word 48))) s =
              word_reversefields 8 (EL 3 rk) /\
            read (memory :> bytes128 (word_add key_p (word 64))) s =
              word_reversefields 8 (EL 4 rk) /\
            read (memory :> bytes128 (word_add key_p (word 80))) s =
              word_reversefields 8 (EL 5 rk) /\
            read (memory :> bytes128 (word_add key_p (word 96))) s =
              word_reversefields 8 (EL 6 rk) /\
            read (memory :> bytes128 (word_add key_p (word 112))) s =
              word_reversefields 8 (EL 7 rk) /\
            read (memory :> bytes128 (word_add key_p (word 128))) s =
              word_reversefields 8 (EL 8 rk) /\
            read (memory :> bytes128 (word_add key_p (word 144))) s =
              word_reversefields 8 (EL 9 rk) /\
            read (memory :> bytes128 (word_add key_p (word 160))) s =
              word_reversefields 8 (EL 10 rk) /\
            read (memory :> bytes128 (word_add key_p (word 176))) s =
              word_reversefields 8 (EL 11 rk) /\
            read (memory :> bytes128 (word_add key_p (word 192))) s =
              word_reversefields 8 (EL 12 rk) /\
            read (memory :> bytes128 (word_add key_p (word 208))) s =
              word_reversefields 8 (EL 13 rk) /\
            read (memory :> bytes128 (word_add key_p (word 224))) s =
              word_reversefields 8 (EL 14 rk) /\
            read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
            read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce 2) /\
            read Q30 s = word_reversefields 32 (ctr_block nonce (8 * i + 15)) /\
            read Q31 s = word 79228162514264337593543950336 /\
            read Q19 s =
              nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) (8 * i)) /\
            read Q8 s = word_xor (aes_ctr_block nonce rk (8 * i + 0)) (inblock (8 * i + 0)) /\
            read Q9 s = word_xor (aes_ctr_block nonce rk (8 * i + 1)) (inblock (8 * i + 1)) /\
            read Q10 s = word_xor (aes_ctr_block nonce rk (8 * i + 2)) (inblock (8 * i + 2)) /\
            read Q11 s = word_xor (aes_ctr_block nonce rk (8 * i + 3)) (inblock (8 * i + 3)) /\
            read Q12 s = word_xor (aes_ctr_block nonce rk (8 * i + 4)) (inblock (8 * i + 4)) /\
            read Q13 s = word_xor (aes_ctr_block nonce rk (8 * i + 5)) (inblock (8 * i + 5)) /\
            read Q14 s = word_xor (aes_ctr_block nonce rk (8 * i + 6)) (inblock (8 * i + 6)) /\
            read Q15 s = word_xor (aes_ctr_block nonce rk (8 * i + 7)) (inblock (8 * i + 7)) /\
            read Q0 s = word_reversefields 8 (ctr_block nonce (8 * i + 10)) /\
            read Q1 s = word_reversefields 8 (ctr_block nonce (8 * i + 11)) /\
            read Q2 s = word_reversefields 8 (ctr_block nonce (8 * i + 12)) /\
            read Q3 s = word_reversefields 8 (ctr_block nonce (8 * i + 13)) /\
            read Q4 s = word_reversefields 8 (ctr_block nonce (8 * i + 14)) /\
            htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
            (!j. j < nb
                 ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                     inblock j) /\
            (!j. j < 8 * (i + 1)
                 ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                     word_xor (aes_ctr_block nonce rk j) (inblock j))) /\
           ((read NF s <=> read VF s) <=> (i = k))` THEN
  REWRITE_TAC[htable_mem_8] THEN
  REPEAT CONJ_TAC THENL
   [(* Subgoal 1: 0 < k *)
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

    (* Subgoal 2: init -- reflexive 0-step (precondition = p 0 at pc+0x498) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8]) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];

    (* Subgoal 3: body -- 339-instr fused GHASH+AES pipeline.                     *)
    (* SESSION 011: the full body now STEPS THROUGH to ENSURES_FINAL_STATE_TAC     *)
    (* with ALL EIGHT ciphertext register facts (read Q8..Q15 s339) intact — the  *)
    (* long-standing "Q11..Q15 facts vanish" blocker is SOLVED (see the           *)
    (* LDP_STEP4_TAC helper above: the ldp 2nd-element read addresses needed a     *)
    (* word_add-flatten + offset-arithmetic reduction to match the input-block     *)
    (* reads, else DISCARD_OLDSTATE dropped them).  Step count is (1--339): the    *)
    (* b.lt@0x9e4 (step 340) is the PUP back-edge (subgoals 4&5), NOT the body.    *)
    (* The 4 plaintext reloads are ldp q,q,[x0],#32 at steps 263/295/303/304;      *)
    (* the first resolves natively, the 3 incremented ones use LDP_STEP4_TAC.      *)
    (*                                                                             *)
    (* SESSION 015: FIXED the +2 counter mismatch — the loop-carried register     *)
    (* counter pins (Q0..Q4, Q30) were off by +2 (empirically: v0 physically =     *)
    (* ctr_block nonce (8i+10) = block 8i+8, but the invariant pinned ctr(8i+8)).  *)
    (* Setup does 13 `add v30` increments; at loop entry v0=ctr(8i+10),..,          *)
    (* v4=ctr(8i+14), Q30=ctr(8i+15).  Pins shifted +2 in pre/inv/post; init/       *)
    (* back-edge/exit re-close (full file reloads clean).  The out-forall stays in  *)
    (* block-index aes_ctr_block form (matches proven x4) — it was correct.        *)
    (*                                                                             *)
    (* REMAINING (CHEAT below): TWO obligations.                                    *)
    (* (1) INCOMING OUT-FORALL preservation across the 4 ciphertext stores.        *)
    (*     `stp q,q,[x2],#32` at steps 330/334/337/338 (pc 0x9bc/9cc/9d8/9dc) write *)
    (*     NEW blocks 8i+8..8i+15.  The invariant-at-i out-forall (`!j.j<8*(i+1)==> *)
    (*     read(out+16j) s = word_xor(aes_ctr_block nonce rk j)(inblock j)`) is     *)
    (*     ADVANCED s->s' at every non-store step (like the input-forall, which     *)
    (*     survives all 339 steps to s339) but DROPPED at the first store: the      *)
    (*     stepper cannot advance a quantified read over the out_p buffer it writes *)
    (*     (per-j disjointness 16j != 128(i+1)+off for j<8i+8 is nonlinear, not     *)
    (*     auto-dischargeable under the !j binder), so DISCARD_OLDSTATE_TAC erases  *)
    (*     it (it still refs the OLD state s329).  CONFIRMED (session 015):         *)
    (*     ARM_VERBOSE_STEP_TAC "s330" (no auto-discard) PRESERVES it (count=1);    *)
    (*     it is DISCARD_OLDSTATE that drops it.  A pre-store SUBGOAL pin does NOT  *)
    (*     survive either (same mechanism).  FIX (LDP_STEP4_TAC analogue for the    *)
    (*     stp stores): at each store use ARM_VERBOSE_STEP_TAC, then ADVANCE the    *)
    (*     out-forall's read s_{n-1}->s_n under the !j binder via read-over-write   *)
    (*     orthogonality (COMPONENT_READ_OVER_WRITE_CONV / the bytes128 store       *)
    (*     component vs out_p+16j, supplying 16j<128(i+1) from j<8*(i+1) minus the  *)
    (*     8 new indices), re-ASSUME the advanced out-forall, THEN DISCARD_OLDSTATE.*)
    (*     The 8 NEW-block store facts survive concretely at s339 (verified) so     *)
    (*     new blocks close via the case-split; only OLD blocks need this.          *)
    (* (2) Q19 GHASH fold (~367k chars): x4 reload_full 1043-1107 scaled 4->8 —     *)
    (*     byteswap128 BITBLAST wrapper, MAP_EVERY ABBREV_TAC                        *)
    (*     sofar/cipherblock_0..7/h0..h7, TRANS_TAC EQ_TRANS to                     *)
    (*     polyval_reduce_prop3(<8-term pmul chain>), PMUL_KARATSUBA_JOIN_ALT +     *)
    (*     karatsuba_mid + POLYVAL_REDUCE_G2 + BITBLAST, then                       *)
    (*     GHASH_POLYVAL_ACC_BATCHED [cipherblock_1..7] + NIST_GHASH_IS_POLYVAL +   *)
    (*     list_of_seq (8*i+8 = SUC^8 (8*i)) + GHASH_ACC_APPEND.                    *)
    (* Cheap conjuncts (X-regs, keys/htable/tag/ivec mem, Q30/Q31, Q0..Q4 counter, *)
    (* Q8..Q15 ciphertext, NEW out-blocks, flag, PC) close via S014_CHEAP3         *)
    (* (/tmp/s014_cheap3.ml): case-split bound 8*((i+1)+1), eor3 WORD_BITWISE_RULE  *)
    (* AC-normalize, CTR_BLOCK_RECONSTRUCT_REV8/REV32 + WORD_SUBWORD_* +            *)
    (* XOR_AES256_CIPHER_RECONSTRUCT + AES_CTR_BLOCK_RECONSTRUCT + FIRST_ASSUM      *)
    (* MATCH + WORD_RULE/ARITH — re-validate against the +2-corrected goal.         *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128 (word_add in_p (word (128 * (i + 1))))) s0 =
      inblock (8 * (i + 1)) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 16)))) s0 =
      inblock (8 * (i + 1) + 1) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 32)))) s0 =
      inblock (8 * (i + 1) + 2) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 48)))) s0 =
      inblock (8 * (i + 1) + 3) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 64)))) s0 =
      inblock (8 * (i + 1) + 4) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 80)))) s0 =
      inblock (8 * (i + 1) + 5) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 96)))) s0 =
      inblock (8 * (i + 1) + 6) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 112)))) s0 =
      inblock (8 * (i + 1) + 7)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE
       `128 * (i + 1) + 16 = 16 * (8 * (i + 1) + 1) /\
        128 * (i + 1) + 32 = 16 * (8 * (i + 1) + 2) /\
        128 * (i + 1) + 48 = 16 * (8 * (i + 1) + 3) /\
        128 * (i + 1) + 64 = 16 * (8 * (i + 1) + 4) /\
        128 * (i + 1) + 80 = 16 * (8 * (i + 1) + 5) /\
        128 * (i + 1) + 96 = 16 * (8 * (i + 1) + 6) /\
        128 * (i + 1) + 112 = 16 * (8 * (i + 1) + 7)`] THEN
      REWRITE_TAC[ARITH_RULE `128 * a = 16 * 8 * a`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
    MAP_EVERY NSTEP_G (1--294) THEN
    LDP_STEP4_TAC 295 THEN
    MAP_EVERY NSTEP_G (296--302) THEN
    LDP_STEP4_TAC 303 THEN
    LDP_STEP4_TAC 304 THEN
    MAP_EVERY NSTEP_G (305--339) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* --- Cheap-conjunct close (session 016): validates the +2 counter fix.    *)
    (* The case-split bound is 8*((i+1)+1) (invariant out-forall at i is         *)
    (* j<8*(i+1), so at i+1 it is j<8*(i+2)); the eor3 3-way store XOR is        *)
    (* AC-normalized to the XOR_AES256_CIPHER_RECONSTRUCT shape; then            *)
    (* AES256_CIPHER_KEYLIST collapses the residual explicit key list            *)
    (* `[EL 0 rk;..;EL 14 rk]` back to `rk` (the piece prior sessions missed —   *)
    (* XOR_AES256_CIPHER_RECONSTRUCT + MAP leaves the list, not `rk`).           *)
    (* SESSION 022 RESTRUCTURE: split the RAW post-FINAL_STATE conjunction     *)
    (* FIRST (before the cheap-close), so the Q19 GHASH-fold conjunct can be    *)
    (* folded while its ext/LO structure is intact.  Session 022 CONFIRMED the  *)
    (* cheap-close's WORD_SIMPLE_SUBWORD_CONV DESTROYS Q19's foldability (the    *)
    (* GSYM ghash_reduce_raw fold-back fails post-cheap-close), so Q19 MUST be   *)
    (* peeled off before it runs.  `REPEAT CONJ_TAC` yields 20 atomic goals     *)
    (* (18 cheap + 1 Q19 + 1 flag); the per-goal dispatcher routes each:        *)
    (*   - Q19 (is_eq, RHS headed by byteswap128): Q19_FOLD_TAC (genuine down   *)
    (*     to the final lane-match, which is CHEAT'd inside Q19_FOLD_TAC);       *)
    (*   - everything else: the cheap-close rewrites (which also handle the      *)
    (*     out-forall case-split), then a nested split + flag-close / CHEAT for  *)
    (*     the out-forall (blocker B, advisor-gated).                           *)
    REPEAT CONJ_TAC THEN
    (fun (asl,w as gl) ->
      if is_eq w &&
         (try fst(dest_const(fst(strip_comb(rhs w)))) = "nist_ghash"
          with _ -> false)
      then Q19_FOLD_TAC gl
      else
       (REWRITE_TAC[MAIN_LOOP_OUT_DISJSPLIT] THEN
        ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
        REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
        REWRITE_TAC[ARITH_RULE `16 * (8 * (i+1) + b) = 128 * (i+1) + 16 * b`] THEN
        REWRITE_TAC[ARITH_RULE `16 * 8 * (i+1) = 128 * (i+1)`] THEN
        CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
        REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
        REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
        ONCE_REWRITE_TAC[WORD_BITWISE_RULE
          `word_xor (word_xor (inb:int128) ch) rk14 =
           word_xor ch (word_xor rk14 inb)`] THEN
        REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
        ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
        REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
        CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
        ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
        REWRITE_TAC[ADD_ASSOC; ARITH] THEN
        REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
        REWRITE_TAC[GSYM cipher_block] THEN
        REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
        REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
        SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
        REWRITE_TAC[WORD_SUBWORD_XOR] THEN
        REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REWRITE_TAC[WORD_SUBWORD_XOR] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
        REWRITE_TAC[AES256_CIPHER_KEYLIST]) gl) THEN
    (* --- Remaining after the split-first dispatcher (session 022):             *)
    (* the ~18 cheap conjuncts + all 16 ciphertext out-blocks CLOSE (validating  *)
    (* the +2 counter fix end-to-end).  Three obligations remain, TWO now GONE:  *)
    (*   (A) Q19 GHASH fold: NOW WIRED via NSTEP_G + the split-first dispatcher   *)
    (*       + Q19_FOLD_TAC (above), which folds the raw body-end reduce all the  *)
    (*       way to the final lane-match `byteswap128(prop3 A)=prop3 B` — that    *)
    (*       ONE lane-identity is the sole remaining CHEAT of blocker A (inside   *)
    (*       Q19_FOLD_TAC).  Everything from the raw ghash reduce down to the     *)
    (*       lane-match is genuinely proved (5-session Q19 dead-end resolved).    *)
    (*   (B) OLD out-forall (!j. j<8*(i+1) ==> read(out+16j) s = ...): the        *)
    (*       incoming invariant out-forall is DROPPED by ASSUMPTION_STATE_UPDATE  *)
    (*       at the first ciphertext store (step 330).  ROOT CAUSE (session 016): *)
    (*       ASSUMPTION_STATE_UPDATE_TAC advances an assumption over a store via  *)
    (*       STATE_UPDATE_RULE -> COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV,     *)
    (*       which DOES descend under the !j binder AND collects the antecedent   *)
    (*       j<8*(i+1) into its context (components.ml:3203) — BUT it then needs  *)
    (*       ORTHOGONAL_COMPONENTS_RULE to discharge orthogonality of             *)
    (*       bytes128(out_p+16*j) vs the store at bytes128(out_p+128*(i+1)),      *)
    (*       which requires the NONLINEAR bound 16*(j+1)<=128*(i+1) from          *)
    (*       j<8*(i+1); the driver machinery does not derive it for a SYMBOLIC    *)
    (*       product offset, so the update fails and the forall is erased.  This  *)
    (*       is genuinely novel: every existing s2n proof (e.g. emontredc) that   *)
    (*       advances a quantified memory forall over a store uses a FIXED unroll *)
    (*       and EXPAND_CASES_CONV to concrete indices; the x8 out-forall bound   *)
    (*       8*(i+1) is symbolic in i and cannot be expanded.  Needs either a     *)
    (*       symbolic-index bytes128 orthogonality lemma fed to the conv, or a    *)
    (*       reformulation.  (verbose-step PRESERVES the s329-ref forall; it is   *)
    (*       the subsequent DISCARD_OLDSTATE of the following NSTEP that drops it.)*)
    (*   (C) FLAG/PC-branch fact: the invariant q(i+1) = ((NF<=>VF)<=>(i+1=k))    *)
    (*       cannot close because MAIN_LOOP's antecedent does NOT constrain        *)
    (*       end_p.  Derived (session 016) from the .S setup (0x34-0x4c) + the    *)
    (*       body cmp@0x978 (X0=in_p+128*(i+2) at the cmp): the missing hyp is    *)
    (*       `end_p = word_add in_p (word (128 * (k + 1)))` (+ a k bound for the  *)
    (*       signed cmp no-overflow).  word_sub cancels in_p, leaving a pure      *)
    (*       k-bounded word fact.  This is a real invariant-completeness gap      *)
    (*       (like s008's v8..v15 and s015's +2) — add the end_p antecedent and   *)
    (*       re-close init/back-edge/exit; reconcile with P7 setup / P9 (end_p    *)
    (*       is how the iteration count k is pinned).                             *)
    (* SESSION 017: (C) is now CLOSED.  Added the two end_p antecedents to        *)
    (* MAIN_LOOP (`end_p = word_add in_p (word (128*(k+1)))` and the no-wrap      *)
    (* bound `val in_p + 128*(k+1) < 2 EXP 63`) and the BRIDGE_GE/IV_ADD lemmas   *)
    (* above.  The residual is A /\ C /\ B (Q19 fold / flag / out-forall+frame),  *)
    (* split by REPEAT CONJ_TAC.  The cheap-close's WORD_ADD normalisation splits *)
    (* the flag offsets to `word_add (word (128*i)) (word 256)` (= X0 = in_p +    *)
    (* 128*(i+2)) and `word_add (word (128*k)) (word 128)` (= end_p, already      *)
    (* substituted by ASM_REWRITE), so the flag close does NOT match FLAG_LEM     *)
    (* syntactically — instead it rewrites BRIDGE_GE (the NF!=VF biconditional =  *)
    (* signed GE `ival end_p <= ival X0`), linearises both additive ivals with    *)
    (* IV_ADD under the no-wrap bound, and finishes by INT/ARITH using `i < k`.   *)
    (* FLAG_LEM (above) packages the same reasoning for the un-normalised shape   *)
    (* and is kept as documentation.  A (Q19 fold) and B (OLD out-forall) still   *)
    (* CHEAT (B advisor-gated).                                                   *)
    REPEAT CONJ_TAC THEN
    (* Guard: fire the flag close ONLY on the flag-shaped goal — the sole
       residual whose conclusion is `<flag biconditional> <=> (i + 1 = k)`
       (RHS = `i + 1 = k`).  This keeps BRIDGE_GE off the ~186k-char Q19 term  *)
    (* (resid A).  CRITICAL: the flag arithmetic uses targeted UNDISCH_TAC of   *)
    (* the two needed hyps (`i < k`, the no-wrap bound) + bare ARITH_TAC — NOT  *)
    (* ASM_ARITH_TAC, which would scan every hyp (incl. the giant ciphertext/   *)
    (* Q19 facts) and wedge the checker (see holctl-operational-gotchas).       *)
    (let flag_arith =
       UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN
       UNDISCH_TAC `(i:num) < k` THEN ARITH_TAC in
     fun (asl,w as gl) ->
       (if (can (term_match [] `xxx:bool <=> (i:num) + 1 = k`) w)
        then
         (REWRITE_TAC[BRIDGE_GE] THEN
          MP_TAC(SPECL [`in_p:int64`; `128 * i + 256`] IV_ADD) THEN
          ANTS_TAC THENL [flag_arith; ALL_TAC] THEN
          MP_TAC(SPECL [`in_p:int64`; `128 * k + 128`] IV_ADD) THEN
          ANTS_TAC THENL [flag_arith; ALL_TAC] THEN
          REWRITE_TAC[GSYM WORD_ADD] THEN
          DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[INT_OF_NUM_LE] THEN flag_arith)
        (* BLOCKER B RESOLVED (session 030): the sole residual reaching this
           branch is the MAYCHANGE FRAME-subsumption goal `(<accumulated>) s0
           s339` (NOT the out-forall — that closes in the first dispatcher's
           cheap-close, since it SURVIVES to s339: re-observed s030, the
           s015/016 "dropped at store 330" finding was stale).  The body
           physically clobbers the FULL Q8..Q15 (the in-flight ciphertext
           blocks), whose low 64 bits the ABI frame forbids (v8-v15 are
           callee-saved).  The MAIN_LOOP conclusion frame was therefore
           widened with `MAYCHANGE [Q8;..;Q15]` (mirroring the proved x4
           kernel aes_gcm_enc_kernel_x4_reload_round_keys_full.ml:764); the
           low-half writes are restored by the d8-d15 epilogue at the
           subroutine wrapper (P10).  With the widened frame,
           MONOTONE_MAYCHANGE_TAC discharges the subsumption (the 8 ciphertext
           stores bytes128(out_p+128*(i+1)+16m) <= bytes(out_p,16*nb) follow
           from the `8*(k+1)<=nb` antecedent via CONTAINED_TAC).  *)
        else MONOTONE_MAYCHANGE_TAC) gl);

    (* Subgoal 4: back-edge taken (0 < i < k => b.lt branches back) *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC AESV8_GCM_8X_ENC_256_EXEC [1] THEN
    ASM_REWRITE_TAC[];

    (* Subgoal 5: exit fall-through (i = k => GE, b.lt not taken) *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC AESV8_GCM_8X_ENC_256_EXEC [1] THEN
    ASM_REWRITE_TAC[]]);;

(* SESSION 035: the SETUP Q30 (rev32 next-group counter) reconstruction.  A    *)
(* monolithic `REWRITE_TAC[ctr_block] THEN WORD_BLAST` on the whole Q30        *)
(* word_join HANGS (>120s, ignores SIGINT) because it bit-blasts the symbolic  *)
(* 96-bit nonce whole.  Lane-decomposition is instant: each 32-bit lane shares *)
(* the symbolic nonce structurally so WORD_BLAST matches it without blasting.  *)
(* Combine with CTR_BLOCK_RECONSTRUCT_REV32 (@~1538) to assemble the full      *)
(* word_reversefields 32 (ctr_block nonce 15).  Validated s035.                *)
let SETUP_Q30_LANES = prove
 (`(word_add (word_add
      (word_reversefields 8
        (word_subword (word_reversefields 8 (ctr_block nonce 2)) (96,32):int32))
      (word 12)) (word 1):int32 = word 15) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce 2)) (64,32):int32)) (word 0):int32
    = word_subword nonce (0,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce 2)) (32,32):int32)) (word 0):int32
    = word_subword nonce (32,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce 2)) (0,32):int32)) (word 0):int32
    = word_subword nonce (64,32))`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* SETUP FINAL_STATE reconstruction dispatcher (session 036).                 *)
(*                                                                           *)
(* After the SETUP drive reaches pc+0x498 and ENSURES_FINAL_STATE_TAC +       *)
(* ASM_REWRITE + REWRITE_TAC[htable_mem_8] + REPEAT CONJ_TAC splits the       *)
(* postcondition, the residual goals are dispatched by conclusion shape.      *)
(*                                                                           *)
(* CIPHER_ID_TAC: the AES-INPUT IDENTITY residual, block j (j=1..7):          *)
(*   word_xor (RF8 (aes256_cipher (RF8 <KS_j>) rk)) (inblock j) =             *)
(*   word_xor (RF8 (aes256_cipher (ctr_block nonce (j+2)) rk)) (inblock j)    *)
(* where <KS_j> is SETUP's rev32-built next-group keystream counter.  Peel    *)
(* the outer word_xor(-)(inblock j) + RF8 + aes256_cipher(-)rk via AP_THM/    *)
(* AP_TERM, leaving RF8<KS_j> = ctr_block nonce (j+2), which ctr_block +      *)
(* WORD_BLAST closes DIRECTLY (~60s).  NB the s034/s035 "monolithic BLAST     *)
(* hangs / type-ambiguity" was a floating-type-var artifact of find_term      *)
(* capture — on the real goal (fully typed) WORD_BLAST is fine because the    *)
(* symbolic 96-bit nonce appears identically on both sides.                   *)
let CIPHER_ID_TAC =
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST;;

(* CIPHER_CLOSE: the MAIN_LOOP body ciphertext chain (file ~3442-3465)         *)
(* specialized to SETUP.  Reduces the raw eor3/aese form                       *)
(*   word_xor (word_xor (inblock j) (aese..aese..rk13)) rk14                   *)
(* to the aes256_cipher form.  For block 0 (counter ctr_block nonce 2, no      *)
(* rev32 rebuild) it closes outright; for the out-forall's j=1..7 it leaves    *)
(* the AES-INPUT IDENTITY residual that CIPHER_ID_TAC then peels.              *)
let CIPHER_CLOSE =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 =
     word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  REWRITE_TAC[AES256_CIPHER_KEYLIST];;

(* CTR_CLOSE: Q0..Q4 (rev8) + Q30 (rev32) fresh-counter reconstruction. *)
let CTR_CLOSE =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SETUP_Q30_LANES; CTR_BLOCK_RECONSTRUCT_REV8;
              CTR_BLOCK_RECONSTRUCT_REV32] THEN
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST;;

(* FLAG_CLOSE: the prepretail-check flag conjunct ((NF<=>VF)<=>(0=k)) at i=0.  *)
(* Rewrite the raw round-down X5 pointer to end_p (X5_END_PTR after the DIV    *)
(* bridge), then discharge the signed compare with SETUP_GE_FALSE_2 (k>=1).    *)
let FLAG_CLOSE =
  REWRITE_TAC[BRIDGE_GE] THEN
  SUBGOAL_THEN
    `word_add (word_and (word_sub (word ((128 * nb) DIV 8):int64) (word 1))
                        (word 18446744073709551488)) in_p =
     word_add in_p (word (128 * (k + 1)))`
    SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM(ASSUME `8 * (k + 2) = nb`)] THEN
    REWRITE_TAC[ARITH_RULE `(128 * (8 * (k + 2))) DIV 8 = 16 * 8 * (k + 2)`] THEN
    MATCH_MP_TAC X5_END_PTR THEN
    MP_TAC(SPEC `in_p:int64` VAL_BOUND_64) THEN
    UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN ARITH_TAC;
    ASM_SIMP_TAC[MATCH_MP SETUP_GE_FALSE_2
      (CONJ (ASSUME `~(k = 0)`)
            (ASSUME `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`))]];;

(* Shape-routed dispatcher (NOT blind FIRST[] — that thrashes WORD_BLAST). *)
let SETUP_RECON_TAC : tactic =
  fun (asl,w as gl) ->
    if is_neg w then FLAG_CLOSE gl
    else if is_forall w then
      (REWRITE_TAC[ARITH_RULE `j < 8 * (0 + 1) <=>
                     j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/
                     j = 4 \/ j = 5 \/ j = 6 \/ j = 7`] THEN
       REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`] THEN
       REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
       CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[WORD_ADD_0] THEN
       REPEAT CONJ_TAC THEN CIPHER_CLOSE THEN TRY CIPHER_ID_TAC THEN
       TRY CIPHER_CLOSE) gl
    else if is_eq w then
      let l,r = dest_eq w in
      let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
      let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
      if rhd = "nist_ghash" then
        (CONV_TAC NUM_REDUCE_CONV THEN
         REWRITE_TAC[list_of_seq; NIST_GHASH_NIL] THEN CONV_TAC WORD_BLAST) gl
      else if lhd = "word_xor" && rhd = "word_xor" then
        (CIPHER_CLOSE THEN TRY CIPHER_ID_TAC THEN TRY CIPHER_CLOSE) gl
      else if lhd = "word_join" && rhd = "word_reversefields" then
        CTR_CLOSE gl
      else if lhd = "word_add" then
        FIRST
          [CONV_TAC WORD_RULE;
           (AP_TERM_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD; DIMINDEX_64] THEN
            AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);
           (ONCE_REWRITE_TAC[GSYM(ASSUME `8 * (k + 2) = nb`)] THEN
            REWRITE_TAC[ARITH_RULE
              `(128 * (8 * (k + 2))) DIV 8 = 16 * 8 * (k + 2)`] THEN
            MATCH_MP_TAC X5_END_PTR THEN
            MP_TAC(SPEC `in_p:int64` VAL_BOUND_64) THEN
            UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN
            ARITH_TAC)] gl
      else (* read = ... : surviving read-only reads (keys/htable/ivec/tag/stack) *)
        (ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV) gl
    else ASM_REWRITE_TAC[] gl;;

(* ------ generalized SETUP reconstruction (session 083) --------------------- *)
(* The g>=2 reassembly sub-leg reuses WB_SETUP's drive under the generalized    *)
(* precond `8*(k+1)<nb /\ nb<=8*(k+2)` (rem 1..8) instead of the rem=8-only     *)
(* `8*(k+2)=nb`.  Two recon closers hardcode `8*(k+2)=nb` + X5_END_PTR and must  *)
(* be generalized to SETUP_X5_END_GEN (valid for the whole rem 1..8 range):     *)
(*  (a) the flag conjunct closer FLAG_CLOSE (routed via the is_neg branch), and *)
(*  (b) the X5=end_p word_add closer (the 3rd FIRST alternative).               *)
(* FLAG_CLOSE_GEN mirrors FLAG_CLOSE but reduces the round-down X5 pointer to    *)
(* end_p via SETUP_X5_END_GEN.  Discovered s083 as the sole `Failure "ABS"`     *)
(* source (the committed FLAG_CLOSE's `GSYM(ASSUME 8*(k+2)=nb)` rewrite of nb    *)
(* raises ABS under the generalized precond); DIAG-probe-validated that with     *)
(* FLAG_CLOSE_GEN + the SETUP_X5_END_GEN word_add closer ALL ~34 recon conjuncts *)
(* close (No subgoals).                                                          *)
let FLAG_CLOSE_GEN =
  REWRITE_TAC[BRIDGE_GE] THEN
  SUBGOAL_THEN
    `word_add (word_and (word_sub (word ((128 * nb) DIV 8):int64) (word 1))
                        (word 18446744073709551488)) in_p =
     word_add in_p (word (128 * (k + 1)))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC SETUP_X5_END_GEN THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MATCH_MP SETUP_GE_FALSE_2
      (CONJ (ASSUME `~(k = 0)`)
            (ASSUME `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`))]];;

(* SETUP_RECON_TAC_GEN = SETUP_RECON_TAC with (1) is_neg -> FLAG_CLOSE_GEN and   *)
(* (2) the word_add X5 branch's 3rd alternative -> ASM_SIMP_TAC[SETUP_X5_END_GEN].*)
let SETUP_RECON_TAC_GEN : tactic =
  fun (asl,w as gl) ->
    if is_neg w then FLAG_CLOSE_GEN gl
    else if is_forall w then
      (REWRITE_TAC[ARITH_RULE `j < 8 * (0 + 1) <=>
                     j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/
                     j = 4 \/ j = 5 \/ j = 6 \/ j = 7`] THEN
       REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`] THEN
       REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
       CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[WORD_ADD_0] THEN
       REPEAT CONJ_TAC THEN CIPHER_CLOSE THEN TRY CIPHER_ID_TAC THEN
       TRY CIPHER_CLOSE) gl
    else if is_eq w then
      let l,r = dest_eq w in
      let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
      let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
      if rhd = "nist_ghash" then
        (CONV_TAC NUM_REDUCE_CONV THEN
         REWRITE_TAC[list_of_seq; NIST_GHASH_NIL] THEN CONV_TAC WORD_BLAST) gl
      else if lhd = "word_xor" && rhd = "word_xor" then
        (CIPHER_CLOSE THEN TRY CIPHER_ID_TAC THEN TRY CIPHER_CLOSE) gl
      else if lhd = "word_join" && rhd = "word_reversefields" then
        CTR_CLOSE gl
      else if lhd = "word_add" then
        FIRST
          [CONV_TAC WORD_RULE;
           (AP_TERM_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD; DIMINDEX_64] THEN
            AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);
           (ASM_SIMP_TAC[SETUP_X5_END_GEN])] gl
      else (* read = ... : surviving read-only reads (keys/htable/ivec/tag/stack) *)
        (ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV) gl
    else ASM_REWRITE_TAC[] gl;;

(* ========================================================================= *)
(* P7 - SETUP (pipeline fill).  Core entry pc+0x30 (just after the prologue's *)
(* stack adjust + callee-save spills + mod-const store + X9/X16/X11/X10       *)
(* remaps) through the pipeline-fill store to pc+0x498 (the main-loop top).   *)
(*                                                                           *)
(* This region: 0x30-0x8c builds the 8 CTR keystream inputs v0..v7 (rev32 of  *)
(* the counter) + loads rk0/rk1; 0x90-0x418 runs the 14 AES rounds on         *)
(* v0..v7 (= AESV8_GCM_8X_ENC_256_AES_SETUP region), with the tag loaded into *)
(* Q19 at 0x2e0 (ld1 v19; ext; rev64 => PLAIN tag0, confirmed by              *)
(* PLAIN_Q19_CHECK); 0x41c sets X4 = in_p + byte_len (tail end-ptr) and does  *)
(* the b.ge tail check (NOT taken when k>=1); 0x428-0x460 loads the 8         *)
(* plaintext blocks (ldp q8..q15,[x0],#32 x4), eor3s them with the AES        *)
(* keystream + rk14 to ciphertext, rev32s the next-group counters into        *)
(* v0..v7; 0x464-0x490 stores the 8 ciphertext blocks (stp q8..q15,[x2],#32   *)
(* x4); 0x494 does the b.ge prepretail check (NOT taken when k>=1) and falls  *)
(* through to 0x498.                                                          *)
(*                                                                           *)
(* Establishes MAIN_LOOP's precondition at i=0.  Because the loop body reads  *)
(* none of X4/X16 (only X0,X2,X5,X6,X10,X11), SETUP must produce X4 =         *)
(* in_p+16*nb (the scratch end-ptr, block-aligned byte_len = 16*nb) and X16 = *)
(* ivec_p (the saved ivec ptr for the counter writeback @0x1180); these were  *)
(* the two conjuncts fixed in MAIN_LOOP this session (s031).                  *)
(*                                                                           *)
(* mod_p is the on-stack modulo constant at stackpointer+0x40 (mov x10,       *)
(* sp,#0x40 @0x2c; the 0xc2..0 const was stored there @0x28).  We state the   *)
(* core with mod_p = word_add stackpointer (word 0x40); the subroutine        *)
(* wrapper (P10) ties stackpointer to the caller SP - 0x50.                   *)
(*                                                                           *)
(* STATUS (s031): interface pinned, body CHEAT'd - the 282-step symbolic exec *)
(* + counter/ciphertext/AES reconstruction is the next fill (mirrors the      *)
(* MAIN_LOOP body cheap-close + AES_SETUP recipe).                            *)
(*                                                                           *)
(* SESSION 031 DE-RISKING (body proof recipe, VALIDATED on the warm server):  *)
(*  - INIT + a SETUP-specific input SUBGOAL for blocks 0..7 at                 *)
(*    word_add in_p (word (16*j)) (NOT the loop body's 128*(i+1)+off) proves   *)
(*    by `REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC`.   *)
(*  - `MAP_EVERY NSTEP (1--252)` steps CLEAN (counter build + 14-round AES +   *)
(*    tag load); reuse the file's NSTEP/NORMOFF/LDP_STEP4 machinery verbatim.  *)
(*    ldp[x0]#32 at steps 255/256/264/265 (256/264/265 need LDP_STEP4-style);  *)
(*    stp[x2]#32 at 270/271/278/280; apply the s009 LENGTH->4604 rewrite.      *)
(*  - THE TWO BRANCH DISCHARGES (the real work): step 254 = b.ge@0x424 (tail   *)
(*    check) and step 282 = b.ge@0x494 (prepretail check).  Each emits a       *)
(*    conditional PC `if in_p >=_s X5 then <skip> else <fall through>` with     *)
(*    X5 = in_p + ((16*nb-1) & ~127).  Discharge `in_p < end_p` via the        *)
(*    file's BRIDGE_GE + IV_ADD signed-ptr lemmas (as the MAIN_LOOP flag       *)
(*    close does).  KEY IDENTITY (why the premise `8*(k+2)=nb`): for nb=8m,     *)
(*    (16*nb-1)&~127 = 128*(m-1), so main-loop-end = in_p+128*(m-1) and the     *)
(*    LAST 8-group is drained by prepretail -> k+1 = m-1 -> k = nb DIV 8 - 2.   *)
(*    (The `8*(k+2)=nb` premise is the s031 hypothesis for this; VERIFY it      *)
(*    against the real branch + reconcile with the P8 tail / P9 assembly.)     *)
(*  - FINAL_STATE reconstruction mirrors the MAIN_LOOP body cheap-close        *)
(*    (XOR_AES256_CIPHER_RECONSTRUCT + AES_CTR_BLOCK_RECONSTRUCT +             *)
(*    AES256_CIPHER_KEYLIST for Q8..Q15; CTR_BLOCK_RECONSTRUCT_* for Q0..Q4;   *)
(*    plain Q19 = nist_ghash..(8*0) = tag0, PROVED trivially s031).            *)
(* ========================================================================= *)

let AESV8_GCM_8X_ENC_256_SETUP = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     tag0 nonce rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 2) = nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (word_add stackpointer (word 0x40), 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x4f0) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 15)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 0)) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 1)) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 2)) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 3)) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 4)) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 5)) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 6)) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 7)) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 10)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 11)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 12)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 13)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 14)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)) /\
           ((read NF s <=> read VF s) <=> (0 = k)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  (* SESSION 033 STATUS — the DRIVE is fully validated; only the FINAL_STATE     *)
  (* reconstruction dispatcher needs shape-routing (blind FIRST[] is too slow).   *)
  (* Body is CHEAT'd so the file loads; the validated recipe below is the fill.   *)
  (*                                                                             *)
  (* KEY DECISION (s033): NSTEP throughout — the s032 "226s/step" wall was a      *)
  (* PLAIN-ARM_STEPS artifact (v30 counter term grows un-simplified under         *)
  (* rev32/add).  NSTEP's per-step WORD_SIMPLE_SUBWORD_CONV keeps v30 small:      *)
  (* NSTEP 1-24 = 2.6s, NSTEP 1-253 = 30s, full drive INIT->FINAL_STATE ~9 min.   *)
  (* DO NOT use the AES_SETUP big-step route — unnecessary.                       *)
  (*                                                                             *)
  (* VALIDATED DRIVE (reaches FINAL_STATE, PC = pc+0x498, 34 post-split goals):   *)
  (*   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;ALLPAIRS;ALL;         *)
  (*               NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN             *)
  (*   ENSURES_INIT_TAC "s0" THEN                                                 *)
  (*   RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]     *)
  (*       `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN                                *)
  (*   MAP_EVERY NSTEP (1--254) THEN NSTEP 255 THEN                              *)
  (*   RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE               *)
  (*     (CONJ (ASSUME `8 * (k + 2) = nb`)                                       *)
  (*           (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`));            *)
  (*     COND_CLAUSES]) THEN                                                      *)
  (*   LDP_SETUP_TAC 255 THEN LDP_SETUP_TAC 256 THEN MAP_EVERY NSTEP (257--263)   *)
  (*   THEN LDP_SETUP_TAC 264 THEN LDP_SETUP_TAC 265 THEN                         *)
  (*   MAP_EVERY NSTEP (266--281) THEN NSTEP 282 THEN                            *)
  (*   RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_2             *)
  (*     (CONJ (ASSUME `~(k = 0)`) (CONJ (ASSUME `8 * (k + 2) = nb`)              *)
  (*           (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`)));           *)
  (*     COND_CLAUSES]) THEN                                                      *)
  (*   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN                        *)
  (*   REWRITE_TAC[htable_mem_8] THEN REPEAT CONJ_TAC THEN <DISPATCHER>           *)
  (*                                                                             *)
  (* RECONSTRUCTION (the remaining fill): 34 goals.  ASM_REWRITE closes the       *)
  (* trivially-matching ones; the rest need per-shape closers (INDIVIDUALLY       *)
  (* VALIDATED this session — see /tmp/s033_validate.ml).  DO NOT use a blind     *)
  (* FIRST[...] over all goals: WORD_BLAST/WORD_RULE thrash on non-matching goals *)
  (* (>19 min, had to interrupt).  Route by goal shape like the MAIN_LOOP body    *)
  (* dispatcher (file ~3353: `if is_eq w && rhs-head = nist_ghash then ...`).     *)
  (* The closers (each proven to work standalone):                               *)
  (*  - X4 `word_add in_p (word_ushr (word (128*nb)) 3) = word_add in_p (16*nb)`: *)
  (*    AP_TERM_TAC THEN REWRITE_TAC[word_ushr;VAL_WORD;DIMINDEX_64] THEN          *)
  (*    AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC  (needs 128*nb<2^64). *)
  (*  - X5 = end_p: the round-down mask; X5_END_PTR (as SETUP_BRANCH_COND_FALSE).  *)
  (*  - pointer conjuncts (128 = 128*(0+1)): CONV_TAC WORD_RULE.                   *)
  (*  - Q19 = tag0: CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[list_of_seq;         *)
  (*    NIST_GHASH_NIL] THEN CONV_TAC WORD_BLAST.                                 *)
  (*  - flag (NF<=>VF)<=>(0=k): REWRITE_TAC[BRIDGE_GE] + SETUP_GE_FALSE_2 (0=k     *)
  (*    false, k>=1).                                                            *)
  (*  - counter Q0..Q4/Q30 + ciphertext Q8..Q15 + out-forall: the MAIN_LOOP body  *)
  (*    cheap-close chain at i=0 (WORD_SUBWORD_REVERSEFIELDS_32 +                  *)
  (*    WORD_SUBWORD_CTR_BLOCK_32 + CTR_BLOCK_RECONSTRUCT_REV8/REV32 +             *)
  (*    XOR_AES256_CIPHER_RECONSTRUCT + AES_CTR_BLOCK_RECONSTRUCT +                *)
  (*    AES256_CIPHER_KEYLIST; out-forall case-split j<8*(0+1)).  NB: verify the   *)
  (*    counter chain actually CLOSES the fresh-build Q0 form (byte-reversed +8    *)
  (*    increments); WORD_BLAST after ctr_block-unfold FAILED in isolation, so     *)
  (*    the MAIN_LOOP CTR chain (not raw WORD_BLAST) is the route — confirm.      *)
  (* ========================================================================= *)
  (* SESSION 034 FINDINGS (recovery of s033).  The DRIVE reaches FINAL_STATE +   *)
  (* the 34-goal split exactly as above (re-validated: S034_NSPLIT: 34).         *)
  (* COUNTER CLOSERS ARE SOLVED (the s033 "one unverified piece"):               *)
  (*  - rev8 Q0..Q4 (5 goals): `REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST`  *)
  (*    closes each in ~5s.  MUST NUM_REDUCE the `8*0+N` counter index to a       *)
  (*    literal first (else WORD_BLAST can't match `word (8*0+10)` on the RHS).   *)
  (*    The s033 CTR_CHAIN (WORD_SUBWORD_REVERSEFIELDS_32 + ...) does NOT close   *)
  (*    the SETUP fresh-build doubly-reversed form — use the ctr_block+BLAST.     *)
  (*  - rev32 Q30 (1 goal): monolithic WORD_BLAST CHURNS >120s on the symbolic    *)
  (*    96-bit nonce.  Use LANE-DECOMPOSITION instead (fast, ~1.4s): prove a      *)
  (*    4-conjunct `SETUP_Q30_LANES` lemma (each lane = `REWRITE_TAC[ctr_block]   *)
  (*    THEN CONV_TAC WORD_BLAST`, symbolic nonce shared so BLAST is instant),    *)
  (*    then `REWRITE_TAC[SETUP_Q30_LANES; CTR_BLOCK_RECONSTRUCT_REV32]`.  The     *)
  (*    lane lemma (validated /tmp/s034_q30full.ml):                              *)
  (*      (word_add (word_add (word_reversefields 8 (word_subword               *)
  (*        (word_reversefields 8 (ctr_block nonce 2)) (96,32):int32)) (word 12)) *)
  (*        (word 1):int32 = word 15) /\ <lanes 64/32/0 = word_subword nonce      *)
  (*        (0/32/64,32)>  — proved by REWRITE_TAC[ctr_block] THEN WORD_BLAST.     *)
  (* Dispatcher (SHAPE-ROUTED, validated /tmp/s034_dispatch.ml): route by concl   *)
  (* head — is_neg->flag(SETUP_GE_FALSE_2); is_forall->out-forall; is_eq split by *)
  (* (lhd,rhd): read/word_xor->AES ciphertext; word_join/nist_ghash->Q19=tag0;    *)
  (* word_join/word_reversefields->counter (lanes-then-mono); word_add->ptr/X4/X5.*)
  (* ~~~ SESSION 035: Q8..Q15 DROP FIXED (s034 root cause was WRONG) ~~~          *)
  (* s034 claimed Q8..Q15 drop at the `stp` store (steps 270-280) via             *)
  (* DISCARD_OLDSTATE.  REFUTED empirically: Q8 is already absent at s255 — right *)
  (* after the FIRST `ldp q8,q9,[x0],#32`@0x428 (step 255), BEFORE any store       *)
  (* (/tmp/s035_probe2/3: s255_Q8_RHS = `read(memory:>bytes128 in_p) s254`, an    *)
  (* UNRESOLVED opaque load).  REAL cause: the block-0 ldp reads at bare `in_p`,  *)
  (* but SETUP_INBLOCKS_TAC's memfact address is `word_add in_p (word (16*0))`    *)
  (* (unreduced) — no syntactic match, so REWRITE_RULE memfacts doesn't fire, the *)
  (* load stays opaque, and DISCARD_OLDSTATE drops it.  FIX (committed s035):     *)
  (* LDP_SETUP_TAC now NORMALIZES the memfacts (NUM_MULT_CONV reduces `16*j`;     *)
  (* WORD_ADD_0 collapses `word_add in_p (word 0)`->in_p) before the substitute.  *)
  (* With the fix, ALL Q8..Q15 survive to s282 (/tmp/s035_probe4).                *)
  (*                                                                             *)
  (* DISPATCHER (s035, /tmp/s035_final.ml — 34 conjuncts split by REPEAT         *)
  (* CONJ_TAC; NB htable_mem_8 stays FOLDED, do NOT unfold — 23 atomic goals):   *)
  (*   drive: INIT + s009 LENGTH rewrite + NSTEP(1-253) + branch254              *)
  (*     SETUP_BRANCH_COND_FALSE + LDP_SETUP_TAC 255/256 + NSTEP(257-263) +       *)
  (*     LDP_SETUP_TAC 264/265 + NSTEP(266-281) + NSTEP 282 +                     *)
  (*     SETUP_BRANCH_COND_FALSE_2 + FINAL_STATE + ASM_REWRITE + REPEAT CONJ_TAC. *)
  (*   post-fix goal shapes + status (disp2 live-goal test):                     *)
  (*     word_add=word_add (ptrs/X4/X5, 4): CLOSE — WORD_RULE / X4 word_ushr /    *)
  (*       X5_END_PTR.  [validated]                                              *)
  (*     word_join=word_reversefields (Q0-Q4 rev8 + Q30 rev32, 6): CLOSE —        *)
  (*       NUM_REDUCE + CTR_BLOCK_RECONSTRUCT_REV8/REV32 + SETUP_Q30_LANES        *)
  (*       (+ ctr_block/WORD_BLAST fallback).  [validated]                        *)
  (*     word_join=nist_ghash (Q19=tag0, 1): CLOSE — NUM_REDUCE + list_of_seq +   *)
  (*       NIST_GHASH_NIL + WORD_BLAST.  [validated]                             *)
  (*     word_xor=word_xor (Q8-Q15 ciphertext, 8): NOT YET closed.  After         *)
  (*       ASM_REWRITE the LHS is the eor3 form `word_xor(word_xor(inblock j)     *)
  (*       (aese..))rk14`.  MUST use the MAIN_LOOP ciphertext chain (file         *)
  (*       ~3442-3465) ending at AES256_CIPHER_KEYLIST — do NOT append            *)
  (*       ctr_block+WORD_BLAST (WORD_BLAST CANNOT blast through aes256_cipher;    *)
  (*       that was the s035_final crash).  The residual after the chain needs    *)
  (*       relating the SETUP-built keystream v0..v7 (rev32 of the fresh counter, *)
  (*       arg `word_join nonce (word 1)`-shaped) to `aes_ctr_block nonce rk j`   *)
  (*       via AES_CTR_BLOCK_RECONSTRUCT — verify the counter arg matches `j+2`.  *)
  (*       NEXT SESSION: capture the post-KEYLIST residual on ONE Q8 goal (avoid  *)
  (*       the rotation-while loop — it churns; use REPEAT CONJ_TAC THEN a        *)
  (*       shape-guarded closer, or peel the 8 ciphertext conjuncts by position). *)
  (*     OTHER (htable_mem_8 folded, 1): needs ASM_REWRITE[htable_mem_8] or the   *)
  (*       MAIN_LOOP htable closer — verify.                                      *)
  (*     FORALL (out-forall j<8*(0+1), 1): case-split j=0..7 + ciphertext chain.  *)
  (*     NEG (flag (NF<=>VF)<=>(0=k), 1): BRIDGE_GE + SETUP_GE_FALSE_2 — the      *)
  (*       disp2 form left a residual; check the exact biconditional shape.       *)
  (*     read=word (stack mod const, 1): ASM_REWRITE + numeral-normalize          *)
  (*       (word 0xc2..0 vs word 13979173243358019584 — same value).             *)
  (* SETUP_Q30_LANES is now a committed lemma (@~line 3567).  The LDP fix is      *)
  (* committed in LDP_SETUP_TAC.                                                  *)
  (* ~~~ SESSION 036: SETUP CLOSED CHEAT-FREE ~~~                                 *)
  (* Two remaining-goal root causes fixed this session:                          *)
  (*  (1) CIPHERTEXT (7 goals): the AES-INPUT IDENTITY residual RF8<KS_j> =       *)
  (*      ctr_block nonce (j+2) closes via CIPHER_ID_TAC (AP_THM/AP_TERM peel +   *)
  (*      ctr_block+WORD_BLAST).  The s034/s035 "monolithic BLAST hangs" was a    *)
  (*      floating-type-var artifact of find_term capture; on the real fully-     *)
  (*      typed goal WORD_BLAST closes each in ~60s.                              *)
  (*  (2) STACK mod-const: the ALLPAIRS had (stack+0x40,8) in the WRITABLE list,  *)
  (*      so nonoverlapping(out_p, stack+0x40) was never generated and the        *)
  (*      read fact was dropped at the ciphertext stores.  FIXED by moving it to  *)
  (*      the read-only list (mirrors MAIN_LOOP's mod_p).                         *)
  (*  (3) htable: the drive now RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8]) +      *)
  (*      REWRITE_TAC[htable_mem_8] so the 12 read-only reads propagate to s282   *)
  (*      (mirrors MAIN_LOOP:3300/3307).                                          *)
  (* Dispatcher = SETUP_RECON_TAC (shape-routed, @~line 3590).                    *)
  (* ========================================================================= *)
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8]) THEN
  SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 3)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 5)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 6)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 7)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
  NSTEP 37 THEN NSTEP 38 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`)); COND_CLAUSES]) THEN
  NSTEP 39 THEN NSTEP 40 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
  NSTEP 41 THEN NSTEP 42 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 3)`)); COND_CLAUSES]) THEN
  NSTEP 43 THEN NSTEP 44 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH5_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 5)`)); COND_CLAUSES]) THEN
  NSTEP 45 THEN NSTEP 46 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH6_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 6)`)); COND_CLAUSES]) THEN
  NSTEP 47 THEN NSTEP 48 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH7_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 7)`)); COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (49--273) THEN NSTEP 274 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE
    (CONJ (ASSUME `8 * (k + 2) = nb`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`)); COND_CLAUSES]) THEN
  LDP_SETUP_TAC 275 THEN LDP_SETUP_TAC 276 THEN MAP_EVERY NSTEP (277--283) THEN
  LDP_SETUP_TAC 284 THEN LDP_SETUP_TAC 285 THEN MAP_EVERY NSTEP (286--301) THEN
  NSTEP 302 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_2
    (CONJ (ASSUME `~(k = 0)`) (CONJ (ASSUME `8 * (k + 2) = nb`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`)));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[htable_mem_8] THEN
  REPEAT CONJ_TAC THEN SETUP_RECON_TAC);;

(* ========================================================================= *)
(* WB_SETUP_GEN (session 083) — the generalized pipeline-fill SETUP for the   *)
(* loop_count>=1 reassembly leg.  Identical to WB_SETUP EXCEPT the precond     *)
(* relaxes the rem=8-only `8*(k+2)=nb` to `8*(k+1)<nb /\ nb<=8*(k+2)` (rem in   *)
(* 1..8, groups=k+1), so the drive covers any leftover-block count the tail     *)
(* cascade drains.  The postcondition is IDENTICAL to WB_SETUP's (all `8*0+N`   *)
(* counter/keystream indices are rem-independent; only X4, the in-forall bound  *)
(* nb, and end_p reference nb).  Drive = WB_SETUP verbatim EXCEPT the two b.ge   *)
(* guard discharges use SETUP_BRANCH_COND_FALSE_GEN / _2_GEN (@~2620/2645) and  *)
(* the reconstruction uses SETUP_RECON_TAC_GEN (generalized flag + X5 closers). *)
(* The two guards fall through (b.ge NOT taken) for groups=k+1>=2, exactly as   *)
(* in WB_SETUP; the round-down end-ptr collapses to in_p+128*(k+1) via          *)
(* X5_END_PTR_GEN for the whole rem range.  Composes into the g>=2 leg as       *)
(* SETUP_GEN -> MAIN_LOOP -> PREPRETAIL -> WB_TAIL_REM(g=k+1, r=nb-8*(k+1)).     *)
let AESV8_GCM_8X_ENC_256_SETUP_GEN = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     tag0 nonce rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (word_add stackpointer (word 0x40), 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x4f0) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 15)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 0)) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 1)) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 2)) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 3)) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 4)) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 5)) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 6)) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 7)) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 10)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 11)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 12)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 13)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 14)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)) /\
           ((read NF s <=> read VF s) <=> (0 = k)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8]) THEN
  SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 3)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 5)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 6)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 7)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
  NSTEP 37 THEN NSTEP 38 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`)); COND_CLAUSES]) THEN
  NSTEP 39 THEN NSTEP 40 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
  NSTEP 41 THEN NSTEP 42 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 3)`)); COND_CLAUSES]) THEN
  NSTEP 43 THEN NSTEP 44 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH5_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 5)`)); COND_CLAUSES]) THEN
  NSTEP 45 THEN NSTEP 46 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH6_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 6)`)); COND_CLAUSES]) THEN
  NSTEP 47 THEN NSTEP 48 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH7_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 7)`)); COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (49--273) THEN NSTEP 274 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_GEN
    (CONJ (ASSUME `8 * (k + 1) < nb`) (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))); COND_CLAUSES]) THEN
  LDP_SETUP_TAC 275 THEN LDP_SETUP_TAC 276 THEN MAP_EVERY NSTEP (277--283) THEN
  LDP_SETUP_TAC 284 THEN LDP_SETUP_TAC 285 THEN MAP_EVERY NSTEP (286--301) THEN
  NSTEP 302 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_2_GEN
    (CONJ (ASSUME `~(k = 0)`) (CONJ (ASSUME `8 * (k + 1) < nb`)
      (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[htable_mem_8] THEN
  REPEAT CONJ_TAC THEN SETUP_RECON_TAC_GEN);;

(* ------------------------------------------------------------------------- *)
(* SETUP_G1 (session 084): the g=1 (k=0) pipeline-fill setup leg.  IDENTICAL   *)
(* drive to WB_SETUP_GEN EXCEPT: precond pins k=0 (so groups=1, nblocks 9..16); *)
(* at step 282 the 2nd main-loop-skip guard (b.ge@0x49c) is TAKEN (not fall-   *)
(* through) because end_p = in_p+128*(0+1) = in_p+128 = X0, so PC jumps to      *)
(* pc+0x9f0 (PREPRETAIL) NOT pc+0x4a0 (main loop top).  Discharge via           *)
(* SETUP_BRANCH_COND_TRUE_2 (vs FALSE_2_GEN).  Postcond = PREPRETAIL_GEN's      *)
(* precond at 0x9f0 in the k=0 (8*0) form (flag conjunct dropped).  0-hyp.      *)
(* ------------------------------------------------------------------------- *)
let AESV8_GCM_8X_ENC_256_SETUP_G1 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     tag0 nonce rk inblock nb k pc.
    k = 0 /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (word_add stackpointer (word 0x40), 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xa40) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 15)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 0)) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 1)) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 2)) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 3)) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 4)) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 5)) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 6)) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 7)) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 10)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 11)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 12)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 13)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 14)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8]) THEN
  SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 3)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 5)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 6)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 7)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
  NSTEP 37 THEN NSTEP 38 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`)); COND_CLAUSES]) THEN
  NSTEP 39 THEN NSTEP 40 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
  NSTEP 41 THEN NSTEP 42 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 3)`)); COND_CLAUSES]) THEN
  NSTEP 43 THEN NSTEP 44 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH5_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 5)`)); COND_CLAUSES]) THEN
  NSTEP 45 THEN NSTEP 46 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH6_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 6)`)); COND_CLAUSES]) THEN
  NSTEP 47 THEN NSTEP 48 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH7_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 7)`)); COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (49--273) THEN NSTEP 274 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_GEN
    (CONJ (ASSUME `8 * (k + 1) < nb`) (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))); COND_CLAUSES]) THEN
  LDP_SETUP_TAC 275 THEN LDP_SETUP_TAC 276 THEN MAP_EVERY NSTEP (277--283) THEN
  LDP_SETUP_TAC 284 THEN LDP_SETUP_TAC 285 THEN MAP_EVERY NSTEP (286--301) THEN
  NSTEP 302 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_TRUE_2
    (CONJ (ASSUME `k = 0`) (CONJ (ASSUME `8 * (k + 1) < nb`)
      (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[htable_mem_8] THEN
  REPEAT CONJ_TAC THEN SETUP_RECON_TAC_GEN);;

(* ========================================================================= *)
(* P7 - PREPRETAIL (pipeline DRAIN):  pc+0x9e8  ->  pc+0xeb8 (.L256_enc_tail) *)
(*                                                                           *)
(* The software pipeline runs one 8-block GHASH group BEHIND the ciphertext  *)
(* stores.  At MAIN_LOOP exit (i = k) the last in-flight group (ciphertext   *)
(* blocks 8k..8k+7, held in v8..v15) has been STORED but NOT yet GHASHed;     *)
(* Q19 still holds nist_ghash..(8*k).  PREPRETAIL is the drain that folds     *)
(* that final group into Q19, advancing it to nist_ghash..(8*(k+1)), and     *)
(* finishes the AES of the NEXT 8 counter blocks (v0..v7, pre-rk14) that the  *)
(* tail cascade will consume.  It performs NO ciphertext stores and NO        *)
(* plaintext loads (all `[x0]`/`[x2]` access is in the tail, >= 0xeb8), and   *)
(* leaves every GPR (X0,X2,X3,X4,X5,X6,X10,X11,X16) UNCHANGED (objdump-       *)
(* verified: no add/sub/mov to those regs in 0x9e8..0xeb4).                   *)
(*                                                                           *)
(* The PREPRETAIL precondition is EXACTLY the MAIN_LOOP postcondition at      *)
(* i = k (the state at pc+0x9e8), plus aligned_bytes_loaded; they are bridged *)
(* at P9 by ENSURES_SEQUENCE_TAC.  The Q19 drain fold is STRUCTURALLY         *)
(* IDENTICAL to the MAIN_LOOP body's (same leading `ext v19`@0xa50 PRE-       *)
(* byteswap, same pmull/pmull2/eor3 Karatsuba chain, same trailing raw        *)
(* MODULO `eor3 v19,v19,v21,v17`@0xe98, NO trailing `ext v19`), so it closes  *)
(* via the ALREADY-PROVEN Q19_FOLD_TAC (route-c plain form).                  *)
(*                                                                           *)
(* SESSION 038 — BODY CLOSED CHEAT-FREE.  The s037 "accumulators drop         *)
(* mid-drive" diagnosis was WRONG: probing register presence + concreteness   *)
(* at s30/s150/s250/s301/s308 shows Q17/Q18/Q19 are all PRESENT and CONCRETE   *)
(* (no old-state refs) through s308; the drive `MAP_EVERY NSTEP_GP (1--308)`   *)
(* reaches pc+0xeb8 with Q19 = the concrete sz365k raw fold.  FINAL_STATE +    *)
(* REPEAT CONJ_TAC leaves exactly 10 residuals: Q30 counter, Q19 GHASH fold,   *)
(* and the 8 v0..v7 AES reconstructions (the rest close by ASM_REWRITE).       *)
(*                                                                           *)
(*   THE REAL (and only) OBSTRUCTION was that the drain's MODULO reduce has a  *)
(*   DIFFERENT instruction schedule from the main-loop/standalone reduce.  Its *)
(*   final `eor3 v19,v19,v21,v17`@0xe98 takes v21 = ext(v18)@0xe74 (-> Q21)    *)
(*   and v17 = pmull(v18,w)@0xe3c (-> Q17).  The plain body stepper NSTEP_G     *)
(*   protects Q17/Q18/Q19 from WORD_SIMPLE_SUBWORD_CONV but NOT Q21, so the     *)
(*   SAME mid-accumulator v18 appeared UN-normalized inside the pmull (via Q17) *)
(*   but NORMALIZED inside the ext (via Q21) — `ghash_reduce_raw`'s q18         *)
(*   requires the two identical, so RECON_GRR (GSYM ghash_reduce_raw) could not *)
(*   higher-order match (verified: WORD_SIMPLE_SUBWORD_CONV on both makes them  *)
(*   equal).  FIX = NSTEP_GP, an extended-guard stepper that ALSO protects      *)
(*   Q20/Q21 (the ext-scratch), keeping v18 un-normalized in both positions.    *)
(*   With NSTEP_GP the AC-swap + RECON_GRR fold-back FIRES (365k -> 69k) and     *)
(*   the k-indexed fold Q19_FOLD_TAC_K (= Q19_FOLD_TAC with i->k) closes it     *)
(*   exactly as the main-loop body does.                                       *)
(*                                                                           *)
(* Exit forms VERIFIED on gate033b (drive to s308):                          *)
(*   PC = pc+0xeb8; X0..X16 all preserved; Q31 preserved;                     *)
(*   Q28 = word_reversefields 8 (EL 14 rk)  (rk14, the tail's fused round key);*)
(*   Q30 exit = word_join lane-decomp of the +3-incremented counter =         *)
(*     word_reversefields 32 (ctr_block nonce (8*k+18))  (3 `add v30`@0x9f0/  *)
(*     0x9fc/0xe80; the high 32-lane gets +2+1);                              *)
(*   Q0..Q4 = 13-round aese/aesmc chain over word_reversefields 8 (ctr_block  *)
(*     nonce (8*k+10+j))  (the pre-loaded counters, pre-rk14 AES state);       *)
(*   Q5..Q7 = same chain over the rev32 word_join decomp of ctr_block nonce   *)
(*     (8*k+15)  (freshly rev32'd from the incremented v30).                  *)
(* The v0..v7 postcondition below states them as XOR_AES256_CIPHER_RECONSTRUCT-*)
(* reducible forms (word_xor (read Qj) rk14 = word_reversefields 8 (aes256_   *)
(* cipher ...)), matching the AES_SETUP convention and what the tail consumes  *)
(* (tail's first `eor3 v9,v8,v0,v28` XORs v0 with v28=rk14).                  *)
(* ========================================================================= *)

(* Extended-guard body stepper for the drain.  NSTEP_G protects Q17/Q18/Q19    *)
(* from the per-step WORD_SIMPLE_SUBWORD_CONV; the drain additionally needs     *)
(* Q20/Q21 protected because its reduce takes ext(v18)->Q21 and pmull(v18)->Q17 *)
(* at DIFFERENT steps (0xe74 vs 0xe3c), and if Q21's subwords are collapsed the *)
(* two copies of the mid-accumulator v18 diverge and RECON_GRR can't match.     *)
let is_ghash_acc_pp th =
  let c = concl th in
  can (find_term (fun t -> match t with
      Comb(Const("read",_), r) ->
        (match r with
         | Const("Q17",_) | Const("Q18",_) | Const("Q19",_)
         | Const("Q20",_) | Const("Q21",_) -> true
         | _ -> false)
    | _ -> false)) c;;

(* PERF (session 060): fold the three per-step RULE_ASSUM_TAC passes into ONE, and     *)
(* extend the is_ghash_acc_pp guard (already on the subword pass since s057) to ALSO    *)
(* cover the word_add-nest REWRITE and NORMOFF passes.  Rationale: those two passes are *)
(* PROOF-PRESERVING no-ops on the giant Q17..Q21 GHASH accumulators — the word_add-nest *)
(* rule fires only on `word_add(word_add _ (word _))(word _)` (register-pointer shape,   *)
(* absent from the word_join/word_subword accumulator folds) and NORMOFF only rewrites  *)
(* `word(c1+c2+..)` offsets (also absent) — yet REWRITE_RULE / CONV_RULE(ONCE_DEPTH)     *)
(* still fully TRAVERSE each ~70k–365k-char accumulator every step (O(term-size) per     *)
(* fact per step).  Skipping the accumulators entirely (all three sweeps are identity    *)
(* on them) makes per-step assumption cost FLAT in accumulator size instead of growing;  *)
(* on every OTHER fact the composed sweep is bit-identical to the old three passes.      *)
(* VALIDATED (session 061, warm s2n-wbtail checkpoint): on the SAME post-prefix state,    *)
(* driving a fixed drain block with the old (s057) vs this stepper yields a BIT-IDENTICAL *)
(* goal (full sorted-hyps+concl signature: len=150012 hash=311606506 both), confirming    *)
(* proof-preserving; and it is measurably faster per step — block 41--70 23.8s->20.6s     *)
(* (~13.5%), heavy-accumulator block 100--125 35.1s->28.7s (~18%, 6.4s), each reproduced   *)
(* twice.  Since every drain step runs this and the late reduce/fold steps dominate, the   *)
(* whole-drive (10--139) speedup is >=13%.                                                 *)
let NSTEP_GP_WADD_RULE = REWRITE_RULE[WORD_RULE
  `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`];;

(* PERF (session 068): guard BOTH the word_add-nest flatten (has_wadd_nest) and the      *)
(* NORMOFF offset renormalisation (has_word_of_sum) with cheap short-circuiting            *)
(* find_terms, so each REWRITE_RULE / CONV_RULE net-walk runs only on facts that actually  *)
(* carry its redex.  Bit-identical to the bare passes per fact (each is a no-op on facts   *)
(* lacking its shape, exactly what the guard skips), but avoids the traversal on the ~110   *)
(* carried facts that lack it.  Measured ~4.7% on the full (10--136) WB_TAIL drive, twice,  *)
(* bit-identical goal signature (see has_wadd_nest / has_word_of_sum above).                *)
let NSTEP_GP n =
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_ghash_acc_pp th then th
    else
      let th1 = if has_wadd_nest (concl th) then NSTEP_GP_WADD_RULE th else th in
      let th2 = if has_word_of_sum (concl th1) then NORMOFF_RULE th1 else th1 in
      SUBWORD_NORM_RULE th2);;

(* The Q19 drain fold: Q19_FOLD_TAC with the accumulator index i -> k (the      *)
(* drain folds the last in-flight 8-block group at loop-bound k, advancing Q19  *)
(* from nist_ghash..(8*k) to nist_ghash..(8*(k+1))).  Structurally identical to *)
(* the main-loop body fold; see Q19_FOLD_TAC above for the full route rationale.*)
let Q19_FOLD_TAC_K =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (x:int128) e) p = word_xor (word_xor x p) e`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_DIST8_PLAIN] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * (k + 1) = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * k))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8*k+1);
       nist_cipher_block nonce rk inblock (8*k+2);
       nist_cipher_block nonce rk inblock (8*k+3);
       nist_cipher_block nonce rk inblock (8*k+4);
       nist_cipher_block nonce rk inblock (8*k+5);
       nist_cipher_block nonce rk inblock (8*k+6);
       nist_cipher_block nonce rk inblock (8*k+7)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8*k))`;
     `nist_cipher_block nonce rk inblock (8*k)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* Q30 counter closer (drain does 3 `add v30`, so exit counter = 8*k+18). *)
let PP_CTR_CLOSE =
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(* v0..v7 AES closer.  v0..v4 are pinned as word_reversefields 8 (ctr_block ..) *)
(* so AES256_CIPHER_RECONSTRUCT + MAP + KEYLIST close directly.  v5..v7 are      *)
(* freshly rev32'd from the incremented v30, so the AES reconstruct leaves a     *)
(* plaintext residual word_reversefields 8 (aes256_cipher <rev-lanes> rk) =      *)
(* ..(ctr_block ..) which the counter-lane reconstruct (WORD_SUBWORD_*32 +       *)
(* CTR_BLOCK_RECONSTRUCT_REV8 + REVERSEFIELDS_REVERSEFIELDS) folds; the TRY      *)
(* makes it a no-op for v0..v4 (already closed).                                *)
let PP_AES_CLOSE =
  ASM_REWRITE_TAC[AES256_CIPHER_RECONSTRUCT; MAP;
                  WORD_REVERSEFIELDS_REVERSEFIELDS; AES256_CIPHER_KEYLIST] THEN
  TRY(REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
      REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      REFL_TAC);;

(* Shape-routed per-goal dispatcher over the 10 post-FINAL_STATE residuals:     *)
(* nist_ghash-RHS -> Q19 fold; word_join=word_reversefields -> Q30 counter;     *)
(* the 8 v-register AES eqs -> PP_AES_CLOSE; anything else -> ASM_REWRITE.       *)
let PP_DISPATCH : tactic = fun (asl,w as gl) ->
  if is_eq w then
    let l,r = dest_eq w in
    let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
    let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
    if rhd = "nist_ghash" then Q19_FOLD_TAC_K gl
    else if lhd = "word_join" && rhd = "word_reversefields" then PP_CTR_CLOSE gl
    else PP_AES_CLOSE gl
  else ASM_REWRITE_TAC[] gl;;

let AESV8_GCM_8X_ENC_256_PREPRETAIL = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (mod_p, 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xa40) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 15)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * k)) /\
           read Q8 s = word_xor (aes_ctr_block nonce rk (8 * k + 0)) (inblock (8 * k + 0)) /\
           read Q9 s = word_xor (aes_ctr_block nonce rk (8 * k + 1)) (inblock (8 * k + 1)) /\
           read Q10 s = word_xor (aes_ctr_block nonce rk (8 * k + 2)) (inblock (8 * k + 2)) /\
           read Q11 s = word_xor (aes_ctr_block nonce rk (8 * k + 3)) (inblock (8 * k + 3)) /\
           read Q12 s = word_xor (aes_ctr_block nonce rk (8 * k + 4)) (inblock (8 * k + 4)) /\
           read Q13 s = word_xor (aes_ctr_block nonce rk (8 * k + 5)) (inblock (8 * k + 5)) /\
           read Q14 s = word_xor (aes_ctr_block nonce rk (8 * k + 6)) (inblock (8 * k + 6)) /\
           read Q15 s = word_xor (aes_ctr_block nonce rk (8 * k + 7)) (inblock (8 * k + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + 10)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + 11)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + 12)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + 13)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + 14)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 18)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * (k + 1))) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 10)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 11)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 12)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 13)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 14)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 15)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 16)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 17)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  (* SESSION 038: body CLOSED CHEAT-FREE.  Drive the 308-instr drain with the   *)
  (* extended-guard stepper NSTEP_GP (protects Q17..Q21 so the reduce's mid      *)
  (* accumulator v18 stays un-normalized in both the pmull and ext positions),   *)
  (* then FINAL_STATE + REPEAT CONJ_TAC + the shape-routed dispatcher            *)
  (* PP_DISPATCH (Q19 fold / Q30 counter / v0..v7 AES / ASM_REWRITE).            *)
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  MAP_EVERY NSTEP_GP (1--308) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN PP_DISPATCH);;

(* ------------------------------------------------------------------------- *)
(* PREPRETAIL_GEN (session 084): PREPRETAIL with the VESTIGIAL `~(k = 0)`      *)
(* precond conjunct DROPPED, so it also covers k=0 (the g=1 reassembly leg,    *)
(* nblocks 9..16, where the main loop runs 0 times and prepretail+tail do all  *)
(* the work).  The body (@4892-4900) is pure straight-line GHASH drain          *)
(* (REWRITE+STRIP+INIT + MAP_EVERY NSTEP_GP (1--308) + FINAL_STATE +           *)
(* PP_DISPATCH) with NO branch and ZERO uses of `~(k = 0)` — verified s084 by   *)
(* diff-check (NSTEP_GP is k-independent; PP_DISPATCH/Q19_FOLD_TAC_K use 8*k    *)
(* symbolically but never case-split k=0).  Re-proves byte-identically         *)
(* (PP_GEN_HYPS=0).  The body below is IDENTICAL to PREPRETAIL's.              *)
(* ------------------------------------------------------------------------- *)
let AESV8_GCM_8X_ENC_256_PREPRETAIL_GEN = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb k pc.
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (mod_p, 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xa40) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 15)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * k)) /\
           read Q8 s = word_xor (aes_ctr_block nonce rk (8 * k + 0)) (inblock (8 * k + 0)) /\
           read Q9 s = word_xor (aes_ctr_block nonce rk (8 * k + 1)) (inblock (8 * k + 1)) /\
           read Q10 s = word_xor (aes_ctr_block nonce rk (8 * k + 2)) (inblock (8 * k + 2)) /\
           read Q11 s = word_xor (aes_ctr_block nonce rk (8 * k + 3)) (inblock (8 * k + 3)) /\
           read Q12 s = word_xor (aes_ctr_block nonce rk (8 * k + 4)) (inblock (8 * k + 4)) /\
           read Q13 s = word_xor (aes_ctr_block nonce rk (8 * k + 5)) (inblock (8 * k + 5)) /\
           read Q14 s = word_xor (aes_ctr_block nonce rk (8 * k + 6)) (inblock (8 * k + 6)) /\
           read Q15 s = word_xor (aes_ctr_block nonce rk (8 * k + 7)) (inblock (8 * k + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + 10)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + 11)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + 12)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + 13)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + 14)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 18)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * (k + 1))) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 10)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 11)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 12)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 13)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 14)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 15)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 16)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 17)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  (* SESSION 038: body CLOSED CHEAT-FREE.  Drive the 308-instr drain with the   *)
  (* extended-guard stepper NSTEP_GP (protects Q17..Q21 so the reduce's mid      *)
  (* accumulator v18 stays un-normalized in both the pmull and ext positions),   *)
  (* then FINAL_STATE + REPEAT CONJ_TAC + the shape-routed dispatcher            *)
  (* PP_DISPATCH (Q19 fold / Q30 counter / v0..v7 AES / ASM_REWRITE).            *)
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  MAP_EVERY NSTEP_GP (1--308) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN PP_DISPATCH);;

(* ========================================================================= *)
(* P8 — TAIL cascade (WHOLE-BLOCKS variant, pc+0xec0 -> pc+0x11a4).           *)
(*                                                                           *)
(* This is the pipeline EPILOGUE: it processes the FINAL in-flight 8-block    *)
(* group (keystreams pre-loaded in Q0..Q7 at prepretail exit, output blocks   *)
(* 8*(k+1)..8*(k+1)+7 = nb-8..nb-1) — storing their ciphertext and folding    *)
(* them into the GHASH accumulator Q19 — then does the final GF(2^128)        *)
(* MODULO reduce (0x1178-0x119c) and the two memory writebacks:               *)
(*   str q30,[x16]  (0x114c) -> ivec  = word_reversefields 8 (ctr_block .. nb+2)*)
(*   st1 {v19},[x3] (0x11a0) -> tag   = word_reversefields 8 (nist_ghash .. nb) *)
(*                                                                           *)
(* SCOPE: block-aligned (nb = 8*(k+2)).  At tail entry the remaining-bytes    *)
(* register x5 = X4 - X0 = 16*nb - 128*(k+1) = 128, so the computed cascade   *)
(* `cmp x5,#0x70; b.gt`@0xee4 ALWAYS takes the full 8-block path (0xfa0);      *)
(* the tail is a single straight-line drain, NOT the 8 partial cascade        *)
(* variants (which the whole-blocks .S never reaches for a whole multiple of  *)
(* 8 blocks).  The final-block path has NO partial-block masking (the .S      *)
(* divergence from the original: deleted the ld1 overread / mvn/lsr/csel mask *)
(* / and v9,v0 / bif — final block is a plain full block).                    *)
(*                                                                           *)
(* The Q19 drain fold is STRUCTURALLY the SAME KIND as PREPRETAIL / MAIN_LOOP *)
(* (pmull/pmull2/eor3 Karatsuba over the 8 fresh cipherblocks, reduce), so it *)
(* reuses the P6/P7 machinery (NSTEP_GP / RECON_GRR / Q19_FOLD_TAC-style).    *)
(* The x4 template is aes_gcm_enc_kernel_x4_fast_tail.ml (single-acc tail).    *)
(*                                                                           *)
(* STATUS (session 039): interface pinned, body CHEAT'd so the file loads.    *)
(* The precondition is PREPRETAIL's postcondition verbatim (pc+0xec0 state).  *)
(* NB the return value X0 = X9 = byte_len (mov x0,x9@0x11a4) is NOT asserted   *)
(* in the postcondition (mirrors x4 fast_tail, whose _CORRECT/_SUBROUTINE     *)
(* both omit the X0 return value); the tail ends at pc+0x11a4 just after the  *)
(* last crypto store, and the wrapper handles the ldp epilogue + ret.         *)
(* ========================================================================= *)

(* Store-permutation lemmas (ported from x4 fast_tail @437/457):              *)
(* TAG_STORE_REV64 = the `ext v19;#8` + `rev64 v19` byte-permutation the tail  *)
(* applies before st1 [x3] equals word_reversefields 8; IVEC_STORE_REV32 = the *)
(* rev32 v30 permutation before str [x16].  Both pure BITBLAST (session 040).  *)
let TAG_STORE_REV64 = prove
 (`!x:int128.
    word_join
     (word_join
      (word_join
       (word_join (word_subword x (0,8):byte) (word_subword x (8,8):byte):int16)
       (word_join (word_subword x (16,8):byte) (word_subword x (24,8):byte):int16):int32)
      (word_join
       (word_join (word_subword x (32,8):byte) (word_subword x (40,8):byte):int16)
       (word_join (word_subword x (48,8):byte) (word_subword x (56,8):byte):int16):int32):int64)
     (word_join
      (word_join
       (word_join (word_subword x (64,8):byte) (word_subword x (72,8):byte):int16)
       (word_join (word_subword x (80,8):byte) (word_subword x (88,8):byte):int16):int32)
      (word_join
       (word_join (word_subword x (96,8):byte) (word_subword x (104,8):byte):int16)
       (word_join (word_subword x (112,8):byte) (word_subword x (120,8):byte):int16):int32):int64):int128
    = word_reversefields 8 x`,
  CONV_TAC BITBLAST_RULE);;

(* [s117] tbl tail-format: the fast2 drain replaces the `ext v19;#8 ; rev64 v19`  *)
(* 16-byte byte-reverse with a single `tbl v19.16b,{v19.16b},v25.16b` where v25 = *)
(* the reverse index [15..0] = word 0x000102030405060708090a0b0c0d0e0f. arm_TBL   *)
(* (datasize 128) yields `usimd16 (\x. word_subword Q19 (8*val x,8)) Q25`; with   *)
(* Q25 = that index this equals word_reversefields 8 Q19, so the drain closes     *)
(* EXACTLY as the ext+rev64 path (TAG_STORE_REV64) did.                           *)
let TBL_IS_REVERSEFIELDS = prove
 (`usimd16 (\x. word_subword (n:int128) (8 * val x,8):byte)
     (word 0x000102030405060708090a0b0c0d0e0f:int128) = word_reversefields 8 n`,
  REWRITE_TAC[usimd16; usimd8; usimd4; usimd2] THEN
  CONV_TAC(TOP_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC WORD_BLAST);;

let IVEC_STORE_REV32 = prove
 (`!y:int128.
    word_join
     (word_join
      (word_reversefields 8 (word_subword (word_reversefields 32 y) (96,32):int32):int32)
      (word_reversefields 8 (word_subword (word_reversefields 32 y) (64,32):int32):int32):int64)
     (word_join
      (word_reversefields 8 (word_subword (word_reversefields 32 y) (32,32):int32):int32)
      (word_reversefields 8 (word_subword (word_reversefields 32 y) (0,32):int32):int32):int64):int128
    = word_reversefields 8 y`,
  CONV_TAC BITBLAST_RULE);;

(* x5 at the tail entry (sub x5,x4,x0@0xec4) = (in_p+16*nb) - (in_p+128*(k+1)) *)
(* = 128 under block-aligned nb = 8*(k+2); once rewritten to `word 128` the    *)
(* NSTEP_GP over cmp x5,#0x70 ; b.gt@0xee4 resolves the branch to pc+0xfa0     *)
(* automatically (concrete flag), so NO separate branch-discharge lemma.       *)
let TAIL_X5_128 = prove
 (`!(in_p:int64) nb k.
     8 * (k + 2) = nb
     ==> word_sub (word_add in_p (word (16 * nb)))
                  (word_add in_p (word (128 * (k + 1)))) = word 128:int64`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE);;

(* KS_SOLVE (session 041): invert a keystream precondition fact                 *)
(* `word_xor (read Vm s) rk14 = KS` into register-concrete form                 *)
(* `read Vm s = word_xor KS rk14`.  This is THE store-retention key for the      *)
(* tail: the 8 `st1 {v9},[x2],#16` ciphertext stores produce facts              *)
(* `read(mem out+off) s = read Q9 s_prev` whose RHS references the keystream     *)
(* register via the eor3; only known in XORed form the store RHS stays          *)
(* state-dependent and DISCARD_OLDSTATE drops it.  Inverting the 8 keystream     *)
(* facts at s0 (before stepping) makes each read Vm register-CONCRETE, so every  *)
(* eor3 ciphertext output (and thus each store fact RHS) is state-independent    *)
(* and survives.  (The x8-tail analogue of why x4 fast_tail, whose AES is inline *)
(* so keystreams are concrete, needs no store retention.)                        *)
let KS_SOLVE = prove
 (`!a b c:int128. word_xor a b = c ==> a = word_xor c b`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* Eta/beta collapse for the accumulator-block (block-0) artifact.  The batched   *)
(* fold's block-0 index 8*(k+1)+0 reduces to 8*(k+1), and higher-order matching in *)
(* GHASH_POLYVAL_ACC_BATCHED leaves the `inblock` slot as a CONSTANT lambda        *)
(* `nist_cipher_block nonce rk (\x. inblock (8*(k+1))) (8*(k+1))` — beta-equal to   *)
(* the clean form but opaque to WORD_BITWISE_RULE (which can't see through         *)
(* nist_cipher_block).  ETA_CONV does NOT fire (the lambda is constant, not \x.f x)*)
(* so a targeted beta-collapse lemma is needed before the final AP_TERM.           *)
let NCB_ETA = prove
 (`nist_cipher_block nonce rk (\x:num. inb (m:num)) m =
   nist_cipher_block nonce rk inb m`,
  REWRITE_TAC[nist_cipher_block; cipher_block] THEN CONV_TAC(DEPTH_CONV BETA_CONV));;

(* The TAIL Q19 drain fold: folds the FINAL in-flight 8-block group                *)
(* 8*(k+1)..8*(k+1)+7, advancing Q19 from nist_ghash..(8*(k+1)) to                  *)
(* nist_ghash..(8*(k+2)) = ..nb (one more GHASH_ACC_APPEND round than PREPRETAIL).  *)
(*                                                                                 *)
(* SESSION 065: this is NOT Q19_FOLD_TAC_K verbatim.  Two hardware divergences make *)
(* the tail's reduce differ from PREPRETAIL's, both byte-verified via objdump:      *)
(*                                                                                 *)
(*  (1) OPERAND ORDER of the final reduce eor3.  PREPRETAIL@0x9d0 emits             *)
(*      `eor3 v19,v19,v21,v17` (ext,pmull) = `word_xor (word_xor p3 ext) pmull`, so *)
(*      it needs a leading AC-swap to reach ghash_reduce_raw's `word_xor(word_xor   *)
(*      p3 pmull) ext` shape.  The TAIL@0x1194 emits `eor3 v19,v19,v17,v21`         *)
(*      (pmull,ext) = ALREADY in ghash_reduce_raw order — so the copied leading     *)
(*      acswap flips it OUT (RECON_GRR no-ops -> AP_TERM_TAC head mismatch = the     *)
(*      full-file-gate `Failure "AP_TERM_TAC"`).  FIX: DROP the leading acswap.      *)
(*                                                                                 *)
(*  (2) BLOCK PROVENANCE.  PREPRETAIL folds the INVARIANT-CLEAN v8..v15 blocks       *)
(*      (`word_xor (aes_ctr_block J) (inblock J)`).  The TAIL recomputes the last 8  *)
(*      blocks fresh (eor3 v9,v8,v0,v28 + KS_SOLVE), so each block enters the reduce *)
(*      as the RAW form `word_xor (word_xor inblock (word_xor aes rk14)) rk14`       *)
(*      (double-rk14, inblock-first, aes NOT folded to aes_ctr_block).  It must be   *)
(*      normalised to the clean `cipher_block` shape BEFORE the proven route:        *)
(*        - blocknorm cancels the double rk14 (word_xor (word_xor i (word_xor a r))  *)
(*          r = word_xor i a);                                                       *)
(*        - WORD_REDUCE_CONV+WORD_XOR_0 clear a spurious word_subword(word 0)(64,64);*)
(*        - comm_ib flips inblock-first -> aes-first (word_xor i (rev8 a) =          *)
(*          word_xor (rev8 a) i);                                                    *)
(*        - the ctr index 8*k+(10+m) = (8*(k+1)+m)+2 lets GSYM aes_ctr_block fold    *)
(*          rev8(aes256_cipher (ctr_block nonce (J+2)) rk) -> aes_ctr_block J, then  *)
(*          GSYM cipher_block + CIPHER_BLOCK_NIST reach nist_cipher_block.           *)
(*                                                                                 *)
(*  After cleaning, the tail's three Karatsuba lanes are ALIGNED (block order        *)
(*  [7..0] paired with h^[0..7] uniformly across all lanes), so GHASH_REDUCE_RAW_XOR *)
(*  (order-agnostic linearity) + KARATSUBA_IS_DOT_HW fire DIRECTLY into 8 clean      *)
(*  polyval_dots — no DIST8_PLAIN (which bakes in the body's misaligned [1;0;3;2..]  *)
(*  cross order and thus no-ops on the tail).  The proven batched-fold continuation  *)
(*  then closes, modulo the block-0 NCB_ETA cleanup above.                           *)
let TAIL_Q19_FOLD =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  REWRITE_TAC[ARITH_RULE `8 * k + 10 = (8 * (k + 1) + 0) + 2`;
              ARITH_RULE `8 * k + 11 = (8 * (k + 1) + 1) + 2`;
              ARITH_RULE `8 * k + 12 = (8 * (k + 1) + 2) + 2`;
              ARITH_RULE `8 * k + 13 = (8 * (k + 1) + 3) + 2`;
              ARITH_RULE `8 * k + 14 = (8 * (k + 1) + 4) + 2`;
              ARITH_RULE `8 * k + 15 = (8 * (k + 1) + 5) + 2`;
              ARITH_RULE `8 * k + 16 = (8 * (k + 1) + 6) + 2`;
              ARITH_RULE `8 * k + 17 = (8 * (k + 1) + 7) + 2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * (k + 2) = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * (k+1)))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8*(k+1)+1);
       nist_cipher_block nonce rk inblock (8*(k+1)+2);
       nist_cipher_block nonce rk inblock (8*(k+1)+3);
       nist_cipher_block nonce rk inblock (8*(k+1)+4);
       nist_cipher_block nonce rk inblock (8*(k+1)+5);
       nist_cipher_block nonce rk inblock (8*(k+1)+6);
       nist_cipher_block nonce rk inblock (8*(k+1)+7)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8*(k+1)))`;
     `nist_cipher_block nonce rk inblock (8*(k+1))`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* PERF (session 067): fold the raw GHASH accumulator to its compact nist_ghash form   *)
(* the INSTANT the final reduce eor3@0x1194 lands (state s136, `read Q19 s136 = <raw    *)
(* ~1.94M-char fold>`), BEFORE the ext@0x1198 / rev64@0x119c / st1@0x11a0 tail.  The    *)
(* old drive `MAP_EVERY NSTEP_GP (10--139)` let ARM_STEPS_TAC substitute the raw ~4M    *)
(* accumulator into the rev64's 16 word_subword slots (~64M term) — measured ~2.4h for  *)
(* the rev64 step + ~39min for the st1, i.e. essentially the WHOLE ~3.08h WB_TAIL cost. *)
(* Rewriting the s136 assumption to the compact `nist_ghash..(8*(k+2))` (via the proven  *)
(* TAIL_Q19_FOLD equality, ~8s on the raw term) makes ext/rev64/st1 inline the small     *)
(* compact term instead: steps 137--139 drop 2.4h+39min -> ~22s.  The tail's FINAL tag   *)
(* closer (TAG_STORE_REV64 captures the ext;rev64 byte-perm as word_reversefields 8 of    *)
(* the s136 value; AP_TERM_TAC exposes `read Q19 s136 = nist_ghash..nb`) then closes on   *)
(* the compact value via the same TAIL_Q19_FOLD — now a near-REFL.  Proof-PRESERVING:     *)
(* the substituted equality is exactly what the un-optimised closer proves, moved one     *)
(* barrier earlier so the giant term is never built.  Validated end-to-end on the warm    *)
(* s2n-wbtail checkpoint: full WB_TAIL drive+close 207s (was ~3.08h); tag conjunct closes.*)

(* Shared closure for the whole FOLD_Q19_* family: rewrite the `read Q19 sN` reduce   *)
(* assumption in place to the compact `nist_ghash..cnt`, using foldtac to prove the    *)
(* raw==compact equality.  Every WB_TAIL / TAIL_REM* fold is one instance, differing   *)
(* only in the state var (lhstm), the block-count term (cnt), and the fold lemma.      *)
let fold_q19_at lhstm cnt foldtac : tactic =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && lhs c = lhstm
    then TRANS th (prove
      (mk_eq(rhs c,
        vsubst [cnt, `n_blocks_fold:num`]
          `nist_ghash (aes256_cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block nonce rk inblock) n_blocks_fold)`),
       foldtac))
    else th);;

let FOLD_Q19_S136 : tactic =
  fold_q19_at `read Q19 s136 : int128` `8 * (k + 2)` TAIL_Q19_FOLD;;

(* s097: dedicated exact-8 drain removed the 7 no-op tag eors + 6 dead movis (13 identity  *)
(* instrs), so the final reduce eor3 landed at drive step s123 (was s136).                   *)
(* s098: eor3-FUSED the drain accumulate chains (3 block-pairs: each pair drops 3 pairwise   *)
(* `eor v17/v18/v19` and folds the 2nd block's products into the 1st via `eor3 acc,acc,      *)
(* prodB,prodA` with the A-block products retargeted to free regs Q13/Q14/Q15).  -9 net      *)
(* instrs (drain 117->108), so the final reduce eor3 now lands at drive step s114 (was s123).*)
(* Value-IDENTICAL: XOR is assoc/comm, so the folded Q19 is byte-identical — TAIL_Q19_FOLD    *)
(* is unchanged; only the state-var index shifts.                                             *)
let FOLD_Q19_S114 : tactic =
  fold_q19_at `read Q19 s115 : int128` `8 * (k + 2)` TAIL_Q19_FOLD;;

(* PERF (session 069): DROP the now-DEAD GHASH-reduce scratch registers right after   *)
(* FOLD_Q19_S136.  The final reduce `eor3 v19,v19,v17,v21`@0x1194 consumes Q17 (pmull)  *)
(* and Q21 (ext) into Q19 (Q18/Q20 are the earlier mid-reduce scratch feeding them);    *)
(* once Q19 is folded to its compact nist_ghash form, NONE of Q17/Q18/Q20/Q21 is read   *)
(* again — steps 137--139 (ext/rev64/st1) touch only Q19, and neither the postcondition *)
(* nor the MAYCHANGE frame mentions them.  But at s136 those four assumptions still      *)
(* carry the RAW ~1.9M/620k/588k-char Karatsuba lane sums (measured: Q21=1.22M, Q17=620k,*)
(* Q18=588k), and every downstream tactic that walks the assumption list pays for them:  *)
(* ARM_STEPS_TAC re-stamps each of the three tail steps over them, and ENSURES_FINAL_    *)
(* STATE_TAC + the out-forall closer traverse them.  Discarding them here is PROOF-       *)
(* PRESERVING (they are unread after the reduce — verified: the full WB_TAIL still closes *)
(* 0 subgoals with them gone) and cuts the post-fold tail (steps 137--139 + FINAL_STATE + *)
(* closers) from ~21.2s to ~12.2s (~9s, measured twice on the warm s2n-wbtail checkpoint  *)
(* from the shared post-fold set-point), i.e. ~6% of the whole WB_TAIL drive+close.        *)
(* Drop every assumption whose read-component register is in `deadl` (the s069     *)
(* reg_of logic, lifted out so both the mid-drive Q27 drop and the post-fold drop   *)
(* below can share it).                                                             *)
let DISCARD_REGS deadl : tactic =
  let reg_of th =
    try let c = concl th in
        if not(is_eq c) then "" else
        let f,args = strip_comb (lhs c) in
        if fst(dest_const f) = "read"
        then (match args with c::_ -> (try fst(dest_const c) with Failure _ -> "") | _ -> "")
        else ""
    with Failure _ -> "" in
  REPEAT(FIRST_X_ASSUM(fun th ->
    if List.mem (reg_of th) deadl then K ALL_TAC th else fail()));;

(* PERF (session 070): s069 dropped only {Q17,Q18,Q20,Q21} and only at s136 (post-fold). *)
(* Two extensions, both PROOF-PRESERVING (full WB_TAIL still closes 0 subgoals) and       *)
(* MEASURED on the warm s2n-wbtail checkpoint (current-source steppers, WHOLE WB_TAIL,     *)
(* twice): 140.94s -> 138.04s = -2.90s / -2.06% (both reps >= 2%).                          *)
(*  (1) Drop Q27 MID-DRIVE at s115.  Q27 is the tail's Karatsuba partial-product lane      *)
(*      (~87k chars by s115); its LAST read is at drive step ~112 (probed: dropping it at   *)
(*      s95/100/105/110/111/112 all FAIL with `AP_TERM_TAC`, s115 closes 0 — so s115 is the *)
(*      earliest proven-sound point).  s069's post-fold drop let ARM_STEPS_TAC re-stamp its *)
(*      87k over steps 116..136 (~21 steps) + FINAL_STATE; dropping it at s115 is a multi-   *)
(*      step win (the `DISCARD_REGS ["Q27"]` between (10--115) and (116--136) in the body).  *)
(*  (2) After FOLD_Q19_S136 EVERY register except Q0..Q7 (the 8 out-block ciphertexts),     *)
(*      Q19 (the folded compact tag) and Q30 (the ivec counter) is dead — none is read by    *)
(*      steps 137..139 (ext/rev64/st1) nor referenced by the postcondition/MAYCHANGE.  So    *)
(*      extend the post-fold drop from 4 regs to ALL 21 dead Q-registers, so steps 137..139  *)
(*      + FINAL_STATE + the out-forall closer walk a minimal assumption list.  (Q27 is        *)
(*      absent here — already dropped at s115.)                                               *)
(* PERF s072: Q28/Q31 removed from this post-fold list — they are now dropped at    *)
(* tail entry (dead from entry; see DISCARD_DEAD_HTABLE / the body).                 *)
let DISCARD_DEAD_REDUCE_SCRATCH : tactic =
  DISCARD_REGS
    ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q12";
     "Q13"; "Q14"; "Q15"];;

(* PERF (session 071): DROP the 15 DEAD round-key memory facts at tail entry.        *)
(* The precondition carries `read (memory :> bytes128 (word_add key_p (word 16*i))) s *)
(* = word_reversefields 8 (EL i rk)` for i=0..14 (the AES-256 expanded round keys in  *)
(* memory).  DISCARD_REGS only drops REGISTER facts (its reg_of returns "" for a       *)
(* `memory :> ..` component), so these 15 facts otherwise survive ALL ~127 drive       *)
(* steps, and ARM_STEPS_TAC re-stamps each one every step (cost is per-CARRIED-FACT,    *)
(* not just per-term-size).  But the tail is a streaming GHASH DRAIN: it runs NO AES    *)
(* rounds (the 8 keystreams Q0..Q7 are already computed at tail entry — see the pre-    *)
(* condition `word_xor (read Qj) rk14 = word_reversefields 8 (aes256_cipher ..)`), so   *)
(* the round keys in memory are DEAD from tail entry onward — no instruction reads      *)
(* key_p memory, and neither the postcondition nor the MAYCHANGE frame mentions it.     *)
(* Dropping them right after the s1..9 prefix (before the 10--136 drive) is PROOF-       *)
(* PRESERVING (full WB_TAIL still closes 0 subgoals) and removes 15 of ~101 carried      *)
(* facts from every subsequent ARM_STEPS re-stamp.  MEASURED on the warm s2n-wbtail     *)
(* checkpoint (current-source steppers, WHOLE WB_TAIL, interleaved A/B, twice): OLD      *)
(* 137.74/137.79s vs NEW 130.30/130.48s = -5.40%/-5.30% (both >= 2%), both closed=true.  *)
(* Complements the s069/s070 register discards (those shrink the reduce scratch; this    *)
(* drops the drive-long dead memory operands the register-only reg_of never reached).     *)
let DISCARD_DEAD_KEYMEM : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (find_term (fun t -> t = `key_p:int64`)) (lhs c) &&
       can (find_term (fun t -> match t with Const("memory",_) -> true | _ -> false))
           (lhs c)
    then K ALL_TAC th else fail()));;

(* PERF (session 072): DROP the 6 DEAD htable (H-power) memory facts at tail entry.  *)
(* htable_mem_8 (unfolded at INIT) contributes 12 `read (memory :> bytes128 (word_add *)
(* htable_p (word off))) s = ..` facts, at offsets 0,16,..,176.  But the executed     *)
(* 8-block tail path (0xfa0..0x11a4) loads x6 (= htable_p) ONLY at offsets            *)
(* {0,16,32,48,64,80} (ldr q25..q20 @0x1080/0x109c/0x10c0/0x1100/0x112c/0x1140) — the *)
(* single-accumulator whole-blocks tail uses only H^1..H^4 + the low Karatsuba mids.  *)
(* The 6 facts at offsets {96,112,128,144,160,176} (byteswap128(h_power 4..7) and the *)
(* word_join karatsuba_mid pairs for h 4..7) are NEVER read by any tail instruction,  *)
(* and the postcondition mentions no htable memory — DEAD FROM ENTRY.  Like the s071  *)
(* round-key drop, dropping them right after the s1..9 prefix removes 6 of the ~101   *)
(* carried facts from every subsequent ARM_STEPS re-stamp.  PROOF-PRESERVING (full     *)
(* WB_TAIL still closes 0 subgoals).  DISCARD_DEAD_KEYMEM/DISCARD_REGS miss them (one  *)
(* keys on key_p, the other on register components).  MEASURED with the entry Q31/Q28  *)
(* drop below — see the body.                                                         *)
let dead_htable_offs = [96; 112; 128; 144; 160; 176];;
let DISCARD_DEAD_HTABLE : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (find_term (fun t -> t = `htable_p:int64`)) (lhs c) &&
       can (find_term (fun t -> match t with Const("memory",_) -> true | _ -> false))
           (lhs c) &&
       can (find_term (fun t -> match t with
              Comb(Const("word",_), n) ->
                (try List.mem (dest_small_numeral n) dead_htable_offs
                 with Failure _ -> false)
            | _ -> false)) (lhs c)
    then K ALL_TAC th else fail()));;

let AESV8_GCM_8X_ENC_256_TAIL = prove
 (`!q18_init q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 2) = nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read Q18 s = q18_init /\
           read Q27 s = q27_init /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 18)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock)
                              (8 * (k + 1))) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 10)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 11)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 12)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 13)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 14)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 15)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 16)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 17)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  (* SESSION 039: interface pinned; body CHEAT'd so the file loads.            *)
  (*                                                                           *)
  (* BODY-FILL RECIPE (for the next session).  The tail is a streaming GHASH   *)
  (* drain of the final 8 blocks + reduce + 2 writebacks.  ~139 executed steps:*)
  (*   entry 0xec0..0xee4 (10 instrs, incl. the computed branch b.gt@0xee4);   *)
  (*   then the 8-block path 0xfa0..0x11a0 (129 instrs); exit at pc+0x11a4.     *)
  (*                                                                           *)
  (* 1. INIT: REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ *)
  (*    ABI; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN *)
  (*    ENSURES_INIT_TAC "s0" THEN the s009 LENGTH->mc-length RULE_ASSUM rewrite*)
  (*    (as PREPRETAIL @~line 4392).                                            *)
  (* 2. COMPUTED BRANCH b.gt@0xee4: the entry does `sub x5,x4,x0`@0xec4 giving  *)
  (*    x5 = (in_p+16*nb) - (in_p+128*(k+1)) = 16*nb - 128*(k+1).  Under        *)
  (*    8*(k+2)=nb this is 16*8*(k+2) - 128*(k+1) = 128*(k+2) - 128*(k+1) = 128 *)
  (*    = 0x80.  `cmp x5,#0x70`@0xedc then b.gt (0x80 > 0x70) is TAKEN -> 0xfa0.*)
  (*    Establish x5=word 128 before the cmp (WORD_RULE from the premise +      *)
  (*    the X0/X4 pins), so the stepper resolves the branch to pc+0xfa0.  This  *)
  (*    is the SOLE control-flow obligation (mirrors SETUP_BRANCH_COND_FALSE    *)
  (*    but here the branch is TAKEN; likely a small `x5=128 ==> 0x80 > 0x70`   *)
  (*    b.gt-discharge helper, or a MAP for the flag then COND_CLAUSES).        *)
  (* 3. DRIVE: MAP_EVERY NSTEP_GP over the 8-block path.  The 8 ldr q,[x0],#16  *)
  (*    plaintext reloads (0xec8/0xfac/0xfe8/0x102c/0x104c/0xa4/.../etc.) use   *)
  (*    the persistent input-forall via an LDP_STEP4/LDP-style re-derive of     *)
  (*    `inblock (8*(k+1)+m)` (the reads advance X0; NORMOFF + input-forall).   *)
  (*    The 8 st1 {v9},[x2],#16 ciphertext stores advance X2 and write the NEW  *)
  (*    output blocks 8*(k+1)..8*(k+1)+7; the incoming out-forall (j<8*(k+1))   *)
  (*    must be preserved across them (same store-side handling MAIN_LOOP uses).*)
  (*    NSTEP_GP protects Q17..Q21 so the reduce's mid-accumulator v18 stays    *)
  (*    un-normalized in both the pmull and ext copies (see PREPRETAIL note).   *)
  (* 4. FINAL_STATE + REPEAT CONJ_TAC + a shape-routed dispatcher:              *)
  (*    - the 8 out-block ciphertext conjuncts j<nb: case-split j<8*(k+1) (OLD, *)
  (*      FIRST_ASSUM the incoming out-forall) vs j in {8*(k+1)..+7} (NEW, the  *)
  (*      just-stored eor3 forms; AC-normalize v9=eor3(pt,ks,rk14) to the       *)
  (*      XOR_AES256_CIPHER_RECONSTRUCT shape + AES256_CIPHER_KEYLIST, exactly  *)
  (*      as the MAIN_LOOP body @~line 3421-3456; here the keystreams come from *)
  (*      v0..v7 whose pre-rk14 forms are the tail's precondition Q0..Q7).      *)
  (*    - tag conjunct read(tag_p)=word_reversefields 8 (nist_ghash..nb): the   *)
  (*      final reduce (0x1178-0x119c) computes v19; the rev64 v19@0x119c then  *)
  (*      st1 [x3]@0x11a0 stores it.  Fold the raw v19 to nist_ghash..(8*(k+2)) *)
  (*      = ..nb via the Q19_FOLD_TAC_K route (RECON_GRR + GHASH_REDUCE_RAW_    *)
  (*      DIST8_PLAIN + GHASH_POLYVAL_ACC_BATCHED); the rev64-store byte-perm    *)
  (*      closes via a TAG_STORE_REV64-style BITBLAST lemma relating the stored *)
  (*      word_join lanes to word_reversefields 8.  NB nb here = 8*(k+2), so    *)
  (*      list_of_seq..nb needs one more GHASH_ACC_APPEND round than the        *)
  (*      PREPRETAIL fold (which went to 8*(k+1)); adapt Q19_FOLD_TAC_K's        *)
  (*      ISPECL block indices (8*k+8..8*k+15) accordingly, or reindex k->k+1.  *)
  (*    - ivec conjunct read(ivec_p)=word_reversefields 8 (ctr_block nonce      *)
  (*      (nb+2)): Q30 at entry = word_reversefields 32 (ctr_block nonce        *)
  (*      (8*k+18)); the 8-block path does NO `sub v30` (only the partial       *)
  (*      cascade fall-throughs do), so the rev32 v30@0x1148 -> str [x16]@0x114c*)
  (*      stores word_reversefields 8 (ctr_block nonce (8*k+18)) = ..(nb+2)     *)
  (*      (since nb+2 = 8*(k+2)+2 = 8*k+18).  Close via an IVEC_STORE_REV32-     *)
  (*      style BITBLAST + CTR_BLOCK_RECONSTRUCT_REV32 (as PP_CTR_CLOSE).        *)
  (* 5. MAYCHANGE frame: MONOTONE_MAYCHANGE_TAC (widened Q8..Q15, as PREPRETAIL/*)
  (*    MAIN_LOOP).  The out_p/tag_p/ivec_p memory writes are all in the frame. *)
  (* The x4 template for the streaming tail is aes_gcm_enc_kernel_x4_fast_tail. *)
  (* ml @~897-1210 (its per-block store+pmull+the final reduce + TAG_STORE_REV64*)
  (* / IVEC_STORE_REV32 closers @437/457).                                      *)
  (*                                                                           *)
  (* SESSION 041: store-retention SOLVED (ivec + out-forall CLOSED; only the    *)
  (* tag GHASH-reduce fold remains CHEAT'd — see the tag branch below).         *)
  (*   (1) INIT unfolds PAIRWISE (NOT just ALLPAIRS) — the tail stores to        *)
  (*       out_p AND ivec_p AND tag_p, so it needs the PAIRWISE-disjointness of  *)
  (*       those three; without PAIRWISE the ivec/tag stores drop ALL the        *)
  (*       accumulated out-stores (they can't be shown disjoint from the store   *)
  (*       target).  (2) KS_SOLVE inverts the 8 keystream facts at s0 so the      *)
  (*       eor3 ciphertext outputs (hence the store RHS) are state-independent.  *)
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  (* Assert the 8 tail input blocks at s0 (in_p+128*(k+1)+16*m = inblock(8*(k+1)+m)). *)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * (k + 1))))) s0 =
    inblock (8 * (k + 1)) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (k + 1) + 16)))) s0 =
    inblock (8 * (k + 1) + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (k + 1) + 32)))) s0 =
    inblock (8 * (k + 1) + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (k + 1) + 48)))) s0 =
    inblock (8 * (k + 1) + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (k + 1) + 64)))) s0 =
    inblock (8 * (k + 1) + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (k + 1) + 80)))) s0 =
    inblock (8 * (k + 1) + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (k + 1) + 96)))) s0 =
    inblock (8 * (k + 1) + 6) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (k + 1) + 112)))) s0 =
    inblock (8 * (k + 1) + 7)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE
     `128 * (k + 1) + 16 = 16 * (8 * (k + 1) + 1) /\
      128 * (k + 1) + 32 = 16 * (8 * (k + 1) + 2) /\
      128 * (k + 1) + 48 = 16 * (8 * (k + 1) + 3) /\
      128 * (k + 1) + 64 = 16 * (8 * (k + 1) + 4) /\
      128 * (k + 1) + 80 = 16 * (8 * (k + 1) + 5) /\
      128 * (k + 1) + 96 = 16 * (8 * (k + 1) + 6) /\
      128 * (k + 1) + 112 = 16 * (8 * (k + 1) + 7)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * a = 16 * 8 * a`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* KEY: invert the 8 keystream facts so registers are concrete (store retention). *)
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  (* Steps 1..9: to the computed b.gt@0xee4.  Rewrite x5 -> word 128 so the       *)
  (* branch resolves concretely (b.gt 0x80>0x70 TAKEN -> pc+0xfa0).               *)
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TAIL_X5_128 (ASSUME `8 * (k + 2) = nb`)]) THEN
  (* PERF s071: the round-key memory facts are DEAD in this GHASH drain (no AES     *)
  (* rounds run here); drop them before the drive so ARM_STEPS stops re-stamping     *)
  (* all 15 every step (whole WB_TAIL 137.8s->130.4s, -5.4%, twice).  See above.     *)
  DISCARD_DEAD_KEYMEM THEN
  (* PERF s072: also drop the 6 dead htable H-power facts (offsets 96..176, never     *)
  (* loaded by the whole-blocks tail) and the two dead precondition register pins      *)
  (* Q31 (the const `word 0x1000..0` — never read by any tail instr) and Q28 (rk14 —   *)
  (* first tail use is a `pmull2 v28`@0xfe4 WRITE, so its entry value is dead).  All 8  *)
  (* are absent from the postcond (which pins no registers) and MAYCHANGE, so they are  *)
  (* DEAD FROM ENTRY; dropping them here stops ARM_STEPS re-stamping them over ~127      *)
  (* drive steps (whole WB_TAIL 129.5s->126.8s, -2.04%/-2.15%, twice).  Q28/Q31 were     *)
  (* previously dropped only post-fold by DISCARD_DEAD_REDUCE_SCRATCH; the entry drop     *)
  (* subsumes that (a no-op there now).                                                  *)
  DISCARD_DEAD_HTABLE THEN
  DISCARD_REGS ["Q31"; "Q28"] THEN
  (* Steps 10..136: the full 8-block drain + Karatsuba + reduce, up to & incl the  *)
  (* final reduce eor3@0x1194 (s136: read Q19 = raw ~1.94M-char GHASH fold).        *)
  (* PERF s070: drop the Karatsuba partial-product lane Q27 at s115 (its last read  *)
  (* is drive step ~112; s115 is the earliest proven-sound drop point) so ARM_STEPS *)
  (* stops re-stamping its ~87k chars over steps 116..136.  See DISCARD_REGS above.  *)
  (* s097: dedicated exact-8 drain (b.gt@0xee8 -> 0x11cc).  s098: eor3-FUSED the        *)
  (* drain accumulate chains (3 block-pairs), -9 net instrs -> drain is 108 instrs      *)
  (* (was 117).  drive-step = 10 + drain-instr-index (step 10 = b.gt@0xee8; step 11 =    *)
  (* drain#1@0x11cc).  Q27's last read is now s93 (`eor3 v18,v18,v27,v15`@0x1314), the   *)
  (* final reduce eor3 (`eor3 v19,v19,v17,v21`@0x1368) is drain#104 = s114 (was s123),   *)
  (* and the ext/rev64/st1/b writebacks are s115..s118 (was s124..s127).                 *)
  MAP_EVERY NSTEP_GP (10--97) THEN
  DISCARD_REGS ["Q27"] THEN
  MAP_EVERY NSTEP_GP (98--115) THEN
  (* PERF s067: fold Q19 to compact nist_ghash NOW, so the ext/rev64/st1 tail       *)
  (* (steps 115--117) inlines a small term instead of the ~4M raw fold (was ~3h).   *)
  FOLD_Q19_S114 THEN
  (* PERF s069: Q19 is now the compact nist_ghash; the reduce scratch Q17/Q18/Q20/Q21 *)
  (* (raw ~1.9M/620k/588k-char Karatsuba sums) is DEAD — drop it so the tail steps and *)
  (* FINAL_STATE/closers stop walking it (post-fold tail ~21.2s->~12.2s, ~6% of TAIL).  *)
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  (* Steps 115..117: ext ; rev64 ; st1 (2 writebacks); s118: b -> epilogue.         *)
  MAP_EVERY NSTEP_GP (116--119) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* 3 conjuncts: ivec store / tag store / out-forall.                            *)
  CONJ_TAC THENL
   [(* ivec: word_join(rev8 lanes of rev32 (ctr_block .. 8k+18)) = rev8(ctr .. nb+2) *)
    REWRITE_TAC[IVEC_STORE_REV32] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `8 * (k + 2) = nb` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* tag store: read(mem tag_p) s139 = rev64(ext(read Q19 s136)) where             *)
    (* read Q19 s136 is the raw modulo-reduced GHASH fold (eor3 v19,v19,v17,v21      *)
    (* @0x1194).  SESSION 042 root cause of the s041 drop: the reduce scratch        *)
    (* Q17/Q18/Q21 were dropped because the tail's Karatsuba starts Q18 and Q27 with *)
    (* PARTIAL-lane writes `mov v18.d[0],v24.d[1]`@0xfb8 / `mov v27.d[0],v8.d[1]`    *)
    (* @0xfb4 that read the DEAD upper lane of the uninitialized register, so the    *)
    (* stepper's `read Q18 s17 = word_insert (read Q18 s16) ...` references          *)
    (* uninitialized state and DISCARD_OLDSTATE drops it (cascading to Q17/Q21 which *)
    (* derive from Q18, hence Q19's fold input dangles).  FIX (VALIDATED s042, now   *)
    (* in the precondition): pin `read Q18 = q18_init` and `read Q27 = q27_init` at   *)
    (* tail entry (mirrors x4 fast_tail which pins read Q18).  With both pinned,      *)
    (* Q17/Q18/Q19/Q21 are all PRESENT + CONCRETE (no dangling state refs) at s136    *)
    (* (probed).  Then the store perm rev64(ext(_)) = word_reversefields 8, i.e.      *)
    (* TAG_STORE_REV64, peels; AP_TERM_TAC exposes `<raw fold> = nist_ghash..nb`;     *)
    (* TAIL_Q19_FOLD (= Q19_FOLD_TAC_K reindexed k->k+1) closes it.  The postcond is  *)
    (* independent of q18_init/q27_init (dead lane overwritten before use), so STEP 5 *)
    (* instantiates them to PREPRETAIL's exit Q18/Q27 values.                         *)
    (* CLOSER (validated mechanism; end-to-end run pending a free server — the s042    *)
    (* pinfull validation client timed out while gate042 kept churning, so the full    *)
    (* FINAL_STATE + this close is NOT yet machine-confirmed; kept CHEAT'd so the file  *)
    (* stays loadable):                                                                *)
    (*   REWRITE_TAC[TAG_STORE_REV64] THEN AP_TERM_TAC THEN TAIL_Q19_FOLD               *)
    FIRST_X_ASSUM(fun th ->
      if concl th = `8 * (k + 2) = nb` then SUBST_ALL_TAC(SYM th) else failwith "") THEN
    REWRITE_TAC[TAG_STORE_REV64] THEN AP_TERM_TAC THEN TAIL_Q19_FOLD;
    ALL_TAC] THEN
  (* out-forall (j<nb): OLD blocks j<8*(k+1) via the incoming out-forall; the 8    *)
  (* NEW blocks via the retained ciphertext stores + the MAIN_LOOP ciphertext      *)
  (* closer (XOR_AES256_CIPHER_RECONSTRUCT + AES256_CIPHER_KEYLIST).               *)
  FIRST_X_ASSUM(fun th ->
    if concl th = `8 * (k + 2) = nb` then SUBST_ALL_TAC(SYM th) else failwith "") THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * (k + 2) <=>
                       j < 8 * (k+1) \/ j = 8*(k+1) \/ j = 8*(k+1) + 1 \/
                       j = 8*(k+1) + 2 \/ j = 8*(k+1) + 3 \/ j = 8*(k+1) + 4 \/
                       j = 8*(k+1) + 5 \/ j = 8*(k+1) + 6 \/ j = 8*(k+1) + 7`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * (k+1) + b) = 128 * (k+1) + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * (k+1) = 128 * (k+1)`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  CONV_TAC WORD_RULE);;


(* ===================================================================== *)
(* SESSION 079 — TAIL CASCADE arm rem=1 (nblocks = 8*g+1), the FIRST of    *)
(* the 1..7-block remainder-cascade legs of the nblocks>=0 generalization. *)
(*                                                                         *)
(* Unlike WB_TAIL (rem=8, exact multiple of 8), the rem<8 arms of the       *)
(* computed b.gt cascade (0xee4..0xf90) `movi v17/v18/v19,#0` — they RESET  *)
(* the GHASH accumulator and rebuild it with a FRESH pmull/eor reduce of    *)
(* only `rem` blocks, so WB_TAIL's symbolic-pinned-Q19 retention (Q18/Q27   *)
(* init pins) does NOT apply.  rem=1 lands on the single-block arm 0x1140.  *)
(*                                                                         *)
(* Two things make the drive retain the store facts:                        *)
(*  (1) the input-block SUBGOAL_THEN (`read(in_p+128*g) s0 = inblock(8*g)`) *)
(*      — without it the plaintext load stays a raw memory read and the      *)
(*      whole ciphertext/GHASH chain dangles + DISCARD_OLDSTATE drops it;    *)
(*  (2) KS_SOLVE inverting the single keystream fact (as WB_TAIL).           *)
(* Then FOLD_Q19_REM1 folds the raw single-block reduce (~130k chars at      *)
(* s78) to the compact `nist_ghash..(8*g+1)` BEFORE the ext/rev64/store, so  *)
(* the rev64 does not balloon (the same lever as WB_TAIL's FOLD_Q19_S136).   *)
(*                                                                         *)
(* NB the counter convention (verified against WB_SETUP0's exit + the        *)
(* aes_ctr_block i = rev8(aes256(ctr_block(i+2))) relation): the single tail *)
(* block is block `8*g` (= nb-1), whose keystream register Q0 holds ctr      *)
(* `8*g+2` (NOT `8*g+10` — that is Q30's counter value, +8 ahead).           *)
(* ===================================================================== *)

(* x5 at the rem=1 tail entry: (in_p+16*nb) - (in_p+128*g) = 16 under       *)
(* nb=8*g+1; once rewritten to `word 16` the cmp/b.gt cascade resolves to    *)
(* the rem=1 arm (b 0x1140) automatically (concrete flags), no branch lemma. *)
let TAIL_X5_REM1 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 1))))
              (word_add in_p (word (128 * g))) = word 16:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

(* Single-block Q19 fold (x4 fast_tail rem=1 route; front-end shared with    *)
(* TAIL_Q19_FOLD, single-block APPEND tail instead of GHASH_POLYVAL_ACC_      *)
(* BATCHED).  Proves the raw single-block ghash_reduce at s78 equals the      *)
(* compact nist_ghash..(8*g+1): RECON_GRR exposes ghash_reduce_raw, the       *)
(* block normalizes to nist_cipher_block(8*g), KARATSUBA_IS_DOT_HW collapses  *)
(* the three Karatsuba pmulls to a single polyval_dot, and the one-element    *)
(* list_of_seq(SUC)/NIST_GHASH_APPEND/CONS + NIST_DOT_IS_POLYVAL_DOT +        *)
(* h_power 0 closes it.                                                       *)
let TAIL_Q19_FOLD_REM1 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 2 = (8 * g) + 2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 1 = SUC(8 * g)`] THEN
  REWRITE_TAC[list_of_seq] THEN
  REWRITE_TAC[NIST_GHASH_APPEND] THEN
  REWRITE_TAC[NIST_GHASH_CONS; nist_ghash] THEN
  REWRITE_TAC[NIST_DOT_IS_POLYVAL_DOT] THEN
  REWRITE_TAC[CONJUNCT1 h_power];;

(* Fold `read Q19 s78` (raw single-block reduce) -> compact nist_ghash..(8*g+1) *)
(* in place, mirroring WB_TAIL's FOLD_Q19_S136.                                 *)
let FOLD_Q19_REM1 : tactic =
  fold_q19_at `read Q19 s82 : int128` `8 * g + 1` TAIL_Q19_FOLD_REM1;;

let AESV8_GCM_8X_ENC_256_TAIL_REM1 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 1 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  (* Assert the single tail input block; WITHOUT this the plaintext load stays *)
  (* a raw memory read and the whole ciphertext/GHASH chain drops (s079).      *)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* Invert the keystream fact so the ciphertext eor3 output is state-indep. *)
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  (* Steps 1..9 to the computed b.gt@0xee4; x5 -> word 16 resolves the cascade *)
  (* concretely to the rem=1 arm (b 0x1140).                                   *)
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM1]) THEN
  (* Steps 10..78: cascade fall-through + single-block fold + reduce, up to    *)
  (* the final reduce eor3@0x1194 (s78: read Q19 = raw ~130k single-block fold).*)
  MAP_EVERY NSTEP_GP (10--82) THEN
  (* Fold Q19 to compact nist_ghash..(8*g+1) BEFORE ext/rev64/store (else rev64 *)
  (* balloons), then drop the dead reduce scratch.                             *)
  FOLD_Q19_REM1 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  (* Steps 79..81: ext@0x1198 ; rev64@0x119c ; st1@0x11a0 (tag) ; exit@0x11a4. *)
  MAP_EVERY NSTEP_GP (83--85) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* ivec store: 7 fall-through `sub v30` roll ctr 8g+10 -> 8g+3 = nb+2.       *)
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1)) (word 1) = word (8 * g + 3)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  (* tag store: read(tag_p) = rev8(nist_ghash..nb) (Q19 already folded).       *)
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* out-forall (j<nb): OLD blocks j<8*g via the incoming out-forall; the ONE  *)
  (* NEW block j=8*g via the retained ciphertext store + double-rk14 cancel.   *)
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 1 <=> j < 8 * g \/ j = 8 * g`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes_ctr_block] THEN CONV_TAC WORD_BITWISE_RULE);;



(* ===================================================================== *)
(* SESSION 080 — TAIL CASCADE arm rem=2 (nblocks = 8*g+2), lands at 0x10fc. *)
(*                                                                         *)
(* The second remainder-cascade leg (after rem=1).  It folds TWO fresh      *)
(* blocks (8*g and 8*g+1) into the GHASH accumulator via a 2-block BATCHED   *)
(* reduce (GHASH_POLYVAL_ACC_BATCHED), vs rem=1's single-block APPEND.       *)
(*                                                                         *)
(* Like WB_TAIL (rem=8), the rem>=2 arms `movi v17/v18/v19,#0` reset the     *)
(* accumulator and rebuild it with a fresh pmull/eor reduce; the 0x10fc arm  *)
(* does `mov v27.d[0],v8.d[1]`@0x1114 — a PARTIAL-lane write on the          *)
(* UNINITIALIZED Q27, so Q27 MUST be pinned (q27_init) at entry or the       *)
(* reduce chain Q18/Q19/Q17/Q21 references dead state and DISCARD_OLDSTATE   *)
(* drops it (the WB_TAIL rem=8 q27_init pin; Q18 is movi-zeroed so needs no  *)
(* pin here — this is why rem=1, whose 0x1140-only arm never touches v27,     *)
(* needed NO reg pin, but rem>=2 does).                                      *)
(* ===================================================================== *)

(* x5 at the rem=2 tail entry: 16*nb - 128*g = 32 under nb=8*g+2; once        *)
(* rewritten to `word 32` the cmp/b.gt cascade resolves to the rem=2 arm      *)
(* (b.gt@0xf90 -> 0x10fc) automatically (concrete flags), no branch lemma.    *)
let TAIL_X5_REM2 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 2))))
              (word_add in_p (word (128 * g))) = word 32:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

(* Two-block Q19 fold: RECON_GRR exposes the reduce; the 2 blocks normalize   *)
(* to nist_cipher_block(8*g),(8*g+1); GHASH_REDUCE_RAW_XOR + KARATSUBA_IS_     *)
(* DOT_HW + KDOT_B0 (block-0 = the accumulator, carries the store-order        *)
(* byteswap) collapse the summed lanes to                                      *)
(*   word_xor (polyval_dot cb(8*g+1) H^0) (polyval_dot (sofar (x) cb(8*g)) H^1)*)
(* which is exactly GHASH_POLYVAL_ACC_BATCHED with bs=[cb(8*g+1)], b=cb(8*g),  *)
(* a=sofar; the RHS nist_ghash..(8*g+2) unfolds to the same via NIST_GHASH_IS_ *)
(* POLYVAL + list_of_seq/APPEND/GHASH_ACC_APPEND + the batched lemma.  Only    *)
(* block 8*g+1's ctr index (8*g+3) needs the (8*g+1)+2 reindex; block 8*g's    *)
(* ctr (8*g+2) already parses as (8*g)+2 so folds directly (a bare 8*g+2       *)
(* reindex would also corrupt the RHS list count 8*g+2 -> DON'T add it).       *)
let TAIL_Q19_FOLD_REM2 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 3 = (8 * g + 1) + 2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 2 = SUC(SUC(8 * g))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8*g+1)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8*g))`;
     `nist_cipher_block nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* Fold `read Q19 s92` (raw 2-block reduce) -> compact nist_ghash..(8*g+2)     *)
(* in place BEFORE ext/rev64/store (mirror FOLD_Q19_S136/FOLD_Q19_REM1).       *)
let FOLD_Q19_REM2 : tactic =
  fold_q19_at `read Q19 s53 : int128` `8 * g + 2` TAIL_Q19_FOLD_REM2;;

let AESV8_GCM_8X_ENC_256_TAIL_REM2 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 2 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  (* Assert the 2 tail input blocks; WITHOUT this the plaintext loads stay      *)
  (* raw memory reads and the ciphertext/GHASH chain drops (s079).              *)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* Invert the keystream facts so the ciphertext eor3 outputs are state-indep. *)
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  (* Steps 1..9 to the computed b.gt@0xee4; x5 -> word 32 resolves the cascade  *)
  (* concretely to the rem=2 arm (b.gt@0xf90 -> 0x10fc).                        *)
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM2]) THEN
  (* Steps 10..92: cascade fall-through + 2-block fold + reduce, up to the      *)
  (* final reduce eor3@0x1194 (s92: read Q19 = raw ~250k 2-block reduce).        *)
  MAP_EVERY NSTEP_GP (10--53) THEN
  (* Fold Q19 to compact nist_ghash..(8*g+2) BEFORE ext/rev64/store, then drop  *)
  (* the dead reduce scratch.                                                   *)
  FOLD_Q19_REM2 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  (* Steps 93..95: ext@0x1198 ; rev64@0x119c ; st1@0x11a0 (tag) ; exit@0x11a4.  *)
  MAP_EVERY NSTEP_GP (54--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* ivec store: 6 fall-through `sub v30` roll ctr 8g+10 -> 8g+4 = nb+2.        *)
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1) = word (8 * g + 4)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  (* tag store: read(tag_p) = rev8(nist_ghash..nb) (Q19 already folded).        *)
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* out-forall (j<nb): OLD blocks j<8*g via the incoming out-forall; the 2 NEW *)
  (* blocks j=8*g, 8*g+1 via the retained ciphertext stores + double-rk14 cancel.*)
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 2 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ===================================================================== *)
(* ===================================================================== *)
(* s115: dedicated REM2_DRAIN leg (0x14bc -> 0x11c4) = the shared rem=2      *)
(* eor3-fused 2-block drain, entered FRESH. Extracted so the fast2 early-    *)
(* dispatch leg can reach it via ENSURES_SEQUENCE (its inline drain dropped  *)
(* accumulator facts after the 102-step AES history; a fresh entry tracks    *)
(* them). Proof = TAIL_REM2 drain drive; contract = TAIL_REM2 state @0x14bc. *)
(* ===================================================================== *)
let AESV8_GCM_8X_ENC_256_REM2_DRAIN = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 2 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x14ec) /\
           read X0 s = word_add in_p (word (128 * g + 16)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read Q1 s =
             word_xor
               (word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 3)) rk))
               (word_reversefields 8 (EL 14 rk)) /\
           read Q9 s =
             word_xor
               (word_xor (inblock (8 * g))
                 (word_xor
                   (word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk))
                   (word_reversefields 8 (EL 14 rk))))
               (word_reversefields 8 (EL 14 rk)) /\
           read Q16 s =
             word_subword
               (word_join
                 (nist_ghash (aes256_cipher (word 0) rk) tag0
                   (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)))
                 (nist_ghash (aes256_cipher (word 0) rk) tag0
                   (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)))
                 : (256)word)
               (64,128) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           read Q29 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY NSTEP_GP (1--40) THEN
  fold_q19_at `read Q19 s40 : int128` `8 * g + 2` TAIL_Q19_FOLD_REM2 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (41--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1) = word (8 * g + 4)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 2 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ===================================================================== *)
(* s115: FAST2_TAIL leg (0x1660 -> 0x11c4) = the fast2 tail-setup (ldr q8;  *)
(* ext v16; mov v29; eor3 v9) + shared rem=2 drain, entered FRESH. The      *)
(* fast2 early-dispatch leg splits here (NOT at 0x14bc) because the inline   *)
(* eor3 v9 block-ct write is dropped by ARM_STEPS after the ~100-step AES    *)
(* history; a fresh entry with keystream PRECONDS (KS_SOLVE at s0, like the  *)
(* TAIL legs) tracks it. Proof = tail-setup drive + REM2_DRAIN drain drive.  *)
(* ===================================================================== *)
let AESV8_GCM_8X_ENC_256_FAST2_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 2 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x1764) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q25 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--45) THEN
  fold_q19_at `read Q19 s45 : int128` `8 * g + 2` TAIL_Q19_FOLD_REM2 THEN
  (*[s118] Q25 is the LIVE tbl index here (not reduce-scratch) -> KEEP it so read Q25 propagates to the tbl step*)
  DISCARD_REGS ["Q17";"Q18";"Q20";"Q21";"Q22";"Q23";"Q24";"Q26";"Q29";"Q16";"Q8";"Q9";"Q10";"Q11";"Q12";"Q13";"Q14";"Q15"] THEN
  MAP_EVERY NSTEP_GP (46--48) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1) = word (8 * g + 4)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN  (*[s118] tbl w/ concrete index expands to the SAME word_join byte-reversal as ext+rev64; TBL_IS_REVERSEFIELDS unused*)
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 2 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ===================================================================== *)
(* [s126] FAST1_TAIL — the fast1 (nb=1, 16B) dedicated tail leg.          *)
(* Clone of FAST2_TAIL for ONE block (keystream Q0 only; ext+rev64 tag    *)
(* format so NO Q25 index).  Entry 0x1b04 (fast1 tail-setup start, ldr q8;*)
(* ext v16; mov v29; eor3 v9), then the single-block drain (7 subs roll   *)
(* v30 base+8=ctr(8g+10) -> base+1=ctr(nb+2)).  Q19 folds at s31.         *)
(* ===================================================================== *)
let AESV8_GCM_8X_ENC_256_FAST1_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 1 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x1b44) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q25 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--31) THEN
  fold_q19_at `read Q19 s31 : int128` `8 * g + 1` TAIL_Q19_FOLD_REM1 THEN
  DISCARD_REGS ["Q17";"Q18";"Q20";"Q21";"Q22";"Q23";"Q24";"Q26";"Q29";"Q16";"Q8";"Q9";"Q10";"Q11";"Q12";"Q13";"Q14";"Q15"] THEN
  MAP_EVERY NSTEP_GP (32--34) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1)) (word 1) = word (8 * g + 3)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 1 <=>
                       j < 8 * g \/ j = 8 * g`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* SESSION 080 — TAIL CASCADE arm rem=3 (nblocks = 8*g+3), lands at 0x10c0. *)
(* 3-block batched Q19 fold; Q27 pinned (dead-lane partial write@0x1114). *)
(* 5 `sub v30` decrements roll ctr 8g+10 -> 8g+5 = nb+2.               *)
(* ===================================================================== *)

let TAIL_X5_REM3 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 3))))
              (word_add in_p (word (128 * g))) = word 48:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_REM3 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + 3 = (8 * g + 1) + 2`;
              ARITH_RULE `8 * g + 4 = (8 * g + 2) + 2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 3 = SUC(SUC(SUC(8 * g)))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8*g+1);
       nist_cipher_block nonce rk inblock (8*g+2)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8*g))`;
     `nist_cipher_block nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM3 : tactic =
  fold_q19_at `read Q19 s107 : int128` `8 * g + 3` TAIL_Q19_FOLD_REM3;;

let AESV8_GCM_8X_ENC_256_TAIL_REM3 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 3 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM3]) THEN
  MAP_EVERY NSTEP_GP (10--107) THEN
  FOLD_Q19_REM3 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (108--110) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word (8 * g + 5)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 3` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 3 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;


(* ===================================================================== *)
(* SESSION 080 — TAIL CASCADE arm rem=4 (nblocks = 8*g+4), lands at 0x107c. *)
(* 4-block batched Q19 fold; Q27 pinned (dead-lane partial write@0x1114). *)
(* 4 `sub v30` decrements roll ctr 8g+10 -> 8g+6 = nb+2.               *)
(* ===================================================================== *)

let TAIL_X5_REM4 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 4))))
              (word_add in_p (word (128 * g))) = word 64:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_REM4 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + 3 = (8 * g + 1) + 2`;
              ARITH_RULE `8 * g + 4 = (8 * g + 2) + 2`;
              ARITH_RULE `8 * g + 5 = (8 * g + 3) + 2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 4 = SUC(SUC(SUC(SUC(8 * g))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8*g+1);
       nist_cipher_block nonce rk inblock (8*g+2);
       nist_cipher_block nonce rk inblock (8*g+3)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8*g))`;
     `nist_cipher_block nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM4 : tactic =
  fold_q19_at `read Q19 s112 : int128` `8 * g + 4` TAIL_Q19_FOLD_REM4;;

let AESV8_GCM_8X_ENC_256_TAIL_REM4 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 4 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM4]) THEN
  MAP_EVERY NSTEP_GP (10--112) THEN
  FOLD_Q19_REM4 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (113--116) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1) = word (8 * g + 6)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 4` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 4 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ===================================================================== *)
(* [s121] FAST4_TAIL — the fast4 (nb=4, 64B) dedicated tail leg.          *)
(* Entry pc+0x191c (fast4 tail-setup start) with 4 keystreams (Q0..Q3)    *)
(* as preconditions (fresh entry so the tail-setup eor3 block0-ct write is *)
(* tracked, exactly like FAST2_TAIL); drives the 15-instr fast4 tail-setup *)
(* (block0 PT load + eor3 + 4 sub-v30 counter decrements + v5/v6/v7 = blk  *)
(* 1/2/3 keystreams) then the SHARED rem4_drain (0x13a0), ending pc+0x11cc. *)
(* Q30 = ctr(8g+10) at entry (base+8, unchanged from counter build) and the *)
(* 4 tail-setup subs roll it to 8g+6 = nb+2, so the counter closer REUSES   *)
(* TAIL_REM4's verbatim.  Fold Q19 at s71 (12 tail-setup + 59 drain) [s122: -3 movs -6 no-op].       *)
(* ===================================================================== *)

let FOLD_Q19_REM4_FAST4 : tactic =
  fold_q19_at `read Q19 s71 : int128` `8 * g + 4` TAIL_Q19_FOLD_REM4;;

let AESV8_GCM_8X_ENC_256_FAST4_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 4 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x196c) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--71) THEN
  FOLD_Q19_REM4_FAST4 THEN
  (*[s121tbl] KEEP Q12 (live tbl index) -> explicit discard = DISCARD_DEAD_REDUCE_SCRATCH minus Q12*)
  DISCARD_REGS ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q13"; "Q14"; "Q15"] THEN
  MAP_EVERY NSTEP_GP (72--74) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1) = word (8 * g + 6)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 4` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 4 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ===================================================================== *)
(* [s126] FAST3_TAIL — the fast3 (nb=3, 48B) dedicated tail leg.          *)
(* Clone of FAST4_TAIL for THREE blocks (keystreams Q0,Q1,Q2; ext+rev64   *)
(* tag format so NO Q12 index).  Entry 0x1cf0 (fast3 tail-setup start),   *)
(* then the eor3-fused 3-block drain (5 subs roll v30 base+8=ctr(8g+10)   *)
(* -> base+3=ctr(nb+2)).  Q19 folds at s57 via the cascade REM3 fold.     *)
(* ===================================================================== *)
let AESV8_GCM_8X_ENC_256_FAST3_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 3 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x1d54) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q25 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--57) THEN
  fold_q19_at `read Q19 s57 : int128` `8 * g + 3` TAIL_Q19_FOLD_REM3 THEN
  DISCARD_REGS ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q12"; "Q13"; "Q14"; "Q15"] THEN
  MAP_EVERY NSTEP_GP (58--60) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1) = word (8 * g + 5)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 3` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 3 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;


(* ===================================================================== *)
(* SESSION 080 — TAIL CASCADE arm rem=5 (nblocks = 8*g+5), lands at 0x1044. *)
(* 5-block batched Q19 fold; Q27 pinned (dead-lane partial write@0x1114). *)
(* 3 `sub v30` decrements roll ctr 8g+10 -> 8g+7 = nb+2.               *)
(* ===================================================================== *)

let TAIL_X5_REM5 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 5))))
              (word_add in_p (word (128 * g))) = word 80:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_REM5 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + 3 = (8 * g + 1) + 2`;
              ARITH_RULE `8 * g + 4 = (8 * g + 2) + 2`;
              ARITH_RULE `8 * g + 5 = (8 * g + 3) + 2`;
              ARITH_RULE `8 * g + 6 = (8 * g + 4) + 2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 5 = SUC(SUC(SUC(SUC(SUC(8 * g)))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8*g+1);
       nist_cipher_block nonce rk inblock (8*g+2);
       nist_cipher_block nonce rk inblock (8*g+3);
       nist_cipher_block nonce rk inblock (8*g+4)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8*g))`;
     `nist_cipher_block nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM5 : tactic =
  fold_q19_at `read Q19 s126 : int128` `8 * g + 5` TAIL_Q19_FOLD_REM5;;

let AESV8_GCM_8X_ENC_256_TAIL_REM5 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 5 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM5]) THEN
  MAP_EVERY NSTEP_GP (10--126) THEN
  FOLD_Q19_REM5 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (127--129) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1) = word (8 * g + 7)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 5` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 5 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ===================================================================== *)
(* SESSION 080 — TAIL CASCADE arm rem=6 (nblocks = 8*g+6), lands at 0x1008. *)
(* 6-block batched Q19 fold; Q27 pinned (dead-lane partial write@0x1114). *)
(* 2 `sub v30` decrements roll ctr 8g+10 -> 8g+8 = nb+2.               *)
(* ===================================================================== *)

let TAIL_X5_REM6 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 6))))
              (word_add in_p (word (128 * g))) = word 96:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_REM6 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + 3 = (8 * g + 1) + 2`;
              ARITH_RULE `8 * g + 4 = (8 * g + 2) + 2`;
              ARITH_RULE `8 * g + 5 = (8 * g + 3) + 2`;
              ARITH_RULE `8 * g + 6 = (8 * g + 4) + 2`;
              ARITH_RULE `8 * g + 7 = (8 * g + 5) + 2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 6 = SUC(SUC(SUC(SUC(SUC(SUC(8 * g))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8*g+1);
       nist_cipher_block nonce rk inblock (8*g+2);
       nist_cipher_block nonce rk inblock (8*g+3);
       nist_cipher_block nonce rk inblock (8*g+4);
       nist_cipher_block nonce rk inblock (8*g+5)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8*g))`;
     `nist_cipher_block nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM6 : tactic =
  fold_q19_at `read Q19 s134 : int128` `8 * g + 6` TAIL_Q19_FOLD_REM6;;

let AESV8_GCM_8X_ENC_256_TAIL_REM6 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 6 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`;
      ARITH_RULE `128 * g + 80 = 16 * (8 * g + 5)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM6]) THEN
  MAP_EVERY NSTEP_GP (10--134) THEN
  FOLD_Q19_REM6 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (135--137) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word (8 * g + 10):int32) (word 1)) (word 1) = word (8 * g + 8)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 6` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 6 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/ j = 8 * g + 5`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ===================================================================== *)
(* SESSION 080 — TAIL CASCADE arm rem=7 (nblocks = 8*g+7), lands at 0xfd0. *)
(* 7-block batched Q19 fold; Q27 pinned (dead-lane partial write@0x1114). *)
(* 1 `sub v30` decrements roll ctr 8g+10 -> 8g+9 = nb+2.               *)
(* ===================================================================== *)

let TAIL_X5_REM7 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 7))))
              (word_add in_p (word (128 * g))) = word 112:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_REM7 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + 3 = (8 * g + 1) + 2`;
              ARITH_RULE `8 * g + 4 = (8 * g + 2) + 2`;
              ARITH_RULE `8 * g + 5 = (8 * g + 3) + 2`;
              ARITH_RULE `8 * g + 6 = (8 * g + 4) + 2`;
              ARITH_RULE `8 * g + 7 = (8 * g + 5) + 2`;
              ARITH_RULE `8 * g + 8 = (8 * g + 6) + 2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 7 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * g)))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8*g+1);
       nist_cipher_block nonce rk inblock (8*g+2);
       nist_cipher_block nonce rk inblock (8*g+3);
       nist_cipher_block nonce rk inblock (8*g+4);
       nist_cipher_block nonce rk inblock (8*g+5);
       nist_cipher_block nonce rk inblock (8*g+6)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8*g))`;
     `nist_cipher_block nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM7 : tactic =
  fold_q19_at `read Q19 s140 : int128` `8 * g + 7` TAIL_Q19_FOLD_REM7;;

let AESV8_GCM_8X_ENC_256_TAIL_REM7 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 7 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 96)))) s0 =
    inblock (8 * g + 6)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`;
      ARITH_RULE `128 * g + 80 = 16 * (8 * g + 5)`;
      ARITH_RULE `128 * g + 96 = 16 * (8 * g + 6)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM7]) THEN
  MAP_EVERY NSTEP_GP (10--140) THEN
  FOLD_Q19_REM7 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (141--143) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word (8 * g + 10):int32) (word 1) = word (8 * g + 9)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 7` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 7 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/ j = 8 * g + 5 \/ j = 8 * g + 6`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;
(* ===================================================================== *)
(* SESSION 081 — TAIL CASCADE arm rem=8 (nblocks = 8*g+8), g-GENERAL.       *)
(*                                                                         *)
(* WB_TAIL (rem=8) above is stated with `~(k=0) /\ 8*(k+2)=nb`, i.e.        *)
(* groups = k+1 >= 2 (nblocks >= 24).  But the reassembly needs the rem=8   *)
(* arm at g=0 (nblocks=8) and g=1 (nblocks=16) too (both hit rem=8 in the   *)
(* (nblocks-1)DIV8 decomposition).  This is WB_TAIL's body reparametrized    *)
(* k+1 -> g so it holds for ALL g>=0; the drive is g-independent (x5=128     *)
(* regardless of g), so the proof transfers verbatim modulo two fixes:       *)
(*  - the fold reindex `8*g+8=(8*g+6)+2` must be LHS-scoped (else it eats     *)
(*    the RHS list-count 8*g+8 before its SUC^8 expansion — the s080 bug);   *)
(*  - block 8*g+6's keystream ctr 8*g+8 collapses to `nb` during the drive   *)
(*    (the 8*g+8=nb hyp rewrites 8*g+8->nb L->R), so re-expand nb->8*g+8 in   *)
(*    ONLY the Q19 fact before the fold (leaving the 8*g+8=nb hyp for the     *)
(*    tag/out closers); and the first new out-block (j=8*g) leaves a          *)
(*    constant-lambda inblock slot closed by unfold+BETA+rev-rev+BITWISE.     *)
(* ===================================================================== *)

(* ===================================================================== *)
(* [s127] FAST5_TAIL — the fast5 (nb=5, 80B) dedicated tail leg.        *)
(* Clone of FAST3_TAIL for 5 blocks (keystreams Q0..Q4; ext+rev64 tag      *)
(* format so NO Q12 index).  Entry pc+0x2034 (fast5 tail-setup start),       *)
(* eor3-fused 5-block drain (3 subs roll v30 base+8=ctr(8g+10) ->          *)
(* base+5=ctr(nb+2)).  Q19 folds at s82 via the cascade REM5 fold.        *)
(* ===================================================================== *)
let AESV8_GCM_8X_ENC_256_FAST5_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 5 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x207c) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[
      ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--82) THEN
  fold_q19_at `read Q19 s82 : int128` `8 * g + 5` TAIL_Q19_FOLD_REM5 THEN
  DISCARD_REGS ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q12"; "Q13"; "Q14"; "Q15"] THEN
  MAP_EVERY NSTEP_GP (83--86) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1) = word (8 * g + 7)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 5` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 5 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;


(* ===================================================================== *)
(* [s127] FAST6_TAIL — the fast6 (nb=6, 96B) dedicated tail leg.        *)
(* Clone of FAST3_TAIL for 6 blocks (keystreams Q0..Q5; ext+rev64 tag      *)
(* format so NO Q12 index).  Entry pc+0x2430 (fast6 tail-setup start),       *)
(* eor3-fused 6-block drain (2 subs roll v30 base+8=ctr(8g+10) ->          *)
(* base+6=ctr(nb+2)).  Q19 folds at s93 via the cascade REM6 fold.        *)
(* ===================================================================== *)
let AESV8_GCM_8X_ENC_256_FAST6_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 6 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x2478) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[
      ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`;
      ARITH_RULE `128 * g + 80 = 16 * (8 * g + 5)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--93) THEN
  fold_q19_at `read Q19 s93 : int128` `8 * g + 6` TAIL_Q19_FOLD_REM6 THEN
  DISCARD_REGS ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q12"; "Q13"; "Q14"; "Q15"] THEN
  MAP_EVERY NSTEP_GP (94--97) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word (8 * g + 10):int32) (word 1)) (word 1) = word (8 * g + 8)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 6` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 6 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/ j = 8 * g + 5`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;


(* ===================================================================== *)
(* [s127] FAST7_TAIL — the fast7 (nb=7, 112B) dedicated tail leg.        *)
(* Clone of FAST3_TAIL for 7 blocks (keystreams Q0..Q6; ext+rev64 tag      *)
(* format so NO Q12 index).  Entry pc+0x28c4 (fast7 tail-setup start),       *)
(* eor3-fused 7-block drain (1 subs roll v30 base+8=ctr(8g+10) ->          *)
(* base+7=ctr(nb+2)).  Q19 folds at s106 via the cascade REM7 fold.        *)
(* ===================================================================== *)
let AESV8_GCM_8X_ENC_256_FAST7_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce rk inblock nb g pc.
    nb = 8 * g + 7 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x290c) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 96)))) s0 =
    inblock (8 * g + 6)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[
      ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`;
      ARITH_RULE `128 * g + 80 = 16 * (8 * g + 5)`;
      ARITH_RULE `128 * g + 96 = 16 * (8 * g + 6)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--106) THEN
  fold_q19_at `read Q19 s106 : int128` `8 * g + 7` TAIL_Q19_FOLD_REM7 THEN
  DISCARD_REGS ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q12"; "Q13"; "Q14"; "Q15"] THEN
  MAP_EVERY NSTEP_GP (107--110) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word (8 * g + 10):int32) (word 1) = word (8 * g + 9)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 7` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 7 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/ j = 8 * g + 5 \/ j = 8 * g + 6`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_BITWISE_RULE);;



let TAIL_X5_128_G = prove
 (`!(in_p:int64) nb g.
     8 * g + 8 = nb
     ==> word_sub (word_add in_p (word (16 * nb)))
                  (word_add in_p (word (128 * g))) = word 128:int64`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_G =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + 2 = (8 * g + 0) + 2`;
              ARITH_RULE `8 * g + 3 = (8 * g + 1) + 2`;
              ARITH_RULE `8 * g + 4 = (8 * g + 2) + 2`;
              ARITH_RULE `8 * g + 5 = (8 * g + 3) + 2`;
              ARITH_RULE `8 * g + 6 = (8 * g + 4) + 2`;
              ARITH_RULE `8 * g + 7 = (8 * g + 5) + 2`;
              ARITH_RULE `8 * g + 8 = (8 * g + 6) + 2`;
              ARITH_RULE `8 * g + 9 = (8 * g + 7) + 2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * g + 8 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * g))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8 * g+1);
       nist_cipher_block nonce rk inblock (8 * g+2);
       nist_cipher_block nonce rk inblock (8 * g+3);
       nist_cipher_block nonce rk inblock (8 * g+4);
       nist_cipher_block nonce rk inblock (8 * g+5);
       nist_cipher_block nonce rk inblock (8 * g+6);
       nist_cipher_block nonce rk inblock (8 * g+7)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g))`;
     `nist_cipher_block nonce rk inblock (8 * g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_S136_G : tactic =
  fold_q19_at `read Q19 s136 : int128` `8 * g + 8` TAIL_Q19_FOLD_G;;

(* s098: general-g twin of FOLD_Q19_S114 — eor3-fused drain (-9 instrs) moved the final     *)
(* reduce to s114 (was s123).  See the WB_TAIL note.                                        *)
let FOLD_Q19_S114_G : tactic =
  fold_q19_at `read Q19 s115 : int128` `8 * g + 8` TAIL_Q19_FOLD_G;;

let AESV8_GCM_8X_ENC_256_TAIL_REM8 = prove
 (`!q18_init q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb g pc.
    8 * g + 8 = nb /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read Q18 s = q18_init /\
           read Q27 s = q27_init /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock)
                              (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
    `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 96)))) s0 =
    inblock (8 * g + 6) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 112)))) s0 =
    inblock (8 * g + 7)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE
     `128 * g + 16 = 16 * (8 * g + 1) /\
      128 * g + 32 = 16 * (8 * g + 2) /\
      128 * g + 48 = 16 * (8 * g + 3) /\
      128 * g + 64 = 16 * (8 * g + 4) /\
      128 * g + 80 = 16 * (8 * g + 5) /\
      128 * g + 96 = 16 * (8 * g + 6) /\
      128 * g + 112 = 16 * (8 * g + 7)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * a = 16 * 8 * a`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TAIL_X5_128_G (ASSUME `8 * g + 8 = nb`)]) THEN
  DISCARD_DEAD_KEYMEM THEN
  DISCARD_DEAD_HTABLE THEN
  DISCARD_REGS ["Q31"; "Q28"] THEN
  (* s098: eor3-fused drain (-9 instrs, drain 117->108) — same step-index shift as WB_TAIL: *)
  (* Q27 last-read s93 (drop after s96), final reduce s114 (was s123), writebacks s115..s118 *)
  (* (was s124..s127).                                                                       *)
  MAP_EVERY NSTEP_GP (10--97) THEN
  DISCARD_REGS ["Q27"] THEN
  MAP_EVERY NSTEP_GP (98--115) THEN
  (* block 8*g+6's keystream ctr 8*g+8 collapsed to nb during the drive (the 8*g+8=nb hyp   *)
  (* rewrites 8*g+8 -> nb L->R); re-expand nb -> 8*g+8 in ONLY the Q19 fact (leave the       *)
  (* 8*g+8=nb hyp intact for the tag/out closers) so the fold reindex fires on all 8 blocks. *)
  RULE_ASSUM_TAC(fun th ->
    if (try lhs(concl th) = `read Q19 s115:int128` with Failure _ -> false)
    then REWRITE_RULE[SYM(ASSUME `8 * g + 8 = nb`)] th else th) THEN
  FOLD_Q19_S114_G THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (116--119) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [
    REWRITE_TAC[IVEC_STORE_REV32] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `8 * g + 8 = nb` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [
    FIRST_X_ASSUM(fun th ->
      if concl th = `8 * g + 8 = nb` then SUBST_ALL_TAC(SYM th) else failwith "") THEN
    REWRITE_TAC[TAG_STORE_REV64] THEN AP_TERM_TAC THEN TAIL_Q19_FOLD_G;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if concl th = `8 * g + 8 = nb` then SUBST_ALL_TAC(SYM th) else failwith "") THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 8 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/
                       j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/
                       j = 8 * g + 5 \/ j = 8 * g + 6 \/ j = 8 * g + 7`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  (* block 8*g (first new out-block) leaves a nist_cipher_block with a constant-lambda inblock *)
  (* slot; unfold+BETA+rev-rev-cancel exposes the clean word_xor cancellation for all 8 blocks. *)
  REWRITE_TAC[nist_cipher_block; cipher_block] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* ===================================================================== *)
(* SESSION 081 — UNIFIED tail cascade: WB_TAIL_REM(rem in 1..8, g>=0).      *)
(*                                                                         *)
(* One theorem covering the whole b.gt cascade at entry pc+0xec0, for any   *)
(* leftover-block count rem in 1..8 and any group count g>=0.  Body =       *)
(* DISJ_CASES on rem, each case weakening the (strongest) unified           *)
(* precondition to that arm's precondition via ENSURES_PRECONDITION_THM     *)
(* (the arms REM1..7 need fewer register pins / keystreams; REM8 needs all) *)
(* then dispatching to the matching WB_TAIL_REM<rem>.  rem=8 uses the        *)
(* g-general WB_TAIL_REM8 (NOT the g>=2-only WB_TAIL).  The unified          *)
(* precondition pins q18_init/q27_init + all 8 keystreams + the 15 key-mem   *)
(* facts (REM8's precond); the weakening drops whatever each smaller arm     *)
(* omits.  BETA_TAC before STRIP_TAC is load-bearing (the precond is a       *)
(* lambda redex; STRIP-first stashes it unreduced — the s052 lesson).        *)
(* ===================================================================== *)

let AESV8_GCM_8X_ENC_256_TAIL_REM = prove
 (`!q18_init q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb r g pc.
    nb = 8 * g + r /\
    1 <= r /\ r <= 8 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read Q18 s = q18_init /\
           read Q27 s = q27_init /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock)
                              (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r=1\/r=2\/r=3\/r=4\/r=5\/r=6\/r=7\/r=8` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AESV8_GCM_8X_ENC_256_TAIL_REM1 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AESV8_GCM_8X_ENC_256_TAIL_REM2 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AESV8_GCM_8X_ENC_256_TAIL_REM3 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AESV8_GCM_8X_ENC_256_TAIL_REM4 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AESV8_GCM_8X_ENC_256_TAIL_REM5 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AESV8_GCM_8X_ENC_256_TAIL_REM6 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AESV8_GCM_8X_ENC_256_TAIL_REM7 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read Q18 s = q18_init /\
           read Q27 s = q27_init /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock)
                              (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AESV8_GCM_8X_ENC_256_TAIL_REM8 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])])]);;



(* ===================================================================== *)
(* STEP 5 (session 045) — AESV8_GCM_8X_ENC_256_CORRECT full body draft. *)
(* To be APPENDED to arm/proofs/aesv8_gcm_8x_enc_256.ml after the TAIL  *)
(* CHEAT is closed. Core: entry pc+0x38 (SETUP) -> exit pc+0x11a4 (TAIL).   *)
(*                                                                         *)
(* Assembly: 3 nested ENSURES_SEQUENCE_TAC at 0x4a0 / 0x9f0 / 0xec0.        *)
(* Each first leg: frame-subsume the segment's MAYCHANGE into the whole     *)
(* frame (ENSURES_FRAME_SUBSUMED + SUBSUMED_MAYCHANGE_TAC), then apply the  *)
(* segment thm via MP_TAC ... DISCH_THEN MATCH_MP_TAC (xts template         *)
(* aes_xts_encrypt.ml ~2621-2718).                                          *)
(* The PREPRETAIL->TAIL join uses the EXISTENTIAL Q18/Q27 mid-state         *)
(* (option D): the mid predicate carries `?v18 v27. read Q18 s=v18 /\       *)
(* read Q27 s=v27 /\ <PP-post-body minus tag-in-mem>`; PP leg proves it by  *)
(* EXISTS_TAC (read Q18 s)/(read Q27 s); TAIL leg strips the ? and applies  *)
(* TAIL SPEC'd to those.                                                    *)
(* ===================================================================== *)

(* Frame note: SETUP/MAIN_LOOP/PREPRETAIL frames are subsets of the CORRECT *)
(* frame (ABI ,, Q8..Q15 ,, mem[out_p;tag_p;ivec_p]).  SETUP frame writes    *)
(* only out_p mem (+ regs); PP writes out_p mem; TAIL writes out+tag+ivec.   *)

let LENGTH_WB_MC =
  (REWRITE_CONV [fst AESV8_GCM_8X_ENC_256_EXEC]) `LENGTH aesv8_gcm_8x_enc_256_mc`;;

(* Helper for the option-D TAIL leg: an ensures with an existential          *)
(* precondition follows from the ensures for every witness. Trivial from the *)
(* ensures def (the precondition ?v w. P is stripped, witnesses specialize   *)
(* the hypothesis).  Two-existential form matching the 0xec0 mid-state.       *)
let ENSURES_EXISTS2_PRECONDITION = prove
 (`!step (P:B->C->A->bool) Q Fr.
        (!v w. ensures step (\s. P v w s) Q Fr)
        ==> ensures step (\s. ?v w. P v w s) Q Fr`,
  REWRITE_TAC[ensures] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:B`; `w:C`]) THEN
  DISCH_THEN(MP_TAC o SPEC `s:A`) THEN ASM_REWRITE_TAC[]);;

let AESV8_GCM_8X_ENC_256_CORRECT = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     tag0 nonce rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 2) = nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  (* NOTE (session 045, VERIFIED against relational.ml:1401 + xts:2604): *)
  (* ENSURES_SEQUENCE_TAC AUTO-ADDS the `aligned_bytes_loaded` (program_decodes) *)
  (* and `read PC s = word pc'` conjuncts to BOTH legs' mid-state — so the `q`   *)
  (* arg must OMIT them (include ONLY the register/memory `Q s` remainder).      *)
  (* Also it fires MAYCHANGE_IDEMPOT_TAC internally, which DIES if the ABI macro *)
  (* is folded (memory P5 gotcha) — so UNFOLD it first.                          *)
  (* Expand the _WB_CORRECT precondition's ALLPAIRS + PAIRWISE into individual  *)
  (* nonoverlapping atoms BEFORE stripping, so each segment leg's antecedent     *)
  (* (out_p vs tag_p/ivec_p live in _WB_CORRECT's PAIRWISE) is available as an    *)
  (* assumption for ASM_SIMP/ASM_REWRITE.  (s049: SETUP's precond needs out_p vs  *)
  (* tag_p & ivec_p, which are PAIRWISE facts in _WB_CORRECT, not in its ALLPAIRS.)*)
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ============ SEQUENCE 1: SETUP  pc+0x38 -> pc+0x4a0 ============ *)
  (* mid-state OMITS aligned_bytes_loaded + read PC (auto-added by the tactic). *)
  ENSURES_SEQUENCE_TAC `pc + 0x4f0`
   `\s. read X0 s = word_add in_p (word (128 * (0 + 1))) /\
        read X2 s = word_add out_p (word (128 * (0 + 1))) /\
        read X3 s = tag_p /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read (memory :> bytes128 (word_add key_p (word 176))) s =
          word_reversefields 8 (EL 11 rk) /\
        read (memory :> bytes128 (word_add key_p (word 192))) s =
          word_reversefields 8 (EL 12 rk) /\
        read (memory :> bytes128 (word_add key_p (word 208))) s =
          word_reversefields 8 (EL 13 rk) /\
        read (memory :> bytes128 (word_add key_p (word 224))) s =
          word_reversefields 8 (EL 14 rk) /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 15)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
        read Q8 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 0)) (inblock (8 * 0 + 0)) /\
        read Q9 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 1)) (inblock (8 * 0 + 1)) /\
        read Q10 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 2)) (inblock (8 * 0 + 2)) /\
        read Q11 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 3)) (inblock (8 * 0 + 3)) /\
        read Q12 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 4)) (inblock (8 * 0 + 4)) /\
        read Q13 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 5)) (inblock (8 * 0 + 5)) /\
        read Q14 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 6)) (inblock (8 * 0 + 6)) /\
        read Q15 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 7)) (inblock (8 * 0 + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 10)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 11)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 12)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 13)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 14)) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (0 + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j)) /\
        ((read NF s <=> read VF s) <=> (0 = k))` THEN
  CONJ_TAC THENL
   [(* SETUP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
     AESV8_GCM_8X_ENC_256_SETUP) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 2: MAIN_LOOP  pc+0x4a0 -> pc+0x9f0 ============ *)
  (* mid-state = PREPRETAIL precondition (pc+0x9f0), OMITTING aligned+PC,     *)
  (* with mod_p := stackpointer+0x40.  Written EXPLICITLY (copy of PP pre     *)
  (* lines 4241-4307, dropping the aligned_bytes_loaded + read PC lines).     *)
  ENSURES_SEQUENCE_TAC `pc + 0xa40`
   `\s. read X0 s = word_add in_p (word (128 * (k + 1))) /\
        read X2 s = word_add out_p (word (128 * (k + 1))) /\
        read X3 s = tag_p /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read (memory :> bytes128 (word_add key_p (word 176))) s =
          word_reversefields 8 (EL 11 rk) /\
        read (memory :> bytes128 (word_add key_p (word 192))) s =
          word_reversefields 8 (EL 12 rk) /\
        read (memory :> bytes128 (word_add key_p (word 208))) s =
          word_reversefields 8 (EL 13 rk) /\
        read (memory :> bytes128 (word_add key_p (word 224))) s =
          word_reversefields 8 (EL 14 rk) /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 15)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * k)) /\
        read Q8 s = word_xor (aes_ctr_block nonce rk (8 * k + 0)) (inblock (8 * k + 0)) /\
        read Q9 s = word_xor (aes_ctr_block nonce rk (8 * k + 1)) (inblock (8 * k + 1)) /\
        read Q10 s = word_xor (aes_ctr_block nonce rk (8 * k + 2)) (inblock (8 * k + 2)) /\
        read Q11 s = word_xor (aes_ctr_block nonce rk (8 * k + 3)) (inblock (8 * k + 3)) /\
        read Q12 s = word_xor (aes_ctr_block nonce rk (8 * k + 4)) (inblock (8 * k + 4)) /\
        read Q13 s = word_xor (aes_ctr_block nonce rk (8 * k + 5)) (inblock (8 * k + 5)) /\
        read Q14 s = word_xor (aes_ctr_block nonce rk (8 * k + 6)) (inblock (8 * k + 6)) /\
        read Q15 s = word_xor (aes_ctr_block nonce rk (8 * k + 7)) (inblock (8 * k + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + 10)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + 11)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + 12)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + 13)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + 14)) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (k + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* MAIN_LOOP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
     AESV8_GCM_8X_ENC_256_MAIN_LOOP) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 3: PREPRETAIL  pc+0x9f0 -> pc+0xec0 (option D) === *)
  (* mid-state = ?v18 v27. read Q18 = v18 /\ read Q27 = v27 /\ <PP-post-body>. *)
  (* Build the join predicate: PREPRETAIL's postcondition body (lines         *)
  (* 4308-4379, mod_p -> stackpointer+0x40) wrapped in ?v18 v27 + the pins.    *)
  (* mid-state OMITS aligned+PC (auto-added).  The existential wraps the pins   *)
  (* + the PP-post body (minus tag-in-mem).  For ENSURES_EXISTS2_PRECONDITION to *)
  (* match on the TAIL leg, the `?v18 v27.` must be the OUTERMOST structure of   *)
  (* the `Q s` remainder — but the tactic wraps it as `aligned /\ PC /\ (?..)`.  *)
  (* NOTE-live: the auto-added aligned+PC sit OUTSIDE the ?; so on the TAIL leg  *)
  (* the precondition is `\s. aligned s /\ read PC s=.. /\ (?v18 v27. ...)`, and *)
  (* ENSURES_EXISTS2_PRECONDITION won't match directly.  Handle by first        *)
  (* SWAPPING: pull the ? outward, OR strip aligned+PC into asms via            *)
  (* ENSURES_PRECONDITION + a lambda that moves ? out (?v w. aligned/\PC/\body). *)
  (* Simplest live fix: make the mid-state itself `\s. ?v18 v27. read Q18 s=v18  *)
  (* /\ ... /\ <body>` and rely on the tactic adding aligned/PC OUTSIDE, then on *)
  (* the TAIL leg do `REWRITE_TAC[RIGHT_EXISTS_AND_THM/LEFT_EXISTS_AND_THM] o.a. *)
  (* to hoist the ? to the top before MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION. *)
  ENSURES_SEQUENCE_TAC `pc + 0xf10`
   `\s. ?v18 v27.
        read Q18 s = v18 /\ read Q27 s = v27 /\
        read X0 s = word_add in_p (word (128 * (k + 1))) /\
        read X2 s = word_add out_p (word (128 * (k + 1))) /\
        read X3 s = tag_p /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read (memory :> bytes128 (word_add key_p (word 176))) s =
          word_reversefields 8 (EL 11 rk) /\
        read (memory :> bytes128 (word_add key_p (word 192))) s =
          word_reversefields 8 (EL 12 rk) /\
        read (memory :> bytes128 (word_add key_p (word 208))) s =
          word_reversefields 8 (EL 13 rk) /\
        read (memory :> bytes128 (word_add key_p (word 224))) s =
          word_reversefields 8 (EL 14 rk) /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q28 s = word_reversefields 8 (EL 14 rk) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 18)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * (k + 1))) /\
        word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 10)) rk) /\
        word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 11)) rk) /\
        word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 12)) rk) /\
        word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 13)) rk) /\
        word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 14)) rk) /\
        word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 15)) rk) /\
        word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 16)) rk) /\
        word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 17)) rk) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (k + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* PREPRETAIL leg: apply PREPRETAIL, then weaken its post to the           *)
    (* existential mid-state (EXISTS the actual Q18/Q27 reads).                *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    (* Weaken the GOAL's post from Q_mid (the ?-existential) to PREPRETAIL's    *)
    (* actual post via ENSURES_POSTCONDITION_TAC (canonical idiom, robust:      *)
    (* it MATCH_MP_TAC's ENSURES_POSTCONDITION_THM + EXISTS_TAC the given post). *)
    (* This leaves TWO subgoals: (1) the pointwise implication PP_post ==>       *)
    (* Q_mid (closed by EXISTS_TAC (read Q18/Q27 s) + ASM_REWRITE), and (2)      *)
    (* `ensures arm PP_pre PP_post frame` = PREPRETAIL applied.                  *)
    (* NB the PP_post lambda passed here must OMIT the aligned+PC (the tactic    *)
    (* handles PC via the ensures) — actually pass PREPRETAIL's FULL post        *)
    (* (lines 4308-4379: read PC .. /\ body), i.e. exactly PREPRETAIL's post.    *)
    ENSURES_POSTCONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
          read PC s = word (pc + 0xf10) /\
          read X0 s = word_add in_p (word (128 * (k + 1))) /\
          read X2 s = word_add out_p (word (128 * (k + 1))) /\
          read X3 s = tag_p /\ read X4 s = word_add in_p (word (16 * nb)) /\
          read X16 s = ivec_p /\ read X5 s = end_p /\ read X6 s = htable_p /\
          read X10 s = word_add stackpointer (word 0x40) /\ read X11 s = key_p /\
          read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
            word 0xc200000000000000 /\
          read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = word_reversefields 8 (EL 1 rk) /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = word_reversefields 8 (EL 2 rk) /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = word_reversefields 8 (EL 3 rk) /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = word_reversefields 8 (EL 4 rk) /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = word_reversefields 8 (EL 5 rk) /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = word_reversefields 8 (EL 6 rk) /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = word_reversefields 8 (EL 7 rk) /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = word_reversefields 8 (EL 8 rk) /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = word_reversefields 8 (EL 9 rk) /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = word_reversefields 8 (EL 10 rk) /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = word_reversefields 8 (EL 11 rk) /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = word_reversefields 8 (EL 12 rk) /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = word_reversefields 8 (EL 13 rk) /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = word_reversefields 8 (EL 14 rk) /\
          read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
          read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
          read Q28 s = word_reversefields 8 (EL 14 rk) /\
          read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 18)) /\
          read Q31 s = word 79228162514264337593543950336 /\
          read Q19 s = nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * (k + 1))) /\
          word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 10)) rk) /\
          word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 11)) rk) /\
          word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 12)) rk) /\
          word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 13)) rk) /\
          word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 14)) rk) /\
          word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 15)) rk) /\
          word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 16)) rk) /\
          word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 17)) rk) /\
          htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
          (!j. j < nb ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
          (!j. j < 8 * (k + 1) ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
    CONJ_TAC THENL
     [(* (1) PP_post(aug) ==> Q_mid.  PREPRETAIL is augmented with aligned in    *)
      (* its post, so ENSURES_POSTCONDITION_TAC's antecedent lambda (above) also  *)
      (* carries aligned.  X_GEN_TAC forces the state var to `s` (so the pin      *)
      (* witnesses match); BETA_TAC reduces BOTH the antecedent redex `(\s.OLD)s` *)
      (* and the consequent redex `(\s.MID)s` BEFORE STRIP_TAC — critical: if     *)
      (* STRIP runs first it stashes the antecedent as ONE unreduced redex and    *)
      (* aligned never lands in the asms.  Then REPEAT(CONJ_TAC ...) peels the     *)
      (* aligned + PC conjuncts (both now in asms) off the mid's conjunction and   *)
      (* EXISTS the actual Q18/Q27 reads on the residual existential.  (s052:      *)
      (* dev-server-validated — SEQ1+SEQ2+SEQ3+TAIL all close, real prove, 0 hyp.) *)
      X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      (* (2) ensures PP_pre PP_post frame = PREPRETAIL applied.                *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
        `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
       AESV8_GCM_8X_ENC_256_PREPRETAIL) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC];
    (* NOTE-live: ENSURES_POSTCONDITION_TAC's post lambda must MATCH PP's post   *)
    (* modulo the frame — PC-conjunct kept, aligned dropped (post has no aligned)*)
    (* If the tactic rejects the shape, fall back to MP_TAC PP + IMP_CONJ +      *)
    (* ENSURES_POSTCONDITION_THM as before.  Pins close by REFL (EXISTS read Qn).*)
    ALL_TAC] THEN

  (* ============ TAIL leg: pc+0xec0 -> pc+0x11a4 ============ *)
  (* Precondition now carries ?v18 v27. Strip it via the helper, apply TAIL   *)
  (* SPEC'd to v18/v27.  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION turns the   *)
  (* goal `ensures step (\s. ?v18 v27. read Q18 s=v18 /\ read Q27 s=v27 /\ B)  *)
  (* post frame` into `!v18 v27. ensures step (\s. read Q18=v18 /\ ... /\ B)`. *)
  (* NOTE the mid-state must be syntactically `\s. ?v18 v27. read Q18 s=v18 /\ *)
  (* read Q27 s=v27 /\ <body>` for the helper's `\s. ?v w. P v w s` to match   *)
  (* (P v w s = read Q18 s=v /\ read Q27 s=w /\ body).  It is (built above).   *)
  (* BUT ENSURES_SEQUENCE_TAC auto-wrapped the precondition as                 *)
  (*   `\s. aligned_bytes_loaded .. /\ read PC s = word(pc+0xec0) /\ (?v w. B)` *)
  (* so the `?` is NOT outermost.  Hoist it out FIRST with GSYM               *)
  (* RIGHT_EXISTS_AND_THM (`P /\ (?x. Q x)` -> `?x. P /\ Q x`), applied under   *)
  (* the \s. binder (REWRITE descends), so the precondition becomes            *)
  (*   `\s. ?v w. aligned .. /\ read PC .. /\ B` and the helper matches.        *)
  (* If the aligned/PC conjuncts don't fully hoist, also try LEFT_EXISTS_AND_  *)
  (* THM / GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV).  (s049 live-note.)    *)
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION THEN
  MAP_EVERY X_GEN_TAC [`v18:int128`; `v27:int128`] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nb);
               memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v18:int128`; `v27:int128`;
    `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
    `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
   AESV8_GCM_8X_ENC_256_TAIL) THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* WB_CORRECT_GEN (session 083) - the loop_count>=1, groups>=2 core for the   *)
(* nblocks>=0 reassembly.  Identical to WB_CORRECT except the precond relaxes  *)
(* the rem=8-only 8*(k+2)=nb to the band 8*(k+1)<nb /\ nb<=8*(k+2) (rem 1..8), *)
(* adds val in_p+16*nb<2^63 (WB_TAIL_REM's buffer bound), and dispatches its    *)
(* four legs SETUP_GEN -> MAIN_LOOP -> PREPRETAIL -> WB_TAIL_REM(g=k+1,          *)
(* r=nb-8*(k+1)) instead of SETUP -> ... -> WB_TAIL.  MAIN_LOOP and PREPRETAIL   *)
(* need only 8*(k+1)<=nb so compose unchanged.  The TAIL leg normalizes the     *)
(* ctr indices 8*(k+1)+M (WB_TAIL_REM at g=k+1) to PREPRETAIL's 8*k+(M+8) form   *)
(* before MATCH_MP_TAC (arithmetically equal, syntactically distinct).          *)
(* This is groups>=2; the g=1 (k=0) boundary is a separate leg (2nd setup guard *)
(* is TAKEN there).                                                             *)
(* ========================================================================= *)
let AESV8_GCM_8X_ENC_256_CORRECT_GEN = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     tag0 nonce rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  (* NOTE (session 045, VERIFIED against relational.ml:1401 + xts:2604): *)
  (* ENSURES_SEQUENCE_TAC AUTO-ADDS the `aligned_bytes_loaded` (program_decodes) *)
  (* and `read PC s = word pc'` conjuncts to BOTH legs' mid-state — so the `q`   *)
  (* arg must OMIT them (include ONLY the register/memory `Q s` remainder).      *)
  (* Also it fires MAYCHANGE_IDEMPOT_TAC internally, which DIES if the ABI macro *)
  (* is folded (memory P5 gotcha) — so UNFOLD it first.                          *)
  (* Expand the _WB_CORRECT precondition's ALLPAIRS + PAIRWISE into individual  *)
  (* nonoverlapping atoms BEFORE stripping, so each segment leg's antecedent     *)
  (* (out_p vs tag_p/ivec_p live in _WB_CORRECT's PAIRWISE) is available as an    *)
  (* assumption for ASM_SIMP/ASM_REWRITE.  (s049: SETUP's precond needs out_p vs  *)
  (* tag_p & ivec_p, which are PAIRWISE facts in _WB_CORRECT, not in its ALLPAIRS.)*)
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ============ SEQUENCE 1: SETUP  pc+0x38 -> pc+0x4a0 ============ *)
  (* mid-state OMITS aligned_bytes_loaded + read PC (auto-added by the tactic). *)
  ENSURES_SEQUENCE_TAC `pc + 0x4f0`
   `\s. read X0 s = word_add in_p (word (128 * (0 + 1))) /\
        read X2 s = word_add out_p (word (128 * (0 + 1))) /\
        read X3 s = tag_p /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read (memory :> bytes128 (word_add key_p (word 176))) s =
          word_reversefields 8 (EL 11 rk) /\
        read (memory :> bytes128 (word_add key_p (word 192))) s =
          word_reversefields 8 (EL 12 rk) /\
        read (memory :> bytes128 (word_add key_p (word 208))) s =
          word_reversefields 8 (EL 13 rk) /\
        read (memory :> bytes128 (word_add key_p (word 224))) s =
          word_reversefields 8 (EL 14 rk) /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 15)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
        read Q8 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 0)) (inblock (8 * 0 + 0)) /\
        read Q9 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 1)) (inblock (8 * 0 + 1)) /\
        read Q10 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 2)) (inblock (8 * 0 + 2)) /\
        read Q11 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 3)) (inblock (8 * 0 + 3)) /\
        read Q12 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 4)) (inblock (8 * 0 + 4)) /\
        read Q13 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 5)) (inblock (8 * 0 + 5)) /\
        read Q14 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 6)) (inblock (8 * 0 + 6)) /\
        read Q15 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 7)) (inblock (8 * 0 + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 10)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 11)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 12)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 13)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 14)) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (0 + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j)) /\
        ((read NF s <=> read VF s) <=> (0 = k))` THEN
  CONJ_TAC THENL
   [(* SETUP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
     AESV8_GCM_8X_ENC_256_SETUP_GEN) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 2: MAIN_LOOP  pc+0x4a0 -> pc+0x9f0 ============ *)
  (* mid-state = PREPRETAIL precondition (pc+0x9f0), OMITTING aligned+PC,     *)
  (* with mod_p := stackpointer+0x40.  Written EXPLICITLY (copy of PP pre     *)
  (* lines 4241-4307, dropping the aligned_bytes_loaded + read PC lines).     *)
  ENSURES_SEQUENCE_TAC `pc + 0xa40`
   `\s. read X0 s = word_add in_p (word (128 * (k + 1))) /\
        read X2 s = word_add out_p (word (128 * (k + 1))) /\
        read X3 s = tag_p /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read (memory :> bytes128 (word_add key_p (word 176))) s =
          word_reversefields 8 (EL 11 rk) /\
        read (memory :> bytes128 (word_add key_p (word 192))) s =
          word_reversefields 8 (EL 12 rk) /\
        read (memory :> bytes128 (word_add key_p (word 208))) s =
          word_reversefields 8 (EL 13 rk) /\
        read (memory :> bytes128 (word_add key_p (word 224))) s =
          word_reversefields 8 (EL 14 rk) /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 15)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * k)) /\
        read Q8 s = word_xor (aes_ctr_block nonce rk (8 * k + 0)) (inblock (8 * k + 0)) /\
        read Q9 s = word_xor (aes_ctr_block nonce rk (8 * k + 1)) (inblock (8 * k + 1)) /\
        read Q10 s = word_xor (aes_ctr_block nonce rk (8 * k + 2)) (inblock (8 * k + 2)) /\
        read Q11 s = word_xor (aes_ctr_block nonce rk (8 * k + 3)) (inblock (8 * k + 3)) /\
        read Q12 s = word_xor (aes_ctr_block nonce rk (8 * k + 4)) (inblock (8 * k + 4)) /\
        read Q13 s = word_xor (aes_ctr_block nonce rk (8 * k + 5)) (inblock (8 * k + 5)) /\
        read Q14 s = word_xor (aes_ctr_block nonce rk (8 * k + 6)) (inblock (8 * k + 6)) /\
        read Q15 s = word_xor (aes_ctr_block nonce rk (8 * k + 7)) (inblock (8 * k + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + 10)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + 11)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + 12)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + 13)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + 14)) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (k + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* MAIN_LOOP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
     AESV8_GCM_8X_ENC_256_MAIN_LOOP) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 3: PREPRETAIL  pc+0x9f0 -> pc+0xec0 (option D) === *)
  (* mid-state = ?v18 v27. read Q18 = v18 /\ read Q27 = v27 /\ <PP-post-body>. *)
  (* Build the join predicate: PREPRETAIL's postcondition body (lines         *)
  (* 4308-4379, mod_p -> stackpointer+0x40) wrapped in ?v18 v27 + the pins.    *)
  (* mid-state OMITS aligned+PC (auto-added).  The existential wraps the pins   *)
  (* + the PP-post body (minus tag-in-mem).  For ENSURES_EXISTS2_PRECONDITION to *)
  (* match on the TAIL leg, the `?v18 v27.` must be the OUTERMOST structure of   *)
  (* the `Q s` remainder — but the tactic wraps it as `aligned /\ PC /\ (?..)`.  *)
  (* NOTE-live: the auto-added aligned+PC sit OUTSIDE the ?; so on the TAIL leg  *)
  (* the precondition is `\s. aligned s /\ read PC s=.. /\ (?v18 v27. ...)`, and *)
  (* ENSURES_EXISTS2_PRECONDITION won't match directly.  Handle by first        *)
  (* SWAPPING: pull the ? outward, OR strip aligned+PC into asms via            *)
  (* ENSURES_PRECONDITION + a lambda that moves ? out (?v w. aligned/\PC/\body). *)
  (* Simplest live fix: make the mid-state itself `\s. ?v18 v27. read Q18 s=v18  *)
  (* /\ ... /\ <body>` and rely on the tactic adding aligned/PC OUTSIDE, then on *)
  (* the TAIL leg do `REWRITE_TAC[RIGHT_EXISTS_AND_THM/LEFT_EXISTS_AND_THM] o.a. *)
  (* to hoist the ? to the top before MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION. *)
  ENSURES_SEQUENCE_TAC `pc + 0xf10`
   `\s. ?v18 v27.
        read Q18 s = v18 /\ read Q27 s = v27 /\
        read X0 s = word_add in_p (word (128 * (k + 1))) /\
        read X2 s = word_add out_p (word (128 * (k + 1))) /\
        read X3 s = tag_p /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read (memory :> bytes128 (word_add key_p (word 176))) s =
          word_reversefields 8 (EL 11 rk) /\
        read (memory :> bytes128 (word_add key_p (word 192))) s =
          word_reversefields 8 (EL 12 rk) /\
        read (memory :> bytes128 (word_add key_p (word 208))) s =
          word_reversefields 8 (EL 13 rk) /\
        read (memory :> bytes128 (word_add key_p (word 224))) s =
          word_reversefields 8 (EL 14 rk) /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q28 s = word_reversefields 8 (EL 14 rk) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 18)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * (k + 1))) /\
        word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 10)) rk) /\
        word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 11)) rk) /\
        word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 12)) rk) /\
        word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 13)) rk) /\
        word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 14)) rk) /\
        word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 15)) rk) /\
        word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 16)) rk) /\
        word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 17)) rk) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (k + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* PREPRETAIL leg: apply PREPRETAIL, then weaken its post to the           *)
    (* existential mid-state (EXISTS the actual Q18/Q27 reads).                *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    (* Weaken the GOAL's post from Q_mid (the ?-existential) to PREPRETAIL's    *)
    (* actual post via ENSURES_POSTCONDITION_TAC (canonical idiom, robust:      *)
    (* it MATCH_MP_TAC's ENSURES_POSTCONDITION_THM + EXISTS_TAC the given post). *)
    (* This leaves TWO subgoals: (1) the pointwise implication PP_post ==>       *)
    (* Q_mid (closed by EXISTS_TAC (read Q18/Q27 s) + ASM_REWRITE), and (2)      *)
    (* `ensures arm PP_pre PP_post frame` = PREPRETAIL applied.                  *)
    (* NB the PP_post lambda passed here must OMIT the aligned+PC (the tactic    *)
    (* handles PC via the ensures) — actually pass PREPRETAIL's FULL post        *)
    (* (lines 4308-4379: read PC .. /\ body), i.e. exactly PREPRETAIL's post.    *)
    ENSURES_POSTCONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
          read PC s = word (pc + 0xf10) /\
          read X0 s = word_add in_p (word (128 * (k + 1))) /\
          read X2 s = word_add out_p (word (128 * (k + 1))) /\
          read X3 s = tag_p /\ read X4 s = word_add in_p (word (16 * nb)) /\
          read X16 s = ivec_p /\ read X5 s = end_p /\ read X6 s = htable_p /\
          read X10 s = word_add stackpointer (word 0x40) /\ read X11 s = key_p /\
          read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
            word 0xc200000000000000 /\
          read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = word_reversefields 8 (EL 1 rk) /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = word_reversefields 8 (EL 2 rk) /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = word_reversefields 8 (EL 3 rk) /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = word_reversefields 8 (EL 4 rk) /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = word_reversefields 8 (EL 5 rk) /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = word_reversefields 8 (EL 6 rk) /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = word_reversefields 8 (EL 7 rk) /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = word_reversefields 8 (EL 8 rk) /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = word_reversefields 8 (EL 9 rk) /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = word_reversefields 8 (EL 10 rk) /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = word_reversefields 8 (EL 11 rk) /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = word_reversefields 8 (EL 12 rk) /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = word_reversefields 8 (EL 13 rk) /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = word_reversefields 8 (EL 14 rk) /\
          read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
          read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
          read Q28 s = word_reversefields 8 (EL 14 rk) /\
          read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 18)) /\
          read Q31 s = word 79228162514264337593543950336 /\
          read Q19 s = nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * (k + 1))) /\
          word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 10)) rk) /\
          word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 11)) rk) /\
          word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 12)) rk) /\
          word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 13)) rk) /\
          word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 14)) rk) /\
          word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 15)) rk) /\
          word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 16)) rk) /\
          word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + 17)) rk) /\
          htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
          (!j. j < nb ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
          (!j. j < 8 * (k + 1) ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
    CONJ_TAC THENL
     [(* (1) PP_post(aug) ==> Q_mid.  PREPRETAIL is augmented with aligned in    *)
      (* its post, so ENSURES_POSTCONDITION_TAC's antecedent lambda (above) also  *)
      (* carries aligned.  X_GEN_TAC forces the state var to `s` (so the pin      *)
      (* witnesses match); BETA_TAC reduces BOTH the antecedent redex `(\s.OLD)s` *)
      (* and the consequent redex `(\s.MID)s` BEFORE STRIP_TAC — critical: if     *)
      (* STRIP runs first it stashes the antecedent as ONE unreduced redex and    *)
      (* aligned never lands in the asms.  Then REPEAT(CONJ_TAC ...) peels the     *)
      (* aligned + PC conjuncts (both now in asms) off the mid's conjunction and   *)
      (* EXISTS the actual Q18/Q27 reads on the residual existential.  (s052:      *)
      (* dev-server-validated — SEQ1+SEQ2+SEQ3+TAIL all close, real prove, 0 hyp.) *)
      X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      (* (2) ensures PP_pre PP_post frame = PREPRETAIL applied.                *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
        `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
       AESV8_GCM_8X_ENC_256_PREPRETAIL) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC];
    (* NOTE-live: ENSURES_POSTCONDITION_TAC's post lambda must MATCH PP's post   *)
    (* modulo the frame — PC-conjunct kept, aligned dropped (post has no aligned)*)
    (* If the tactic rejects the shape, fall back to MP_TAC PP + IMP_CONJ +      *)
    (* ENSURES_POSTCONDITION_THM as before.  Pins close by REFL (EXISTS read Qn).*)
    ALL_TAC] THEN

  (* ============ TAIL leg: pc+0xec0 -> pc+0x11a4 ============ *)
  (* Precondition now carries ?v18 v27. Strip it via the helper, apply TAIL   *)
  (* SPEC'd to v18/v27.  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION turns the   *)
  (* goal `ensures step (\s. ?v18 v27. read Q18 s=v18 /\ read Q27 s=v27 /\ B)  *)
  (* post frame` into `!v18 v27. ensures step (\s. read Q18=v18 /\ ... /\ B)`. *)
  (* NOTE the mid-state must be syntactically `\s. ?v18 v27. read Q18 s=v18 /\ *)
  (* read Q27 s=v27 /\ <body>` for the helper's `\s. ?v w. P v w s` to match   *)
  (* (P v w s = read Q18 s=v /\ read Q27 s=w /\ body).  It is (built above).   *)
  (* BUT ENSURES_SEQUENCE_TAC auto-wrapped the precondition as                 *)
  (*   `\s. aligned_bytes_loaded .. /\ read PC s = word(pc+0xec0) /\ (?v w. B)` *)
  (* so the `?` is NOT outermost.  Hoist it out FIRST with GSYM               *)
  (* RIGHT_EXISTS_AND_THM (`P /\ (?x. Q x)` -> `?x. P /\ Q x`), applied under   *)
  (* the \s. binder (REWRITE descends), so the precondition becomes            *)
  (*   `\s. ?v w. aligned .. /\ read PC .. /\ B` and the helper matches.        *)
  (* If the aligned/PC conjuncts don't fully hoist, also try LEFT_EXISTS_AND_  *)
  (* THM / GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV).  (s049 live-note.)    *)
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION THEN
  MAP_EVERY X_GEN_TAC [`v18:int128`; `v27:int128`] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nb);
               memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v18:int128`; `v27:int128`;
    `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
    `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `nb - 8 * (k + 1)`; `k + 1`; `pc:num`]
   AESV8_GCM_8X_ENC_256_TAIL_REM) THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `8 * (k + 1) + 2 = 8 * k + 10`;
              ARITH_RULE `8 * (k + 1) + 3 = 8 * k + 11`;
              ARITH_RULE `8 * (k + 1) + 4 = 8 * k + 12`;
              ARITH_RULE `8 * (k + 1) + 5 = 8 * k + 13`;
              ARITH_RULE `8 * (k + 1) + 6 = 8 * k + 14`;
              ARITH_RULE `8 * (k + 1) + 7 = 8 * k + 15`;
              ARITH_RULE `8 * (k + 1) + 8 = 8 * k + 16`;
              ARITH_RULE `8 * (k + 1) + 9 = 8 * k + 17`;
              ARITH_RULE `8 * (k + 1) + 10 = 8 * k + 18`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* STEP 1c (session 085) — AESV8_GCM_8X_ENC_256_CORRECT_G1: the g=1 leg    *)
(* (loop_count = 0, i.e. nblocks 9..16).  At g=1 the main loop is SKIPPED     *)
(* (the 2nd setup guard b.ge@0x49c is TAKEN, SETUP_G1 lands directly at        *)
(* pc+0x9f0 = PREPRETAIL).  So this is WB_CORRECT_GEN's 4-leg compose MINUS    *)
(* the MAIN_LOOP SEQUENCE 2: SETUP_G1 -> PREPRETAIL_GEN(k=0) -> WB_TAIL_REM    *)
(* (g = 0+1, r = nb-8).  SETUP_G1 post @0x9f0 == WB_CORRECT_GEN SEQ2-mid at    *)
(* k:=0 (s084 boundary check), so all mids/ISPECL are written in literal-0     *)
(* form.  Buffer bound `val in_p + 16*nb < 2 EXP 63` carried for WB_TAIL_REM.  *)
(* ========================================================================= *)
let AESV8_GCM_8X_ENC_256_CORRECT_G1 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     tag0 nonce rk inblock nb k pc.
    k = 0 /\
    8 * (0 + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (0 + 1) < nb /\ nb <= 8 * (0 + 2) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    end_p = word_add in_p (word (128 * (0 + 1))) /\
    val in_p + 128 * (0 + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ===== SEQUENCE 1: SETUP_G1  pc+0x38 -> pc+0x9f0 (skips main loop) ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xa40`
   `\s. read X0 s = word_add in_p (word (128 * (0 + 1))) /\
        read X2 s = word_add out_p (word (128 * (0 + 1))) /\
        read X3 s = tag_p /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read (memory :> bytes128 (word_add key_p (word 176))) s =
          word_reversefields 8 (EL 11 rk) /\
        read (memory :> bytes128 (word_add key_p (word 192))) s =
          word_reversefields 8 (EL 12 rk) /\
        read (memory :> bytes128 (word_add key_p (word 208))) s =
          word_reversefields 8 (EL 13 rk) /\
        read (memory :> bytes128 (word_add key_p (word 224))) s =
          word_reversefields 8 (EL 14 rk) /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 15)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
        read Q8 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 0)) (inblock (8 * 0 + 0)) /\
        read Q9 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 1)) (inblock (8 * 0 + 1)) /\
        read Q10 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 2)) (inblock (8 * 0 + 2)) /\
        read Q11 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 3)) (inblock (8 * 0 + 3)) /\
        read Q12 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 4)) (inblock (8 * 0 + 4)) /\
        read Q13 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 5)) (inblock (8 * 0 + 5)) /\
        read Q14 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 6)) (inblock (8 * 0 + 6)) /\
        read Q15 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 7)) (inblock (8 * 0 + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 10)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 11)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 12)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 13)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 14)) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (0 + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SETUP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `0`; `pc:num`]
     AESV8_GCM_8X_ENC_256_SETUP_G1) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 3: PREPRETAIL  pc+0x9f0 -> pc+0xec0 (option D) === *)
  (* mid-state = ?v18 v27. read Q18 = v18 /\ read Q27 = v27 /\ <PP-post-body>. *)
  (* Build the join predicate: PREPRETAIL's postcondition body (lines         *)
  (* 4308-4379, mod_p -> stackpointer+0x40) wrapped in ?v18 v27 + the pins.    *)
  (* mid-state OMITS aligned+PC (auto-added).  The existential wraps the pins   *)
  (* + the PP-post body (minus tag-in-mem).  For ENSURES_EXISTS2_PRECONDITION to *)
  (* match on the TAIL leg, the `?v18 v27.` must be the OUTERMOST structure of   *)
  (* the `Q s` remainder — but the tactic wraps it as `aligned /\ PC /\ (?..)`.  *)
  (* NOTE-live: the auto-added aligned+PC sit OUTSIDE the ?; so on the TAIL leg  *)
  (* the precondition is `\s. aligned s /\ read PC s=.. /\ (?v18 v27. ...)`, and *)
  (* ENSURES_EXISTS2_PRECONDITION won't match directly.  Handle by first        *)
  (* SWAPPING: pull the ? outward, OR strip aligned+PC into asms via            *)
  (* ENSURES_PRECONDITION + a lambda that moves ? out (?v w. aligned/\PC/\body). *)
  (* Simplest live fix: make the mid-state itself `\s. ?v18 v27. read Q18 s=v18  *)
  (* /\ ... /\ <body>` and rely on the tactic adding aligned/PC OUTSIDE, then on *)
  (* the TAIL leg do `REWRITE_TAC[RIGHT_EXISTS_AND_THM/LEFT_EXISTS_AND_THM] o.a. *)
  (* to hoist the ? to the top before MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION. *)
  ENSURES_SEQUENCE_TAC `pc + 0xf10`
   `\s. ?v18 v27.
        read Q18 s = v18 /\ read Q27 s = v27 /\
        read X0 s = word_add in_p (word (128 * (0 + 1))) /\
        read X2 s = word_add out_p (word (128 * (0 + 1))) /\
        read X3 s = tag_p /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
        read (memory :> bytes128 (word_add key_p (word 16))) s =
          word_reversefields 8 (EL 1 rk) /\
        read (memory :> bytes128 (word_add key_p (word 32))) s =
          word_reversefields 8 (EL 2 rk) /\
        read (memory :> bytes128 (word_add key_p (word 48))) s =
          word_reversefields 8 (EL 3 rk) /\
        read (memory :> bytes128 (word_add key_p (word 64))) s =
          word_reversefields 8 (EL 4 rk) /\
        read (memory :> bytes128 (word_add key_p (word 80))) s =
          word_reversefields 8 (EL 5 rk) /\
        read (memory :> bytes128 (word_add key_p (word 96))) s =
          word_reversefields 8 (EL 6 rk) /\
        read (memory :> bytes128 (word_add key_p (word 112))) s =
          word_reversefields 8 (EL 7 rk) /\
        read (memory :> bytes128 (word_add key_p (word 128))) s =
          word_reversefields 8 (EL 8 rk) /\
        read (memory :> bytes128 (word_add key_p (word 144))) s =
          word_reversefields 8 (EL 9 rk) /\
        read (memory :> bytes128 (word_add key_p (word 160))) s =
          word_reversefields 8 (EL 10 rk) /\
        read (memory :> bytes128 (word_add key_p (word 176))) s =
          word_reversefields 8 (EL 11 rk) /\
        read (memory :> bytes128 (word_add key_p (word 192))) s =
          word_reversefields 8 (EL 12 rk) /\
        read (memory :> bytes128 (word_add key_p (word 208))) s =
          word_reversefields 8 (EL 13 rk) /\
        read (memory :> bytes128 (word_add key_p (word 224))) s =
          word_reversefields 8 (EL 14 rk) /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q28 s = word_reversefields 8 (EL 14 rk) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 18)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * (0 + 1))) /\
        word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 10)) rk) /\
        word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 11)) rk) /\
        word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 12)) rk) /\
        word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 13)) rk) /\
        word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 14)) rk) /\
        word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 15)) rk) /\
        word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 16)) rk) /\
        word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 17)) rk) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (0 + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* PREPRETAIL leg: apply PREPRETAIL, then weaken its post to the           *)
    (* existential mid-state (EXISTS the actual Q18/Q27 reads).                *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    (* Weaken the GOAL's post from Q_mid (the ?-existential) to PREPRETAIL's    *)
    (* actual post via ENSURES_POSTCONDITION_TAC (canonical idiom, robust:      *)
    (* it MATCH_MP_TAC's ENSURES_POSTCONDITION_THM + EXISTS_TAC the given post). *)
    (* This leaves TWO subgoals: (1) the pointwise implication PP_post ==>       *)
    (* Q_mid (closed by EXISTS_TAC (read Q18/Q27 s) + ASM_REWRITE), and (2)      *)
    (* `ensures arm PP_pre PP_post frame` = PREPRETAIL applied.                  *)
    (* NB the PP_post lambda passed here must OMIT the aligned+PC (the tactic    *)
    (* handles PC via the ensures) — actually pass PREPRETAIL's FULL post        *)
    (* (lines 4308-4379: read PC .. /\ body), i.e. exactly PREPRETAIL's post.    *)
    ENSURES_POSTCONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
          read PC s = word (pc + 0xf10) /\
          read X0 s = word_add in_p (word (128 * (0 + 1))) /\
          read X2 s = word_add out_p (word (128 * (0 + 1))) /\
          read X3 s = tag_p /\ read X4 s = word_add in_p (word (16 * nb)) /\
          read X16 s = ivec_p /\ read X5 s = end_p /\ read X6 s = htable_p /\
          read X10 s = word_add stackpointer (word 0x40) /\ read X11 s = key_p /\
          read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
            word 0xc200000000000000 /\
          read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = word_reversefields 8 (EL 1 rk) /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = word_reversefields 8 (EL 2 rk) /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = word_reversefields 8 (EL 3 rk) /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = word_reversefields 8 (EL 4 rk) /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = word_reversefields 8 (EL 5 rk) /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = word_reversefields 8 (EL 6 rk) /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = word_reversefields 8 (EL 7 rk) /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = word_reversefields 8 (EL 8 rk) /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = word_reversefields 8 (EL 9 rk) /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = word_reversefields 8 (EL 10 rk) /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = word_reversefields 8 (EL 11 rk) /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = word_reversefields 8 (EL 12 rk) /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = word_reversefields 8 (EL 13 rk) /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = word_reversefields 8 (EL 14 rk) /\
          read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
          read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce 2) /\
          read Q28 s = word_reversefields 8 (EL 14 rk) /\
          read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 18)) /\
          read Q31 s = word 79228162514264337593543950336 /\
          read Q19 s = nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block nonce rk inblock) (8 * (0 + 1))) /\
          word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 10)) rk) /\
          word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 11)) rk) /\
          word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 12)) rk) /\
          word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 13)) rk) /\
          word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 14)) rk) /\
          word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 15)) rk) /\
          word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 16)) rk) /\
          word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 17)) rk) /\
          htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
          (!j. j < nb ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
          (!j. j < 8 * (0 + 1) ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
    CONJ_TAC THENL
     [(* (1) PP_post(aug) ==> Q_mid.  PREPRETAIL is augmented with aligned in    *)
      (* its post, so ENSURES_POSTCONDITION_TAC's antecedent lambda (above) also  *)
      (* carries aligned.  X_GEN_TAC forces the state var to `s` (so the pin      *)
      (* witnesses match); BETA_TAC reduces BOTH the antecedent redex `(\s.OLD)s` *)
      (* and the consequent redex `(\s.MID)s` BEFORE STRIP_TAC — critical: if     *)
      (* STRIP runs first it stashes the antecedent as ONE unreduced redex and    *)
      (* aligned never lands in the asms.  Then REPEAT(CONJ_TAC ...) peels the     *)
      (* aligned + PC conjuncts (both now in asms) off the mid's conjunction and   *)
      (* EXISTS the actual Q18/Q27 reads on the residual existential.  (s052:      *)
      (* dev-server-validated — SEQ1+SEQ2+SEQ3+TAIL all close, real prove, 0 hyp.) *)
      X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      (* (2) ensures PP_pre PP_post frame = PREPRETAIL applied.                *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
        `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `0`; `pc:num`]
       AESV8_GCM_8X_ENC_256_PREPRETAIL_GEN) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC];
    (* NOTE-live: ENSURES_POSTCONDITION_TAC's post lambda must MATCH PP's post   *)
    (* modulo the frame — PC-conjunct kept, aligned dropped (post has no aligned)*)
    (* If the tactic rejects the shape, fall back to MP_TAC PP + IMP_CONJ +      *)
    (* ENSURES_POSTCONDITION_THM as before.  Pins close by REFL (EXISTS read Qn).*)
    ALL_TAC] THEN

  (* ============ TAIL leg: pc+0xec0 -> pc+0x11a4 ============ *)
  (* Precondition now carries ?v18 v27. Strip it via the helper, apply TAIL   *)
  (* SPEC'd to v18/v27.  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION turns the   *)
  (* goal `ensures step (\s. ?v18 v27. read Q18 s=v18 /\ read Q27 s=v27 /\ B)  *)
  (* post frame` into `!v18 v27. ensures step (\s. read Q18=v18 /\ ... /\ B)`. *)
  (* NOTE the mid-state must be syntactically `\s. ?v18 v27. read Q18 s=v18 /\ *)
  (* read Q27 s=v27 /\ <body>` for the helper's `\s. ?v w. P v w s` to match   *)
  (* (P v w s = read Q18 s=v /\ read Q27 s=w /\ body).  It is (built above).   *)
  (* BUT ENSURES_SEQUENCE_TAC auto-wrapped the precondition as                 *)
  (*   `\s. aligned_bytes_loaded .. /\ read PC s = word(pc+0xec0) /\ (?v w. B)` *)
  (* so the `?` is NOT outermost.  Hoist it out FIRST with GSYM               *)
  (* RIGHT_EXISTS_AND_THM (`P /\ (?x. Q x)` -> `?x. P /\ Q x`), applied under   *)
  (* the \s. binder (REWRITE descends), so the precondition becomes            *)
  (*   `\s. ?v w. aligned .. /\ read PC .. /\ B` and the helper matches.        *)
  (* If the aligned/PC conjuncts don't fully hoist, also try LEFT_EXISTS_AND_  *)
  (* THM / GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV).  (s049 live-note.)    *)
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION THEN
  MAP_EVERY X_GEN_TAC [`v18:int128`; `v27:int128`] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nb);
               memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v18:int128`; `v27:int128`;
    `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
    `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `nb - 8 * (0 + 1)`; `0 + 1`; `pc:num`]
   AESV8_GCM_8X_ENC_256_TAIL_REM) THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `8 * (0 + 1) + 2 = 8 * 0 + 10`;
              ARITH_RULE `8 * (0 + 1) + 3 = 8 * 0 + 11`;
              ARITH_RULE `8 * (0 + 1) + 4 = 8 * 0 + 12`;
              ARITH_RULE `8 * (0 + 1) + 5 = 8 * 0 + 13`;
              ARITH_RULE `8 * (0 + 1) + 6 = 8 * 0 + 14`;
              ARITH_RULE `8 * (0 + 1) + 7 = 8 * 0 + 15`;
              ARITH_RULE `8 * (0 + 1) + 8 = 8 * 0 + 16`;
              ARITH_RULE `8 * (0 + 1) + 9 = 8 * 0 + 17`;
              ARITH_RULE `8 * (0 + 1) + 10 = 8 * 0 + 18`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC);;

(* ===================================================================== *)
(* STEP 5b (session 053) — AESV8_GCM_8X_ENC_256_SUBROUTINE_CORRECT.     *)
(* The externally-used spec: lifts _WB_CORRECT through the 2 entry guards, *)
(* the d8-d15 save/restore frame (80 bytes), and the final RET.            *)
(*                                                                         *)
(* Wrapper shape (disasm-verified vs _wb.o, s049/s053):                    *)
(*   PROLOGUE 0x00 cbz x1,0x11c0 ; 0x04 tst x1,#0x7f ; 0x08 b.ne 0x11c0 ;  *)
(*     0x0c sub sp,#0x50 ; stp d8..d15 ; lsr x9,x1,#3 ; mov x16,x4 ;       *)
(*     mov x11,x5 ; mov x5,#0xc2..; stp x5,xzr,[sp,#64] ; add x10,sp,#0x40; *)
(*     0x38 = CORE ENTRY (_WB_CORRECT).                                     *)
(*   EPILOGUE 0x11a4 mov x0,x9 ; ldp d8..d15 ; add sp,#0x50 ; 0x11bc ret.   *)
(*   RETURN-0 0x11c0 mov w0,#0 ; ret (NOT reached under the precond).       *)
(* Entry C-ABI: X0=in_p X1=bit_len X2=out_p X3=tag_p X4=ivec_p X5=key_p    *)
(*   X6=htable_p; prologue moves X4->X16, X5->X11, x9=X1>>3.                *)
(*                                                                         *)
(* Not a clean ARM_ADD_RETURN_STACK_TAC: its internal ARM_STEPS (1--pre_n) *)
(* would hit the 2 CONDITIONAL guards (cbz/b.ne) and leave a conditional   *)
(* PC.  So it is HAND-ASSEMBLED (option i) — the guards fall through under  *)
(* the precond, discharged by WB_GUARD1_NONZERO + WB_GUARD2_MASK below.    *)
(* ===================================================================== *)

(* GUARD1: cbz x1 does NOT branch — X1 = word (128*nb) is nonzero, since    *)
(* nb = 8*(k+2) >= 16 > 0 and 128*nb < 2 EXP 64 (so val = 128*nb).          *)
let WB_GUARD1_NONZERO = prove
 (`!k nb. 8 * (k + 2) = nb /\ 128 * nb < 2 EXP 64
          ==> ~(word (128 * nb):int64 = word 0) /\
              ~(val(word (128 * nb):int64) = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
  SUBGOAL_THEN `val(word(128 * nb):int64) = 128 * nb` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* GUARD2: tst x1,#0x7f ; b.ne falls through — the low-7-bit mask AND is 0  *)
(* because 128 = 2 EXP 7 divides 128*nb.                                    *)
let WB_GUARD2_MASK = prove
 (`!k nb. 8 * (k + 2) = nb /\ 128 * nb < 2 EXP 64
          ==> word_and (word (128 * nb):int64) (word 0x7f) = word 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `0x7f = 2 EXP 7 - 1`; WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val(word(128 * nb):int64) = 128 * nb` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`] THEN
    MP_TAC(SPECL [`128`; `nb:num`] MOD_MULT) THEN ARITH_TAC]);;

(* GUARD3 (X9): the prologue `lsr x9,x1,#3` leaves X9 = word_ushr (word bit_len) *)
(* 3; the core entry precond needs X9 = word (bit_len DIV 8).  Reconcile them    *)
(* (val(word(128*nb)) = 128*nb since 128*nb < 2 EXP 64, and 2 EXP 3 = 8).        *)
let WB_X9_NORM = prove
 (`128 * nb < 2 EXP 64
   ==> word_ushr (word (128 * nb):int64) 3 = word ((128 * nb) DIV 8)`,
  STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 3 = 8`] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

(* ===================================================================== *)
(* GENERALIZATION ARC (session 075) — full functional correctness over    *)
(* ALL whole-block counts nblocks >= 0 (see orchestrator GENERALIZE_PLAN). *)
(* ===================================================================== *)

(* ---- loop_count = 0 branch mechanics (nblocks in 1..8) --------------------- *)
(* When groups = (nb-1) DIV 8 = 0 (i.e. nb <= 8), the round-down end pointer     *)
(* x5 = in_p + ((16*nb - 1) AND ~0x7f) collapses to in_p, because 16*nb-1 <= 127 *)
(* (< 128 = 2^7), so masking off the low 7 bits gives 0.  Then `cmp x0,x5;       *)
(* b.ge`@0x42c (x0 = in_p) is TAKEN, skipping the whole main loop and jumping    *)
(* straight to the tail cascade at pc+0xec0.  These two lemmas are the analogues *)
(* of SETUP_BRANCH_COND_FALSE / X5_END_PTR for the groups=0 leg — there the      *)
(* branch FALLS THROUGH (groups>=2); here it is TAKEN.                           *)

(* x5 (rounded-down last-full-group ptr) = in_p for nb in 1..8.                  *)
let WB_X5_GROUPS0 = prove
 (`!(in_p:int64) nb.
     1 <= nb /\ nb <= 8
     ==> word_add
           (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                     (word 18446744073709551488))
           in_p = in_p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (16 * nb)) (word 1):int64 = word (16 * nb - 1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word 18446744073709551488:int64 = word_not (word (2 EXP 7 - 1))`
    SUBST1_TAC THENL
   [CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV NUM_REDUCE_CONV))) THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `val(word (16 * nb - 1):int64) DIV 2 EXP 7 = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN
    SUBGOAL_THEN `val(word (16 * nb - 1):int64) = 16 * nb - 1` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0]]);;

(* The b.ge@0x42c condition (the exact NF!=VF biconditional the stepper emits    *)
(* for `cmp x0,x5` with x0 = in_p) collapses to T for nb in 1..8, so the         *)
(* conditional PC resolves to the tail entry pc+0xec0.                           *)
let WB_BRANCH_COND_TRUE = prove
 (`!(in_p:int64) nb.
     1 <= nb /\ nb <= 8
     ==> ((ival (word_sub in_p
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival in_p -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub in_p
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> T)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WB_X5_GROUPS0] THEN
  REWRITE_TAC[WORD_SUB_REFL; INT_SUB_REFL; IVAL_WORD_0] THEN
  INT_ARITH_TAC);;

(* ========================================================================= *)
(* GENERALIZATION ARC (nblocks>=0): WB_SETUP0 — the loop_count=0 setup leg.   *)
(*                                                                           *)
(* For 1 <= nblocks <= 8 (groups = (nb-1) DIV 8 = 0) the b.ge@0x42c is TAKEN  *)
(* (WB_BRANCH_COND_TRUE), so the main loop is SKIPPED: setup runs pc+0x38 ->  *)
(* pc+0xec0 (the tail entry) building the 8 CTR keystreams Q0..Q7 (ctr idx    *)
(* 2..9), the next-group counter Q30 = ctr_block nonce 10, and Q19 = the      *)
(* untouched GHASH accumulator = nist_ghash..[] = tag0.  This is the branch-  *)
(* TAKEN analogue of WB_SETUP (which falls through to the main loop for       *)
(* groups>=2).  The postcondition is WB_TAIL's precondition reindexed to      *)
(* groups=0 (Q0..Q7 pre-rk14 keystreams, Q30=10, Q19=[], X5=in_p, out-forall  *)
(* j<0 vacuous), so the generalized tail-cascade leg composes with it via     *)
(* ENSURES_SEQUENCE_TAC.                                                      *)
(*                                                                           *)
(* Drive = the WB_SETUP drive truncated at the branch: NSTEP(1--253) + NSTEP  *)
(* 254 (the b.ge) + WB_BRANCH_COND_TRUE resolves PC to pc+0xec0.  Closers     *)
(* (all validated s077): keystreams via KSCLOSE (AES256_CIPHER_RECONSTRUCT +  *)
(* CTR_BLOCK_RECONSTRUCT_REV8 + ctr_block/WORD_BLAST); Q30 via the index-10   *)
(* lane lemma SETUP_Q30_LANES_10 (the +7+1=8 analogue of SETUP_Q30_LANES) +   *)
(* CTR_BLOCK_RECONSTRUCT_REV32; Q19 via NIST_GHASH_NIL; X4 via the word_ushr  *)
(* /MOD_LT bridge; X5 via WB_X5_GROUPS0.                                      *)
(* ========================================================================= *)

(* SETUP_Q30_LANES_10: the index-10 counter lane lemma (base+7+1=8 => nonce 10). *)
let SETUP_Q30_LANES_10 = prove
 (`(word_add (word_add
      (word_reversefields 8
        (word_subword (word_reversefields 8 (ctr_block nonce 2)) (96,32):int32))
      (word 7)) (word 1):int32 = word 10) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce 2)) (64,32):int32)) (word 0):int32
    = word_subword nonce (0,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce 2)) (32,32):int32)) (word 0):int32
    = word_subword nonce (32,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce 2)) (0,32):int32)) (word 0):int32
    = word_subword nonce (64,32))`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* Keystream closer (KSCLOSE from s076 recipe): the pre-rk14 aese chain register  *)
(* Qj, XORed with rk14, is rev8(aes256_cipher(ctr_block nonce (j+2)) rk).         *)
let KSCLOSE =
  ASM_REWRITE_TAC[AES256_CIPHER_RECONSTRUCT; MAP;
                  WORD_REVERSEFIELDS_REVERSEFIELDS; AES256_CIPHER_KEYLIST] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN REWRITE_TAC[ctr_block] THEN
  CONV_TAC WORD_BLAST;;

(* Q30 counter closer (index 10). *)
let SETUP0_CTR_CLOSE =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SETUP_Q30_LANES_10; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST;;

(* Q19 init closer: nist_ghash over the empty list = tag0. *)
let SETUP0_Q19_CLOSE =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[list_of_seq; NIST_GHASH_NIL] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BLAST;;

(* Shape-routed dispatcher for the groups=0 setup postcond. *)
let SETUP0_DISPATCH : tactic = fun (asl,w as gl) ->
  if is_forall w then
    (* the input-forall (j<nb) and the vacuous out-forall (j<0) *)
    (REWRITE_TAC[ARITH_RULE `j < 8 * 0 <=> F`] THEN ASM_REWRITE_TAC[]) gl
  else if is_eq w then
    let l,r = dest_eq w in
    let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
    let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
    if rhd = "nist_ghash" then SETUP0_Q19_CLOSE gl
    else if lhd = "word_join" && rhd = "word_reversefields" then SETUP0_CTR_CLOSE gl
    else if lhd = "word_xor" then KSCLOSE gl
    else if lhd = "word_add" && rhd = "word_add" then
      (* X4: word_add in_p (word_ushr(word(128*nb))3) = word_add in_p (word(16*nb)). *)
      (AP_TERM_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD; DIMINDEX_64] THEN
       AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC) gl
    else if lhd = "word_add" then
      (* X5: word_add (round-down expr) in_p = in_p (via WB_X5_GROUPS0). *)
      ASM_SIMP_TAC[WB_X5_GROUPS0] gl
    else ASM_REWRITE_TAC[] gl
  else ASM_REWRITE_TAC[] gl;;

let AESV8_GCM_8X_ENC_256_SETUP0 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce rk inblock nb pc.
    1 <= nb /\ nb <= 8 /\ ~(nb = 2) /\ ~(nb = 4) /\ ~(nb = 1) /\ ~(nb = 3) /\
    ~(nb = 5) /\ ~(nb = 6) /\ ~(nb = 7) /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (word_add stackpointer (word 0x40), 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = in_p /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = in_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce 10) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) 0) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 2) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 3) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 4) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 5) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 6) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 7) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 8) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 9) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8]) THEN
  SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 3)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 5)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 6)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 7)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
  NSTEP 37 THEN NSTEP 38 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`)); COND_CLAUSES]) THEN
  NSTEP 39 THEN NSTEP 40 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
  NSTEP 41 THEN NSTEP 42 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 3)`)); COND_CLAUSES]) THEN
  NSTEP 43 THEN NSTEP 44 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH5_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 5)`)); COND_CLAUSES]) THEN
  NSTEP 45 THEN NSTEP 46 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH6_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 6)`)); COND_CLAUSES]) THEN
  NSTEP 47 THEN NSTEP 48 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH7_NOT_TAKEN
    (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 7)`)); COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (49--273) THEN NSTEP 274 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_BRANCH_COND_TRUE
     (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 8`)); COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[htable_mem_8] THEN REPEAT CONJ_TAC THEN SETUP0_DISPATCH);;

(* ===================================================================== *)
(* loop_count=0 leg (session 082): compose WB_SETUP0 (pc+0x38 -> pc+0xec0)  *)
(* with WB_TAIL_REM (rem=nblocks, g=0; pc+0xec0 -> pc+0x11a4) via           *)
(* ENSURES_SEQUENCE_TAC at pc+0xec0.  Covers nblocks 1..8 (one full tail    *)
(* group, no main loop).  Q18/Q27 are unpinned at SETUP0's exit -> option-D *)
(* existential mid-state (mirror of the WB_CORRECT PREPRETAIL->TAIL leg).   *)
(* ===================================================================== *)
let AESV8_GCM_8X_ENC_256_SETUP0_TAIL = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce rk inblock nb pc.
    1 <= nb /\ nb <= 8 /\ ~(nb = 2) /\ ~(nb = 4) /\ ~(nb = 1) /\ ~(nb = 3) /\
    ~(nb = 5) /\ ~(nb = 6) /\ ~(nb = 7) /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ===== SEQUENCE: SETUP0  pc+0x38 -> pc+0xec0 (option D) ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xf10`
   `\s. ?v18 v27.
        read Q18 s = v18 /\ read Q27 s = v27 /\
           read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = word_add in_p (word (128 * 0)) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock)
                              (8 * 0)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 8)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 9)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SETUP0 leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    ENSURES_POSTCONDITION_TAC
     `      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0xf10) /\
           read X0 s = in_p /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = in_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce 10) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) 0) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 2) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 3) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 4) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 5) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 6) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 7) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 8) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce 9) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0]) THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
        `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `pc:num`]
       AESV8_GCM_8X_ENC_256_SETUP0) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN

  (* ===== TAIL leg: pc+0xec0 -> pc+0x11a4 ===== *)
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION THEN
  MAP_EVERY X_GEN_TAC [`v18:int128`; `v27:int128`] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nb);
               memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v18:int128`; `v27:int128`;
    `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
    `word_add in_p (word (128 * 0)):int64`;
    `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `nb:num`; `0`; `pc:num`]
   AESV8_GCM_8X_ENC_256_TAIL_REM) THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN
  ASM_ARITH_TAC);;




(* ===================================================================== *)
(* s115: FAST2 leg (pc+0x38 -> pc+0x11c4, nb=2) = the 32B early-dispatch    *)
(* fast path. ENSURES_SEQUENCE at 0x1660: segment A = dispatch(DISPATCH_    *)
(* TAKEN)+2-block AES; segment B = FAST2_TAIL. Split at 0x1660 (NOT 0x14bc) *)
(* so the tail-setup eor3 block-ct write is tracked (fresh entry).          *)
(* ===================================================================== *)
let FAST2_MID_D2 : tactic = fun (asl,w as gl) ->
  if is_forall w then
    ((GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) ORELSE
     REWRITE_TAC[ARITH_RULE `8 * 0 = 0`; ARITH_RULE `!j:num. j < 0 <=> F`]) gl
  else if is_eq w then
    let l,r = dest_eq w in
    let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
    let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
    if lhd = "word_xor" then (FIRST_ASSUM ACCEPT_TAC ORELSE KSCLOSE) gl
    else
      (FIRST_ASSUM ACCEPT_TAC ORELSE
       (ASM_REWRITE_TAC[] THEN
        (if rhd = "nist_ghash" then SETUP0_Q19_CLOSE
         else if rhd = "word_reversefields" then SETUP0_CTR_CLOSE
         else if rhd = "word_add" then
            (REWRITE_TAC[ARITH_RULE `128 * 0 = 0`; WORD_ADD_0] THEN REFL_TAC)
         else (REFL_TAC ORELSE CONV_TAC WORD_BLAST)))) gl  (*[s117] Q25 index closer*)
  else (REWRITE_TAC[htable_mem_8] THEN ASM_REWRITE_TAC[]) gl;;
let AESV8_GCM_8X_ENC_256_FAST2 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce rk inblock nb pc.
    nb = 2 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x1764`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q25 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x1660 *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_TAKEN (ASSUME `nb = 2`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (37--107) THEN
    SUBGOAL_THEN `word_xor (read Q0 s107) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q1 s107) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x1660 -> 0x11c4 = FAST2_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AESV8_GCM_8X_ENC_256_FAST2_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;

(* ========================================================================= *)
(* [s121] FAST4 — the nb=4 (64B) early-dispatch leg, entry pc+0x38.          *)
(* Mirrors FAST2 exactly but for 4 blocks: the fast2 dispatch @0xc0 falls    *)
(* through (nb<>2), the fast4 dispatch @0xc8 is TAKEN (nb=4) -> 4-block AES   *)
(* (blocks 0-3 only) at 0x1750, then ENSURES_SEQUENCE-splits at 0x191c (the  *)
(* fast4 tail-setup start, keystreams as preconds) into FAST4_TAIL.          *)
(* ========================================================================= *)
let AESV8_GCM_8X_ENC_256_FAST4 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce rk inblock nb pc.
    nb = 4 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x196c`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 5)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x191c (dispatch + 4-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
    NSTEP 37 THEN NSTEP 38 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_TAKEN (ASSUME `nb = 4`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (39--163) THEN
    SUBGOAL_THEN `word_xor (read Q0 s163) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q1 s163) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q2 s163) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q3 s163) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 5)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x191c -> 0x11cc = FAST4_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AESV8_GCM_8X_ENC_256_FAST4_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;

(* ========================================================================= *)
(* [s126] FAST1 — the nb=1 (16B) early-dispatch leg, entry pc+0x38.          *)
(* fast2/fast4 dispatches fall through (nb<>2,4); the fast1 dispatch @0xd0   *)
(* is TAKEN (nb=1) -> 1-block AES (block 0 only) at 0x1a7c, then ENSURES_    *)
(* SEQUENCE-splits at 0x1b04 (fast1 tail-setup start, keystream Q0 as        *)
(* precond) into FAST1_TAIL.                                                 *)
(* ========================================================================= *)
let AESV8_GCM_8X_ENC_256_FAST1 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce rk inblock nb pc.
    nb = 1 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x1b44`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q25 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x1b04 (dispatch + 1-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
    NSTEP 37 THEN NSTEP 38 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`)); COND_CLAUSES]) THEN
    NSTEP 39 THEN NSTEP 40 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_TAKEN (ASSUME `nb = 1`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (41--84) THEN
    SUBGOAL_THEN `word_xor (read Q0 s84) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x1b04 -> 0x11dc = FAST1_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AESV8_GCM_8X_ENC_256_FAST1_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;

(* ========================================================================= *)
(* [s126] FAST3 — the nb=3 (48B) early-dispatch leg, entry pc+0x38.          *)
(* fast2/fast4/fast1 dispatches fall through (nb<>2,4,1); the fast3 dispatch *)
(* @0xd8 is TAKEN (nb=3) -> 3-block AES (blocks 0-2) at 0x1b90, then         *)
(* ENSURES_SEQUENCE-splits at 0x1cf0 (fast3 tail-setup start, 3 keystreams   *)
(* as preconds) into FAST3_TAIL.                                             *)
(* ========================================================================= *)
let AESV8_GCM_8X_ENC_256_FAST3 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce rk inblock nb pc.
    nb = 3 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x1d54`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q25 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x1cf0 (dispatch + 3-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
    NSTEP 37 THEN NSTEP 38 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`)); COND_CLAUSES]) THEN
    NSTEP 39 THEN NSTEP 40 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
    NSTEP 41 THEN NSTEP 42 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_TAKEN (ASSUME `nb = 3`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (43--140) THEN
    SUBGOAL_THEN `word_xor (read Q0 s140) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q1 s140) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q2 s140) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x1cf0 -> 0x11dc = FAST3_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AESV8_GCM_8X_ENC_256_FAST3_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;


let AESV8_GCM_8X_ENC_256_FAST5 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce rk inblock nb pc.
    nb = 5 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x207c`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 6)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x2034 (dispatch + 5-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 4)))) s0 = inblock 4`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 3)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
    NSTEP 37 THEN NSTEP 38 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`)); COND_CLAUSES]) THEN
    NSTEP 39 THEN NSTEP 40 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
    NSTEP 41 THEN NSTEP 42 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 3)`)); COND_CLAUSES]) THEN
    NSTEP 43 THEN NSTEP 44 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH5_TAKEN (ASSUME `nb = 5`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (45--186) THEN
    SUBGOAL_THEN `word_xor (read Q0 s186) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q1 s186) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q2 s186) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q3 s186) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 5)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q4 s186) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 6)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x2034 -> 0x11f4 = FAST5_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AESV8_GCM_8X_ENC_256_FAST5_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;



let AESV8_GCM_8X_ENC_256_FAST6 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce rk inblock nb pc.
    nb = 6 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2478`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 7)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x2430 (dispatch + 6-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 4)))) s0 = inblock 4`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 5)))) s0 = inblock 5`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 3)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 5)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
    NSTEP 37 THEN NSTEP 38 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`)); COND_CLAUSES]) THEN
    NSTEP 39 THEN NSTEP 40 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
    NSTEP 41 THEN NSTEP 42 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 3)`)); COND_CLAUSES]) THEN
    NSTEP 43 THEN NSTEP 44 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH5_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 5)`)); COND_CLAUSES]) THEN
    NSTEP 45 THEN NSTEP 46 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH6_TAKEN (ASSUME `nb = 6`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (47--215) THEN
    SUBGOAL_THEN `word_xor (read Q0 s215) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q1 s215) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q2 s215) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q3 s215) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 5)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q4 s215) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 6)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q5 s215) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 7)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x2430 -> 0x11f4 = FAST6_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AESV8_GCM_8X_ENC_256_FAST6_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;



let AESV8_GCM_8X_ENC_256_FAST7 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce rk inblock nb pc.
    nb = 7 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x290c`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 5)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 6)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 7)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 8)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 10)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x28c4 (dispatch + 7-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_mc`]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 4)))) s0 = inblock 4`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 5)))) s0 = inblock 5`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 6)))) s0 = inblock 6`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 3)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 5)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 6)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--34) THEN NSTEP 35 THEN NSTEP 36 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
    NSTEP 37 THEN NSTEP 38 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`)); COND_CLAUSES]) THEN
    NSTEP 39 THEN NSTEP 40 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
    NSTEP 41 THEN NSTEP 42 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 3)`)); COND_CLAUSES]) THEN
    NSTEP 43 THEN NSTEP 44 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH5_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 5)`)); COND_CLAUSES]) THEN
    NSTEP 45 THEN NSTEP 46 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH6_NOT_TAKEN
      (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 6)`)); COND_CLAUSES]) THEN
    NSTEP 47 THEN NSTEP 48 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH7_TAKEN (ASSUME `nb = 7`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (49--244) THEN
    SUBGOAL_THEN `word_xor (read Q0 s244) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 2)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q1 s244) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 3)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q2 s244) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 4)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q3 s244) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 5)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q4 s244) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 6)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q5 s244) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 7)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q6 s244) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + 8)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x28c4 -> 0x11f4 = FAST7_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AESV8_GCM_8X_ENC_256_FAST7_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;




(* ========================================================================= *)
(* STEP 2 (session 085) — AESV8_GCM_8X_ENC_256_CORRECT_ALL: the general    *)
(* core over ALL whole-block counts nb >= 1, entry pc+0x38 -> exit pc+0x11a4. *)
(* Case-splits on the group count g = (nb-1) DIV 8:                            *)
(*   nb 1..8  (g=0) -> SETUP0_TAIL ; nb 9..16 (g=1) -> WB_CORRECT_G1 ;         *)
(*   nb >= 17 (g>=2) -> WB_CORRECT_GEN with k = g-1.  All three legs share the *)
(* identical post/frame (ciphertext + nist_ghash tag + advanced counter).     *)
(* ========================================================================= *)
let AESV8_GCM_8X_ENC_256_CORRECT_ALL = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce rk inblock nb pc.
    1 <= nb /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x11f4) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nb <= 8 \/ (9 <= nb /\ nb <= 16) \/ 17 <= nb` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* ===== g = 0  (nb 1..8) ===== *)
    ASM_CASES_TAC `nb = 1` THENL
     [(* nb = 1 (16B): the fast1 early-dispatch path *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
        `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `pc:num`]
       AESV8_GCM_8X_ENC_256_FAST1) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
      (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
    ASM_CASES_TAC `nb = 2` THENL
     [(* nb = 2 (32B): the fast2 early-dispatch path *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
        `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `pc:num`]
       AESV8_GCM_8X_ENC_256_FAST2) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
      (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
      ASM_CASES_TAC `nb = 3` THENL
       [(* nb = 3 (48B): the fast3 early-dispatch path *)
        MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
          `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AESV8_GCM_8X_ENC_256_FAST3) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
      (* nb <> 3: split nb = 4 (fast4, 64B) vs nb not in {1,2,3,4} (SETUP0_TAIL) *)
      ASM_CASES_TAC `nb = 4` THENL
       [(* nb = 4 (64B): the fast4 early-dispatch path *)
        MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
          `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AESV8_GCM_8X_ENC_256_FAST4) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
        (* nb = 5 (80B): the fast5 early-dispatch path *)
        ASM_CASES_TAC `nb = 5` THENL
         [MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
          `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AESV8_GCM_8X_ENC_256_FAST5) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
        ASM_CASES_TAC `nb = 6` THENL
         [(* nb = 6 (96B): the fast6 early-dispatch path *)
          MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
          `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AESV8_GCM_8X_ENC_256_FAST6) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
        ASM_CASES_TAC `nb = 7` THENL
         [(* nb = 7 (112B): the fast7 early-dispatch path *)
          MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
          `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AESV8_GCM_8X_ENC_256_FAST7) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
        (* nb not in {1..7} (128B in this group): SETUP0_TAIL *)
        MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
          `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AESV8_GCM_8X_ENC_256_SETUP0_TAIL) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]]]]]]];
    (* ===== g = 1  (nb 9..16): WB_CORRECT_G1 (k=0) ===== *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
      `word_add in_p (word (128 * (0 + 1))):int64`;
      `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `0`; `pc:num`]
     AESV8_GCM_8X_ENC_256_CORRECT_G1) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
    (* ===== g >= 2  (nb >= 17): WB_CORRECT_GEN (k = groups-1) ===== *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
      `word_add in_p (word (128 * (((nb - 1) DIV 8 - 1) + 1))):int64`;
      `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `(nb - 1) DIV 8 - 1`; `pc:num`]
     AESV8_GCM_8X_ENC_256_CORRECT_GEN) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    ABBREV_TAC `q = (nb - 1) DIV 8` THEN ABBREV_TAC `r = (nb - 1) MOD 8` THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);;


(* Generalized entry-guard lemmas (session 085) for the general nblocks>=0     *)
(* wrapper's nb>=1 leg: GUARD1 (cbz x1 does not branch, word(128*nb) nonzero    *)
(* for nb>=1) and GUARD2 (tst x1,#0x7f falls through, 128 | 128*nb).  These     *)
(* generalize WB_GUARD1_NONZERO / WB_GUARD2_MASK from `8*(k+2)=nb` to `1<=nb`.  *)
let WB_GUARD1_NONZERO_GEN = prove
 (`!nb. 1 <= nb /\ 128 * nb < 2 EXP 64
        ==> ~(word (128 * nb):int64 = word 0) /\
            ~(val(word (128 * nb):int64) = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
  SUBGOAL_THEN `val(word(128 * nb):int64) = 128 * nb` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let WB_GUARD2_MASK_GEN = prove
 (`!nb. 1 <= nb /\ 128 * nb < 2 EXP 64
        ==> word_and (word (128 * nb):int64) (word 0x7f) = word 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `0x7f = 2 EXP 7 - 1`; WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val(word(128 * nb):int64) = 128 * nb` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`] THEN
    MP_TAC(SPECL [`128`; `nb:num`] MOD_MULT) THEN ARITH_TAC]);;

(* Hand-assembled wrapper (not a clean ARM_ADD_RETURN_STACK_TAC: the 2 entry   *)
(* guards leave a conditional PC that the tactic's internal ARM_STEPS cannot    *)
(* consume).  The drive (STEPS A-E, machine-validated session 055 on a real-    *)
(* EXEC server): A unfold ABI+preserve d8-d15/SP/X30+INIT+unfold htable_mem_8;  *)
(* B step the 3 guards, collapsing the cbz/b.ne fall-throughs via WB_GUARD1/2;  *)
(* C step the 11-instr prologue to pc+0x38, normalizing X9 via WB_X9_NORM;      *)
(* D apply _WB_CORRECT as a big step (in-frame SP = stackpointer-0x50);         *)
(* E step the 7-instr epilogue to the RET, restoring d8-d15.                    *)
let AESV8_GCM_8X_ENC_256_SUBROUTINE_CORRECT = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p
     tag0 nonce rk inblock nb k pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ~(k = 0) /\
    8 * (k + 2) = nb /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 80), 80)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 80), 80)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; word (128 * nb); out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           (!n. n < 15
                ==> read (memory :> bytes128 (word_add key_p (word (16 * n)))) s =
                    word_reversefields 8 (EL n rk)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = returnaddress /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 80), 80)])`,
  (* ---- STEP A: unfold ABI + preserve d8..d15/SP/X30 + INIT + unfold htable ---- *)
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
    [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(
    EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    REWRITE_CONV[WORD_ADD_0]))) THEN
  (* ---- STEP B: step the 3 guards, discharging both fall-throughs ---- *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD1_NONZERO
    (CONJ (ASSUME `8 * (k + 2) = nb`) (ASSUME `128 * nb < 2 EXP 64`));
    COND_CLAUSES]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [2] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD2_MASK
    (CONJ (ASSUME `8 * (k + 2) = nb`) (ASSUME `128 * nb < 2 EXP 64`));
    VAL_WORD_0; COND_CLAUSES]) THEN
  (* ---- STEP C: step prologue 0xc..0x34 (steps 4-14) -> PC=pc+0x38 ---- *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (4--14) THEN
  (* normalize X9 (lsr x1,#3): word_ushr -> word(_ DIV 8) for the BIGSTEP match *)
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_X9_NORM (ASSUME `128 * nb < 2 EXP 64`)]) THEN
  (* ---- STEP D: apply _WB_CORRECT via BIGSTEP (in-frame SP = stackpointer-0x50) ---- *)
  MP_TAC(SPECL
   [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`;
    `word_sub stackpointer (word 0x50):int64`;
    `128 * nb`;
    `word_add in_p (word (128 * (k + 1))):int64`;
    `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
   AESV8_GCM_8X_ENC_256_CORRECT) THEN
  REWRITE_TAC[LENGTH_WB_MC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS;
    htable_mem_8] THEN
  ARM_BIGSTEP_TAC AESV8_GCM_8X_ENC_256_EXEC "s15" THEN
  (* ---- STEP E: step epilogue 0x11a4..0x11bc (steps 16-22) -> ret ---- *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (16--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH] THEN
  CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* GENERAL SUBROUTINE WRAPPER over ALL whole-block counts nblocks >= 0        *)
(* (generalization arc, session 086 — the FINAL leg of the nblocks>=0 arc).   *)
(*                                                                            *)
(* Generalizes AESV8_GCM_8X_ENC_256_SUBROUTINE_CORRECT (above, scope       *)
(* `~(k=0) /\ 8*(k+2)=nb`, i.e. nb>=24 and 8|nb) to EVERY nb>=0.  Statement   *)
(* is identical to the narrow wrapper except: `nb` is a free variable (no k), *)
(* the buffer bound is `val in_p + 16*nb < 2 EXP 63` (WB_CORRECT_ALL's bound, *)
(* equal to the narrow `val in_p + 128*(k+1) < 2^63` at 8*(k+2)=nb), and the  *)
(* two scope conjuncts `~(k=0)` / `8*(k+2)=nb` are dropped.                    *)
(*                                                                            *)
(* Proof case-splits on nb=0:                                                 *)
(*   - nb=0: X1 = word(128*0) = word 0, so `cbz x1` at entry is TAKEN,         *)
(*     jumping to the return-0 path (mov w0,#0; ret).  No frame, no memory     *)
(*     write; tag/ivec preserved; the postcondition holds because             *)
(*     nist_ghash H tag0 (list_of_seq _ 0) = nist_ghash H tag0 [] = tag0,      *)
(*     ctr_block nonce (0+2) = ctr_block nonce 2, and both ciphertext/input    *)
(*     foralls are vacuous (j < 0).  (Inline 3-step drive; the memory frame is *)
(*     subsumed since nothing is written.)                                     *)
(*   - nb>=1: the narrow-wrapper drive STEPS A-E, but the two entry guards are *)
(*     discharged by WB_GUARD1_NONZERO_GEN / WB_GUARD2_MASK_GEN (needing only  *)
(*     1<=nb, from ~(nb=0)) and STEP D applies WB_CORRECT_ALL (the general     *)
(*     core, nb>=1) as the big step instead of the narrow WB_CORRECT.          *)
(*                                                                            *)
(* This is the externally-used spec for the whole-blocks AES-256-GCM 8x        *)
(* encrypt kernel.  The narrow WB_CORRECT / _SUBROUTINE_CORRECT are kept for   *)
(* provenance (they are the cold-gated base and special cases of the general  *)
(* theorems).                                                                 *)
(* ========================================================================= *)
let AESV8_GCM_8X_ENC_256_SUBROUTINE_CORRECT_GEN = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p
     tag0 nonce rk inblock nb pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 80), 80)]
      [(word pc, LENGTH aesv8_gcm_8x_enc_256_mc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 80), 80)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; word (128 * nb); out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           (!n. n < 15
                ==> read (memory :> bytes128 (word_add key_p (word (16 * n)))) s =
                    word_reversefields 8 (EL n rk)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = returnaddress /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + 2)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 80), 80)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `nb = 0` THENL
   [(* ============ nb = 0: cbz x1 TAKEN -> return 0 ============ *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ARITH_RULE `128 * 0 = 0`] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [1;2;3] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[list_of_seq; nist_ghash] THEN
    REWRITE_TAC[ARITH_RULE `j < 0 <=> F`];
    (* ============ nb >= 1: STEPS A-E, WB_CORRECT_ALL BIGSTEP ============ *)
    SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
      [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(
      EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV THENC
      REWRITE_CONV[WORD_ADD_0]))) THEN
    ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD1_NONZERO_GEN
      (CONJ (ASSUME `1 <= nb`) (ASSUME `128 * nb < 2 EXP 64`));
      COND_CLAUSES]) THEN
    ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [2] THEN
    ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [3] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD2_MASK_GEN
      (CONJ (ASSUME `1 <= nb`) (ASSUME `128 * nb < 2 EXP 64`));
      VAL_WORD_0; COND_CLAUSES]) THEN
    ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (4--14) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_X9_NORM
      (ASSUME `128 * nb < 2 EXP 64`)]) THEN
    MP_TAC(SPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`;
      `word_sub stackpointer (word 0x50):int64`;
      `128 * nb`;
      `tag0:int128`; `nonce:(96)word`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `pc:num`]
     AESV8_GCM_8X_ENC_256_CORRECT_ALL) THEN
    REWRITE_TAC[LENGTH_WB_MC] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
      REPEAT CONJ_TAC THEN
      (NONOVERLAPPING_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
       ASM_REWRITE_TAC[]);
      ALL_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
      MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS;
      htable_mem_8] THEN
    ARM_BIGSTEP_TAC AESV8_GCM_8X_ENC_256_EXEC "s15" THEN
    ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (16--22) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH] THEN
    CONV_TAC WORD_RULE]);;
