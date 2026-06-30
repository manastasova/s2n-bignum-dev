(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional specification of the MD5 compression function (RFC 1321).      *)
(*                                                                           *)
(* This is the algorithmic ground truth (Layer 1) for the md5_block          *)
(* correctness proof.  It mirrors the reference C implementation in          *)
(* aws-lc crypto/fipsmodule/md5/md5.c (the optimized F/G/H/I macro forms     *)
(* attributed to Wei Dai / Peter Gutmann / Rich Schroeppel) and RFC 1321.    *)
(*                                                                           *)
(* The four-word state (A,B,C,D) is carried as an int32 4-tuple.  Each MD5   *)
(* step updates one word and rotates the roles, exactly matching the         *)
(* R0..R3(A,B,C,D); R0..R3(D,A,B,C); ... cycle in md5.c.  After 64 steps     *)
(* (16 four-step cycles) the roles realign with the initial (A,B,C,D), and   *)
(* md5_block_spec adds the saved initial state back in (the MD5 "add-back"). *)
(*                                                                           *)
(* Validated in HOL against RFC 1321 Appendix A.5: MD5("") and MD5("abc")    *)
(* (see the regression theorems MD5_KAT_EMPTY / MD5_KAT_ABC at the end).     *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* The four auxiliary (round) functions, in the optimized forms from md5.c:  *)
(*   F(b,c,d) = ((c ^ d) & b) ^ d                                            *)
(*   G(b,c,d) = ((b ^ c) & d) ^ c                                            *)
(*   H(b,c,d) = b ^ c ^ d                                                    *)
(*   I(b,c,d) = (~d | b) ^ c                                                 *)
(* ------------------------------------------------------------------------- *)

let md5_f = new_definition
  `md5_f (b:int32) (c:int32) (d:int32) : int32 =
     word_xor (word_and (word_xor c d) b) d`;;

let md5_g = new_definition
  `md5_g (b:int32) (c:int32) (d:int32) : int32 =
     word_xor (word_and (word_xor b c) d) c`;;

let md5_h = new_definition
  `md5_h (b:int32) (c:int32) (d:int32) : int32 =
     word_xor (word_xor b c) d`;;

let md5_i = new_definition
  `md5_i (b:int32) (c:int32) (d:int32) : int32 =
     word_xor (word_or (word_not d) b) c`;;

(* Aux function selected by the step index: F for steps 0..15, G for 16..31, *)
(* H for 32..47, I for 48..63.                                               *)
let md5_aux = new_definition
  `md5_aux (i:num) (b:int32) (c:int32) (d:int32) : int32 =
     if i < 16 then md5_f b c d
     else if i < 32 then md5_g b c d
     else if i < 48 then md5_h b c d
     else md5_i b c d`;;

(* ------------------------------------------------------------------------- *)
(* The three per-step tables, all indexed by step number 0..63.              *)
(* ------------------------------------------------------------------------- *)

(* The 64 additive constants T[1..64] of RFC 1321 (= floor(2^32 |sin(i)|)),  *)
(* listed in execution (step) order as in md5.c's R0..R3 calls.              *)
let md5_T = define
 `md5_T =
    [word 0xd76aa478; word 0xe8c7b756; word 0x242070db; word 0xc1bdceee;
     word 0xf57c0faf; word 0x4787c62a; word 0xa8304613; word 0xfd469501;
     word 0x698098d8; word 0x8b44f7af; word 0xffff5bb1; word 0x895cd7be;
     word 0x6b901122; word 0xfd987193; word 0xa679438e; word 0x49b40821;
     word 0xf61e2562; word 0xc040b340; word 0x265e5a51; word 0xe9b6c7aa;
     word 0xd62f105d; word 0x02441453; word 0xd8a1e681; word 0xe7d3fbc8;
     word 0x21e1cde6; word 0xc33707d6; word 0xf4d50d87; word 0x455a14ed;
     word 0xa9e3e905; word 0xfcefa3f8; word 0x676f02d9; word 0x8d2a4c8a;
     word 0xfffa3942; word 0x8771f681; word 0x6d9d6122; word 0xfde5380c;
     word 0xa4beea44; word 0x4bdecfa9; word 0xf6bb4b60; word 0xbebfbc70;
     word 0x289b7ec6; word 0xeaa127fa; word 0xd4ef3085; word 0x04881d05;
     word 0xd9d4d039; word 0xe6db99e5; word 0x1fa27cf8; word 0xc4ac5665;
     word 0xf4292244; word 0x432aff97; word 0xab9423a7; word 0xfc93a039;
     word 0x655b59c3; word 0x8f0ccc92; word 0xffeff47d; word 0x85845dd1;
     word 0x6fa87e4f; word 0xfe2ce6e0; word 0xa3014314; word 0x4e0811a1;
     word 0xf7537e82; word 0xbd3af235; word 0x2ad7d2bb; word 0xeb86d391]
    : int32 list`;;

(* The message-word index g(i) used at each step (which of M[0..15] is read). *)
let md5_msgidx = define
 `md5_msgidx =
    [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15;
     1; 6; 11; 0; 5; 10; 15; 4; 9; 14; 3; 8; 13; 2; 7; 12;
     5; 8; 11; 14; 1; 4; 7; 10; 13; 0; 3; 6; 9; 12; 15; 2;
     0; 7; 14; 5; 12; 3; 10; 1; 8; 15; 6; 13; 4; 11; 2; 9] : num list`;;

(* The left-rotate amount s used at each step.                               *)
let md5_shift = define
 `md5_shift =
    [7; 12; 17; 22; 7; 12; 17; 22; 7; 12; 17; 22; 7; 12; 17; 22;
     5; 9; 14; 20; 5; 9; 14; 20; 5; 9; 14; 20; 5; 9; 14; 20;
     4; 11; 16; 23; 4; 11; 16; 23; 4; 11; 16; 23; 4; 11; 16; 23;
     6; 10; 15; 21; 6; 10; 15; 21; 6; 10; 15; 21; 6; 10; 15; 21] : num list`;;

(* ------------------------------------------------------------------------- *)
(* One MD5 step.  The state (a,b,c,d) here is in "role order": this step      *)
(* updates `a`, using b,c,d as the aux inputs:                               *)
(*     a' = rotl(a + aux(b,c,d) + M[g(i)] + T[i], s[i]) + b                   *)
(* and then the roles rotate, so the next step updates what was `d`:         *)
(*     (a,b,c,d) |-> (d, a', b, c).                                          *)
(* This reproduces md5.c's R(A,B,C,D); R(D,A,B,C); R(C,D,A,B); R(B,C,D,A);    *)
(* cycle exactly (a 4-step cycle returns the roles to A,B,C,D order).        *)
(* ------------------------------------------------------------------------- *)

let md5_step = new_definition
  `md5_step (i:num) (msg:num->int32) (a,b,c,d):int32#int32#int32#int32 =
     let t = word_add (word_add (word_add a (md5_aux i b c d))
                                (msg (EL i md5_msgidx)))
                      (EL i md5_T) in
     let a' = word_add (word_rol t (EL i md5_shift)) b in
     (d, a', b, c)`;;

(* Apply steps 0,1,...,n-1 in order (step 0 first, step n-1 outermost/last). *)
let md5_steps = define
  `(md5_steps 0 (msg:num->int32) st = st) /\
   (md5_steps (SUC n) msg st = md5_step n msg (md5_steps n msg st))`;;

(* Single-block compression: run all 64 steps from the incoming state, then  *)
(* add the incoming state back in (componentwise mod 2^32).                  *)
let md5_block_spec = new_definition
  `md5_block_spec (st:int32#int32#int32#int32) (msg:num->int32) =
     let (A,B,C,D) = st in
     let (a,b,c,d) = md5_steps 64 msg st in
     (word_add A a, word_add B b, word_add C c, word_add D d)`;;

(* Absorb n consecutive 16-word blocks.  `msg k` is the k-th 32-bit message  *)
(* word of the whole input stream; block i occupies words 16*i .. 16*i+15.   *)
let md5_blocks = define
  `(md5_blocks 0 st (msg:num->int32) = st) /\
   (md5_blocks (SUC n) st msg =
      md5_blocks n (md5_block_spec st msg) (\k. msg (k + 16)))`;;

(* ------------------------------------------------------------------------- *)
(* Shape lemmas: each per-step table has exactly 64 entries.                 *)
(* ------------------------------------------------------------------------- *)

let MD5_T_LENGTH = prove
 (`LENGTH (md5_T:int32 list) = 64`,
  REWRITE_TAC[md5_T; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_MSGIDX_LENGTH = prove
 (`LENGTH md5_msgidx = 64`,
  REWRITE_TAC[md5_msgidx; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_SHIFT_LENGTH = prove
 (`LENGTH md5_shift = 64`,
  REWRITE_TAC[md5_shift; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Evaluator used for the test-vector regression theorems below.  It exposes *)
(* SUC on the iteration counts, unfolds the recursions, reduces the table    *)
(* lookups and word arithmetic.                                              *)
(* ------------------------------------------------------------------------- *)

let MD5_STEPS_CONV =
  REPEATC
   (CHANGED_CONV
     (ONCE_DEPTH_CONV num_CONV THENC
      REWRITE_CONV[md5_steps] THENC
      REWRITE_CONV[md5_step; md5_aux; md5_f; md5_g; md5_h; md5_i;
                   md5_T; md5_msgidx; md5_shift] THENC
      DEPTH_CONV(EL_CONV ORELSEC NUM_RED_CONV) THENC
      TOP_DEPTH_CONV let_CONV THENC
      WORD_REDUCE_CONV));;

let MD5_BLOCKS_CONV =
  ONCE_DEPTH_CONV num_CONV THENC
  REWRITE_CONV[md5_blocks] THENC
  REWRITE_CONV[md5_block_spec] THENC
  ONCE_DEPTH_CONV MD5_STEPS_CONV THENC
  TOP_DEPTH_CONV let_CONV THENC
  WORD_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Known-answer regression theorems (RFC 1321 Appendix A.5).                 *)
(*                                                                           *)
(* The MD5 digest is the little-endian byte serialization of (A,B,C,D); the  *)
(* result words below serialize to the published digests:                    *)
(*   MD5("")    = d41d8cd98f00b204e9800998ecf8427e                           *)
(*   MD5("abc") = 900150983cd24fb0d6963f7d28e17f72                           *)
(* The standard IV is (0x67452301,0xefcdab89,0x98badcfe,0x10325476).         *)
(* ------------------------------------------------------------------------- *)

(* Empty string, padded to one block: M[0]=0x80, all other words 0.          *)
let MD5_KAT_EMPTY = prove
 (`md5_blocks 1 (word 0x67452301,word 0xefcdab89,word 0x98badcfe,word 0x10325476)
     (\k. if k = 0 then word 0x80 else word 0) =
   (word 0xd98c1dd4, word 0x04b2008f, word 0x980980e9, word 0x7e42f8ec)`,
  CONV_TAC MD5_BLOCKS_CONV);;

(* "abc", padded to one block: M[0]="abc"||0x80 = 0x80636261, M[14]=24 (the   *)
(* bit length), all other words 0.                                           *)
let MD5_KAT_ABC = prove
 (`md5_blocks 1 (word 0x67452301,word 0xefcdab89,word 0x98badcfe,word 0x10325476)
     (\k. if k = 0 then word 0x80636261 else if k = 14 then word 24 else word 0) =
   (word 0x98500190, word 0xb04fd23c, word 0x7d3f96d6, word 0x727fe128)`,
  CONV_TAC MD5_BLOCKS_CONV);;
