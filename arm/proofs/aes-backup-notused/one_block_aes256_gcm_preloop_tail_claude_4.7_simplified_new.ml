(* ========================================================================= *)
(* Correctness proof for one_block_aes256_gcm_preloop_tail (NEW SIMPLIFIED)  *)
(*                                                                           *)
(* Refactor of one_block_aes256_gcm_preloop_tail_claude_4.7_simplified.ml.   *)
(* The GHASH closure (lines 738--786 of the previous file) and the           *)
(* post-simulation normalization (lines 712--727) have been lifted into      *)
(* two named tactics, mirroring the AES-XTS pattern (XTSENC_TAC):            *)
(*                                                                           *)
(*   GCM_POST_SIM_NORMALIZE_TAC : the bookkeeping that runs once after the   *)
(*     ARM simulation finishes.  Folds STACK_PTR_CANCEL, mask collapses,     *)
(*     KAR_MID_BRIDGE, and the post-simulation pmul-arg normalization.       *)
(*                                                                           *)
(*   GCM_GHASH_STEP_TAC : closes the GHASH subgoal of one block.             *)
(*     Internally:                                                           *)
(*       1. unfold ghash_polyval_acc + apply the bridge                      *)
(*          GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT (one MATCH_MP)              *)
(*       2. unfold ghash_1block_karatsuba into its 17 lets                   *)
(*       3. identify word_xor xi (... aes256_block_enc ...) = word_xor xi ct *)
(*          via SUBGOAL_THEN                                                 *)
(*       4. run the reversefield / KAR_MID_BRIDGE / subword-distrib chain    *)
(*       5. ABBREV_ALL_PMUL_TAC + PMUL_ARG_SORT_CONV + WORD_BLAST            *)
(*                                                                           *)
(*   GCM_CT_STEP_TAC : closes the ciphertext subgoal of one block.           *)
(*     Just unfolds aes256_block_enc and rewrites with the abbreviation.     *)
(*                                                                           *)
(* The main proof's CONJ_TAC THENL block now has *one* tactic per branch.    *)
(* ========================================================================= *)

Sys.chdir "/home/ubuntu/auto_proofs/s2n-bignum";;

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/new_instructions.ml";;
needs "arm/proofs/utils/one_block_preloop_tail_spec.ml";;
needs "common/ghash_spec.ml";;

(* ---- Karatsuba limb extraction lemmas (256-bit word_pmul layout) --------- *)

let KARATSUBA_LIMB_0_63 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (0,64) : 64 word =
    word_subword xl (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_64_127 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (64,64) : 64 word =
    word_xor (word_subword xl (64,64)) (word_subword mid (0,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_128_191 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (128,64) : 64 word =
    word_xor (word_subword xh (0,64)) (word_subword mid (64,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_192_255 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (192,64) : 64 word =
    word_subword xh (64,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMBS = CONJ (CONJ KARATSUBA_LIMB_0_63 KARATSUBA_LIMB_64_127)
                           (CONJ KARATSUBA_LIMB_128_191 KARATSUBA_LIMB_192_255);;

(* ---- Pmul argument-order normalizer -------------------------------------- *)

let PMUL_NORM_CONV tm =
  match tm with
  | Comb(Comb(Const("word_pmul",_), a), b) ->
    if term_order a b then SPECL [a;b] WORD_PMUL_SYM
    else failwith "already normalized"
  | _ -> failwith "not word_pmul";;

(* ---- Assembly-shaped spec: Karatsuba multiply + Prop3 reduction ---------- *)

let ghash_1block_karatsuba = new_definition
 `ghash_1block_karatsuba (input:int128) (h:int128) (hk:int128) : int128 =
  let a_lo:64 word = word_subword input (0,64) in
  let a_hi:64 word = word_subword input (64,64) in
  let h_lo:64 word = word_subword h (0,64) in
  let h_hi:64 word = word_subword h (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl:int128 = word_pmul a_lo h_hi in
  let ph:int128 = word_pmul a_hi h_lo in
  let pm:int128 = word_pmul (word_xor a_lo a_hi) hk_lo in
  let mid:int128 = word_xor (word_xor pm ph) pl in
  let a:64 word = word_subword pl (0,64) in
  let b:64 word = word_xor (word_subword pl (64,64)) (word_subword mid (0,64)) in
  let c:64 word = word_xor (word_subword ph (0,64)) (word_subword mid (64,64)) in
  let d:64 word = word_subword ph (64,64) in
  let w:64 word = word 13979173243358019584 in
  let wa:128 word = word_pmul a w in
  let wa_lo:64 word = word_subword wa (0,64) in
  let wa_hi:64 word = word_subword wa (64,64) in
  let v:64 word = word_xor b wa_lo in
  let u:64 word = word_xor (word_xor c a) wa_hi in
  let wv:128 word = word_pmul v w in
  let wv_lo:64 word = word_subword wv (0,64) in
  let wv_hi:64 word = word_subword wv (64,64) in
  let f:64 word = word_xor u wv_lo in
  let g:64 word = word_xor (word_xor d v) wv_hi in
  word_reversefields 8 (word_join g f : 128 word)`;;

(* ---- polyval_dot expressed in Karatsuba + Prop3 form --------------------- *)

let POLYVAL_DOT_KARATSUBA = prove(
  `!(input:int128) (h:int128).
    polyval_dot input h =
    (let p_lo = word_pmul (word_subword input (0,64):(64)word)
                          (word_subword h (0,64):(64)word) : int128 in
     let p_hi = word_pmul (word_subword input (64,64):(64)word)
                          (word_subword h (64,64):(64)word) : int128 in
     let p_mid = word_pmul
        (word_xor (word_subword input (0,64):(64)word) (word_subword input (64,64)))
        (word_xor (word_subword h (0,64):(64)word) (word_subword h (64,64))) : int128 in
     let mid = word_xor (word_xor p_mid p_lo) p_hi in
     let a:64 word = word_subword p_lo (0,64) in
     let b:64 word = word_xor (word_subword p_lo (64,64)) (word_subword mid (0,64)) in
     let c:64 word = word_xor (word_subword p_hi (0,64)) (word_subword mid (64,64)) in
     let d:64 word = word_subword p_hi (64,64) in
     let w:64 word = word 13979173243358019584 in
     let wa:128 word = word_pmul a w in
     let wa_lo:64 word = word_subword wa (0,64) in
     let wa_hi:64 word = word_subword wa (64,64) in
     let v:64 word = word_xor b wa_lo in
     let u:64 word = word_xor (word_xor c a) wa_hi in
     let wv:128 word = word_pmul v w in
     let wv_lo:64 word = word_subword wv (0,64) in
     let wv_hi:64 word = word_subword wv (64,64) in
     let f:64 word = word_xor u wv_lo in
     let g:64 word = word_xor (word_xor d v) wv_hi in
     word_join g f : 128 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_dot; polyval_reduce_prop3; LET_DEF; LET_END_DEF;
              REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[KARATSUBA_LIMBS] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC]);;

(* ---- Bridge: ghash_1block_karatsuba(input, byteswap128 h, hk) =
               word_reversefields 8 (polyval_dot input h) ------------------- *)

let BYTESWAP128_SUBWORD_LO = prove(
  `!(h:int128). word_subword (byteswap128 h) (0,64):(64)word = word_subword h (64,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let BYTESWAP128_SUBWORD_HI = prove(
  `!(h:int128). word_subword (byteswap128 h) (64,64):(64)word = word_subword h (0,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_XOR_COMM = prove(
  `!(a:(N)word) (b:(N)word) n.
    word_subword (word_xor a (word_xor b c)) n:(M)word =
    word_subword (word_xor a (word_xor c b)) n`,
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT = prove(
  `!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==> ghash_1block_karatsuba input (byteswap128 h) hk =
        word_reversefields 8 (polyval_dot input h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI;
              REWRITE_RULE[LET_DEF; LET_END_DEF] POLYVAL_DOT_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC; WORD_SUBWORD_XOR_COMM]);;

(* ---- Machine code --------------------------------------------------------- *)

let one_block_prelooptail_2_mc = define_assert_from_elf
  "one_block_prelooptail_2_mc"
  "/home/ubuntu/auto_proofs/s2n-bignum/arm/aes-gcm/aes256_gcm_one_block.o"
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
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
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

let ONE_BLOCK_PRELOOP_TAIL_EXEC =
  ARM_MK_EXEC_RULE one_block_prelooptail_2_mc;;

(* ---- SIMD per-lane reversal fold lemmas ---------------------------------- *)

let REV64_LOWER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (0,8):(8)word) (word_subword xi (8,8):(8)word):(16)word)
                 (word_join (word_subword xi (16,8):(8)word) (word_subword xi (24,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (32,8):(8)word) (word_subword xi (40,8):(8)word):(16)word)
                 (word_join (word_subword xi (48,8):(8)word) (word_subword xi (56,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (0,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REV64_UPPER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (64,8):(8)word) (word_subword xi (72,8):(8)word):(16)word)
                 (word_join (word_subword xi (80,8):(8)word) (word_subword xi (88,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (96,8):(8)word) (word_subword xi (104,8):(8)word):(16)word)
                 (word_join (word_subword xi (112,8):(8)word) (word_subword xi (120,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REV64_128 = prove(
  `!(xi:(128)word).
    word_join
      (word_reversefields 8 (word_subword xi (64,64):(64)word))
      (word_reversefields 8 (word_subword xi (0,64):(64)word)):(128)word =
    word_subword (word_join (word_reversefields 8 xi:(128)word)
                            (word_reversefields 8 xi:(128)word):(256)word) (64,128)`,
  CONV_TAC WORD_BLAST);;

let WORD_SWAP_HALVES_INVOLUTION = prove(
  `!(a:(128)word).
    word_subword
      (word_join
        (word_subword (word_join a a:(256)word) (64,128):(128)word)
        (word_subword (word_join a a:(256)word) (64,128):(128)word):(256)word)
      (64,128):(128)word = a`,
  CONV_TAC WORD_BLAST);;

let SIMD_SIMPLIFY_RULES = [REV64_LOWER_LANE; REV64_UPPER_LANE; REV64_128];;

let SIMD_SIMPLIFY_ASSUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th);;

(* ---- Mask / word simplification lemmas ----------------------------------- *)

let MASK_IS_ONES = prove(
  `!(x:(128)word).
    word_insert (word_insert x (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word =
    (word_not(word 0):(128)word)`, CONV_TAC WORD_BLAST);;
let WORD_AND_MASK = prove(
  `!(x:(128)word) (y:(128)word).
    word_and x (word_insert (word_insert y (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word) = x`,
  REWRITE_TAC[MASK_IS_ONES; WORD_AND_NOT0]);;
let WORD_AND_MASK_SYM = prove(
  `!(x:(128)word) (y:(128)word).
    word_and (word_insert (word_insert y (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word) x = x`,
  REWRITE_TAC[MASK_IS_ONES; WORD_AND_NOT0]);;
let BIF_MASK = prove(
  `!(d:(128)word) (n:(128)word) (m:(128)word).
    word_or (word_and d (word_insert (word_insert m (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word))
    (word_and n (word_not (word_insert (word_insert m (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word))) = d`,
  CONV_TAC WORD_BLAST);;
let WORD_ZX_ALLONES_64_128 = prove(
  `word_zx (word 18446744073709551615:(64)word):(128)word =
   word 18446744073709551615:(128)word`, CONV_TAC WORD_BLAST);;
let MASK_IS_ONES_64 = prove(
  `!(x:(128)word).
    word_insert (word_insert x (0,64) (word 18446744073709551615:(64)word):(128)word)
      (64,64) (word 18446744073709551615:(64)word):(128)word =
    (word_not(word 0):(128)word)`, CONV_TAC WORD_BLAST);;
let WORD_AND_MASK_64 = prove(
  `!(x:(128)word) (y:(128)word).
    word_and x (word_insert (word_insert y (0,64) (word 18446744073709551615:(64)word):(128)word)
      (64,64) (word 18446744073709551615:(64)word):(128)word) = x`,
  REWRITE_TAC[MASK_IS_ONES_64; WORD_AND_NOT0]);;
let WORD_AND_MASK_SYM_64 = prove(
  `!(x:(128)word) (y:(128)word).
    word_and (word_insert (word_insert y (0,64) (word 18446744073709551615:(64)word):(128)word)
      (64,64) (word 18446744073709551615:(64)word):(128)word) x = x`,
  REWRITE_TAC[MASK_IS_ONES_64; WORD_AND_NOT0]);;

(* Stack/pointer arithmetic normalizer *)
let STACK_PTR_CANCEL = WORD_RULE
  `!(x:(N)word) y. word_sub (word_add x y) y = x`;;

(* ---- Per-step cleanup, called after every ARM_STEPS_TAC step ------------- *)
let GCM_ENC_SIMPLIFY_TAC =
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION;
    WORD_ZX_ALLONES_64_128; WORD_AND_MASK; WORD_AND_MASK_SYM; BIF_MASK;
    WORD_AND_MASK_64; WORD_AND_MASK_SYM_64]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th);;

(* ---- GHASH closure lemmas ------------------------------------------------ *)

let WORD_XOR_0_LEFT = WORD_BITWISE_RULE
  `word_xor (word 0) x = (x:(N)word)`;;

let WORD_INSERT_AS_JOIN_1 = prove(
  `!(a:(128)word) (b:(128)word).
    word_insert a (0,64) (word_subword b (64,64):(128)word) =
    (word_join (word_subword a (64,64):(64)word) (word_subword b (64,64):(64)word):(128)word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
              BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128;
              SUB_0; LE_0; ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COND_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 128 /\ ~(i < 64) ==> i - 64 < 64`;
               ARITH_RULE `i < 128 /\ ~(i < 64) ==> 64 + i - 64 = i`]);;

let WORD_INSERT_AS_JOIN_2 = prove(
  `!(a:(128)word) (b:(128)word).
    word_insert a (64,64) (word_subword b (0,64):(128)word) =
    (word_join (word_subword b (0,64):(64)word) (word_subword a (0,64):(64)word):(128)word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
              BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128;
              SUB_0; LE_0; ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COND_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `64 <= i /\ i < 128 ==> ~(i < 64)`;
               ARITH_RULE `64 <= i /\ i < 128 ==> i - 64 < 64`;
               ARITH_RULE `~(64 <= i /\ i < 128) /\ i < 128 ==> i < 64`;
               ARITH_RULE `0 + i = i`]);;

let KAR_SUBWORD_LEMMA = prove(
  `!(xi_rev:(128)word).
    word_subword
      (word_xor xi_rev
        (word_subword (word_join xi_rev xi_rev:(256)word) (64,128)))
      (0,64):(64)word =
    word_xor (word_subword xi_rev (0,64):(64)word)
             (word_subword xi_rev (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REVERSEFIELDS8_SUBWORD_LO = prove(
  `!(x:(128)word).
    word_reversefields 8 (word_subword x (0,64):(64)word) =
    word_subword (word_reversefields 8 x:(128)word) (64,64):(64)word`,
  CONV_TAC WORD_BLAST);;
let REVERSEFIELDS8_SUBWORD_HI = prove(
  `!(x:(128)word).
    word_reversefields 8 (word_subword x (64,64):(64)word) =
    word_subword (word_reversefields 8 x:(128)word) (0,64):(64)word`,
  CONV_TAC WORD_BLAST);;
let WORD_REVERSEFIELDS_XOR_8_128 = prove(
  `!(x:(128)word) (y:(128)word).
    word_reversefields 8 (word_xor x y) =
    word_xor (word_reversefields 8 x) (word_reversefields 8 y)`,
  CONV_TAC WORD_BLAST);;
let KAR_MID_BRIDGE = prove(
  `!(xi:(128)word) (ct:(128)word).
    word_xor (word_subword (word_reversefields 8 xi) (64,64):(64)word)
             (word_xor (word_subword (word_reversefields 8 ct) (64,64))
                       (word_subword (word_reversefields 8 (word_xor xi ct)) (0,64))) =
    word_xor (word_subword (word_reversefields 8 (word_xor xi ct)) (0,64))
             (word_subword (word_reversefields 8 (word_xor xi ct)) (64,64))`,
  REWRITE_TAC[WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  CONV_TAC WORD_RULE);;
let HALFSWAP_XOR = prove(
  `!(a:(128)word) (b:(128)word).
    word_xor
      (word_join (word_join (word_subword a (64,64):(64)word) (word_subword a (0,64):(64)word):(128)word)
                 (word_join (word_subword a (64,64):(64)word) (word_subword a (0,64):(64)word):(128)word):(256)word)
      (word_join b b:(256)word) =
    word_join (word_xor a b:(128)word) (word_xor a b:(128)word):(256)word`,
  CONV_TAC WORD_BLAST);;
let REV8_JOIN_FOLD = prove(
  `!(lo:(64)word) (hi:(64)word).
    word_join (word_reversefields 8 lo) (word_reversefields 8 hi):(128)word =
    word_reversefields 8 (word_join hi lo:(128)word)`,
  CONV_TAC WORD_BLAST);;

(* ---- Tactics for closing the GHASH subgoal: abbreviate word_pmul terms,
   sort XOR arguments inside word_pmul canonically ------------------------ *)

let ABBREV_ALL_PMUL_TAC : tactic = fun (asl,w) ->
  let pms = find_terms (fun t -> try
    let (f,_) = dest_comb t in
    let (g,_) = dest_comb f in
    name_of g = "word_pmul"
    with _ -> false) w in
  let uniq = setify pms in
  let all_frees =
    frees w @ List.concat (map (fun (_,th) -> frees(concl th)) asl) in
  let rec process all n ts (asl,w) =
    match ts with
    | [] -> ALL_TAC (asl,w)
    | t :: rest ->
      let v = variant all (mk_var("pm" ^ string_of_int n, type_of t)) in
      (ABBREV_TAC (mk_eq(v, t)) THEN process (v::all) (n+1) rest) (asl,w) in
  process all_frees 0 uniq (asl,w);;

let PMUL_ARG_SORT_CONV tm =
  match tm with
  | Comb(Comb(Const("word_pmul",_), a), b) ->
    let rec collect t =
      try let l,r = dest_binary "word_xor" t in collect l @ collect r
      with _ -> [t] in
    let compare_term a b =
      if term_order a b then 1
      else if term_order b a then -1
      else 0 in
    let sort_xor x =
      let leaves = collect x in
      let sorted = sort (fun a b -> compare_term a b < 0) leaves in
      if leaves = sorted then None else
      let op = try rator(rator x) with _ -> failwith "no xor" in
      let rebuilt = end_itlist (fun a b -> mk_comb(mk_comb(op, a), b)) sorted in
      Some (WORD_RULE(mk_eq(x, rebuilt))) in
    (match (try sort_xor a with _ -> None) with
     | Some th -> AP_THM (AP_TERM (rator(rator tm)) th) b
     | None ->
       (match (try sort_xor b with _ -> None) with
        | Some th -> AP_TERM (mk_comb(rator(rator tm), a)) th
        | None -> failwith "already sorted or no xor"))
  | _ -> failwith "not word_pmul";;

let DOUBLE_SUBWORD_JOIN = prove(
  `!(x:(128)word).
    word_subword (word_subword (word_join x x:(256)word) (64,128):(128)word) (0,64):(64)word =
    word_subword x (64,64)`,
  CONV_TAC WORD_BLAST);;
let DOUBLE_SUBWORD_JOIN_HI = prove(
  `!(x:(128)word).
    word_subword (word_subword (word_join x x:(256)word) (64,128):(128)word) (64,64):(64)word =
    word_subword x (0,64)`,
  CONV_TAC WORD_BLAST);;

(* ================================================================== *)
(*           NEW NAMED TACTICS — the GCM analog of XTS's tactics      *)
(* ================================================================== *)

(* GCM_POST_SIM_NORMALIZE_TAC : the bookkeeping that runs once after the
   last ARM step.  Folds away stack arithmetic, mask collapses, the
   key KAR_MID_BRIDGE rewrite, and post-simulation pmul-arg normalization.
   This is the GCM analog of XTS's "between simulation and closure"
   normalisation block. *)
let GCM_POST_SIM_NORMALIZE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_MASK; WORD_AND_MASK_SYM;
    WORD_AND_MASK_64; WORD_AND_MASK_SYM_64;
    WORD_XOR_ASSOC; GSYM Q9; GSYM Q30; GSYM Q31; DREG]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0; KAR_MID_BRIDGE]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV PMUL_NORM_CONV)) th
    with _ -> th);;

(* GCM_CT_STEP_TAC : closes the ciphertext subgoal of the 1-block proof.
   Assumes the proof has already abbreviated `ct` and `s13` for the AES
   chain.  (See the main proof body.) *)
let GCM_CT_STEP_TAC =
  EXPAND_TAC "ct" THEN EXPAND_TAC "s13" THEN
  REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
  ASM_REWRITE_TAC[];;


(* GCM_GHASH_STEP_TAC : closes the GHASH subgoal of the 1-block proof.
   Uses common-pattern abbreviations (no h-mappings) AND the 2-block-style
   final_xi inversion (avoids byte-level term explosion from REV64).
   1. Apply bridge lemma + standard normalization (subword/halfswap/PMUL_NORM).
   2. Invert the rev64 byte expansion via final_xi ABBREV (MATCH_MP_TAC + SYM).
   3. ABBREV the 4 atomic subwords common to both sides (uA0/uA1, uD0/uD1).
   4. ABBREV the 3 inner pmuls (p1, p2, p3).
   5. DOUBLE_SUBWORD_JOIN unfolding to collapse word_subword(word_join Y Y).
   6. ABBREV the 7 z-vars (subwords of pmul outputs and the small outer pmul).
   7. ASM_REWRITE to fold zD on the RHS.
   8. SUBGOAL_THEN equating two pmul forms via XOR-AC of args.
   9. ABBREV qBigP, qSmallP and their subword extractions.
  10. BINOP_TAC THENL [WORD_RULE; WORD_RULE]. *)
let GCM_GHASH_STEP_TAC =
  REWRITE_TAC[ghash_polyval_acc; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT th)]) THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN
    `word_xor xi (word_xor pt
       (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                         rk8 rk9 rk10 rk11 rk12 rk13 rk14)) =
     word_xor xi ct:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ct" THEN EXPAND_TAC "s13" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC];
    ALL_TAC
  ] THEN
  ASM_REWRITE_TAC[] THEN
  (* Invert the rev64 + halfswap byte-level expansion via final_xi.
     This is the key 2-block-style optimization for the LHS collapse. *)
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
  (* Common-pattern atomic abbreviations *)
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[karatsuba_mid] THEN
  ABBREV_TAC `(uA0:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ct)) (0,64)` THEN
  ABBREV_TAC `(uA1:(64)word) =
    word_subword (word_reversefields 8 (word_xor (xi:(128)word) ct)) (64,64)` THEN
  ABBREV_TAC `(uD0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(uD1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  (* 3 inner pmul abbreviations *)
  ABBREV_TAC `(p1:(128)word) = word_pmul (uA0:(64)word) (uD0:(64)word)` THEN
  ABBREV_TAC `(p2:(128)word) = word_pmul (uA1:(64)word) (uD1:(64)word)` THEN
  ABBREV_TAC `(p3:(128)word) =
    word_pmul (word_xor (uA0:(64)word) (uA1:(64)word))
              (word_xor (uD0:(64)word) (uD1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  (* 7 atomic subwords of pmul outputs *)
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
  (* Normalize the BIG pmul args (XOR-AC) *)
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
  (* ABBREV the outer pmul terms and their subword extractions *)
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
  (* Final closure *)
  BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE];;



(* ================================================================== *)
(*                         THE PROOF                                   *)
(* ================================================================== *)

let ONE_BLOCK_PRELOOP_TAIL_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) stackptr pc.
    aligned 16 stackptr /\
    nonoverlapping (word pc,448) (in_ptr:int64,16) /\
    nonoverlapping (word pc,448) (out_ptr:int64,16) /\
    nonoverlapping (word pc,448) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,448) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,448) (key_ptr:int64,240) /\
    nonoverlapping (word pc,448) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,448) (stackptr:int64,80) /\
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
    nonoverlapping (ivec_ptr,16) (word pc,448) /\
    nonoverlapping (xi_ptr,16) (word pc,448) /\
    nonoverlapping (out_ptr,16) (word pc,448)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) one_block_prelooptail_2_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word 128; out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt /\
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
           read PC s = word(pc + 444) /\
           read X0 s = word 16 /\
           read (memory :> bytes128 out_ptr) s = ct /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct]))
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
              fst ONE_BLOCK_PRELOOP_TAIL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue. *)
  ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-84: AES rounds, tail entry, mask, loads *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--84) THEN

  (* Abbreviate AES output *)
  ABBREV_TAC `ct = word_xor (word_xor pt (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese ivec rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13)) rk14:(128)word` THEN
  ABBREV_TAC `s13 = aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese ivec rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13:(128)word` THEN

  (* Steps 85-93: EOR that combines reversed xi and ct *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (85--93) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION;
    REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI;
    GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
    WORD_XOR_0; WORD_XOR_ASSOC]) THEN

  (* Steps 94-103: GHASH Karatsuba + reduction up to final EOR3 in Q19.
     Stop BEFORE the EXT/REV64 byte-level explosion of Q19. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (94--103) THEN

  (* Post-simulation normalization, lifted into a named tactic. *)
  GCM_POST_SIM_NORMALIZE_TAC THEN

  (* Abbreviate Q19 (the assembled Karatsuba+Barrett result) as `final_xi`
     BEFORE step 104's EXT + step 105's REV64 — avoids the byte-level term
     explosion AND lets the GHASH closure invert the rev64 via SUBST(SYM).
     This mirrors the 2-block proof's strategy. *)
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q19 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("final_xi",type_of rhs), rhs))
    else NO_TAC) THEN

  (* Steps 104-111: EXT, REV64, ST1, MOV, LDP*4, RET — now Q19 is opaque. *)
  ARM_STEPS_TAC ONE_BLOCK_PRELOOP_TAIL_EXEC (104--111) THEN

  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    GCM_CT_STEP_TAC;
    GCM_GHASH_STEP_TAC
  ]);;
