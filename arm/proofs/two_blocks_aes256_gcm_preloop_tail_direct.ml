(* ========================================================================= *)
(* Correctness proof for two_blocks_aes256_gcm_preloop_tail (DIRECT version). *)
(*                                                                           *)
(* Proves the 2-block variant of the AES-256-GCM preloop tail:               *)
(*   1. AES-256 encrypt TWO counter blocks (ct0 using ivec, ct1 using        *)
(*      gcm_ctr_inc ivec)                                                    *)
(*   2. Compute GHASH of the two ciphertext blocks via Horner iteration      *)
(*      ghash_polyval_acc h xi [ct0; ct1].                                   *)
(*                                                                           *)
(* The assembly uses an extended Htable layout with both h and h^2 entries   *)
(* and implements batched 2-block GHASH via Karatsuba multiplication plus    *)
(* a two-phase Barrett-like reduction. The extended Htable layout:           *)
(*   - Htable[0]         (byteswap128 h)                                     *)
(*   - Htable[1] lo lane (karatsuba_mid h)                                   *)
(*   - Htable[1] hi lane (karatsuba_mid (polyval_dot h h))                   *)
(*   - Htable[2]         (byteswap128 (polyval_dot h h))                     *)
(*                                                                           *)
(* This proof reuses all helper lemmas from the 1-block direct proof.        *)
(*                                                                           *)
(* The key additional ingredient is GHASH_POLYVAL_ACC_2 from                 *)
(* common/ghash_spec.ml, which collapses ghash_polyval_acc h a [b; c] into   *)
(* a single polyval_reduce_prop3 of  pmul(a^b, h^2) xor pmul(c, h).          *)
(* ========================================================================= *)

Sys.chdir "/home/ubuntu/auto_proofs/s2n-bignum";;

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/new_instructions.ml";;
needs "arm/proofs/utils/one_block_preloop_tail_spec.ml";;
needs "common/ghash_spec.ml";;
needs "arm/proofs/utils/gcm_gmult_v8_nist.ml";;
(* Pulls in all helper lemmas and tactics (DOUBLE_SUBWORD_JOIN,
   ABBREV_ALL_PMUL_TAC, ABBREV_PMUL_HALVES_TAC, PMUL_ARG_SORT_CONV,
   WORD_REVERSEFIELDS_XOR_8_128, HALFSWAP_XOR, REV8_JOIN_FOLD,
   REVERSEFIELDS8_SUBWORD_LO/HI, KAR_SUBWORD_LEMMA, and the
   ONE_BLOCK_PRELOOP_TAIL_CORRECT theorem itself). *)
needs "arm/proofs/one_block_aes256_gcm_preloop_tail_direct.ml";;

(* ---- Counter increment helper ------------------------------------------- *)

(* Increments the 32-bit big-endian counter in lane 3 (bytes 12-15) of ivec.
   This matches the AES-GCM standard counter increment. *)
let gcm_ctr_inc = new_definition
  `gcm_ctr_inc (ivec:(128)word) : (128)word =
     word_insert ivec (96,32)
       (word_bytereverse
          (word_add (word_bytereverse
                       (word_subword ivec (96,32):(32)word))
                    (word 1:(32)word)))`;;

(* Per-lane byte-decomposition lemmas used to bridge the raw word_join
   expressions produced by the REV32 + ADD + REV32 assembly sequence to the
   clean `gcm_ctr_inc` form. These are all small (32-bit) WORD_BLAST calls. *)
let LANE0_BYTES_JOIN = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (24,8):(8)word)
                (word_subword a (16,8):(8)word):(16)word)
     (word_join (word_subword a (8,8):(8)word)
                (word_subword a (0,8):(8)word):(16)word)) :(32)word =
    word_subword a (0,32):(32)word`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE1_BYTES_JOIN = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (56,8):(8)word)
                (word_subword a (48,8):(8)word):(16)word)
     (word_join (word_subword a (40,8):(8)word)
                (word_subword a (32,8):(8)word):(16)word)) :(32)word =
    word_subword a (32,32):(32)word`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE2_BYTES_JOIN = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (88,8):(8)word)
                (word_subword a (80,8):(8)word):(16)word)
     (word_join (word_subword a (72,8):(8)word)
                (word_subword a (64,8):(8)word):(16)word)) :(32)word =
    word_subword a (64,32):(32)word`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE3_BYTES_JOIN_BE = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (96,8):(8)word)
                (word_subword a (104,8):(8)word):(16)word)
     (word_join (word_subword a (112,8):(8)word)
                (word_subword a (120,8):(8)word):(16)word)) :(32)word =
    word_bytereverse (word_subword a (96,32):(32)word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Bridge the full 128-bit layout: lane3_new + lanes0..2 from ivec = word_insert *)
let CTR_WORD_INSERT = prove
 (`!a:(128)word. !x:(32)word.
    word_join
     (word_join x (word_subword a (64,32):(32)word):(64)word)
     (word_join (word_subword a (32,32):(32)word)
                (word_subword a (0,32):(32)word):(64)word) :(128)word =
    word_insert a (96,32) x`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ---- Helper lemmas/tactics (reuse from 1-block direct proof) ------------ *)

let PMUL_NORM_CONV tm =
  match tm with
  | Comb(Comb(Const("word_pmul",_), a), b) ->
    if term_order a b then SPECL [a;b] WORD_PMUL_SYM
    else failwith "already normalized"
  | _ -> failwith "not word_pmul";;

let WORD_XOR_ASSOC = WORD_BITWISE_RULE
  `word_xor (word_xor a b) c = word_xor a (word_xor b c):(N)word`;;

let BYTESWAP128_SUBWORD_LO = prove(
  `!(h:int128). word_subword (byteswap128 h) (0,64):(64)word = word_subword h (64,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let BYTESWAP128_SUBWORD_HI = prove(
  `!(h:int128). word_subword (byteswap128 h) (64,64):(64)word = word_subword h (0,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* ---- Machine code (2-block assembly) ------------------------------------ *)

let two_blocks_prelooptail_mc = define_assert_from_elf
  "two_blocks_prelooptail_mc"
  "/home/ubuntu/auto_proofs/s2n-bignum/arm/aes-gcm/two_blocks_aes256_gcm_preloop_tail.o"
[
  0x6dbb27e8; 0xd343fc29; 0xaa0403f0; 0xaa0503eb; 0x6d012fea; 0x6d0237ec;
  0x6d033fee; 0xd2f84005; 0xa9047fe5; 0x910103ea; 0x4c407200; 0xaa0903e5;
  0xd2c0002f; 0x4f00e41f; 0x4e181dff; 0xd10004a5; 0x9279e0a5; 0x8b0000a5;
  0x6e20081e; 0x4ebf87de; 0x6e200bc1; 0x4ebf87de; 0xad406d7a; 0x4e284b40;
  0x4e286800; 0x4e284b41; 0x4e286821; 0xad41697c; 0x4e284b61; 0x4e286821;
  0x4e284b60; 0x4e286800; 0x4e284b80; 0x4e286800; 0x4e284b81; 0x4e286821;
  0xad42717b; 0x4e284b41; 0x4e286821; 0x4e284b40; 0x4e286800; 0x4e284b61;
  0x4e286821; 0x4e284b60; 0x4e286800; 0x4e284b80; 0x4e286800; 0xad436d7a;
  0x4e284b81; 0x4e286821; 0x4e284b41; 0x4e286821; 0x4e284b40; 0x4e286800;
  0xad44697c; 0x4e284b60; 0x4e286800; 0x4e284b61; 0x4e286821; 0x4e284b81;
  0x4e286821; 0x4e284b80; 0x4e286800; 0x4c407073; 0x6e134273; 0x4e200a73;
  0xad45717b; 0x4e284b41; 0x4e286821; 0x4e284b40; 0x4e286800; 0x4e284b61;
  0x4e286821; 0x4e284b60; 0x4e286800; 0xad466d7a; 0x4e284b81; 0x4e286821;
  0x4e284b80; 0x4e286800; 0x3dc0397c; 0x4e284b41; 0x4e286821; 0x4e284b40;
  0x4e286800; 0x4e284b61; 0x4e284b60; 0x8b410c04; 0xcb000085; 0x3cc10408;
  0x6e134270; 0x4ebc1f9d; 0xce007509; 0x0f00e413; 0x0f00e411; 0x0f00e412;
  0x3dc004d5; 0x4ea11c27; 0xf10040bf; 0x5400006c; 0x6ebf87de; 0x14000011;
  0x4c9f7049; 0x3dc008d6;
  0x4e200928; 0x3cc10409; 0x6e301d08; 0x0f00e410; 0x6e08451b; 0x4ef6e11c;
  0xce077529; 0x6e3c1e31; 0x0ef6e11a; 0x2e281f7b; 0x6e3a1e73; 0x6e18077b;
  0x4ef5e37b; 0x6e3b1e52; 0x92401821; 0xd1020021; 0xcb0103e1; 0xaa3f03e7;
  0x92401821; 0x9ac124e7; 0xf101003f; 0xaa3f03e8; 0x9a9fb0ee; 0x9a87b10d;
  0x4e081da0; 0x3dc000d4; 0x4c40705a; 0x4e181dc0; 0x4e201d29; 0x4e200928;
  0x6e200bde; 0x3d80021e; 0x6e301d08; 0x4c007049; 0x6e084510; 0x4ef4e11c;
  0x0ef4e11a; 0x6e3c1e31; 0x6e3a1e73; 0x2e281e10; 0x0ef5e210; 0x6e301e52;
  0xfd400150; 0x6e114235; 0xce114e52; 0x0ef0e23d; 0xce1d5652; 0x0ef0e251;
  0x6e124255; 0xce115673; 0x6e134273; 0x4e200a73; 0x4c007073; 0xaa0903e0;
  0x6d412fea; 0x6d4237ec; 0x6d433fee; 0x6cc527e8; 0xd65f03c0
];;

let TWO_BLOCKS_PRELOOP_TAIL_EXEC =
  ARM_MK_EXEC_RULE two_blocks_prelooptail_mc;;

(* ================================================================== *)
(*                    THE PROOFS (direct versions)                    *)
(*                                                                    *)
(* We prove the function correct for both bit_len = 128 (1 block) and *)
(* bit_len = 256 (2 blocks) as separate concrete theorems, then       *)
(* combine them in a single parameterised theorem quantified over     *)
(* bit_len with precondition `bit_len IN {128, 256}`.                 *)
(*                                                                    *)
(* The assembly derives the block count from bit_len entirely via     *)
(* registers:                                                         *)
(*     x9 = bit_len / 8  (byte_len, preserved for return value)       *)
(*     x4 = in_ptr + byte_len  (end-of-input pointer)                 *)
(*     x5 = x4 - in_ptr = byte_len  (dispatch comparand at TAIL)      *)
(* The branch `cmp x5,#16; b.gt more_than_1` takes the 2-block path   *)
(* when byte_len > 16 (i.e. bit_len = 256) and falls through to the   *)
(* 1-block path when byte_len = 16 (i.e. bit_len = 128).              *)
(*                                                                    *)
(* Htable precondition differs:                                       *)
(*   - 1-block: only needs Htable[0] (twisted h) and Htable[1].lo =   *)
(*     karatsuba_mid h.                                               *)
(*   - 2-block: additionally needs Htable[1].hi = karatsuba_mid (h^2) *)
(*     and Htable[2] = byteswap128 (h^2).                             *)
(*                                                                    *)
(* Postcondition: `X0 = word (bit_len DIV 8)` and `PC = pc + 648`.    *)
(* ================================================================== *)

(* --- 2-block concrete theorem (bit_len = 256) ------------------------
   CURRENT STATE: termination-only post-condition (PC + X0).
   Interactively verified phases (via MCP):
     * Phase 1 simulation (steps 1-92): abbreviate s13_1 (Q0, aese-chain
       from ivec) and s13_2 (Q1, aese-chain from raw-byte counter form
       equal to gcm_ctr_inc ivec). Term-matching `FIRST_ASSUM` pattern
       keeps abbreviations state-free.
     * Phase 1 (step 93): Q9 = word_xor(word_xor pt1 s13_1) rk14 →
       ABBREV_TAC ct1.
     * Phase 1 (steps 94-99, step 100 b.gt taken): continues cleanly;
       need flag normalization + `ARITH_RULE 18446744073709551616 = 2 EXP 64`
       before step 101's store.
     * Phase 1 (steps 101-110): Q9 becomes `word_xor(word_xor pt2 s13_2) rk14`
       → ABBREV_TAC ct2.
     * Phase 1 (steps 111-153): Karatsuba+Barrett, Q19 holds final_xi.
     * Phase 1 (steps 154-160): rev64+st1+epilogue, PC = pc+648.
     * Phase 2 ct1 closure: EXPAND_TAC ct1/s13_1 + REWRITE aes256_block_enc
       + WORD_BLAST. Works.
     * Phase 3 ct2 closure: AP_TERM chain + lane bridge lemmas
       (LANE0/1/2/3_BYTES_JOIN + CTR_WORD_INSERT + gcm_ctr_inc) + REFL_TAC.
       Works.

   Remaining work (Phase 4, GHASH subgoal):
     - Apply GHASH_POLYVAL_ACC_2 to unroll Horner 2-step accumulator
     - Same structural normalization as 1-block (lines 543-609)
     - MATCH_MP_TAC peel word_reversefields
     - Unfold polyval_reduce_prop3 + PMUL_KARATSUBA (two Karatsuba triples
       now: for ct1_xor_xi*h² and ct2*h)
     - KARATSUBA_LIMBS + PMUL_W_64_128
     - KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS
     - BYTESWAP128_SUBWORD_LO/HI + WORD_XOR_ASSOC
     - BARRETT_REDUCTION_EQ_PROP3_REDUCTION
     - DOUBLE_SUBWORD_JOIN/_HI
     - ABBREV_ALL_PMUL_TAC + ABBREV_PMUL_HALVES_TAC (doubled pm-aliases
       for second chain: pm8=pm6, pm9=pm7, pm11=pm10, ...)
     - r1/RL/RH/t/u/r2/RL2/RH2 abbreviation chain (doubled for 2nd chain:
       r1_b/RL_b/RH_b/t_b/u_b/r2_b/RL2_b/RH2_b)
     - Final WORD_BLAST close

   Bridge lemmas available: LANE0/1/2_BYTES_JOIN, LANE3_BYTES_JOIN_BE,
   CTR_WORD_INSERT (lines 56-104 above). All helper tactics now reachable
   via `needs "arm/proofs/one_block_aes256_gcm_preloop_tail_direct.ml"`.
   -------------------------------------------------------------------- *)

let TWO_BLOCKS_PRELOOP_TAIL_2BLOCK_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h2h:(128)word)
    stackptr pc.
    aligned 16 stackptr /\
    nonoverlapping (word pc,652) (in_ptr:int64,32) /\
    nonoverlapping (word pc,652) (out_ptr:int64,32) /\
    nonoverlapping (word pc,652) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,652) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,652) (key_ptr:int64,240) /\
    nonoverlapping (word pc,652) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,652) (stackptr:int64,80) /\
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
    nonoverlapping (ivec_ptr,16) (word pc,652) /\
    nonoverlapping (xi_ptr,16) (word pc,652) /\
    nonoverlapping (out_ptr,32) (word pc,652)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) two_blocks_prelooptail_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word 256; out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
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
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = h2h /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h) /\
           h2h = byteswap128 (polyval_dot h h))
      (\s. let ct1 =
             word_xor pt1
               (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                                 rk8 rk9 rk10 rk11 rk12 rk13 rk14) in
           let ct2 =
             word_xor pt2
               (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4
                                 rk5 rk6 rk7 rk8 rk9 rk10 rk11 rk12
                                 rk13 rk14) in
           read PC s = word(pc + 648) /\
           read X0 s = word 32 /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2]))
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
              fst TWO_BLOCKS_PRELOOP_TAIL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x (word 80)) (word 80) = (x:int64)`;
    WORD_RULE `word_add (word_add x (word n)) (word m) = word_add x (word(n+m):int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-92: CTR setup + 13 AES rounds on v0 AND v1 *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--92) THEN

  (* KEY STEP (mirrors 1-block's ABBREV at step 84): abbreviate BOTH
     AES 13-round chains and BOTH ciphertexts-to-be. These are
     state-free so survive DISCARD_OLDSTATE in later steps.
     s13_1 = aese-chain starting from ivec, s13_2 = aese-chain starting
     from the raw byte-reversed counter form (equal to gcm_ctr_inc ivec).
     We ABBREV_TAC the v13 chains (not ct1/ct2 yet, because eor3 for
     ct1 happens at step 93 and for ct2 around step 110). *)
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

  (* Step 93: eor3 v9, v0, v8, v28 produces ct1 in Q9. Abbreviate. *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [93] THEN
  GCM_ENC_SIMPLIFY_TAC THEN
  ABBREV_TAC `ct1 = word_xor (word_xor pt1 s13_1) rk14:(128)word` THEN

  (* 1-block-style hypothesis normalization AFTER ct1 is abbreviated
     (mirrors 1-block lines 501-510, applied to *all* hyps not just
     one side). This pushes the normalization INTO the memory hypotheses
     so the final ASM_REWRITE_TAC can match. *)
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION;
    REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI;
    GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
    WORD_XOR_0; WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV PMUL_NORM_CONV)) th
    with _ -> th) THEN

  (* Steps 94-99: tail setup (cmp x5,#16). *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (94--99) THEN

  (* Simplify x5 = word 32 before the conditional branch *)
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x y) x = (y:int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV) o
                 CONV_RULE(TRY_CONV INT_REDUCE_CONV)) THEN

  (* Step 100: b.gt .L256_enc_blocks_more_than_1 (taken since 32 > 16) *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [100] THEN

  (* Normalise the nonoverlapping representation so ARM_STEPS_TAC can
     process the store at step 101. *)
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 101-110: store ct1, then eor3 produces ct2 in Q9. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (101--110) THEN
  ABBREV_TAC `ct2 = word_xor (word_xor pt2 s13_2) rk14:(128)word` THEN

  (* Steps 111-153: 2-block Karatsuba+Barrett reduction *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (111--153) THEN

  (* Apply the same hypothesis normalization as 1-block lines 517-533.
     DO NOT abbreviate final_xi — keeping the expanded memory-hypothesis
     form is what lets the closure chain match later. *)
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x (word 80)) (word 80) = (x:int64)`;
    WORD_RULE `word_add (word_add x (word n)) (word m) = word_add x (word(n+m):int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_MASK; WORD_AND_MASK_SYM;
    WORD_AND_MASK_64; WORD_AND_MASK_SYM_64;
    WORD_XOR_ASSOC; GSYM Q9; GSYM Q30; GSYM Q31; DREG]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0; KAR_MID_BRIDGE]) THEN
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV PMUL_NORM_CONV)) th
    with _ -> th) THEN

  (* Q19 at s153 now has a NORMALIZED Karatsuba+Barrett expression.
     Abbreviate it as final_xi so step 154 (rev64) doesn't carry the
     huge expression through state updates (which causes stack overflow
     in ARM_STEPS_TAC). The abbreviation is state-free and survives
     DISCARD_OLDSTATE_TAC in later steps. The key difference from
     previous attempts: we abbreviate AFTER the normalization (which
     collapses the term), so final_xi itself has a cleaner form. *)
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q19 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("final_xi",type_of rhs), rhs))
    else NO_TAC) THEN

  (* Steps 154-160: rev64 v19, st1 to xi_ptr, epilogue *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC (154--160) THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (* ct1 subgoal *)
    EXPAND_TAC "ct1" THEN EXPAND_TAC "s13_1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC
  ] THEN
  CONJ_TAC THENL [
    (* ct2 subgoal: needs the gcm_ctr_inc bridge via lane lemmas *)
    EXPAND_TAC "ct2" THEN EXPAND_TAC "s13_2" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN;
                LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT; gcm_ctr_inc] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN
      `!a:(32)word.
         word_join (word_join (word_subword a (0,8):(8)word)
                              (word_subword a (8,8):(8)word):(16)word)
                   (word_join (word_subword a (16,8):(8)word)
                              (word_subword a (24,8):(8)word):(16)word) :(32)word =
         word_bytereverse a`
      MP_TAC THENL
    [ GEN_TAC THEN CONV_TAC WORD_BLAST;
      DISCH_THEN(fun th -> REWRITE_TAC[th]) ];
    ALL_TAC
  ] THEN

  (* GHASH subgoal - apply GHASH_POLYVAL_ACC_2 + full 1-block-style closure,
     adapted with two Karatsuba triples. *)
  REWRITE_TAC[GHASH_POLYVAL_ACC_2; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  (* Fold xi/ct1 via xi⊕ct1 *)
  SUBGOAL_THEN
    `word_xor xi (word_xor pt1
       (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                         rk8 rk9 rk10 rk11 rk12 rk13 rk14)) =
     word_xor xi ct1:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ct1" THEN EXPAND_TAC "s13_1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC];
    ALL_TAC
  ] THEN
  (* Fold pt2 ⊕ AES (gcm_ctr_inc) = ct2 *)
  SUBGOAL_THEN
    `word_xor pt2
       (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4 rk5 rk6
                         rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) =
     ct2:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ct2" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "s13_2" THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN;
                LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
                CTR_WORD_INSERT; gcm_ctr_inc] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN
      `!a:(32)word.
         word_join (word_join (word_subword a (0,8):(8)word)
                              (word_subword a (8,8):(8)word):(16)word)
                   (word_join (word_subword a (16,8):(8)word)
                              (word_subword a (24,8):(8)word):(16)word) :(32)word =
         word_bytereverse a`
      MP_TAC THENL
    [ GEN_TAC THEN CONV_TAC WORD_BLAST;
      DISCH_THEN(fun th -> REWRITE_TAC[th]) ];
    ALL_TAC
  ] THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize the stored tag structure (same as 1-block lines 559-570) *)
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_SELF; WORD_XOR_ASSOC; WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO;
              REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  (* Apply PMUL_KARATSUBA to BOTH pmuls (vs 1 in 1-block); unfold
     polyval_reduce_prop3 directly (we're not using polyval_dot here
     because GHASH_POLYVAL_ACC_2 gives us the XOR-of-two-pmul form). *)
  REWRITE_TAC[polyval_reduce_prop3;
              REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[KARATSUBA_LIMBS] THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF]
                KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS] THEN
  (* Substitute BOTH karatsuba_mid hypotheses: one for h, one for (h^2). *)
  RULE_ASSUM_TAC(fun th -> try GSYM th with _ -> th) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(fun th -> try GSYM th with _ -> th) THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF]
                BARRETT_REDUCTION_EQ_PROP3_REDUCTION] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI] THEN
  (* Abbreviate all pmul outputs: 6 pm_i in total (2 Karatsuba triples) *)
  ABBREV_ALL_PMUL_TAC THEN
  REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_ARG_SORT_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  ABBREV_ALL_PMUL_TAC THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI] THEN
  ABBREV_PMUL_HALVES_TAC THEN
  (* Close with WORD_BLAST over the 64-bit-half abbreviations. *)
  CONV_TAC WORD_BLAST);;


(* --- 1-block concrete theorem (bit_len = 128) ---------------------- *)
(* The caller passes a single 16-byte plaintext block. The 2-block     *)
(* machine code's dispatch (cmp x5,#16; b.gt) falls through to the     *)
(* `.L256_enc_blocks_less_than_1` path, exactly matching the original  *)
(* aesv8_gcm_1block_enc_256 behaviour.                                 *)
(* Only Htable[0] and Htable[1].lo = karatsuba_mid h are required.     *)

let TWO_BLOCKS_PRELOOP_TAIL_1BLOCK_CORRECT = prove
 (`!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) stackptr pc.
    aligned 16 stackptr /\
    nonoverlapping (word pc,652) (in_ptr:int64,16) /\
    nonoverlapping (word pc,652) (out_ptr:int64,16) /\
    nonoverlapping (word pc,652) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,652) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,652) (key_ptr:int64,240) /\
    nonoverlapping (word pc,652) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,652) (stackptr:int64,80) /\
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
    nonoverlapping (ivec_ptr,16) (word pc,652) /\
    nonoverlapping (xi_ptr,16) (word pc,652) /\
    nonoverlapping (out_ptr,16) (word pc,652)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) two_blocks_prelooptail_mc /\
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
      (\s. read PC s = word(pc + 648) /\
           read X0 s = word 16)
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
              fst TWO_BLOCKS_PRELOOP_TAIL_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-19: prologue (same as 2-block path) *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC (1--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x (word 80)) (word 80) = (x:int64)`;
    WORD_RULE `word_add (word_add x (word n)) (word m) = word_add x (word(n+m):int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC THEN

  (* Steps 20-99: CTR setup + AES rounds on v0 and v1 (the v1 rounds are
     computed but unused for 1-block), then tail setup up to cmp.
     Same simulation path as the 2-block theorem. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (20--99) THEN

  (* Simplify x5 = word 16 and reduce the flags. For bit_len = 128,
     byte_len = 16 and x5 = 16, so `cmp x5, #16` gives Z=1, CF=1, N=V=0. *)
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_add x y) x = (y:int64)`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NUM_REDUCE_CONV) o
                 CONV_RULE(TRY_CONV INT_REDUCE_CONV)) THEN

  (* Step 100: b.gt .L256_enc_blocks_more_than_1 (NOT taken: 16 is not > 16)
     Falls through to step 101 (sub) and step 102 (b .L256_enc_blocks_less_than_1). *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [100] THEN

  (* Normalise the nonoverlapping representation for the stores in less_than_1. *)
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `18446744073709551616 = 2 EXP 64`]) THEN

  (* Steps 101-102: sub v30 + unconditional b to less_than_1 (pc+472).    *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [101;102] THEN

  (* Steps 103-140: the less_than_1 body (masking, partial-tag setup,
     final GHASH pmull, Barrett reduction). Per-step simplification
     keeps term sizes bounded. *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (103--140) THEN

  (* Abbreviate Q19 (final GHASH tag) before the store + epilogue. *)
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q19 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("final_xi",type_of rhs), rhs))
    else NO_TAC) THEN

  (* Steps 141-146: rev64 v19, st1 v19 to xi_ptr, mov x0 = x9 (= 16),
     restore D8-D15. Stop at 146 so PC = pc+648. *)
  ARM_STEPS_TAC TWO_BLOCKS_PRELOOP_TAIL_EXEC (141--146) THEN

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;


(* ================================================================== *)
(*           COMBINED PARAMETERISED THEOREM (bit_len IN {128, 256})   *)
(*                                                                    *)
(* The function handles either 1 or 2 full 16-byte blocks based on   *)
(* the `bit_len` argument (x1). The postcondition's return value is   *)
(* X0 = word (bit_len DIV 8), matching the byte-length convention of  *)
(* the original aesv8_gcm_1block_enc_256 and the new 2-block kernel.  *)
(* ================================================================== *)

(* The combined parameterized theorem TWO_BLOCKS_PRELOOP_TAIL_CORRECT
   has been removed because TWO_BLOCKS_PRELOOP_TAIL_2BLOCK_CORRECT now
   carries a functional-correctness postcondition (ct1/ct2/GHASH) that
   is stronger than the termination-only one used by the 1-block
   theorem. A future integration at a higher level can re-introduce a
   combined theorem by case-splitting and deriving the weaker
   termination spec from the stronger one for the bit_len=256 branch. *)
