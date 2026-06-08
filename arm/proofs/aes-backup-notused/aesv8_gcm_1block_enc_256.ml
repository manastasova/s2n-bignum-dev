(* ========================================================================= *)
(* Correctness proof for aesv8_gcm_1block_enc_256                            *)
(* AES-256-GCM single-block encrypt + GHASH (eor3 version)                  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/aes.ml";;
needs "arm/proofs/utils/gcm_gmult_v8_spec.ml";;
needs "arm/proofs/utils/aesv8_gcm_1block_enc_256_spec.ml";;

(* Machine code: 72 instructions, 288 bytes. Uses eor3 (SHA3 extension). *)

let aesv8_gcm_1block_enc_256_mc = define_assert_from_elf
  "aesv8_gcm_1block_enc_256_mc"
  "/home/ubuntu/auto_proofs/s2n-bignum/arm/aes-gcm/aesv8_gcm_1block_enc_256.o"
[
  0x3dc00080;       (* ldr q0, [x4] *)
  0xad406cba;       (* ldp q26, q27, [x5] *)
  0x4e284b40;       (* aese v0.16b, v26.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0x4e284b60;       (* aese v0.16b, v27.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0xad416cba;       (* ldp q26, q27, [x5, #32] *)
  0x4e284b40;       (* aese v0.16b, v26.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0x4e284b60;       (* aese v0.16b, v27.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0xad426cba;       (* ldp q26, q27, [x5, #64] *)
  0x4e284b40;       (* aese v0.16b, v26.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0x4e284b60;       (* aese v0.16b, v27.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0xad436cba;       (* ldp q26, q27, [x5, #96] *)
  0x4e284b40;       (* aese v0.16b, v26.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0x4e284b60;       (* aese v0.16b, v27.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0xad446cba;       (* ldp q26, q27, [x5, #128] *)
  0x4e284b40;       (* aese v0.16b, v26.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0x4e284b60;       (* aese v0.16b, v27.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0xad456cba;       (* ldp q26, q27, [x5, #160] *)
  0x4e284b40;       (* aese v0.16b, v26.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0x4e284b60;       (* aese v0.16b, v27.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0xad466cba;       (* ldp q26, q27, [x5, #192] *)
  0x4e284b40;       (* aese v0.16b, v26.16b *)
  0x4e286800;       (* aesmc v0.16b, v0.16b *)
  0x4e284b60;       (* aese v0.16b, v27.16b *)
  0x3dc038bc;       (* ldr q28, [x5, #224] *)
  0x3dc00008;       (* ldr q8, [x0] *)
  0xce007108;       (* eor3 v8.16b, v8.16b, v0.16b, v28.16b *)
  0x3d800048;       (* str q8, [x2] *)
  0xb9400c8a;       (* ldr w10, [x4, #12] *)
  0x5ac0094a;       (* rev w10, w10 *)
  0x1100054a;       (* add w10, w10, #0x1 *)
  0x5ac0094a;       (* rev w10, w10 *)
  0xb9000c8a;       (* str w10, [x4, #12] *)
  0x3dc00073;       (* ldr q19, [x3] *)
  0x6e134273;       (* ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200a73;       (* rev64 v19.16b, v19.16b *)
  0x4e200900;       (* rev64 v0.16b, v8.16b *)
  0x6e134273;       (* ext v19.16b, v19.16b, v19.16b, #8 *)
  0x6e331c00;       (* eor v0.16b, v0.16b, v19.16b *)
  0x3dc000d4;       (* ldr q20, [x6] *)
  0x3dc004d5;       (* ldr q21, [x6, #16] *)
  0x6e084410;       (* mov v16.d[0], v0.d[1] *)
  0x4ef4e011;       (* pmull2 v17.1q, v0.2d, v20.2d *)
  0x0ef4e013;       (* pmull v19.1q, v0.1d, v20.1d *)
  0x2e201e10;       (* eor v16.8b, v16.8b, v0.8b *)
  0x0ef5e210;       (* pmull v16.1q, v16.1d, v21.1d *)
  0x4eb01e12;       (* mov v18.16b, v16.16b *)
  0xd2f8400a;       (* mov x10, #0xc200000000000000 *)
  0x4e081d50;       (* mov v16.d[0], x10 *)
  0x6e114235;       (* ext v21.16b, v17.16b, v17.16b, #8 *)
  0xce114e52;       (* eor3 v18.16b, v18.16b, v17.16b, v19.16b *)
  0x0ef0e23d;       (* pmull v29.1q, v17.1d, v16.1d *)
  0xce1d5652;       (* eor3 v18.16b, v18.16b, v29.16b, v21.16b *)
  0x0ef0e251;       (* pmull v17.1q, v18.1d, v16.1d *)
  0x6e124255;       (* ext v21.16b, v18.16b, v18.16b, #8 *)
  0xce115673;       (* eor3 v19.16b, v19.16b, v17.16b, v21.16b *)
  0x6e134273;       (* ext v19.16b, v19.16b, v19.16b, #8 *)
  0x4e200a73;       (* rev64 v19.16b, v19.16b *)
  0xd343fc20;       (* lsr x0, x1, #3 *)
  0x3d800073;       (* str q19, [x3] *)
  0xd65f03c0        (* ret *)
];;

let AESV8_GCM_1BLOCK_ENC_256_EXEC =
  ARM_MK_EXEC_RULE aesv8_gcm_1block_enc_256_mc;;

(* Per-step simplification tactic.
   Uses FIRST_X_ASSUM to only touch the most recent int128 register hypothesis,
   preserving other SIMD register hypotheses (especially Q19 for GHASH).
   This follows the pattern from mlkem_basemul_k4.ml's SIMD_SIMPLIFY_TAC. *)
let GCM_ENC_SIMPLIFY_TAC =
  let simdable = can (term_match [] `read X (s:armstate):int128 = whatever`) in
  TRY(FIRST_X_ASSUM
   ((fun th ->
     let th' = REWRITE_RULE(SIMD_SIMPLIFY_RULES @
       [WORD_SWAP_HALVES_INVOLUTION]) th in
     let th'' = try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th'
                with _ -> th' in
     ASSUME_TAC th'') o
   check (simdable o concl)));;

(* Lemmas for matching word_insert from INS to word_join in spec *)
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

(* ORR with itself = identity (from mov v18, v16 = orr v18, v16, v16) *)
let WORD_OR_SELF = WORD_BITWISE_RULE `word_or x x = (x:(N)word)`;;

let KAR_SUBWORD_LEMMA = prove(
  `!(xi_rev:(128)word).
    word_subword
      (word_xor xi_rev
        (word_subword (word_join xi_rev xi_rev:(256)word) (64,128)))
      (0,64):(64)word =
    word_xor (word_subword xi_rev (0,64):(64)word)
             (word_subword xi_rev (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

(* ----------------------------------------------------------------------- *)
(* Main correctness theorem: EXEC_CORRECT                                   *)
(* 71 instructions simulated (all except ret).                              *)
(* Postcondition: CT output matches eor3 term,                              *)
(*   Xi output matches gcm_gmult_spec applied to (ct XOR xi).              *)
(* ----------------------------------------------------------------------- *)

let AESV8_GCM_1BLOCK_ENC_256_EXEC_CORRECT = prove
 (`!in_ptr bit_len out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (hhl:(128)word) pc.
    nonoverlapping (word pc,288) (in_ptr:int64,16) /\
    nonoverlapping (word pc,288) (out_ptr:int64,16) /\
    nonoverlapping (word pc,288) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,288) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,288) (key_ptr:int64,240) /\
    nonoverlapping (word pc,288) (htable_ptr:int64,32) /\
    nonoverlapping (in_ptr,16) (out_ptr,16) /\
    nonoverlapping (in_ptr,16) (xi_ptr,16) /\
    nonoverlapping (in_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,16) (xi_ptr,16) /\
    nonoverlapping (out_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,16) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,32) (out_ptr,16) /\
    nonoverlapping (htable_ptr,32) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,32) (ivec_ptr,16)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_1block_enc_256_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; bit_len; out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
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
           read (memory :> bytes128 htable_ptr) s = h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = hhl /\
           read (memory :> bytes128 xi_ptr) s = xi)
      (\s. read PC s = word(pc + 284) /\
           read (memory :> bytes128 out_ptr) s =
             word_xor (word_xor pt
               (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
               (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
               (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese ivec
               rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9))
               rk10)) rk11)) rk12)) rk13)) rk14 /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_gmult_spec
               (word_xor
                 (word_xor (word_xor pt
                   (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
                   (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
                   (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
                   ivec rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7))
                   rk8)) rk9)) rk10)) rk11)) rk12)) rk13)) rk14)
                 xi) h hhl)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,16);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)])`,

  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              NONOVERLAPPING_CLAUSES; SOME_FLAGS;
              fst AESV8_GCM_1BLOCK_ENC_256_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_INIT_TAC "s0" THEN

  (* Steps 1-55: normal simulation with SIMD simplification *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AESV8_GCM_1BLOCK_ENC_256_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (1--55) THEN

  (* Abbreviate Q19 (GHASH acc_l from PMULL) and Q17 (acc_h) values.
     The abbreviations are state-free so they survive DISCARD_OLDSTATE_TAC.
     Keep the original register hypotheses for the simulator. *)
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q19 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("ghash_acc_l",type_of rhs), rhs))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q17 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("ghash_acc_h",type_of rhs), rhs))
    else NO_TAC) THEN

  (* Steps 56-62: continue normal simulation *)
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AESV8_GCM_1BLOCK_ENC_256_EXEC [n] THEN
    GCM_ENC_SIMPLIFY_TAC) (56--62) THEN

  (* Steps 63-71: verbose steps (no DISCARD_OLDSTATE) to preserve Q19.
     CLARIFY_TAC propagates register values. GCM_ENC_SIMPLIFY_TAC
     keeps SIMD terms manageable. The abbreviations keep terms small. *)
  MAP_EVERY (fun n ->
    let s = "s" ^ string_of_int n in
    ARM_VERBOSE_STEP_TAC AESV8_GCM_1BLOCK_ENC_256_EXEC s THEN
    CLARIFY_TAC THEN GCM_ENC_SIMPLIFY_TAC) (63--71) THEN

  (* Expand abbreviations back to full expressions *)
  MAP_EVERY EXPAND_TAC ["ghash_acc_l"; "ghash_acc_h"] THEN

  (* Normalize all hypotheses *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th) THEN
  (* Right-associate all XOR in hypotheses *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_ASSOC]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Expand gcm_gmult_spec and normalize *)
  REWRITE_TAC[gcm_gmult_spec; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_SELF; WORD_XOR_ASSOC; WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  ASM_REWRITE_TAC[]);;

(* ----------------------------------------------------------------------- *)
(* Subroutine correctness wrapper                                           *)
(* ----------------------------------------------------------------------- *)

let AESV8_GCM_1BLOCK_ENC_256_SUBROUTINE_CORRECT = prove
 (`!in_ptr bit_len out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (hhl:(128)word) pc returnaddress.
    nonoverlapping (word pc,288) (in_ptr:int64,16) /\
    nonoverlapping (word pc,288) (out_ptr:int64,16) /\
    nonoverlapping (word pc,288) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,288) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,288) (key_ptr:int64,240) /\
    nonoverlapping (word pc,288) (htable_ptr:int64,32) /\
    nonoverlapping (in_ptr,16) (out_ptr,16) /\
    nonoverlapping (in_ptr,16) (xi_ptr,16) /\
    nonoverlapping (in_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,16) (xi_ptr,16) /\
    nonoverlapping (out_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,16) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,32) (out_ptr,16) /\
    nonoverlapping (htable_ptr,32) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,32) (ivec_ptr,16)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_1block_enc_256_mc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [in_ptr; bit_len; out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
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
           read (memory :> bytes128 htable_ptr) s = h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = hhl /\
           read (memory :> bytes128 xi_ptr) s = xi)
      (\s. read PC s = returnaddress /\
           read (memory :> bytes128 out_ptr) s =
             word_xor (word_xor pt
               (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
               (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
               (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese ivec
               rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9))
               rk10)) rk11)) rk12)) rk13)) rk14 /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_gmult_spec
               (word_xor
                 (word_xor (word_xor pt
                   (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
                   (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
                   (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
                   ivec rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7))
                   rk8)) rk9)) rk10)) rk11)) rk12)) rk13)) rk14)
                 xi) h hhl)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,16);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    AESV8_GCM_1BLOCK_ENC_256_EXEC
    AESV8_GCM_1BLOCK_ENC_256_EXEC_CORRECT);;
