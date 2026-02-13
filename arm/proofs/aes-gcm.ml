(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compiler-generated "naive" Keccak-f1600 code not using lazy rotations.    *)
(* ========================================================================= *)
Sys.chdir "/home/ubuntu/s2n-bignum";;
needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/ghash_spec.ml";;

(**** print_literal_from_elf "arm/sha3/aes-gcm.o";;
 ****)

let aes-gcm_mc = define_assert_from_elf
  "aes-gcm_mc" "arm/sha3/aes-gcm.o"
[
 
];;

let AES-GCM_EXEC = ARM_MK_EXEC_RULE aes-gcm_mc;;

(* ------------------------------------------------------------------------- *)
(* Additional tactic used in proof.                                          *)
(* ------------------------------------------------------------------------- *)

(*** Introduce ghost variables for the state reads in a list ***)

let GHOST_STATELIST_TAC =
  W(fun (asl,w) ->
        let regreads = dest_list(find_term is_list w) in
        let ghostvars = make_args "Ai_" [] (map type_of regreads) in
        EVERY(map2 GHOST_INTRO_TAC ghostvars (map rator regreads)));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, for whole subroutine without separate core.            *)
(* ------------------------------------------------------------------------- *)

let AES-GCM_SUBROUTINE_CORRECT = prove
 (`!a rc A pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 208),208))
            [(word pc,0x3d0); (a,200); (rc,192)] /\
        nonoverlapping (a,200) (word pc,0x3d0)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) aes-gcm_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; rc] s /\
                  wordlist_from_memory(a,25) s = A /\
                  wordlist_from_memory(rc,24) s = round_constants)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200);
                memory :> bytes (word_sub stackpointer (word 208),208)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `rc:int64`; `A:int64 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 208 THEN X_GEN_TAC `stackpointer:int64` THEN
  STRIP_TAC THEN

  REWRITE_TAC[fst AES-GCM_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Register saves - we include this since they are mixed up in the
   *** main code by the compiler; this does mean we then need to state
   *** this in our loop invariant, and it means we don't follow the
   *** usual methodology of separating the core from the save/restore.
   ***)

  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN

  (*** Set up the loop invariant ***)

  ENSURES_WHILE_PUP_TAC `24` `pc + 0xc0` `pc + 0x334`
   `\i s.
    (read SP s = stackpointer /\
     read (memory :> bytes64(word_add stackpointer (word 8))) s =
     returnaddress /\
     wordlist_from_memory(rc,24) s = round_constants /\
     read (memory :> bytes64 stackpointer) s = x29_init /\
     read (memory :> bytes64(word_add stackpointer (word 16))) s = x19_init /\
     read (memory :> bytes64(word_add stackpointer (word 24))) s = x20_init /\
     read (memory :> bytes64(word_add stackpointer (word 32))) s = x21_init /\
     read (memory :> bytes64(word_add stackpointer (word 40))) s = x22_init /\
     read (memory :> bytes64(word_add stackpointer (word 48))) s = x23_init /\
     read (memory :> bytes64(word_add stackpointer (word 56))) s = x24_init /\
     read (memory :> bytes64(word_add stackpointer (word 64))) s = x25_init /\
     read (memory :> bytes64(word_add stackpointer (word 72))) s = x26_init /\
     read (memory :> bytes64(word_add stackpointer (word 80))) s = x27_init /\
     read (memory :> bytes64(word_add stackpointer (word 88))) s = x28_init /\
     read (memory :> bytes64(word_add stackpointer (word 144))) s = word i /\
     read (memory :> bytes64(word_add stackpointer (word 200))) s = a /\
     read (memory :> bytes64(word_add stackpointer (word 192))) s = rc /\
     [read (memory :> bytes64 (word_add stackpointer (word 112))) s;
      read (memory :> bytes64 (word_add stackpointer (word 152))) s;
      read (memory :> bytes64 (word_add stackpointer (word 160))) s;
      read (memory :> bytes64 (word_add stackpointer (word 136))) s;
      read (memory :> bytes64 (word_add stackpointer (word 120))) s;
      read (memory :> bytes64 (word_add stackpointer (word 168))) s;
      read X8 s;
      read X16 s;
      read (memory :> bytes64 (word_add stackpointer (word 128))) s;
      read X28 s;
      read X15 s;
      read X25 s;
      read X5 s;
      read X23 s;
      read X19 s;
      read X26 s;
      read X3 s;
      read X30 s;
      read X6 s;
      read X24 s;
      read X2 s;
      read X9 s;
      read X4 s;
      read X27 s;
      read X7 s] =
     keccak i A) /\
   (read ZF s <=> i = 24)` THEN
  REWRITE_TAC[condition_semantics] THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 25)) s0` THEN
    FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC AES-GCM_EXEC (1--48) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[keccak];

    (*** Preservation of the invariant including end condition code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    GHOST_STATELIST_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes64(word_add rc (word(8 * i)))) s0 =
      EL i round_constants`
    ASSUME_TAC THENL
     [UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ARM_STEPS_TAC AES-GCM_EXEC (1--157) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)] THEN
    REWRITE_TAC[keccak] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[keccak_round] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN BITBLAST_TAC;

    (*** The trivial loop-back goal ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ARM_SIM_TAC AES-GCM_EXEC [1] THEN
    VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_SIMP_TAC[LT_IMP_NE];

    (*** The writeback tail ***)

    REWRITE_TAC[DREG_EXPAND_CLAUSES; READ_ZEROTOP_64] THEN
    GHOST_STATELIST_TAC THEN
    ARM_SIM_TAC AES-GCM_EXEC (1--39) THEN
    CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "aes-gcm" subroutine_signatures)
    AES-GCM_SUBROUTINE_CORRECT
    AES-GCM_EXEC;;

let AES-GCM_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a rc pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 208),208))
           [word pc,976; a,200; rc,192] /\
           nonoverlapping (a,200) (word pc,976)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    aes-gcm_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; rc] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 =
                        f_events rc a pc (word_sub stackpointer (word 208))
                        returnaddress /\
                        memaccess_inbounds e2
                        [a,200; rc,192; a,200;
                         word_sub stackpointer (word 208),208]
                        [a,200; word_sub stackpointer (word 208),208])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars AES-GCM_EXEC);;
