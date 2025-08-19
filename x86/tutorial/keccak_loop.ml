(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Prove a property of a simple program that has a loop.
******************************************************************************)

needs "x86/proofs/base.ml";;

(**** print_coda_from_elf (-1) "x86/tutorial/keccak_loop.o";;
 ****)
 
let keccak_loop_mc_I,keccak_loop_data_I =
  define_coda_literal_from_elf
  "keccak_loop_mc_I" "keccak_loop_data_I"
  "x86/tutorial/keccak_loop.o"
  [
    0x4c; 0x8d; 0x3d; 0x39; 0x01; 0x00; 0x00;
                             (* LEA (% r15) (Riprel (word 313)) *)
    0x4d; 0x8d; 0x7f; 0x08;  (* LEA (% r15) (%% (r15,8)) *)
    0x49; 0xf7; 0xc7; 0xff; 0x00; 0x00; 0x00;
                             (* TEST (% r15) (Imm32 (word 255)) *)
    0x75; 0xf3;              (* JNE (Imm8 (word 243)) *)
    0xc3;                    (* RET *)
    0xe9; 0xe6; 0x00; 0x00; 0x00
                             (* JMP (Imm32 (word 230)) *)
  ]
  [102; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31; 132; 0; 0;
   0; 0; 0; 102; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31;
   132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46;
   15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102;
   102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31; 132; 0; 0; 0; 0;
   0; 102; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31; 132; 0;
   0; 0; 0; 0; 102; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31;
   132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46;
   15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102;
   102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31; 132; 0; 0; 0; 0;
   0; 102; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 102; 102; 46; 15; 31; 132; 0;
   0; 0; 0; 0; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 130; 128; 0; 0; 0; 0; 0; 0; 138; 128;
   0; 0; 0; 0; 0; 128; 0; 128; 0; 128; 0; 0; 0; 128; 139; 128; 0; 0; 0; 0; 0;
   0; 1; 0; 0; 128; 0; 0; 0; 0; 129; 128; 0; 128; 0; 0; 0; 128; 9; 128; 0; 0;
   0; 0; 0; 128; 138; 0; 0; 0; 0; 0; 0; 0; 136; 0; 0; 0; 0; 0; 0; 0; 9; 128; 0;
   128; 0; 0; 0; 0; 10; 0; 0; 128; 0; 0; 0; 0; 139; 128; 0; 128; 0; 0; 0; 0;
   139; 0; 0; 0; 0; 0; 0; 128; 137; 128; 0; 0; 0; 0; 0; 128; 3; 128; 0; 0; 0;
   0; 0; 128; 2; 128; 0; 0; 0; 0; 0; 128; 128; 0; 0; 0; 0; 0; 0; 128; 10; 128;
   0; 0; 0; 0; 0; 0; 10; 0; 0; 128; 0; 0; 0; 128; 129; 128; 0; 128; 0; 0; 0;
   128; 128; 128; 0; 0; 0; 0; 0; 128; 1; 0; 0; 128; 0; 0; 0; 0; 8; 128; 0; 128;
   0; 0; 0; 128];;
  

let EXEC = X86_MK_EXEC_RULE keccak_loop_mc_I;;

let keccak_loop_SPEC = prove(
  `forall pc stackpointer table_addr.
  ensures x86
    // Precondition
    (\s. bytes_loaded s (word pc) keccak_loop_mc_I /\
         read RIP s = word pc /\
         read RIP s = word_add table_addr (word 0x139)/\
         read RSP s = stackpointer)
    // Postcondition
    (\s. read RIP s = word (pc+26))
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [RSP;RIP;R15] ,, MAYCHANGE SOME_FLAGS)`,,
  (* Unfold flag registers! *)
  REWRITE_TAC[SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN

  (* ENSURES_WHILE_PAUP_TAC is one of several tactics for declaring a hoare triple of a loop.
     PAUP means:
     - "P": The loop ends with a flag-setting instruction such as 'cmp' or 'add'.
            'read ZF s <=> i = 10' in the below statement relates the flag with
            the loop counter.
     - "A": The loop counter starts from variable 'a', In this tactic, this is 0.
            Actually, when a = 0, you can also use ENSURES_WHILE_PUP_TAC.
     - "UP": The counter goes up. *)
  ENSURES_WHILE_PAUP_TAC
    `table_addr` (* counter begin number *)
    `table_addr + 0xff` (* counter end number *)
    `pc + 0x7` (* loop body start PC *)
    `pc + 0x12` (* loop backedge branch PC *)
    `\i s. // loop invariant at the end of the loop
           (read R15 s = word_add (word_add (word pc) (word 0x139)) (word 256) /\
            read RSP s = stackpointer) /\
           // loop backedge condition
           (read ZF s <=> table_addr = pc + (word 0x139) + (word 256))` THEN
  REPEAT CONJ_TAC THENL [
    (* counter begin < counter end *)
    ARITH_TAC;

    (* entrance to the loop *)
    (* Let's use X86_SIM_TAC which is ENSURES_INIT_TAC + X86_STEPS_TAC +
       ENSURES_FINAL_STATE_TAC + some post-processing. *)
    X86_SIM_TAC EXEC (1--2) THEN
    CONV_TAC WORD_RULE;

    (* The loop body. let's prove this later. *)
    (* If you are interactively exploring this proof, try `r 1;;`. *)
    ALL_TAC;

    (* Prove that backedge is taken if i != 10. *)
    REPEAT STRIP_TAC THEN
    X86_SIM_TAC EXEC [1];

    (* Loop exit to the end of the program *)
    X86_SIM_TAC EXEC (1--2) THEN
    (* word (10*2) = word 20 *)
    CONV_TAC WORD_RULE
  ] THEN

  (* The loop body *)
  REPEAT STRIP_TAC THEN
  X86_SIM_TAC EXEC (1--3) THEN
  REPEAT CONJ_TAC THENL [
    (* `word_add (word i) (word 1) = word (i + 1)` *)
    CONV_TAC WORD_RULE;

    (* `word_add (word (i * 2)) (word 2) = word ((i + 1) * 2)` *)
    CONV_TAC WORD_RULE;

    (* `val (word_add (word i) (word 18446744073709551607)) = 0 <=> i + 1 = 10` *)
    (* This goal is slightly complicated to prove using automatic solvers.
       Let's manually attack this. *)
    (* Yes, we also have 'WORD_BLAST' that works like bit-blasting. *)
    REWRITE_TAC [WORD_BLAST `word_add x (word 18446744073709551607):int64 =
                             word_sub x (word 9)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
    (* Rewrite all '_ MOD 2 EXP 64' to '_' because they are known to be less
       than 2 EXP 64. *)
    IMP_REWRITE_TAC[MOD_LT; ARITH_RULE`9 < 2 EXP 64`] THEN
    CONJ_TAC THENL [ (* will create two arithmetic subgoals. *)
      UNDISCH_TAC `i < 10` THEN ARITH_TAC;
      ARITH_TAC
    ]
  ]);;
