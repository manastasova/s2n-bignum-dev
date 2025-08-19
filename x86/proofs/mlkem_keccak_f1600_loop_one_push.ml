(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

 needs "x86/proofs/base.ml";;

(******************************************************************************
  Proving a mlkem_keccak_f1600 property about program 'mlkem_keccak_f1600.S'
******************************************************************************)

(* When there is no table *)
 (**** print_literal_from_elf "x86/mlkem/mlkem_keccak_f1600_loop_one_push.o";;
 ****)

let mlkem_keccak_f1600_mc_loop_one_push = define_assert_from_elf
  "mlkem_keccak_f1600_mc_loop_one_push" "x86/mlkem/mlkem_keccak_f1600_loop_one_push.o"         
[
  0x53;                    (* PUSH (% rbx) *)
  0x49; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Imm32 (word 0)) *)
  0x41; 0x50;              (* PUSH (% r8) *)
  0x41; 0x58;              (* POP (% r8) *)
  0x49; 0x83; 0xc0; 0x01;  (* ADD (% r8) (Imm8 (word 1)) *)
  0x49; 0x83; 0xf8; 0x18;  (* CMP (% r8) (Imm8 (word 24)) *)
  0x75; 0xf2;              (* JNE (Imm8 (word 242)) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

 let MLKEM_KECCAK_F1600_EXEC_loop_one_push = X86_MK_EXEC_RULE mlkem_keccak_f1600_mc_loop_one_push;;

  let MLKEM_KECCAK_F1600_SPEC = prove(
  `forall pc:num stackpointer:int64 returnaddress.
  nonoverlapping_modulo (2 EXP 64) (pc,0x18) (val (word_sub stackpointer (word 16)), 16)
      ==> ensures x86
  // Precondition
  (\s. bytes_loaded s (word pc) mlkem_keccak_f1600_mc_loop_one_push /\
       read RIP s = word pc /\
       read RSP s = stackpointer /\
       read (memory :> bytes64 stackpointer) s = returnaddress)
  // Postcondition
  (\s.  read RIP s = returnaddress /\
        read RSP s = word_add stackpointer (word 8))
  (MAYCHANGE [RIP;RSP;RAX;RBX;RCX;RDX;RBP;R8;R9;R10;R11;R12;R13;R14;R15;RDI;RSI] ,, MAYCHANGE SOME_FLAGS,, 
  MAYCHANGE [memory :> bytes (word_sub stackpointer (word 16), 16)])`
  ,

  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`pc:num`] THEN

  WORD_FORALL_OFFSET_TAC 16 THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REPEAT STRIP_TAC THEN

    ENSURES_WHILE_PAUP_TAC
    `0` (* loop_one_push begin number *)
    `24` (* loop_one_push end number *)
    `pc + 0x8` (* loop body start PC *)
    `pc + 0x14` (* loop backedge branch PC -- including the jmp *)
    `\i s. // loop invariant at the end of the iteration
           (read R8 s = word i /\
            read RSP s = word_add stackpointer (word 8) /\
            read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress) /\
           // loop backedge condition
           (read ZF s <=> i = 24)` THEN

    REPEAT CONJ_TAC THENL 
    [
      (* loop_one_push begin < loop_one_push end *)
      ARITH_TAC;

      (* entrance to the loop *)
      (* Let's use X86_SIM_TAC which is ENSURES_INIT_TAC + X86_STEPS_TAC +
        ENSURES_FINAL_STATE_TAC + some post-processing. *)
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_loop_one_push (1--2);

      (* the body of the loop *)
      REPEAT STRIP_TAC THEN
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_loop_one_push (1--4) THEN
      REPEAT CONJ_TAC THENL 
      [
        CONV_TAC WORD_RULE;

        REWRITE_TAC [WORD_BLAST `word_add x (word 18446744073709551593):int64 =
                             word_sub x (word 23)`] THEN

        REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
        REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN

        IMP_REWRITE_TAC[MOD_LT; ARITH_RULE`23 < 2 EXP 64`] THEN

        CONJ_TAC THENL 
        [ (* will create two arithmetic subgoals. *)
          UNDISCH_TAC `i < 24` 
          THEN ARITH_TAC;

          ARITH_TAC
        ]
      ];

      (* Prove that backedge is taken if i != 24. *)
      REPEAT STRIP_TAC THEN
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_loop_one_push [1];

      (* Loop exit to the end of the program *)
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_loop_one_push (1--3);
  ]);
