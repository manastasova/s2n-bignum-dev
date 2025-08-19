(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

 needs "x86/proofs/base.ml";;

(******************************************************************************
  Proving a mlkem_keccak_f1600 property about program 'mlkem_keccak_f1600.S'
******************************************************************************)

(* When there is no table *)
 (**** print_literal_from_elf "x86/mlkem/mlkem_keccak_f1600_loop_body.o";;
 ****)

let mlkem_keccak_f1600_mc_loop_body = define_assert_from_elf
  "mlkem_keccak_f1600_mc_loop_body" "x86/mlkem/mlkem_keccak_f1600_loop_body.o"         
[
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x49; 0x89; 0xf7;        (* MOV (% r15) (% rsi) *)
  0x48; 0x8d; 0x7f; 0x64;  (* LEA (% rdi) (%% (rdi,100)) *)
  0x48; 0x81; 0xec; 0xc8; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 200)) *)
  0x48; 0xf7; 0x57; 0xa4;  (* NOT (Memop Quadword (%% (rdi,18446744073709551524))) *)
  0x48; 0xf7; 0x57; 0xac;  (* NOT (Memop Quadword (%% (rdi,18446744073709551532))) *)
  0x48; 0xf7; 0x57; 0xdc;  (* NOT (Memop Quadword (%% (rdi,18446744073709551580))) *)
  0x48; 0xf7; 0x57; 0xfc;  (* NOT (Memop Quadword (%% (rdi,18446744073709551612))) *)
  0x48; 0xf7; 0x57; 0x24;  (* NOT (Memop Quadword (%% (rdi,36))) *)
  0x48; 0xf7; 0x57; 0x3c;  (* NOT (Memop Quadword (%% (rdi,60))) *)
  0x48; 0x8d; 0x74; 0x24; 0x64;
                           (* LEA (% rsi) (%% (rsp,100)) *)
  0x48; 0x8b; 0x47; 0x3c;  (* MOV (% rax) (Memop Quadword (%% (rdi,60))) *)
  0x48; 0x8b; 0x5f; 0x44;  (* MOV (% rbx) (Memop Quadword (%% (rdi,68))) *)
  0x48; 0x8b; 0x4f; 0x4c;  (* MOV (% rcx) (Memop Quadword (%% (rdi,76))) *)
  0x48; 0x8b; 0x57; 0x54;  (* MOV (% rdx) (Memop Quadword (%% (rdi,84))) *)
  0x48; 0x8b; 0x6f; 0x5c;  (* MOV (% rbp) (Memop Quadword (%% (rdi,92))) *)
  0x49; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Imm32 (word 0)) *)
  0x41; 0x50;              (* PUSH (% r8) *)
  0x41; 0x58;              (* POP (% r8) *)
  0x49; 0x83; 0xc0; 0x01;  (* ADD (% r8) (Imm8 (word 1)) *)
  0x49; 0x83; 0xf8; 0x18;  (* CMP (% r8) (Imm8 (word 24)) *)
  0x75; 0xf2;              (* JNE (Imm8 (word 242)) *)
  0x4d; 0x8d; 0xbf; 0x40; 0xff; 0xff; 0xff;
                           (* LEA (% r15) (%% (r15,18446744073709551424)) *)
  0x48; 0xf7; 0x57; 0xa4;  (* NOT (Memop Quadword (%% (rdi,18446744073709551524))) *)
  0x48; 0xf7; 0x57; 0xac;  (* NOT (Memop Quadword (%% (rdi,18446744073709551532))) *)
  0x48; 0xf7; 0x57; 0xdc;  (* NOT (Memop Quadword (%% (rdi,18446744073709551580))) *)
  0x48; 0xf7; 0x57; 0xfc;  (* NOT (Memop Quadword (%% (rdi,18446744073709551612))) *)
  0x48; 0xf7; 0x57; 0x24;  (* NOT (Memop Quadword (%% (rdi,36))) *)
  0x48; 0xf7; 0x57; 0x3c;  (* NOT (Memop Quadword (%% (rdi,60))) *)
  0x48; 0x8d; 0x7f; 0x9c;  (* LEA (% rdi) (%% (rdi,18446744073709551516)) *)
  0x48; 0x81; 0xc4; 0xc8; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 200)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

 let MLKEM_KECCAK_F1600_EXEC_loop_body = X86_MK_EXEC_RULE mlkem_keccak_f1600_mc_loop_body;;

  let MLKEM_KECCAK_F1600_SPEC = prove(
  `forall pc:num stackpointer:int64 returnaddress bitstate table.
  nonoverlapping_modulo (2 EXP 64) (pc,0x93) (val (word_sub stackpointer (word 256)), 256) /\ 
  nonoverlapping_modulo (2 EXP 64) (pc, 0x93) (val (word_add (bitstate) (word 0):int64),200) /\
  nonoverlapping_modulo (2 EXP 64) (pc,0x93) (val (word_add (table) (word 0):int64), 192)
      ==> ensures x86
  // Precondition
  (\s. bytes_loaded s (word pc) mlkem_keccak_f1600_mc_loop_body /\
       read RIP s = word pc /\
       read RDI s = bitstate /\
       read RSP s = stackpointer /\
       read (memory :> bytes64 stackpointer) s = returnaddress)
  // Postcondition
  (\s.  read RIP s = returnaddress /\
        read RSP s = word_add stackpointer (word 8))
  (MAYCHANGE [RIP;RSP;RAX;RBX;RCX;RDX;RBP;R8;R9;R10;R11;R12;R13;R14;R15;RDI;RSI] ,, MAYCHANGE SOME_FLAGS,, 
  MAYCHANGE [memory :> bytes (word_sub stackpointer (word 256), 256)],,
  MAYCHANGE [memory :> bytes (bitstate, 200)])`
  ,

  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`pc:num`] THEN

  WORD_FORALL_OFFSET_TAC 256 THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  MAP_EVERY X_GEN_TAC [`bitstate:int64`] THEN
  REPEAT STRIP_TAC THEN

    ENSURES_WHILE_PAUP_TAC
    `0` (* loop_body begin number *)
    `24` (* loop_body end number *)
    `pc + 0x50` (* loop body start PC *)
    `pc + 0x5c` (* loop backedge branch PC -- including the jmp *)
    `\i s. // loop invariant at the end of the iteration
           (read R8 s = word i /\
            read RDI s = (word_add bitstate (word 100)) /\
            read RSP s = (word_add stackpointer (word 248)) /\
            read (memory :> bytes64 (word_add stackpointer (word 256))) s = returnaddress) /\
           // loop backedge condition
           (read ZF s <=> i = 24)` THEN

    REPEAT CONJ_TAC THENL 
    [
      (* loop_body begin < loop_body end *)
      ARITH_TAC;

      (* entrance to the loop *)
      (* Let's use X86_SIM_TAC which is ENSURES_INIT_TAC + X86_STEPS_TAC +
        ENSURES_FINAL_STATE_TAC + some post-processing. *)
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_loop_body (1--22) THEN
      REPEAT CONJ_TAC THENL   
      [

      CONV_TAC WORD_RULE;

  
      (* the body of the loop *)
      REPEAT STRIP_TAC THEN
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_loop_body (1--4) THEN
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
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_loop_body [1];

      (* Loop exit to the end of the program *)
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_loop_body (1--2);
  ]);
