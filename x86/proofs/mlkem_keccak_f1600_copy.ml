(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

 Sys.chdir "/home/ubuntu/hol/my_s2n-bignum-dev/s2n-bignum-dev";;
 needs "x86/proofs/base.ml";;
 needs "x86/proofs/utils/keccak_spec.ml";;

 x86_print_log := true;;
 components_print_log := true;;

(******************************************************************************
  Proving a mlkem_keccak_f1600 property about program 'mlkem_keccak_f1600.S'
******************************************************************************)

(* When there is no bitstate_out *)
 (**** print_literal_from_elf "x86/mlkem/mlkem_keccak_f1600_no_stack.o";;
 ****)

 (* GHOST_INTRO_TAC `init_rax:int64` `read RAX` THEN
          GHOST_INTRO_TAC `init_rbx:int64` `read RBX` THEN
          GHOST_INTRO_TAC `init_rcx:int64` `read RCX` THEN
          GHOST_INTRO_TAC `init_rdx:int64` `read RDX` THEN
          GHOST_INTRO_TAC `init_rbp:int64` `read RBP` THEN
          GHOST_INTRO_TAC `init_rsi:int64` `read RSI` THEN
          GHOST_INTRO_TAC `init_r15:int64` `read R15` THEN
          GHOST_INTRO_TAC `init_r8:int64` `read R8` THEN *)

          (* REPEAT STRIP_TAC THEN *)

           (* GHOST_INTRO_TAC `init_rsi:int64` `read RSI` THEN *)

          (* REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (0w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (8w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (16w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (24w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (32w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (40w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (48w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (56w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (64w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (72w:int64)),1) s:int64 list`] THEN

          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (80w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (88w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (96w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (104w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (112w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (120w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (128w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (136w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (144w:int64)),1) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (152w:int64)),1) s:int64 list`] THEN  *)

          (* REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (160w:int64)),1) s:int64 list`] THEN A_20 -> rax
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (168w:int64)),1) s:int64 list`] THEN A_21 -> rbx
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (176w:int64)),1) s:int64 list`] THEN A_22 -> rcx
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (184w:int64)),1) s:int64 list`] THEN A_23 -> rdx
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory((word_add (bitstate_in:int64) (192w:int64)),1) s:int64 list`] THEN A_24 -> rbp *)
(* MAP2 (\(x:bool) (y:(64)word). (if x then (word_not y) else y))
              [false; true;  true;  false; false; 
              false; false; false; true;  false; 
              false; false; true;  false; false; 
              false; false; true;  false; false;
              true;  false; false; false; false]
              (wordlist_from_memory(bitstate_in,25) s) = keccak (2*i) A  *)            
              (* read R15 s = word_add rc_pointer (word (16 * i)) /\ *)
 (* !!!! COND_CASES_TAC
 SIMPLE_ARITH_TAC

 ASM_ARITH_TAC, but much faster *)

(* let GHOST_REGLIST_TAC =
  W(fun (asl,w) ->
        let regreads = map rator (dest_list(find_term is_list w)) in
        let regnames = map ((^) "init_" o name_of o rand) regreads in
        let ghostvars = map (C (curry mk_var) `:int64`) regnames in
        EVERY(map2 GHOST_INTRO_TAC ghostvars regreads));; *)

let WORD_ROR_NOT = prove
 (`!(x:N word) n. word_ror (word_not x) n = word_not (word_ror x n)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ROR; BIT_WORD_NOT] THEN
  REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
  ASM_SIMP_TAC[TAUT `(p /\ q <=> q) <=> q ==> p`] THEN
  ASM_ARITH_TAC);;
  

let mlkem_keccak_f1600_x86_mc_9 = define_assert_from_elf
  "mlkem_keccak_f1600_x86_mc_9" "x86/mlkem/mlkem_keccak_f1600_no_stack.o"
[
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xd0; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 208)) *)
  0x48; 0xf7; 0x57; 0x08;  (* NOT (Memop Quadword (%% (rdi,8))) *)
  0x48; 0xf7; 0x57; 0x10;  (* NOT (Memop Quadword (%% (rdi,16))) *)
  0x48; 0xf7; 0x57; 0x40;  (* NOT (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xf7; 0x57; 0x60;  (* NOT (Memop Quadword (%% (rdi,96))) *)
  0x48; 0xf7; 0x97; 0x88; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,136))) *)
  0x48; 0xf7; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,160))) *)
  0x4c; 0x8d; 0x3c; 0x24;  (* LEA (% r15) (%% (rsp,0)) *)
  0x48; 0x8b; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rdi,160))) *)
  0x48; 0x8b; 0x9f; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rdi,168))) *)
  0x48; 0x8b; 0x8f; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Memop Quadword (%% (rdi,176))) *)
  0x48; 0x8b; 0x97; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rdi,184))) *)
  0x48; 0x8b; 0xaf; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rdi,192))) *)
  0x49; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Imm32 (word 0)) *)
  0x4c; 0x89; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r8) *)
  0x4c; 0x8b; 0x07;        (* MOV (% r8) (Memop Quadword (%% (rdi,0))) *)
  0x4c; 0x8b; 0x4f; 0x30;  (* MOV (% r9) (Memop Quadword (%% (rdi,48))) *)
  0x4c; 0x8b; 0x57; 0x60;  (* MOV (% r10) (Memop Quadword (%% (rdi,96))) *)
  0x4c; 0x8b; 0x9f; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,144))) *)
  0x48; 0x33; 0x4f; 0x10;  (* XOR (% rcx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x33; 0x57; 0x18;  (* XOR (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x31; 0xc0;        (* XOR (% rax) (% r8) *)
  0x48; 0x33; 0x5f; 0x08;  (* XOR (% rbx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x33; 0x4f; 0x38;  (* XOR (% rcx) (Memop Quadword (%% (rdi,56))) *)
  0x48; 0x33; 0x47; 0x28;  (* XOR (% rax) (Memop Quadword (%% (rdi,40))) *)
  0x49; 0x89; 0xec;        (* MOV (% r12) (% rbp) *)
  0x48; 0x33; 0x6f; 0x20;  (* XOR (% rbp) (Memop Quadword (%% (rdi,32))) *)
  0x4c; 0x31; 0xd1;        (* XOR (% rcx) (% r10) *)
  0x48; 0x33; 0x47; 0x50;  (* XOR (% rax) (Memop Quadword (%% (rdi,80))) *)
  0x48; 0x33; 0x57; 0x40;  (* XOR (% rdx) (Memop Quadword (%% (rdi,64))) *)
  0x4c; 0x31; 0xcb;        (* XOR (% rbx) (% r9) *)
  0x48; 0x33; 0x6f; 0x48;  (* XOR (% rbp) (Memop Quadword (%% (rdi,72))) *)
  0x48; 0x33; 0x8f; 0x88; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rdi,136))) *)
  0x48; 0x33; 0x47; 0x78;  (* XOR (% rax) (Memop Quadword (%% (rdi,120))) *)
  0x48; 0x33; 0x57; 0x68;  (* XOR (% rdx) (Memop Quadword (%% (rdi,104))) *)
  0x48; 0x33; 0x5f; 0x58;  (* XOR (% rbx) (Memop Quadword (%% (rdi,88))) *)
  0x48; 0x33; 0x6f; 0x70;  (* XOR (% rbp) (Memop Quadword (%% (rdi,112))) *)
  0x49; 0x89; 0xcd;        (* MOV (% r13) (% rcx) *)
  0x48; 0xd1; 0xc1;        (* ROL (% rcx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xc1;        (* XOR (% rcx) (% rax) *)
  0x4c; 0x31; 0xda;        (* XOR (% rdx) (% r11) *)
  0x48; 0xd1; 0xc0;        (* ROL (% rax) (Imm8 (word 1)) *)
  0x48; 0x31; 0xd0;        (* XOR (% rax) (% rdx) *)
  0x48; 0x33; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* XOR (% rbx) (Memop Quadword (%% (rdi,128))) *)
  0x48; 0xd1; 0xc2;        (* ROL (% rdx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xda;        (* XOR (% rdx) (% rbx) *)
  0x48; 0x33; 0xaf; 0x98; 0x00; 0x00; 0x00;
                           (* XOR (% rbp) (Memop Quadword (%% (rdi,152))) *)
  0x48; 0xd1; 0xc3;        (* ROL (% rbx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
  0x48; 0xd1; 0xc5;        (* ROL (% rbp) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xed;        (* XOR (% rbp) (% r13) *)
  0x49; 0x31; 0xc9;        (* XOR (% r9) (% rcx) *)
  0x49; 0x31; 0xd2;        (* XOR (% r10) (% rdx) *)
  0x49; 0xc1; 0xc1; 0x2c;  (* ROL (% r9) (Imm8 (word 44)) *)
  0x49; 0x31; 0xeb;        (* XOR (% r11) (% rbp) *)
  0x49; 0x31; 0xc4;        (* XOR (% r12) (% rax) *)
  0x49; 0xc1; 0xc2; 0x2b;  (* ROL (% r10) (Imm8 (word 43)) *)
  0x49; 0x31; 0xd8;        (* XOR (% r8) (% rbx) *)
  0x4d; 0x89; 0xcd;        (* MOV (% r13) (% r9) *)
  0x49; 0xc1; 0xc3; 0x15;  (* ROL (% r11) (Imm8 (word 21)) *)
  0x4d; 0x09; 0xd1;        (* OR (% r9) (% r10) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x49; 0xc1; 0xc4; 0x0e;  (* ROL (% r12) (Imm8 (word 14)) *)
  0x4c; 0x33; 0x0e;        (* XOR (% r9) (Memop Quadword (%% (rsi,0))) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4d; 0x89; 0x0f;        (* MOV (Memop Quadword (%% (r15,0))) (% r9) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4d; 0x89; 0x67; 0x10;  (* MOV (Memop Quadword (%% (r15,16))) (% r12) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x4c; 0x8b; 0xa7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,176))) *)
  0x4d; 0x31; 0xea;        (* XOR (% r10) (% r13) *)
  0x4d; 0x89; 0x57; 0x08;  (* MOV (Memop Quadword (%% (r15,8))) (% r10) *)
  0x4d; 0x21; 0xc5;        (* AND (% r13) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x48;  (* MOV (% r9) (Memop Quadword (%% (rdi,72))) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x8b; 0x57; 0x50;  (* MOV (% r10) (Memop Quadword (%% (rdi,80))) *)
  0x4d; 0x89; 0x6f; 0x20;  (* MOV (Memop Quadword (%% (r15,32))) (% r13) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x47; 0x18;  (* MOV (% r8) (Memop Quadword (%% (rdi,24))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,128))) *)
  0x4d; 0x89; 0x77; 0x18;  (* MOV (Memop Quadword (%% (r15,24))) (% r14) *)
  0x49; 0x31; 0xe8;        (* XOR (% r8) (% rbp) *)
  0x49; 0x31; 0xd4;        (* XOR (% r12) (% rdx) *)
  0x49; 0xc1; 0xc0; 0x1c;  (* ROL (% r8) (Imm8 (word 28)) *)
  0x49; 0x31; 0xcb;        (* XOR (% r11) (% rcx) *)
  0x49; 0x31; 0xc1;        (* XOR (% r9) (% rax) *)
  0x49; 0xc1; 0xc4; 0x3d;  (* ROL (% r12) (Imm8 (word 61)) *)
  0x49; 0xc1; 0xc3; 0x2d;  (* ROL (% r11) (Imm8 (word 45)) *)
  0x49; 0x31; 0xda;        (* XOR (% r10) (% rbx) *)
  0x49; 0xc1; 0xc1; 0x14;  (* ROL (% r9) (Imm8 (word 20)) *)
  0x4d; 0x89; 0xc5;        (* MOV (% r13) (% r8) *)
  0x4d; 0x09; 0xe0;        (* OR (% r8) (% r12) *)
  0x49; 0xc1; 0xc2; 0x03;  (* ROL (% r10) (Imm8 (word 3)) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x4d; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (r15,64))) (% r8) *)
  0x4d; 0x89; 0xce;        (* MOV (% r14) (% r9) *)
  0x4d; 0x21; 0xe9;        (* AND (% r9) (% r13) *)
  0x4c; 0x8b; 0x47; 0x08;  (* MOV (% r8) (Memop Quadword (%% (rdi,8))) *)
  0x4d; 0x31; 0xe1;        (* XOR (% r9) (% r12) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x4d; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (r15,72))) (% r9) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4c; 0x8b; 0x4f; 0x38;  (* MOV (% r9) (Memop Quadword (%% (rdi,56))) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x4d; 0x89; 0x67; 0x38;  (* MOV (Memop Quadword (%% (r15,56))) (% r12) *)
  0x4d; 0x21; 0xd3;        (* AND (% r11) (% r10) *)
  0x4c; 0x8b; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,160))) *)
  0x4d; 0x31; 0xf3;        (* XOR (% r11) (% r14) *)
  0x4d; 0x89; 0x5f; 0x30;  (* MOV (Memop Quadword (%% (r15,48))) (% r11) *)
  0x4d; 0x09; 0xd6;        (* OR (% r14) (% r10) *)
  0x4c; 0x8b; 0x57; 0x68;  (* MOV (% r10) (Memop Quadword (%% (rdi,104))) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4c; 0x8b; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,152))) *)
  0x4d; 0x89; 0x77; 0x28;  (* MOV (Memop Quadword (%% (r15,40))) (% r14) *)
  0x49; 0x31; 0xea;        (* XOR (% r10) (% rbp) *)
  0x49; 0x31; 0xc3;        (* XOR (% r11) (% rax) *)
  0x49; 0xc1; 0xc2; 0x19;  (* ROL (% r10) (Imm8 (word 25)) *)
  0x49; 0x31; 0xd1;        (* XOR (% r9) (% rdx) *)
  0x49; 0xc1; 0xc3; 0x08;  (* ROL (% r11) (Imm8 (word 8)) *)
  0x49; 0x31; 0xdc;        (* XOR (% r12) (% rbx) *)
  0x49; 0xc1; 0xc1; 0x06;  (* ROL (% r9) (Imm8 (word 6)) *)
  0x49; 0x31; 0xc8;        (* XOR (% r8) (% rcx) *)
  0x49; 0xc1; 0xc4; 0x12;  (* ROL (% r12) (Imm8 (word 18)) *)
  0x4d; 0x89; 0xd5;        (* MOV (% r13) (% r10) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x49; 0xd1; 0xc0;        (* ROL (% r8) (Imm8 (word 1)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x31; 0xca;        (* XOR (% r10) (% r9) *)
  0x4d; 0x89; 0x57; 0x58;  (* MOV (Memop Quadword (%% (r15,88))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4c; 0x8b; 0x57; 0x58;  (* MOV (% r10) (Memop Quadword (%% (rdi,88))) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x89; 0x67; 0x60;  (* MOV (Memop Quadword (%% (r15,96))) (% r12) *)
  0x4d; 0x09; 0xcd;        (* OR (% r13) (% r9) *)
  0x4c; 0x8b; 0xa7; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,184))) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4d; 0x89; 0x6f; 0x50;  (* MOV (Memop Quadword (%% (r15,80))) (% r13) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4d; 0x89; 0x4f; 0x70;  (* MOV (Memop Quadword (%% (r15,112))) (% r9) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rdi,40))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,136))) *)
  0x4d; 0x89; 0x77; 0x68;  (* MOV (Memop Quadword (%% (r15,104))) (% r14) *)
  0x4c; 0x8b; 0x47; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rdi,32))) *)
  0x49; 0x31; 0xca;        (* XOR (% r10) (% rcx) *)
  0x49; 0x31; 0xd3;        (* XOR (% r11) (% rdx) *)
  0x49; 0xc1; 0xc2; 0x0a;  (* ROL (% r10) (Imm8 (word 10)) *)
  0x49; 0x31; 0xd9;        (* XOR (% r9) (% rbx) *)
  0x49; 0xc1; 0xc3; 0x0f;  (* ROL (% r11) (Imm8 (word 15)) *)
  0x49; 0x31; 0xec;        (* XOR (% r12) (% rbp) *)
  0x49; 0xc1; 0xc1; 0x24;  (* ROL (% r9) (Imm8 (word 36)) *)
  0x49; 0x31; 0xc0;        (* XOR (% r8) (% rax) *)
  0x49; 0xc1; 0xc4; 0x38;  (* ROL (% r12) (Imm8 (word 56)) *)
  0x4d; 0x89; 0xd5;        (* MOV (% r13) (% r10) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x49; 0xc1; 0xc0; 0x1b;  (* ROL (% r8) (Imm8 (word 27)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x31; 0xca;        (* XOR (% r10) (% r9) *)
  0x4d; 0x89; 0x97; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,128))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x89; 0xa7; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,136))) (% r12) *)
  0x4d; 0x21; 0xcd;        (* AND (% r13) (% r9) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4d; 0x89; 0x6f; 0x78;  (* MOV (Memop Quadword (%% (r15,120))) (% r13) *)
  0x4d; 0x09; 0xc1;        (* OR (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4d; 0x89; 0x8f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,152))) (% r9) *)
  0x4d; 0x21; 0xf0;        (* AND (% r8) (% r14) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x4d; 0x89; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,144))) (% r8) *)
  0x48; 0x33; 0x57; 0x10;  (* XOR (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x33; 0x6f; 0x40;  (* XOR (% rbp) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xc1; 0xc2; 0x3e;  (* ROL (% rdx) (Imm8 (word 62)) *)
  0x48; 0x33; 0x8f; 0xa8; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rdi,168))) *)
  0x48; 0xc1; 0xc5; 0x37;  (* ROL (% rbp) (Imm8 (word 55)) *)
  0x48; 0x33; 0x47; 0x70;  (* XOR (% rax) (Memop Quadword (%% (rdi,112))) *)
  0x48; 0xc1; 0xc1; 0x02;  (* ROL (% rcx) (Imm8 (word 2)) *)
  0x48; 0x33; 0x5f; 0x78;  (* XOR (% rbx) (Memop Quadword (%% (rdi,120))) *)
  0x4c; 0x87; 0xff;        (* XCHG (% r15) (% rdi) *)
  0x48; 0xc1; 0xc0; 0x27;  (* ROL (% rax) (Imm8 (word 39)) *)
  0x48; 0xc1; 0xc3; 0x29;  (* ROL (% rbx) (Imm8 (word 41)) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0x21; 0xea;        (* AND (% rdx) (% rbp) *)
  0x48; 0xf7; 0xd5;        (* NOT (% rbp) *)
  0x48; 0x31; 0xca;        (* XOR (% rdx) (% rcx) *)
  0x48; 0x89; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,192))) (% rdx) *)
  0x49; 0x89; 0xc6;        (* MOV (% r14) (% rax) *)
  0x48; 0x21; 0xe8;        (* AND (% rax) (% rbp) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x48; 0x89; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% rax) *)
  0x49; 0x09; 0xcd;        (* OR (% r13) (% rcx) *)
  0x49; 0x31; 0xdd;        (* XOR (% r13) (% rbx) *)
  0x4c; 0x89; 0xaf; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% r13) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x4c; 0x31; 0xf1;        (* XOR (% rcx) (% r14) *)
  0x48; 0x89; 0x8f; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% rcx) *)
  0x4c; 0x09; 0xf3;        (* OR (% rbx) (% r14) *)
  0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
  0x48; 0x89; 0x9f; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% rbx) *)
  0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x48; 0x8d; 0x76; 0x08;  (* LEA (% rsi) (%% (rsi,8)) *)
  0x4c; 0x8b; 0x07;        (* MOV (% r8) (Memop Quadword (%% (rdi,0))) *)
  0x4c; 0x8b; 0x4f; 0x30;  (* MOV (% r9) (Memop Quadword (%% (rdi,48))) *)
  0x4c; 0x8b; 0x57; 0x60;  (* MOV (% r10) (Memop Quadword (%% (rdi,96))) *)
  0x4c; 0x8b; 0x9f; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,144))) *)
  0x48; 0x33; 0x4f; 0x10;  (* XOR (% rcx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x33; 0x57; 0x18;  (* XOR (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x31; 0xc0;        (* XOR (% rax) (% r8) *)
  0x48; 0x33; 0x5f; 0x08;  (* XOR (% rbx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x33; 0x4f; 0x38;  (* XOR (% rcx) (Memop Quadword (%% (rdi,56))) *)
  0x48; 0x33; 0x47; 0x28;  (* XOR (% rax) (Memop Quadword (%% (rdi,40))) *)
  0x49; 0x89; 0xec;        (* MOV (% r12) (% rbp) *)
  0x48; 0x33; 0x6f; 0x20;  (* XOR (% rbp) (Memop Quadword (%% (rdi,32))) *)
  0x4c; 0x31; 0xd1;        (* XOR (% rcx) (% r10) *)
  0x48; 0x33; 0x47; 0x50;  (* XOR (% rax) (Memop Quadword (%% (rdi,80))) *)
  0x48; 0x33; 0x57; 0x40;  (* XOR (% rdx) (Memop Quadword (%% (rdi,64))) *)
  0x4c; 0x31; 0xcb;        (* XOR (% rbx) (% r9) *)
  0x48; 0x33; 0x6f; 0x48;  (* XOR (% rbp) (Memop Quadword (%% (rdi,72))) *)
  0x48; 0x33; 0x8f; 0x88; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rdi,136))) *)
  0x48; 0x33; 0x47; 0x78;  (* XOR (% rax) (Memop Quadword (%% (rdi,120))) *)
  0x48; 0x33; 0x57; 0x68;  (* XOR (% rdx) (Memop Quadword (%% (rdi,104))) *)
  0x48; 0x33; 0x5f; 0x58;  (* XOR (% rbx) (Memop Quadword (%% (rdi,88))) *)
  0x48; 0x33; 0x6f; 0x70;  (* XOR (% rbp) (Memop Quadword (%% (rdi,112))) *)
  0x49; 0x89; 0xcd;        (* MOV (% r13) (% rcx) *)
  0x48; 0xd1; 0xc1;        (* ROL (% rcx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xc1;        (* XOR (% rcx) (% rax) *)
  0x4c; 0x31; 0xda;        (* XOR (% rdx) (% r11) *)
  0x48; 0xd1; 0xc0;        (* ROL (% rax) (Imm8 (word 1)) *)
  0x48; 0x31; 0xd0;        (* XOR (% rax) (% rdx) *)
  0x48; 0x33; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* XOR (% rbx) (Memop Quadword (%% (rdi,128))) *)
  0x48; 0xd1; 0xc2;        (* ROL (% rdx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xda;        (* XOR (% rdx) (% rbx) *)
  0x48; 0x33; 0xaf; 0x98; 0x00; 0x00; 0x00;
                           (* XOR (% rbp) (Memop Quadword (%% (rdi,152))) *)
  0x48; 0xd1; 0xc3;        (* ROL (% rbx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
  0x48; 0xd1; 0xc5;        (* ROL (% rbp) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xed;        (* XOR (% rbp) (% r13) *)
  0x49; 0x31; 0xc9;        (* XOR (% r9) (% rcx) *)
  0x49; 0x31; 0xd2;        (* XOR (% r10) (% rdx) *)
  0x49; 0xc1; 0xc1; 0x2c;  (* ROL (% r9) (Imm8 (word 44)) *)
  0x49; 0x31; 0xeb;        (* XOR (% r11) (% rbp) *)
  0x49; 0x31; 0xc4;        (* XOR (% r12) (% rax) *)
  0x49; 0xc1; 0xc2; 0x2b;  (* ROL (% r10) (Imm8 (word 43)) *)
  0x49; 0x31; 0xd8;        (* XOR (% r8) (% rbx) *)
  0x4d; 0x89; 0xcd;        (* MOV (% r13) (% r9) *)
  0x49; 0xc1; 0xc3; 0x15;  (* ROL (% r11) (Imm8 (word 21)) *)
  0x4d; 0x09; 0xd1;        (* OR (% r9) (% r10) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x49; 0xc1; 0xc4; 0x0e;  (* ROL (% r12) (Imm8 (word 14)) *)
  0x4c; 0x33; 0x0e;        (* XOR (% r9) (Memop Quadword (%% (rsi,0))) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4d; 0x89; 0x0f;        (* MOV (Memop Quadword (%% (r15,0))) (% r9) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4d; 0x89; 0x67; 0x10;  (* MOV (Memop Quadword (%% (r15,16))) (% r12) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x4c; 0x8b; 0xa7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,176))) *)
  0x4d; 0x31; 0xea;        (* XOR (% r10) (% r13) *)
  0x4d; 0x89; 0x57; 0x08;  (* MOV (Memop Quadword (%% (r15,8))) (% r10) *)
  0x4d; 0x21; 0xc5;        (* AND (% r13) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x48;  (* MOV (% r9) (Memop Quadword (%% (rdi,72))) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x8b; 0x57; 0x50;  (* MOV (% r10) (Memop Quadword (%% (rdi,80))) *)
  0x4d; 0x89; 0x6f; 0x20;  (* MOV (Memop Quadword (%% (r15,32))) (% r13) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x47; 0x18;  (* MOV (% r8) (Memop Quadword (%% (rdi,24))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,128))) *)
  0x4d; 0x89; 0x77; 0x18;  (* MOV (Memop Quadword (%% (r15,24))) (% r14) *)
  0x49; 0x31; 0xe8;        (* XOR (% r8) (% rbp) *)
  0x49; 0x31; 0xd4;        (* XOR (% r12) (% rdx) *)
  0x49; 0xc1; 0xc0; 0x1c;  (* ROL (% r8) (Imm8 (word 28)) *)
  0x49; 0x31; 0xcb;        (* XOR (% r11) (% rcx) *)
  0x49; 0x31; 0xc1;        (* XOR (% r9) (% rax) *)
  0x49; 0xc1; 0xc4; 0x3d;  (* ROL (% r12) (Imm8 (word 61)) *)
  0x49; 0xc1; 0xc3; 0x2d;  (* ROL (% r11) (Imm8 (word 45)) *)
  0x49; 0x31; 0xda;        (* XOR (% r10) (% rbx) *)
  0x49; 0xc1; 0xc1; 0x14;  (* ROL (% r9) (Imm8 (word 20)) *)
  0x4d; 0x89; 0xc5;        (* MOV (% r13) (% r8) *)
  0x4d; 0x09; 0xe0;        (* OR (% r8) (% r12) *)
  0x49; 0xc1; 0xc2; 0x03;  (* ROL (% r10) (Imm8 (word 3)) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x4d; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (r15,64))) (% r8) *)
  0x4d; 0x89; 0xce;        (* MOV (% r14) (% r9) *)
  0x4d; 0x21; 0xe9;        (* AND (% r9) (% r13) *)
  0x4c; 0x8b; 0x47; 0x08;  (* MOV (% r8) (Memop Quadword (%% (rdi,8))) *)
  0x4d; 0x31; 0xe1;        (* XOR (% r9) (% r12) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x4d; 0x89; 0x4f; 0x48;  (* MOV (Memop Quadword (%% (r15,72))) (% r9) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4c; 0x8b; 0x4f; 0x38;  (* MOV (% r9) (Memop Quadword (%% (rdi,56))) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x4d; 0x89; 0x67; 0x38;  (* MOV (Memop Quadword (%% (r15,56))) (% r12) *)
  0x4d; 0x21; 0xd3;        (* AND (% r11) (% r10) *)
  0x4c; 0x8b; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,160))) *)
  0x4d; 0x31; 0xf3;        (* XOR (% r11) (% r14) *)
  0x4d; 0x89; 0x5f; 0x30;  (* MOV (Memop Quadword (%% (r15,48))) (% r11) *)
  0x4d; 0x09; 0xd6;        (* OR (% r14) (% r10) *)
  0x4c; 0x8b; 0x57; 0x68;  (* MOV (% r10) (Memop Quadword (%% (rdi,104))) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4c; 0x8b; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,152))) *)
  0x4d; 0x89; 0x77; 0x28;  (* MOV (Memop Quadword (%% (r15,40))) (% r14) *)
  0x49; 0x31; 0xea;        (* XOR (% r10) (% rbp) *)
  0x49; 0x31; 0xc3;        (* XOR (% r11) (% rax) *)
  0x49; 0xc1; 0xc2; 0x19;  (* ROL (% r10) (Imm8 (word 25)) *)
  0x49; 0x31; 0xd1;        (* XOR (% r9) (% rdx) *)
  0x49; 0xc1; 0xc3; 0x08;  (* ROL (% r11) (Imm8 (word 8)) *)
  0x49; 0x31; 0xdc;        (* XOR (% r12) (% rbx) *)
  0x49; 0xc1; 0xc1; 0x06;  (* ROL (% r9) (Imm8 (word 6)) *)
  0x49; 0x31; 0xc8;        (* XOR (% r8) (% rcx) *)
  0x49; 0xc1; 0xc4; 0x12;  (* ROL (% r12) (Imm8 (word 18)) *)
  0x4d; 0x89; 0xd5;        (* MOV (% r13) (% r10) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x49; 0xd1; 0xc0;        (* ROL (% r8) (Imm8 (word 1)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x31; 0xca;        (* XOR (% r10) (% r9) *)
  0x4d; 0x89; 0x57; 0x58;  (* MOV (Memop Quadword (%% (r15,88))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4c; 0x8b; 0x57; 0x58;  (* MOV (% r10) (Memop Quadword (%% (rdi,88))) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x89; 0x67; 0x60;  (* MOV (Memop Quadword (%% (r15,96))) (% r12) *)
  0x4d; 0x09; 0xcd;        (* OR (% r13) (% r9) *)
  0x4c; 0x8b; 0xa7; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,184))) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4d; 0x89; 0x6f; 0x50;  (* MOV (Memop Quadword (%% (r15,80))) (% r13) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4d; 0x89; 0x4f; 0x70;  (* MOV (Memop Quadword (%% (r15,112))) (% r9) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rdi,40))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,136))) *)
  0x4d; 0x89; 0x77; 0x68;  (* MOV (Memop Quadword (%% (r15,104))) (% r14) *)
  0x4c; 0x8b; 0x47; 0x20;  (* MOV (% r8) (Memop Quadword (%% (rdi,32))) *)
  0x49; 0x31; 0xca;        (* XOR (% r10) (% rcx) *)
  0x49; 0x31; 0xd3;        (* XOR (% r11) (% rdx) *)
  0x49; 0xc1; 0xc2; 0x0a;  (* ROL (% r10) (Imm8 (word 10)) *)
  0x49; 0x31; 0xd9;        (* XOR (% r9) (% rbx) *)
  0x49; 0xc1; 0xc3; 0x0f;  (* ROL (% r11) (Imm8 (word 15)) *)
  0x49; 0x31; 0xec;        (* XOR (% r12) (% rbp) *)
  0x49; 0xc1; 0xc1; 0x24;  (* ROL (% r9) (Imm8 (word 36)) *)
  0x49; 0x31; 0xc0;        (* XOR (% r8) (% rax) *)
  0x49; 0xc1; 0xc4; 0x38;  (* ROL (% r12) (Imm8 (word 56)) *)
  0x4d; 0x89; 0xd5;        (* MOV (% r13) (% r10) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x49; 0xc1; 0xc0; 0x1b;  (* ROL (% r8) (Imm8 (word 27)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x31; 0xca;        (* XOR (% r10) (% r9) *)
  0x4d; 0x89; 0x97; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,128))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x89; 0xa7; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,136))) (% r12) *)
  0x4d; 0x21; 0xcd;        (* AND (% r13) (% r9) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4d; 0x89; 0x6f; 0x78;  (* MOV (Memop Quadword (%% (r15,120))) (% r13) *)
  0x4d; 0x09; 0xc1;        (* OR (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4d; 0x89; 0x8f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,152))) (% r9) *)
  0x4d; 0x21; 0xf0;        (* AND (% r8) (% r14) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x4d; 0x89; 0x87; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (r15,144))) (% r8) *)
  0x48; 0x33; 0x57; 0x10;  (* XOR (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x33; 0x6f; 0x40;  (* XOR (% rbp) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xc1; 0xc2; 0x3e;  (* ROL (% rdx) (Imm8 (word 62)) *)
  0x48; 0x33; 0x8f; 0xa8; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rdi,168))) *)
  0x48; 0xc1; 0xc5; 0x37;  (* ROL (% rbp) (Imm8 (word 55)) *)
  0x48; 0x33; 0x47; 0x70;  (* XOR (% rax) (Memop Quadword (%% (rdi,112))) *)
  0x48; 0xc1; 0xc1; 0x02;  (* ROL (% rcx) (Imm8 (word 2)) *)
  0x48; 0x33; 0x5f; 0x78;  (* XOR (% rbx) (Memop Quadword (%% (rdi,120))) *)
  0x4c; 0x87; 0xff;        (* XCHG (% r15) (% rdi) *)
  0x48; 0xc1; 0xc0; 0x27;  (* ROL (% rax) (Imm8 (word 39)) *)
  0x48; 0xc1; 0xc3; 0x29;  (* ROL (% rbx) (Imm8 (word 41)) *)
  0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
  0x48; 0x21; 0xea;        (* AND (% rdx) (% rbp) *)
  0x48; 0xf7; 0xd5;        (* NOT (% rbp) *)
  0x48; 0x31; 0xca;        (* XOR (% rdx) (% rcx) *)
  0x48; 0x89; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,192))) (% rdx) *)
  0x49; 0x89; 0xc6;        (* MOV (% r14) (% rax) *)
  0x48; 0x21; 0xe8;        (* AND (% rax) (% rbp) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x48; 0x89; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,160))) (% rax) *)
  0x49; 0x09; 0xcd;        (* OR (% r13) (% rcx) *)
  0x49; 0x31; 0xdd;        (* XOR (% r13) (% rbx) *)
  0x4c; 0x89; 0xaf; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,184))) (% r13) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x4c; 0x31; 0xf1;        (* XOR (% rcx) (% r14) *)
  0x48; 0x89; 0x8f; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,176))) (% rcx) *)
  0x4c; 0x09; 0xf3;        (* OR (% rbx) (% r14) *)
  0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
  0x48; 0x89; 0x9f; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rdi,168))) (% rbx) *)
  0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x48; 0x8d; 0x76; 0x08;  (* LEA (% rsi) (%% (rsi,8)) *)
  0x4c; 0x8b; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,200))) *)
  0x49; 0x83; 0xc0; 0x02;  (* ADD (% r8) (Imm8 (word 2)) *)
  0x49; 0x83; 0xf8; 0x18;  (* CMP (% r8) (Imm8 (word 24)) *)
  0x0f; 0x85; 0x2a; 0xfa; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294965802)) *)
  0x48; 0x8d; 0xb6; 0x40; 0xff; 0xff; 0xff;
                           (* LEA (% rsi) (%% (rsi,18446744073709551424)) *)
  0x48; 0xf7; 0x57; 0x08;  (* NOT (Memop Quadword (%% (rdi,8))) *)
  0x48; 0xf7; 0x57; 0x10;  (* NOT (Memop Quadword (%% (rdi,16))) *)
  0x48; 0xf7; 0x57; 0x40;  (* NOT (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xf7; 0x57; 0x60;  (* NOT (Memop Quadword (%% (rdi,96))) *)
  0x48; 0xf7; 0x97; 0x88; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,136))) *)
  0x48; 0xf7; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,160))) *)
  0x48; 0x81; 0xc4; 0xd0; 0x00; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 208)) *)
  0x5e;                    (* POP (% rsi) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;


let MLKEM_KECCAK_F1600_EXEC_9 = X86_MK_EXEC_RULE mlkem_keccak_f1600_x86_mc_9;;

 let wordlist_from_memory = define
 `wordlist_from_memory(bitstate_in,0) s = [] /\
  wordlist_from_memory(bitstate_in,SUC n) s =
  APPEND (wordlist_from_memory(bitstate_in,n) s)
         [read (memory :> bytes64(word_add bitstate_in (word(8 * n)))) s]`;;

let WORDLIST_FROM_MEMORY_CONV =
  let uconv =
    (LAND_CONV(RAND_CONV num_CONV) THENC
     GEN_REWRITE_CONV I [CONJUNCT2 wordlist_from_memory]) ORELSEC
     GEN_REWRITE_CONV I [CONJUNCT1 wordlist_from_memory] in
  let conv =
    TOP_DEPTH_CONV uconv THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [WORD_ADD_0] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [APPEND]
  and filt = can (term_match [] `wordlist_from_memory(bitstate_in,NUMERAL n) s`) in
  conv o check filt;;

  let MLKEM_KECCAK_F1600_SPEC = prove(
  `forall rc_pointer:int64 pc:num stackpointer:int64 bitstate_in:int64 A.
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH mlkem_keccak_f1600_x86_mc_9) (val  stackpointer, 264) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH mlkem_keccak_f1600_x86_mc_9) (val bitstate_in, 200) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH mlkem_keccak_f1600_x86_mc_9) (val rc_pointer, 192) /\

  nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val rc_pointer,192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val stackpointer, 264) /\

  nonoverlapping_modulo (2 EXP 64) (val stackpointer, 264) (val rc_pointer,192)
      ==> ensures x86
  // Precondition
  (\s. bytes_loaded s (word pc) mlkem_keccak_f1600_x86_mc_9 /\
       read RIP s = word (pc + 0x11) /\
       read RSP s = stackpointer /\
       read RSI s = rc_pointer /\
       C_ARGUMENTS [bitstate_in; rc_pointer] s /\
                wordlist_from_memory(rc_pointer,24) s = rc_table /\
                wordlist_from_memory(bitstate_in,25) s = A
                )
  // Postcondition
  (\s. read RSP s = stackpointer /\
        wordlist_from_memory(bitstate_in,25) s = keccak 24 A)
  (MAYCHANGE [RIP;RSP;RAX;RBX;RCX;RDX;RBP;R8;R9;R10;R11;R12;R13;R14;R15;RDI;RSI] ,, MAYCHANGE SOME_FLAGS,, 
  MAYCHANGE [memory :> bytes (stackpointer, 264)],,
  MAYCHANGE [memory :> bytes (bitstate_in, 200)]
  )`,

  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`rc_pointer:int64`; `pc:num`] THEN
  REWRITE_TAC [(REWRITE_CONV [mlkem_keccak_f1600_x86_mc_9] THENC LENGTH_CONV) `LENGTH mlkem_keccak_f1600_x86_mc_9`] THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`;`bitstate_in:int64`;`A:int64 list`] THEN
  REWRITE_TAC[fst MLKEM_KECCAK_F1600_EXEC_9] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN


     ASM_CASES_TAC `LENGTH(A:int64 list) = 25` THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN


    ENSURES_WHILE_PAUP_TAC
    `0` (* loop_body begin number *)
    `12` (* loop_body end number *)
    `pc + 0x5d` (* loop body start PC *)
    `pc + 0x62d` (* loop backedge branch PC -- including the jmp *) 
    `\i s. // loop invariant at the end of the iteration
            (read R8 s = word (2*i) /\
            read RDI s = bitstate_in /\
            read RSP s = stackpointer /\
            read R15 s = stackpointer /\
               read RAX s = (read (memory :> bytes64 (word_add bitstate_in (word 160))) s) /\
               read RBX s = (read (memory :> bytes64 (word_add bitstate_in (word 168))) s) /\
               read RCX s = (read (memory :> bytes64 (word_add bitstate_in (word 176))) s) /\
               read RDX s = (read (memory :> bytes64 (word_add bitstate_in (word 184))) s) /\
               read RBP s = (read (memory :> bytes64 (word_add bitstate_in (word 192))) s) /\
            read RSI s = word_add rc_pointer (word (16 * i)) /\
            wordlist_from_memory(rc_pointer,24) s = rc_table /\
            wordlist_from_memory(bitstate_in,25) s = MAP2 (\(x:bool) (y:(64)word). (if x then (word_not y) else y)) (
              [false; true;  true;  false; false; 
              false; false; false; true;  false; 
              false; false; true;  false; false; 
              false; false; true;  false; false;
              true;  false; false; false; false]) (keccak (2*i) A))  /\
           // loop backedge condition
           (read ZF s <=> i = 12)` THEN

    REPEAT CONJ_TAC THENL 
    [
          (* loop_body begin < loop_body end *)
          ARITH_TAC;

          (* program_begin until loop_entry *)
          REWRITE_TAC[rc_table; CONS_11; GSYM CONJ_ASSOC; WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`] THEN
          REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN
          ENSURES_INIT_TAC "s0" THEN
          BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 25)) s0` THEN
          ASM_REWRITE_TAC[] THEN
          X86_STEPS_TAC MLKEM_KECCAK_F1600_EXEC_9 (1--13) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

          REPEAT CONJ_TAC THENL 
          [
                CONV_TAC WORD_RULE;

                CONV_TAC WORD_RULE;

                EXPAND_TAC "A" THEN
                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 * 0 = 0`]) THEN
                CHANGED_TAC(REWRITE_TAC[keccak]) THEN 
                CHANGED_TAC(REWRITE_TAC[MAP2]);
          ]

        (* strip the i universal quantifier *)
        CHANGED_TAC(X_GEN_TAC `i:num`) THEN 
        (* Automatically "strip" the outermost logical structure from a goal *)
        CHANGED_TAC(STRIP_TAC) THEN
        (* Handle conversions between num (natural numbers) and 64-bit integer representations *)
        CHANGED_TAC(MAP_EVERY VAL_INT64_TAC [`i:num`; `2 * i`; `2 * i + 1`]) THEN

         MP_TAC(WORD_RULE
            `word_add (word (2 * i)) (word 1):int64 = word(2 * i + 1)`) THEN

        (* Equational rewriting on goals using provided theorems *)
        DISCH_TAC THEN CONV_TAC(RATOR_CONV(LAND_CONV
          (ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THENC
          ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN

        ASM_REWRITE_TAC[rc_table; CONS_11; GSYM CONJ_ASSOC; WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`] THEN
        ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN

        MP_TAC(ISPECL [`A:int64 list`; `2 * i`] LENGTH_KECCAK) THEN
        ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
          DISCH_TAC THEN
        REWRITE_TAC[MAP] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MAP2; CONS_11; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN

        (* Convert a big number representation into individual "digits" or "limbs" *)
        BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 25)) s0` THEN
        (* FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN *)


         ASM_REWRITE_TAC[] THEN
        (* EXPAND_TAC "A" THEN *)
        (* Create a new subgoal to prove, then uses the proved result *)
        SUBGOAL_THEN
            `read (memory :> bytes64 (word_add rc_pointer (word(8 * i)))) s0 =
              EL i rc_table /\
              read (memory :> bytes64 (word_add rc_pointer (word(2 * 8 * i)))) s0 =
              EL (2 * i) rc_table /\
              read (memory :> bytes64 (word_add rc_pointer (word(16 * i)))) s0 =
              EL (2 * i) rc_table /\
              read (memory :> bytes64 (word_add (word_add rc_pointer (word(16 * i))) (word(8)))) s0 =
              EL (2 * i + 1) rc_table`
              (* Takes the proved statement and adds it to assumptions *)
              ASSUME_TAC THENL
            [UNDISCH_TAC `i < 12` THEN
             SPEC_TAC(`i:num`,`i:num`) THEN
            CONV_TAC EXPAND_CASES_CONV THEN
            REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN 
            CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
            ASM_REWRITE_TAC[rc_table; WORD_ADD_0] THEN
            (* REWRITE_TAC[ARITH_RULE`2*11+1 = 23`] THEN *)
            CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN 
           (* REWRITE_TAC[] THEN FAIL_TAC THEN *)
            REWRITE_TAC[];
            ALL_TAC] THEN
            ASM_REWRITE_TAC[] THEN

      X86_STEPS_TAC MLKEM_KECCAK_F1600_EXEC_9 (1--394) THEN
      ENSURES_FINAL_STATE_TAC THEN 
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [
            CONV_TAC WORD_RULE;
            CONV_TAC WORD_RULE;
            (* EXPAND_TAC "A" THEN *)
              UNDISCH_TAC `i < 12` THEN SPEC_TAC(`i:num`,`i:num`) THEN
              (* Expand for all value of i *)
              CONV_TAC EXPAND_CASES_CONV THEN
              CHANGED_TAC(CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV))] THEN

               GEN_REWRITE_TAC I [CONJ_ASSOC] THEN 
               REPEAT CONJ_TAC THENL
     [CONJ_TAC THEN 
     CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[];

              [CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
              CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
              ASM_REWRITE_TAC[];
              ALL_TAC] THEN
               [
                  (* Why when CHANGED_TAC fails when now , it splits the goal into subgoals *)
                 ASM_REWRITE_TAC[];
                  CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 = (0 + 1) + 1`]) THEN
                  REWRITE_TAC[keccak] THEN
                  (* CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `(0 + 1) = 1`]) THEN *)
                  CHANGED_TAC(REWRITE_TAC[keccak_round]) THEN
                  (* CHANGED_TAC(CONV_TAC(ONCE_DEPTH_CONV EL_CONV)) THEN *)
                  CHANGED_TAC(CONV_TAC(TOP_DEPTH_CONV let_CONV)) THEN
                  CHANGED_TAC(REWRITE_TAC[MAP2; CONS_11]) THEN 
                  CHANGED_TAC(REPEAT CONJ_TAC) THEN
                  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN 

                  (* UNTIL HERE *)

                  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV ) THEN


                  EXPAND_TAC "A" THEN
    


                  ASM_REWRITE_TAC[] THEN

                  CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `(0 + 1) = 1`]) THEN

                   CHANGED_TAC(REWRITE_TAC[rc_table]) THEN 
                        
     CHANGED_TAC( KECCAK_BITBLAST_TAC);


                  CONV_TAC WORD_RULE;

                  CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN

                 MP_TAC(ISPECL[`0`; `A`] EL_THM)









REWRITE_TAC[ARITH_RULE`2 * ( i + 1) = 2 * i + 2`] THEN 

               (* r 1 ;;  *)
               CONV_TAC WORD_RULE;

               CONV_TAC WORD_RULE;

               UNDISCH_TAC `i < 12` THEN SPEC_TAC(`i:num`,`i:num`) THEN









               CONV_TAC EXPAND_CASES_CONV THEN

               CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)] THEN

               GEN_REWRITE_TAC I [CONJ_ASSOC] THEN
               
               CONJ_TAC THENL

REWRITE_TAC[WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`; WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN
          

                CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
                      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN

        REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[keccak; keccak_round] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[MAP2; CONS_11] THEN REPEAT CONJ_TAC THEN
      KECCAK_BITBLAST_TAC;

















               GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[ARITH_RULE `2 * (i + 1) = (2 * i + 1) + 1`] THEN


                 REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
            CONJ_TAC THENL
     [
      REWRITE_TAC[keccak; keccak_round] THEN

                EXPAND_TAC "A" THEN

                REWRITE_TAC[keccak; MAP2] THEN

                CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN


      UNDISCH_TAC `i < 12` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN


      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN 

      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)] THEN

    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL

     [CONJ_TAC THEN CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[];


      REWRITE_TAC[MAP2; CONS_11] THEN REPEAT CONJ_TAC THEN

                EXPAND_TAC "A" THEN
                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2 * 1`]) THEN
                

               GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[ARITH_RULE `2 * 1 = (0 + 1) + 1`] THEN

                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 * i = (0 + 1) * i + 1*i`]) THEN

                CHANGED_TAC(REWRITE_TAC[keccak]) THEN 
                CHANGED_TAC(REWRITE_TAC[MAP2;CONS_11]);



    REWRITE_TAC [WORD_BLAST `word_add word_add (rc_pointer) (word 0):int64 (word 18446744073709551594):int64 =
                             word_sub (((2):(64)word)*x) (word 9)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_94] THEN
    (* Rewrite all '_ MOD 2 EXP 64' to '_' because they are known to be less
       than 2 EXP 64. *)
    IMP_REWRITE_TAC[MOD_LT; ARITH_RULE`12 < 2 EXP 64`] THEN




               X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `2 * i`; `2 * (i + 1)`; `2 * i + 2`] THEN
    MP_TAC(WORD_RULE`word_add (word (2 * i)) (word 2):int64 = word(2 * i + 2)`) THEN
      DISCH_TAC THEN
      
                EXPAND_TAC "A" THEN

                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`]) THEN

                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`]) THEN

                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 = (0 + 1) + 1`]) THEN
                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `(0 + 1) + 1 =  1 + 1`]) THEN
                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `1 + 1 =  2`]) THEN
                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `(2 * i) + 2 = (2 * (i + 1))`]) THEN

                 CONV_TAC WORD_RULE THEN

                 ASM_REWRITE_TAC[] THEN

                 GEN_REWRITE_TAC THEN

                  CHANGED_TAC(REWRITE_TAC[keccak;rc_table]) THEN 
                CHANGED_TAC(REWRITE_TAC[MAP2;CONS_11]);


                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 * i + 2 = (2 * i + ((0 + 1) + 1))`]) THEN
                CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 * 1 = (2 * i + ((0 + 1) + 1))`]) THEN
                CHANGED_TAC(REWRITE_TAC[keccak; MAP2]);

            ]








          EXPAND_TAC "A" THEN
          CHANGED_TAC(PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 * 0 = 0`]) THEN
          CHANGED_TAC(REWRITE_TAC[keccak; MAP2]);


  (* CHANGED_TAC(GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [ARITH_RULE `2 * 1 = (0 + 1) + 1`]) THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN
      



REWRITE_TAC[NOT_NOT_ELIM_9] THEN

MATCH_MP_TAC NOT_NOT_ELIM THEN
   

 CONV_TAC(RAND_CONV NUM_REDUCE_CONV) THEN
(* ASM_REWRITE_TAC[rc_table; WORD_ADD_0] THEN *)
CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
 REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]


    REWRITE_TAC[keccak; rc_table; EL; HD] THEN
    REWRITE_TAC[rc_table] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    (* CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN *)
    REWRITE_TAC[MAP2] THEN REWRITE_TAC[CONS_11] THEN

 REWRITE_TAC[NOT_DEF] THEN
    
REPEAT CONJ_TAC THEN BITBLAST_TAC; *)

      (* X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_9 (1--21); *)

      (* the body of the loop *)
     

      REWRITE_TAC[condition_semantics] THEN
      
      REPEAT CONJ_TAC THENL
      REWRITE_TAC[rc_table; CONS_11; GSYM CONJ_ASSOC; WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`] THEN

     X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_9 (1--394) THEN

      REPEAT CONJ_TAC THENL
      [
        CONV_TAC WORD_RULE;

        REWRITE_TAC [WORD_BLAST `word_add x (word 18446744073709551605):int64 =
                             word_sub x (word 11)`] THEN

        REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
        REWRITE_TAC[VAL_WORD;DIMINDEX_94] THEN

        IMP_REWRITE_TAC[MOD_LT; ARITH_RULE`11 < 2 EXP 64`] THEN

        CONJ_TAC THENL 
        [ (* will create two arithmetic subgoals. *)
          UNDISCH_TAC `i < 12` 
          THEN ARITH_TAC;

          ARITH_TAC
        ]
      ];

      REWRITE_TAC[condition_semantics] THEN REPEAT CONJ_TAC THENL
      REWRITE_TAC[rc_table; CONS_11; GSYM CONJ_ASSOC; WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`] THEN

      (* Prove that backedge is taken if i != 12. *)
      REPEAT STRIP_TAC THEN
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_9 [1];

       REWRITE_TAC[condition_semantics] THEN REPEAT CONJ_TAC THENL
      REWRITE_TAC[rc_table; CONS_11; GSYM CONJ_ASSOC; WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`] THEN
      

      (* Loop exit to the end of the program *)
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_9 (1--16);
  ]);

