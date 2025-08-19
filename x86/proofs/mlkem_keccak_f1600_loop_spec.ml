(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

 needs "x86/proofs/base.ml";;
 needs "x86/proofs/utils/keccak_spec.ml";;

(******************************************************************************
  Proving a mlkem_keccak_f1600 property about program 'mlkem_keccak_f1600.S'
******************************************************************************)

(* When there is no bitstate_out *)
 (**** print_literal_from_elf "x86/mlkem/mlkem_keccak_f1600_loop_unroll_x2.o";;
 ****)


let rc_table = define
 `rc_table:int64 list =
   [word 0x0000000000000001;
    word 0x0000000000008082;
    word 0x800000000000808a;
    word 0x8000000080008000;
    word 0x000000000000808b;
    word 0x0000000080000001;
    word 0x8000000080008081;
    word 0x8000000000008009;
    word 0x000000000000008a;
    word 0x0000000000000088;
    word 0x0000000080008009;
    word 0x000000008000000a;
    word 0x000000008000808b;
    word 0x800000000000008b;
    word 0x8000000000008089;
    word 0x8000000000008003;
    word 0x8000000000008002;
    word 0x8000000000000080;
    word 0x000000000000800a;
    word 0x800000008000000a;
    word 0x8000000080008081;
    word 0x8000000000008080;
    word 0x0000000080000001;
    word 0x8000000080008008]`;;


let mlkem_keccak_f1600_mc_spec = define_assert_from_elf
  "mlkem_keccak_f1600_mc_spec" "x86/mlkem/mlkem_keccak_f1600_loop_unroll_x2.o"
[
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x49; 0x89; 0xf7;        (* MOV (% r15) (% rsi) *)
  0x48; 0x81; 0xec; 0xc8; 0x00; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 200)) *)
  0x48; 0xf7; 0x57; 0x08;  (* NOT (Memop Quadword (%% (rdi,8))) *)
  0x48; 0xf7; 0x57; 0x10;  (* NOT (Memop Quadword (%% (rdi,16))) *)
  0x48; 0xf7; 0x57; 0x40;  (* NOT (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xf7; 0x57; 0x60;  (* NOT (Memop Quadword (%% (rdi,96))) *)
  0x48; 0xf7; 0x97; 0x88; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,136))) *)
  0x48; 0xf7; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,160))) *)
  0x48; 0x8d; 0x34; 0x24;  (* LEA (% rsi) (%% (rsp,0)) *)
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
  0x41; 0x50;              (* PUSH (% r8) *)
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
  0x4d; 0x33; 0x0f;        (* XOR (% r9) (Memop Quadword (%% (r15,0))) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4c; 0x89; 0x0e;        (* MOV (Memop Quadword (%% (rsi,0))) (% r9) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4c; 0x89; 0x66; 0x10;  (* MOV (Memop Quadword (%% (rsi,16))) (% r12) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x4c; 0x8b; 0xa7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,176))) *)
  0x4d; 0x31; 0xea;        (* XOR (% r10) (% r13) *)
  0x4c; 0x89; 0x56; 0x08;  (* MOV (Memop Quadword (%% (rsi,8))) (% r10) *)
  0x4d; 0x21; 0xc5;        (* AND (% r13) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x48;  (* MOV (% r9) (Memop Quadword (%% (rdi,72))) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x8b; 0x57; 0x50;  (* MOV (% r10) (Memop Quadword (%% (rdi,80))) *)
  0x4c; 0x89; 0x6e; 0x20;  (* MOV (Memop Quadword (%% (rsi,32))) (% r13) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x47; 0x18;  (* MOV (% r8) (Memop Quadword (%% (rdi,24))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,128))) *)
  0x4c; 0x89; 0x76; 0x18;  (* MOV (Memop Quadword (%% (rsi,24))) (% r14) *)
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
  0x4c; 0x89; 0x46; 0x40;  (* MOV (Memop Quadword (%% (rsi,64))) (% r8) *)
  0x4d; 0x89; 0xce;        (* MOV (% r14) (% r9) *)
  0x4d; 0x21; 0xe9;        (* AND (% r9) (% r13) *)
  0x4c; 0x8b; 0x47; 0x08;  (* MOV (% r8) (Memop Quadword (%% (rdi,8))) *)
  0x4d; 0x31; 0xe1;        (* XOR (% r9) (% r12) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x4c; 0x89; 0x4e; 0x48;  (* MOV (Memop Quadword (%% (rsi,72))) (% r9) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4c; 0x8b; 0x4f; 0x38;  (* MOV (% r9) (Memop Quadword (%% (rdi,56))) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x4c; 0x89; 0x66; 0x38;  (* MOV (Memop Quadword (%% (rsi,56))) (% r12) *)
  0x4d; 0x21; 0xd3;        (* AND (% r11) (% r10) *)
  0x4c; 0x8b; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,160))) *)
  0x4d; 0x31; 0xf3;        (* XOR (% r11) (% r14) *)
  0x4c; 0x89; 0x5e; 0x30;  (* MOV (Memop Quadword (%% (rsi,48))) (% r11) *)
  0x4d; 0x09; 0xd6;        (* OR (% r14) (% r10) *)
  0x4c; 0x8b; 0x57; 0x68;  (* MOV (% r10) (Memop Quadword (%% (rdi,104))) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4c; 0x8b; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,152))) *)
  0x4c; 0x89; 0x76; 0x28;  (* MOV (Memop Quadword (%% (rsi,40))) (% r14) *)
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
  0x4c; 0x89; 0x56; 0x58;  (* MOV (Memop Quadword (%% (rsi,88))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4c; 0x8b; 0x57; 0x58;  (* MOV (% r10) (Memop Quadword (%% (rdi,88))) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4c; 0x89; 0x66; 0x60;  (* MOV (Memop Quadword (%% (rsi,96))) (% r12) *)
  0x4d; 0x09; 0xcd;        (* OR (% r13) (% r9) *)
  0x4c; 0x8b; 0xa7; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,184))) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4c; 0x89; 0x6e; 0x50;  (* MOV (Memop Quadword (%% (rsi,80))) (% r13) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4c; 0x89; 0x4e; 0x70;  (* MOV (Memop Quadword (%% (rsi,112))) (% r9) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rdi,40))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,136))) *)
  0x4c; 0x89; 0x76; 0x68;  (* MOV (Memop Quadword (%% (rsi,104))) (% r14) *)
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
  0x4c; 0x89; 0x96; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsi,128))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4c; 0x89; 0xa6; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsi,136))) (% r12) *)
  0x4d; 0x21; 0xcd;        (* AND (% r13) (% r9) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4c; 0x89; 0x6e; 0x78;  (* MOV (Memop Quadword (%% (rsi,120))) (% r13) *)
  0x4d; 0x09; 0xc1;        (* OR (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4c; 0x89; 0x8e; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsi,152))) (% r9) *)
  0x4d; 0x21; 0xf0;        (* AND (% r8) (% r14) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x4c; 0x89; 0x86; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsi,144))) (% r8) *)
  0x48; 0x33; 0x57; 0x10;  (* XOR (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x33; 0x6f; 0x40;  (* XOR (% rbp) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xc1; 0xc2; 0x3e;  (* ROL (% rdx) (Imm8 (word 62)) *)
  0x48; 0x33; 0x8f; 0xa8; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rdi,168))) *)
  0x48; 0xc1; 0xc5; 0x37;  (* ROL (% rbp) (Imm8 (word 55)) *)
  0x48; 0x33; 0x47; 0x70;  (* XOR (% rax) (Memop Quadword (%% (rdi,112))) *)
  0x48; 0xc1; 0xc1; 0x02;  (* ROL (% rcx) (Imm8 (word 2)) *)
  0x48; 0x33; 0x5f; 0x78;  (* XOR (% rbx) (Memop Quadword (%% (rdi,120))) *)
  0x48; 0x87; 0xf7;        (* XCHG (% rsi) (% rdi) *)
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
  0x4d; 0x8d; 0x7f; 0x08;  (* LEA (% r15) (%% (r15,8)) *)
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
  0x4d; 0x33; 0x0f;        (* XOR (% r9) (Memop Quadword (%% (r15,0))) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4c; 0x89; 0x0e;        (* MOV (Memop Quadword (%% (rsi,0))) (% r9) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4c; 0x89; 0x66; 0x10;  (* MOV (Memop Quadword (%% (rsi,16))) (% r12) *)
  0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
  0x4c; 0x8b; 0xa7; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,176))) *)
  0x4d; 0x31; 0xea;        (* XOR (% r10) (% r13) *)
  0x4c; 0x89; 0x56; 0x08;  (* MOV (Memop Quadword (%% (rsi,8))) (% r10) *)
  0x4d; 0x21; 0xc5;        (* AND (% r13) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x48;  (* MOV (% r9) (Memop Quadword (%% (rdi,72))) *)
  0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
  0x4c; 0x8b; 0x57; 0x50;  (* MOV (% r10) (Memop Quadword (%% (rdi,80))) *)
  0x4c; 0x89; 0x6e; 0x20;  (* MOV (Memop Quadword (%% (rsi,32))) (% r13) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x47; 0x18;  (* MOV (% r8) (Memop Quadword (%% (rdi,24))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,128))) *)
  0x4c; 0x89; 0x76; 0x18;  (* MOV (Memop Quadword (%% (rsi,24))) (% r14) *)
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
  0x4c; 0x89; 0x46; 0x40;  (* MOV (Memop Quadword (%% (rsi,64))) (% r8) *)
  0x4d; 0x89; 0xce;        (* MOV (% r14) (% r9) *)
  0x4d; 0x21; 0xe9;        (* AND (% r9) (% r13) *)
  0x4c; 0x8b; 0x47; 0x08;  (* MOV (% r8) (Memop Quadword (%% (rdi,8))) *)
  0x4d; 0x31; 0xe1;        (* XOR (% r9) (% r12) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x4c; 0x89; 0x4e; 0x48;  (* MOV (Memop Quadword (%% (rsi,72))) (% r9) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4c; 0x8b; 0x4f; 0x38;  (* MOV (% r9) (Memop Quadword (%% (rdi,56))) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x4c; 0x89; 0x66; 0x38;  (* MOV (Memop Quadword (%% (rsi,56))) (% r12) *)
  0x4d; 0x21; 0xd3;        (* AND (% r11) (% r10) *)
  0x4c; 0x8b; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,160))) *)
  0x4d; 0x31; 0xf3;        (* XOR (% r11) (% r14) *)
  0x4c; 0x89; 0x5e; 0x30;  (* MOV (Memop Quadword (%% (rsi,48))) (% r11) *)
  0x4d; 0x09; 0xd6;        (* OR (% r14) (% r10) *)
  0x4c; 0x8b; 0x57; 0x68;  (* MOV (% r10) (Memop Quadword (%% (rdi,104))) *)
  0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
  0x4c; 0x8b; 0x9f; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,152))) *)
  0x4c; 0x89; 0x76; 0x28;  (* MOV (Memop Quadword (%% (rsi,40))) (% r14) *)
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
  0x4c; 0x89; 0x56; 0x58;  (* MOV (Memop Quadword (%% (rsi,88))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x4c; 0x8b; 0x57; 0x58;  (* MOV (% r10) (Memop Quadword (%% (rdi,88))) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4c; 0x89; 0x66; 0x60;  (* MOV (Memop Quadword (%% (rsi,96))) (% r12) *)
  0x4d; 0x09; 0xcd;        (* OR (% r13) (% r9) *)
  0x4c; 0x8b; 0xa7; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r12) (Memop Quadword (%% (rdi,184))) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4c; 0x89; 0x6e; 0x50;  (* MOV (Memop Quadword (%% (rsi,80))) (% r13) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4c; 0x89; 0x4e; 0x70;  (* MOV (Memop Quadword (%% (rsi,112))) (% r9) *)
  0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
  0x4c; 0x8b; 0x4f; 0x28;  (* MOV (% r9) (Memop Quadword (%% (rdi,40))) *)
  0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
  0x4c; 0x8b; 0x9f; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rdi,136))) *)
  0x4c; 0x89; 0x76; 0x68;  (* MOV (Memop Quadword (%% (rsi,104))) (% r14) *)
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
  0x4c; 0x89; 0x96; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsi,128))) (% r10) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4c; 0x89; 0xa6; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsi,136))) (% r12) *)
  0x4d; 0x21; 0xcd;        (* AND (% r13) (% r9) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4c; 0x89; 0x6e; 0x78;  (* MOV (Memop Quadword (%% (rsi,120))) (% r13) *)
  0x4d; 0x09; 0xc1;        (* OR (% r9) (% r8) *)
  0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
  0x4c; 0x89; 0x8e; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsi,152))) (% r9) *)
  0x4d; 0x21; 0xf0;        (* AND (% r8) (% r14) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x4c; 0x89; 0x86; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsi,144))) (% r8) *)
  0x48; 0x33; 0x57; 0x10;  (* XOR (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x33; 0x6f; 0x40;  (* XOR (% rbp) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xc1; 0xc2; 0x3e;  (* ROL (% rdx) (Imm8 (word 62)) *)
  0x48; 0x33; 0x8f; 0xa8; 0x00; 0x00; 0x00;
                           (* XOR (% rcx) (Memop Quadword (%% (rdi,168))) *)
  0x48; 0xc1; 0xc5; 0x37;  (* ROL (% rbp) (Imm8 (word 55)) *)
  0x48; 0x33; 0x47; 0x70;  (* XOR (% rax) (Memop Quadword (%% (rdi,112))) *)
  0x48; 0xc1; 0xc1; 0x02;  (* ROL (% rcx) (Imm8 (word 2)) *)
  0x48; 0x33; 0x5f; 0x78;  (* XOR (% rbx) (Memop Quadword (%% (rdi,120))) *)
  0x48; 0x87; 0xf7;        (* XCHG (% rsi) (% rdi) *)
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
  0x4d; 0x8d; 0x7f; 0x08;  (* LEA (% r15) (%% (r15,8)) *)
  0x41; 0x58;              (* POP (% r8) *)
  0x49; 0x83; 0xc0; 0x01;  (* ADD (% r8) (Imm8 (word 1)) *)
  0x49; 0x83; 0xf8; 0x0c;  (* CMP (% r8) (Imm8 (word 12)) *)
  0x0f; 0x85; 0x36; 0xfa; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294965814)) *)
  0x4d; 0x8d; 0xbf; 0x40; 0xff; 0xff; 0xff;
                           (* LEA (% r15) (%% (r15,18446744073709551424)) *)
  0x48; 0xf7; 0x57; 0x08;  (* NOT (Memop Quadword (%% (rdi,8))) *)
  0x48; 0xf7; 0x57; 0x10;  (* NOT (Memop Quadword (%% (rdi,16))) *)
  0x48; 0xf7; 0x57; 0x40;  (* NOT (Memop Quadword (%% (rdi,64))) *)
  0x48; 0xf7; 0x57; 0x60;  (* NOT (Memop Quadword (%% (rdi,96))) *)
  0x48; 0xf7; 0x97; 0x88; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,136))) *)
  0x48; 0xf7; 0x97; 0xa0; 0x00; 0x00; 0x00;
                           (* NOT (Memop Quadword (%% (rdi,160))) *)
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

 let MLKEM_KECCAK_F1600_EXEC_spec = X86_MK_EXEC_RULE mlkem_keccak_f1600_mc_spec;;

 let wordlist_from_memory = define
 `wordlist_from_memory(a,0) s = [] /\
  wordlist_from_memory(a,SUC n) s =
  APPEND (wordlist_from_memory(a,n) s)
         [read (memory :> bytes64(word_add a (word(8 * n)))) s]`;;

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
  and filt = can (term_match [] `wordlist_from_memory(a,NUMERAL n) s`) in
  conv o check filt;;


  let MLKEM_KECCAK_F1600_SPEC = prove(
  `forall rc_pointer pc:num stackpointer:int64 returnaddress bitstate_in.
  nonoverlapping_modulo (2 EXP 64) (pc,0x661) (val  (word_sub stackpointer (word 256)), 264) /\
  nonoverlapping_modulo (2 EXP 64) (pc, 0x661) (val (word_add (bitstate_in) (word 0):int64),200) /\
  nonoverlapping_modulo (2 EXP 64) (pc, 0x661) (val (word_add (rc_pointer) (word 0):int64),192) /\

  nonoverlapping_modulo (2 EXP 64) (val (word_add (bitstate_in) (word 0):int64),200) (val (word_sub stackpointer (word 256)),264) /\
  nonoverlapping_modulo (2 EXP 64) (val (word_add (bitstate_in) (word 0):int64),200) (val (word_add (rc_pointer) (word 0):int64),192) /\

  nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 256)), 264) (val (word_add (rc_pointer) (word 0):int64),192)

  // RSI is used to pass the rc bitstate_out address, however, it is later assigned as a bitsate' 
  // bitstate_in/bitstate_in' are used as input/output value for the keccak loop
  // each iterantion uses bitstate_in as an input value and stores the resulting bitstate_in in output bitstate_in'
  // after termination of an iteration, input/output bitstate_in values are swapped (rsi <-> rdi): 
  // the output of the previous interaiton will serve as an input to the following iteration
      ==> ensures x86
  // Precondition
  (\s. bytes_loaded s (word pc) mlkem_keccak_f1600_mc_spec /\
       read RIP s = word pc /\
       read RSP s = stackpointer /\
       read RDI s = bitstate_in /\
       read (memory :> bytes64 stackpointer) s = returnaddress /\
       C_ARGUMENTS [bitstate_in; rc_pointer] s /\
                wordlist_from_memory(bitstate_in, 25) s = A /\
                wordlist_from_memory(rc_pointer, 24) s = rc_table
                )
  // Postcondition
  (\s.  read RIP s = returnaddress /\
        read RSP s = word_add stackpointer (word 8) /\
        wordlist_from_memory(bitstate_in, 25) s = keccak_x2 12 A)
  (MAYCHANGE [RIP;RSP;RAX;RBX;RCX;RDX;RBP;R8;R9;R10;R11;R12;R13;R14;R15;RDI;RSI] ,, MAYCHANGE SOME_FLAGS,, 
  MAYCHANGE [memory :> bytes (word_sub stackpointer (word 256), 256)],,
  MAYCHANGE [memory :> bytes (bitstate_in, 200)]
  )`
  ,

  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`rc_pointer:int64`; `pc:num`] THEN
WORD_FORALL_OFFSET_TAC 256 THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN

    MAP_EVERY X_GEN_TAC [`stackpointer:int64`;`returnaddress:int64`;`bitstate_in:int64`] THEN


  REWRITE_TAC[fst MLKEM_KECCAK_F1600_EXEC_spec] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  
  REPEAT STRIP_TAC THEN

    ENSURES_WHILE_PAUP_TAC
    `0` (* loop_body begin number *)
    `24` (* loop_body end number *)
    `pc + 0x60` (* loop body start PC *)
    `pc + 0x624` (* loop backedge branch PC -- including the jmp *) 
    `\i s. // loop invariant at the end of the iteration
            (read R8 s = word i /\
            read RDI s = bitstate_in /\
            read RSP s = word_add stackpointer (word 8) /\
            read RSI s = word_add stackpointer (word 8) /\
            wordlist_from_memory(rc_pointer,24) s = rc_table /\
            read (memory :> bytes64 (word_add stackpointer (word 256))) s = returnaddress /\
            [ read X1 s; read X6 s; read X11 s; read X16 s; read X21 s;
              read X2 s; read X7 s; read X12 s; read X17 s; read X22 s;
              read X3 s; read X8 s; read X13 s; read X28 s; read X23 s;
              read X4 s; read X9 s; read X14 s; read X19 s; read X24 s;
              read X5 s; read X10 s; read X15 s; read X20 s; read X25 s] = keccak i A)  /\
           // loop backedge condition
           (read ZF s <=> i = 24)` THEN

    REPEAT CONJ_TAC THENL 
    [
      (* loop_body begin < loop_body end *)
      ARITH_TAC;

      REWRITE_TAC[condition_semantics] THEN REPEAT CONJ_TAC THENL
      REWRITE_TAC[rc_table; CONS_11; GSYM CONJ_ASSOC; WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`] THEN

      (* entrance to the loop *)
      (* Use  X86_SIM_TAC which is ENSURES_INIT_TAC + X86_STEPS_TAC +
        ENSURES_FINAL_STATE_TAC + some post-processing. *)
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_spec (1--21);

      (* the body of the loop *)
      REPEAT STRIP_TAC THEN

      REWRITE_TAC[condition_semantics] THEN REPEAT CONJ_TAC THENL
      REWRITE_TAC[rc_table; CONS_11; GSYM CONJ_ASSOC; WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`] THEN

     X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_spec (1--394) THEN

      REPEAT CONJ_TAC THENL
      [
        CONV_TAC WORD_RULE;

        REWRITE_TAC [WORD_BLAST `word_add x (word 18446744073709551605):int64 =
                             word_sub x (word 11)`] THEN

        REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
        REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN

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
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_spec [1];

       REWRITE_TAC[condition_semantics] THEN REPEAT CONJ_TAC THENL
      REWRITE_TAC[rc_table; CONS_11; GSYM CONJ_ASSOC; WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`] THEN
      

      (* Loop exit to the end of the program *)
      X86_SIM_TAC MLKEM_KECCAK_F1600_EXEC_spec (1--16);
  ]);
