(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

 needs "x86/proofs/base.ml";;

(******************************************************************************
  Proving a mlkem_keccak_f1600 property about program 'mlkem_keccak_f1600.S'
******************************************************************************)

(* The following program
 
mlkem/mlkem_keccak_f1600_obj.o:     file format elf64-x86-64

  ... performs KeccakF1600 cryptography algorithm along with saving 
  the callee-saved registers on the stack.
*)

let mlkem_keccak_f1600_mc_obj,iotas_x86_64_obj = define_coda_literal_from_elf
  "mlkem_keccak_f1600_mc_obj" "iotas_x86_64_obj" 
  "x86/mlkem/mlkem_keccak_f1600_obj.o"         
  [
    0x53;                    (* PUSH (% rbx) *)
    0x55;                    (* PUSH (% rbp) *)
    0x41; 0x54;              (* PUSH (% r12) *)
    0x41; 0x55;              (* PUSH (% r13) *)
    0x41; 0x56;              (* PUSH (% r14) *)
    0x41; 0x57;              (* PUSH (% r15) *)
    0x48; 0x8d; 0x7f; 0x64;  (* LEA (% rdi) (%% (rdi,100)) *)
    0x48; 0x81; 0xec; 0xc8; 0x00; 0x00; 0x00;
                             (* SUB (% rsp) (Imm32 (word 200)) *)
    0x48; 0xf7; 0x57; 0xa4;  (* NOT (Memop Quadword (%% (rdi,18446744073709551524))) *)
    0x48; 0xf7; 0x57; 0xac;  (* NOT (Memop Quadword (%% (rdi,18446744073709551532))) *)
    0x48; 0xf7; 0x57; 0xdc;  (* NOT (Memop Quadword (%% (rdi,18446744073709551580))) *)
    0x48; 0xf7; 0x57; 0xfc;  (* NOT (Memop Quadword (%% (rdi,18446744073709551612))) *)
    0x48; 0xf7; 0x57; 0x24;  (* NOT (Memop Quadword (%% (rdi,36))) *)
    0x48; 0xf7; 0x57; 0x3c;  (* NOT (Memop Quadword (%% (rdi,60))) *)
    0x4c; 0x8d; 0x3d; 0x0c; 0x04; 0x00; 0x00;
                             (* LEA (% r15) (Riprel (word 1036)) *)
    0x48; 0x8d; 0x74; 0x24; 0x64;
                             (* LEA (% rsi) (%% (rsp,100)) *)
    0x48; 0x8b; 0x47; 0x3c;  (* MOV (% rax) (Memop Quadword (%% (rdi,60))) *)
    0x48; 0x8b; 0x5f; 0x44;  (* MOV (% rbx) (Memop Quadword (%% (rdi,68))) *)
    0x48; 0x8b; 0x4f; 0x4c;  (* MOV (% rcx) (Memop Quadword (%% (rdi,76))) *)
    0x48; 0x8b; 0x57; 0x54;  (* MOV (% rdx) (Memop Quadword (%% (rdi,84))) *)
    0x48; 0x8b; 0x6f; 0x5c;  (* MOV (% rbp) (Memop Quadword (%% (rdi,92))) *)
    0x4c; 0x8b; 0x47; 0x9c;  (* MOV (% r8) (Memop Quadword (%% (rdi,18446744073709551516))) *)
    0x4c; 0x8b; 0x4f; 0xcc;  (* MOV (% r9) (Memop Quadword (%% (rdi,18446744073709551564))) *)
    0x4c; 0x8b; 0x57; 0xfc;  (* MOV (% r10) (Memop Quadword (%% (rdi,18446744073709551612))) *)
    0x4c; 0x8b; 0x5f; 0x2c;  (* MOV (% r11) (Memop Quadword (%% (rdi,44))) *)
    0x48; 0x33; 0x4f; 0xac;  (* XOR (% rcx) (Memop Quadword (%% (rdi,18446744073709551532))) *)
    0x48; 0x33; 0x57; 0xb4;  (* XOR (% rdx) (Memop Quadword (%% (rdi,18446744073709551540))) *)
    0x4c; 0x31; 0xc0;        (* XOR (% rax) (% r8) *)
    0x48; 0x33; 0x5f; 0xa4;  (* XOR (% rbx) (Memop Quadword (%% (rdi,18446744073709551524))) *)
    0x48; 0x33; 0x4f; 0xd4;  (* XOR (% rcx) (Memop Quadword (%% (rdi,18446744073709551572))) *)
    0x48; 0x33; 0x47; 0xc4;  (* XOR (% rax) (Memop Quadword (%% (rdi,18446744073709551556))) *)
    0x49; 0x89; 0xec;        (* MOV (% r12) (% rbp) *)
    0x48; 0x33; 0x6f; 0xbc;  (* XOR (% rbp) (Memop Quadword (%% (rdi,18446744073709551548))) *)
    0x4c; 0x31; 0xd1;        (* XOR (% rcx) (% r10) *)
    0x48; 0x33; 0x47; 0xec;  (* XOR (% rax) (Memop Quadword (%% (rdi,18446744073709551596))) *)
    0x48; 0x33; 0x57; 0xdc;  (* XOR (% rdx) (Memop Quadword (%% (rdi,18446744073709551580))) *)
    0x4c; 0x31; 0xcb;        (* XOR (% rbx) (% r9) *)
    0x48; 0x33; 0x6f; 0xe4;  (* XOR (% rbp) (Memop Quadword (%% (rdi,18446744073709551588))) *)
    0x48; 0x33; 0x4f; 0x24;  (* XOR (% rcx) (Memop Quadword (%% (rdi,36))) *)
    0x48; 0x33; 0x47; 0x14;  (* XOR (% rax) (Memop Quadword (%% (rdi,20))) *)
    0x48; 0x33; 0x57; 0x04;  (* XOR (% rdx) (Memop Quadword (%% (rdi,4))) *)
    0x48; 0x33; 0x5f; 0xf4;  (* XOR (% rbx) (Memop Quadword (%% (rdi,18446744073709551604))) *)
    0x48; 0x33; 0x6f; 0x0c;  (* XOR (% rbp) (Memop Quadword (%% (rdi,12))) *)
    0x49; 0x89; 0xcd;        (* MOV (% r13) (% rcx) *)
    0x48; 0xd1; 0xc1;        (* ROL (% rcx) (Imm8 (word 1)) *)
    0x48; 0x31; 0xc1;        (* XOR (% rcx) (% rax) *)
    0x4c; 0x31; 0xda;        (* XOR (% rdx) (% r11) *)
    0x48; 0xd1; 0xc0;        (* ROL (% rax) (Imm8 (word 1)) *)
    0x48; 0x31; 0xd0;        (* XOR (% rax) (% rdx) *)
    0x48; 0x33; 0x5f; 0x1c;  (* XOR (% rbx) (Memop Quadword (%% (rdi,28))) *)
    0x48; 0xd1; 0xc2;        (* ROL (% rdx) (Imm8 (word 1)) *)
    0x48; 0x31; 0xda;        (* XOR (% rdx) (% rbx) *)
    0x48; 0x33; 0x6f; 0x34;  (* XOR (% rbp) (Memop Quadword (%% (rdi,52))) *)
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
    0x4d; 0x8d; 0x7f; 0x08;  (* LEA (% r15) (%% (r15,8)) *)
    0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
    0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
    0x4c; 0x89; 0x4e; 0x9c;  (* MOV (Memop Quadword (%% (rsi,18446744073709551516))) (% r9) *)
    0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
    0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
    0x4c; 0x89; 0x66; 0xac;  (* MOV (Memop Quadword (%% (rsi,18446744073709551532))) (% r12) *)
    0x4d; 0x09; 0xda;        (* OR (% r10) (% r11) *)
    0x4c; 0x8b; 0x67; 0x4c;  (* MOV (% r12) (Memop Quadword (%% (rdi,76))) *)
    0x4d; 0x31; 0xea;        (* XOR (% r10) (% r13) *)
    0x4c; 0x89; 0x56; 0xa4;  (* MOV (Memop Quadword (%% (rsi,18446744073709551524))) (% r10) *)
    0x4d; 0x21; 0xc5;        (* AND (% r13) (% r8) *)
    0x4c; 0x8b; 0x4f; 0xe4;  (* MOV (% r9) (Memop Quadword (%% (rdi,18446744073709551588))) *)
    0x4d; 0x31; 0xf5;        (* XOR (% r13) (% r14) *)
    0x4c; 0x8b; 0x57; 0xec;  (* MOV (% r10) (Memop Quadword (%% (rdi,18446744073709551596))) *)
    0x4c; 0x89; 0x6e; 0xbc;  (* MOV (Memop Quadword (%% (rsi,18446744073709551548))) (% r13) *)
    0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
    0x4c; 0x8b; 0x47; 0xb4;  (* MOV (% r8) (Memop Quadword (%% (rdi,18446744073709551540))) *)
    0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
    0x4c; 0x8b; 0x5f; 0x1c;  (* MOV (% r11) (Memop Quadword (%% (rdi,28))) *)
    0x4c; 0x89; 0x76; 0xb4;  (* MOV (Memop Quadword (%% (rsi,18446744073709551540))) (% r14) *)
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
    0x4c; 0x89; 0x46; 0xdc;  (* MOV (Memop Quadword (%% (rsi,18446744073709551580))) (% r8) *)
    0x4d; 0x89; 0xce;        (* MOV (% r14) (% r9) *)
    0x4d; 0x21; 0xe9;        (* AND (% r9) (% r13) *)
    0x4c; 0x8b; 0x47; 0xa4;  (* MOV (% r8) (Memop Quadword (%% (rdi,18446744073709551524))) *)
    0x4d; 0x31; 0xe1;        (* XOR (% r9) (% r12) *)
    0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
    0x4c; 0x89; 0x4e; 0xe4;  (* MOV (Memop Quadword (%% (rsi,18446744073709551588))) (% r9) *)
    0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
    0x4c; 0x8b; 0x4f; 0xd4;  (* MOV (% r9) (Memop Quadword (%% (rdi,18446744073709551572))) *)
    0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
    0x4c; 0x89; 0x66; 0xd4;  (* MOV (Memop Quadword (%% (rsi,18446744073709551572))) (% r12) *)
    0x4d; 0x21; 0xd3;        (* AND (% r11) (% r10) *)
    0x4c; 0x8b; 0x67; 0x3c;  (* MOV (% r12) (Memop Quadword (%% (rdi,60))) *)
    0x4d; 0x31; 0xf3;        (* XOR (% r11) (% r14) *)
    0x4c; 0x89; 0x5e; 0xcc;  (* MOV (Memop Quadword (%% (rsi,18446744073709551564))) (% r11) *)
    0x4d; 0x09; 0xd6;        (* OR (% r14) (% r10) *)
    0x4c; 0x8b; 0x57; 0x04;  (* MOV (% r10) (Memop Quadword (%% (rdi,4))) *)
    0x4d; 0x31; 0xee;        (* XOR (% r14) (% r13) *)
    0x4c; 0x8b; 0x5f; 0x34;  (* MOV (% r11) (Memop Quadword (%% (rdi,52))) *)
    0x4c; 0x89; 0x76; 0xc4;  (* MOV (Memop Quadword (%% (rsi,18446744073709551556))) (% r14) *)
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
    0x4c; 0x89; 0x56; 0xf4;  (* MOV (Memop Quadword (%% (rsi,18446744073709551604))) (% r10) *)
    0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
    0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
    0x4c; 0x8b; 0x57; 0xf4;  (* MOV (% r10) (Memop Quadword (%% (rdi,18446744073709551604))) *)
    0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
    0x4c; 0x89; 0x66; 0xfc;  (* MOV (Memop Quadword (%% (rsi,18446744073709551612))) (% r12) *)
    0x4d; 0x09; 0xcd;        (* OR (% r13) (% r9) *)
    0x4c; 0x8b; 0x67; 0x54;  (* MOV (% r12) (Memop Quadword (%% (rdi,84))) *)
    0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
    0x4c; 0x89; 0x6e; 0xec;  (* MOV (Memop Quadword (%% (rsi,18446744073709551596))) (% r13) *)
    0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
    0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
    0x4c; 0x89; 0x4e; 0x0c;  (* MOV (Memop Quadword (%% (rsi,12))) (% r9) *)
    0x4d; 0x09; 0xc6;        (* OR (% r14) (% r8) *)
    0x4c; 0x8b; 0x4f; 0xc4;  (* MOV (% r9) (Memop Quadword (%% (rdi,18446744073709551556))) *)
    0x4d; 0x31; 0xde;        (* XOR (% r14) (% r11) *)
    0x4c; 0x8b; 0x5f; 0x24;  (* MOV (% r11) (Memop Quadword (%% (rdi,36))) *)
    0x4c; 0x89; 0x76; 0x04;  (* MOV (Memop Quadword (%% (rsi,4))) (% r14) *)
    0x4c; 0x8b; 0x47; 0xbc;  (* MOV (% r8) (Memop Quadword (%% (rdi,18446744073709551548))) *)
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
    0x4c; 0x89; 0x56; 0x1c;  (* MOV (Memop Quadword (%% (rsi,28))) (% r10) *)
    0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
    0x4d; 0x09; 0xdc;        (* OR (% r12) (% r11) *)
    0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
    0x4c; 0x89; 0x66; 0x24;  (* MOV (Memop Quadword (%% (rsi,36))) (% r12) *)
    0x4d; 0x21; 0xcd;        (* AND (% r13) (% r9) *)
    0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
    0x4c; 0x89; 0x6e; 0x14;  (* MOV (Memop Quadword (%% (rsi,20))) (% r13) *)
    0x4d; 0x09; 0xc1;        (* OR (% r9) (% r8) *)
    0x4d; 0x31; 0xf1;        (* XOR (% r9) (% r14) *)
    0x4c; 0x89; 0x4e; 0x34;  (* MOV (Memop Quadword (%% (rsi,52))) (% r9) *)
    0x4d; 0x21; 0xf0;        (* AND (% r8) (% r14) *)
    0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
    0x4c; 0x89; 0x46; 0x2c;  (* MOV (Memop Quadword (%% (rsi,44))) (% r8) *)
    0x48; 0x33; 0x57; 0xac;  (* XOR (% rdx) (Memop Quadword (%% (rdi,18446744073709551532))) *)
    0x48; 0x33; 0x6f; 0xdc;  (* XOR (% rbp) (Memop Quadword (%% (rdi,18446744073709551580))) *)
    0x48; 0xc1; 0xc2; 0x3e;  (* ROL (% rdx) (Imm8 (word 62)) *)
    0x48; 0x33; 0x4f; 0x44;  (* XOR (% rcx) (Memop Quadword (%% (rdi,68))) *)
    0x48; 0xc1; 0xc5; 0x37;  (* ROL (% rbp) (Imm8 (word 55)) *)
    0x48; 0x33; 0x47; 0x0c;  (* XOR (% rax) (Memop Quadword (%% (rdi,12))) *)
    0x48; 0xc1; 0xc1; 0x02;  (* ROL (% rcx) (Imm8 (word 2)) *)
    0x48; 0x33; 0x5f; 0x14;  (* XOR (% rbx) (Memop Quadword (%% (rdi,20))) *)
    0x48; 0x87; 0xf7;        (* XCHG (% rsi) (% rdi) *)
    0x48; 0xc1; 0xc0; 0x27;  (* ROL (% rax) (Imm8 (word 39)) *)
    0x48; 0xc1; 0xc3; 0x29;  (* ROL (% rbx) (Imm8 (word 41)) *)
    0x49; 0x89; 0xd5;        (* MOV (% r13) (% rdx) *)
    0x48; 0x21; 0xea;        (* AND (% rdx) (% rbp) *)
    0x48; 0xf7; 0xd5;        (* NOT (% rbp) *)
    0x48; 0x31; 0xca;        (* XOR (% rdx) (% rcx) *)
    0x48; 0x89; 0x57; 0x5c;  (* MOV (Memop Quadword (%% (rdi,92))) (% rdx) *)
    0x49; 0x89; 0xc6;        (* MOV (% r14) (% rax) *)
    0x48; 0x21; 0xe8;        (* AND (% rax) (% rbp) *)
    0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
    0x48; 0x89; 0x47; 0x3c;  (* MOV (Memop Quadword (%% (rdi,60))) (% rax) *)
    0x49; 0x09; 0xcd;        (* OR (% r13) (% rcx) *)
    0x49; 0x31; 0xdd;        (* XOR (% r13) (% rbx) *)
    0x4c; 0x89; 0x6f; 0x54;  (* MOV (Memop Quadword (%% (rdi,84))) (% r13) *)
    0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
    0x4c; 0x31; 0xf1;        (* XOR (% rcx) (% r14) *)
    0x48; 0x89; 0x4f; 0x4c;  (* MOV (Memop Quadword (%% (rdi,76))) (% rcx) *)
    0x4c; 0x09; 0xf3;        (* OR (% rbx) (% r14) *)
    0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
    0x48; 0x89; 0x5f; 0x44;  (* MOV (Memop Quadword (%% (rdi,68))) (% rbx) *)
    0x48; 0x89; 0xd5;        (* MOV (% rbp) (% rdx) *)
    0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
    0x49; 0xf7; 0xc7; 0xff; 0x00; 0x00; 0x00;
                             (* TEST (% r15) (Imm32 (word 255)) *)
    0x0f; 0x85; 0x51; 0xfd; 0xff; 0xff;
                             (* JNE (Imm32 (word 4294966609)) *)
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
    0xc3;                    (* RET *)
    0xe9; 0xca; 0x00; 0x00; 0x00
                             (* JMP (Imm32 (word 202)) *)
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
   0; 15; 31; 64; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0;
   0; 0; 0; 130; 128; 0; 0; 0; 0; 0; 0; 138; 128; 0; 0; 0; 0; 0; 128; 0; 128;
   0; 128; 0; 0; 0; 128; 139; 128; 0; 0; 0; 0; 0; 0; 1; 0; 0; 128; 0; 0; 0; 0;
   129; 128; 0; 128; 0; 0; 0; 128; 9; 128; 0; 0; 0; 0; 0; 128; 138; 0; 0; 0; 0;
   0; 0; 0; 136; 0; 0; 0; 0; 0; 0; 0; 9; 128; 0; 128; 0; 0; 0; 0; 10; 0; 0;
   128; 0; 0; 0; 0; 139; 128; 0; 128; 0; 0; 0; 0; 139; 0; 0; 0; 0; 0; 0; 128;
   137; 128; 0; 0; 0; 0; 0; 128; 3; 128; 0; 0; 0; 0; 0; 128; 2; 128; 0; 0; 0;
   0; 0; 128; 128; 0; 0; 0; 0; 0; 0; 128; 10; 128; 0; 0; 0; 0; 0; 0; 10; 0; 0;
   128; 0; 0; 0; 128; 129; 128; 0; 128; 0; 0; 0; 128; 128; 128; 0; 0; 0; 0; 0;
   128; 1; 0; 0; 128; 0; 0; 0; 0; 8; 128; 0; 128; 0; 0; 0; 128];;


let mlkem_keccak_f1600_tmc = define_trimmed "mlkem_keccak_f1600_tmc" mlkem_keccak_f1600_mc_obj;;

let EXEC =
  X86_MK_EXEC_RULE mlkem_keccak_f1600_tmc;;

let MLKEM_KECCAK_F1600_SPEC = prove(
  `forall pc:num stackpointer:int64 rdi_1:int64.
  nonoverlapping_modulo (2 EXP 64) (pc, 0x501) (val (word_sub stackpointer (word 248):int64),248) /\
  nonoverlapping_modulo (2 EXP 64) (pc, 0x501) (val (word_add (rdi_1) (word 0):int64),200)
    ==> ensures x86
  // Precondition
  (\s. bytes_loaded s (word pc) mlkem_keccak_f1600_tmc /\
       read RIP s = word pc /\
       read RSP s = stackpointer  /\
       read RDI s = rdi_1)
  // Postcondition
  (\s. read RIP s = word (pc+0x501))
  (MAYCHANGE [RIP;RSP;RAX;RBX;RCX;RDX;RBP;R8;R9;R10;R11;R12;R13;R14;R15;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,, 
  MAYCHANGE [memory :> bytes (word_sub stackpointer (word 248), 248)],, 
  MAYCHANGE [memory :> bytes (word_add rdi_1 (word 0), 200)])`
  ,

  REWRITE_TAC[fst EXEC] THEN 
  MAP_EVERY X_GEN_TAC [`pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 248 THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`;`rdi_1:int64`] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN 
  ENSURES_INIT_TAC "s0" THEN

  X86_STEPS_TAC EXEC (1--1) THEN
  X86_STEPS_TAC EXEC (2--2) THEN
  X86_STEPS_TAC EXEC (3--3) THEN
  X86_STEPS_TAC EXEC (4--18) THEN
  X86_STEPS_TAC EXEC (19--213) THEN
  X86_STEPS_TAC EXEC (214--214) THEN
  X86_STEPS_TAC EXEC (215--215) THEN

  ENSURES_FINAL_STATE_TAC THEN

  ASM_REWRITE_TAC[]
  );;
