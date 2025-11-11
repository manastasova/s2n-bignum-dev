(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

 Sys.chdir "/home/ubuntu/hol/my_s2n-bignum-dev/s2n-bignum-dev";;
 needs "x86/proofs/base.ml";;
 needs "x86/proofs/utils/keccak_spec.ml";;

(**** print_literal_from_elf "x86/sha3/sha3_keccak4_f1600.o";;
****)

let sha3_keccak4_f1600_mc = define_assert_from_elf
  "sha3_keccak4_f1600_mc" "x86/sha3/sha3_keccak4_f1600.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x48; 0x89; 0xe5;        (* MOV (% rbp) (% rsp) *)
  0x48; 0x83; 0xe4; 0xe0;  (* AND (% rsp) (Imm8 (word 224)) *)
  0x48; 0x81; 0xec; 0x60; 0x03; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 864)) *)
  0xc5; 0xfe; 0x6f; 0x07;  (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,200))) *)
  0xc5; 0xfe; 0x6f; 0x97; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rdi,400))) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,600))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xe9;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xf3;  (* VPUNPCKLQDQ (%_% ymm6) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0xed; 0x6d; 0xfb;  (* VPUNPCKHQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc6; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd6; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm6) (Imm8 (word 49)) *)
  0xc4; 0xe3; 0x55; 0x46; 0xcf; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm5) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x55; 0x46; 0xdf; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm5) (%_% ymm7) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0xe8;  (* VMOVDQA (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x0c; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm1) *)
  0xc5; 0xfd; 0x7f; 0x54; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x5c; 0x24; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rsp,64))) (%_% ymm3) *)
  0xc5; 0xfe; 0x6f; 0x47; 0x20;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0xe8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,232))) *)
  0xc5; 0xfe; 0x6f; 0x97; 0xb0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rdi,432))) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0x78; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,632))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc7; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x7f; 0x44; 0x24; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rsp,96))) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x8c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,128))) (%_% ymm1) *)
  0xc5; 0xfd; 0x7f; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,160))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,192))) (%_% ymm3) *)
  0xc5; 0xfe; 0x6f; 0x47; 0x40;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,264))) *)
  0xc5; 0xfe; 0x6f; 0x97; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rdi,464))) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0x98; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,664))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc7; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x7f; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,224))) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x8c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,256))) (%_% ymm1) *)
  0xc5; 0xfd; 0x7f; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,288))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,320))) (%_% ymm3) *)
  0xc5; 0xfe; 0x6f; 0x47; 0x60;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0x28; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,296))) *)
  0xc5; 0xfe; 0x6f; 0x97; 0xf0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rdi,496))) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0xb8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,696))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc7; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x7f; 0x84; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,352))) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x8c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,384))) (%_% ymm1) *)
  0xc5; 0xfd; 0x7f; 0x94; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,416))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,448))) (%_% ymm3) *)
  0xc5; 0xfe; 0x6f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0x48; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,328))) *)
  0xc5; 0xfe; 0x6f; 0x97; 0x10; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rdi,528))) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0xd8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,728))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc7; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x7f; 0x84; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,480))) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,512))) (%_% ymm1) *)
  0xc5; 0xfd; 0x7f; 0x94; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,544))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x9c; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,576))) (%_% ymm3) *)
  0xc5; 0xfe; 0x6f; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm0) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0xfe; 0x6f; 0x8f; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm1) (Memop Word256 (%% (rdi,360))) *)
  0xc5; 0xfe; 0x6f; 0x97; 0x30; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm2) (Memop Word256 (%% (rdi,560))) *)
  0xc5; 0xfe; 0x6f; 0x9f; 0xf8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%% (rdi,760))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc7; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x7f; 0x84; 0x24; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,608))) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x8c; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,640))) (%_% ymm1) *)
  0xc5; 0xfd; 0x7f; 0x94; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,672))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x9c; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,704))) (%_% ymm3) *)
  0xc5; 0xfa; 0x7e; 0x8f; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVQ (%_% xmm1) (Memop Quadword (%% (rdi,192))) *)
  0xc4; 0xe3; 0xf1; 0x22; 0x8f; 0x88; 0x01; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm1) (%_% xmm1) (Memop Quadword (%% (rdi,392))) (Imm8 (word 1)) *)
  0xc5; 0xfa; 0x7e; 0x97; 0x50; 0x02; 0x00; 0x00;
                           (* VMOVQ (%_% xmm2) (Memop Quadword (%% (rdi,592))) *)
  0xc4; 0xe3; 0xe9; 0x22; 0x97; 0x18; 0x03; 0x00; 0x00; 0x01;
                           (* VPINSRQ (%_% xmm2) (%_% xmm2) (Memop Quadword (%% (rdi,792))) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x75; 0x38; 0xda; 0x01;
                           (* VINSERTI128 (%_% ymm3) (%_% ymm1) (%_% xmm2) (Imm8 (word 1)) *)
  0xc5; 0xfd; 0x7f; 0x9c; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,736))) (%_% ymm3) *)
  0x48; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 0)) *)
  0xc5; 0x7d; 0x6f; 0xa4; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rsp,128))) *)
  0xc5; 0x7d; 0x6f; 0xac; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm13) (Memop Word256 (%% (rsp,288))) *)
  0xc5; 0x7d; 0x6f; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rsp,448))) *)
  0xc5; 0x7d; 0x6f; 0x94; 0x24; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rsp,608))) *)
  0xc4; 0xc1; 0x55; 0xef; 0xcc;
                           (* VPXOR (%_% ymm1) (%_% ymm5) (%_% ymm12) *)
  0xc4; 0xc1; 0x15; 0xef; 0xc3;
                           (* VPXOR (%_% ymm0) (%_% ymm13) (%_% ymm11) *)
  0xc5; 0xf5; 0xef; 0xc8;  (* VPXOR (%_% ymm1) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xc1; 0x75; 0xef; 0xca;
                           (* VPXOR (%_% ymm1) (%_% ymm1) (%_% ymm10) *)
  0xc5; 0xfd; 0x6f; 0x24; 0x24;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rsp,0))) *)
  0xc5; 0xfd; 0x6f; 0xb4; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsp,480))) *)
  0xc5; 0x5d; 0xef; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VPXOR (%_% ymm8) (%_% ymm4) (Memop Word256 (%% (rsp,160))) *)
  0xc5; 0xcd; 0xef; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm0) (%_% ymm6) (Memop Word256 (%% (rsp,320))) *)
  0xc5; 0x3d; 0xef; 0xc0;  (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm0) *)
  0xc5; 0x3d; 0xef; 0x84; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (Memop Word256 (%% (rsp,640))) *)
  0xc5; 0xfd; 0x6f; 0x44; 0x24; 0x20;
                           (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsp,32))) *)
  0xc5; 0xfd; 0xef; 0xbc; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* VPXOR (%_% ymm7) (%_% ymm0) (Memop Word256 (%% (rsp,192))) *)
  0xc5; 0x7d; 0x6f; 0xb4; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm14) (Memop Word256 (%% (rsp,512))) *)
  0xc5; 0x8d; 0xef; 0x84; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm0) (%_% ymm14) (Memop Word256 (%% (rsp,352))) *)
  0xc5; 0xc5; 0xef; 0xf8;  (* VPXOR (%_% ymm7) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0xc5; 0xef; 0xbc; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm7) (%_% ymm7) (Memop Word256 (%% (rsp,672))) *)
  0xc5; 0xfd; 0x6f; 0x5c; 0x24; 0x40;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsp,64))) *)
  0xc5; 0xe5; 0xef; 0xb4; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* VPXOR (%_% ymm6) (%_% ymm3) (Memop Word256 (%% (rsp,224))) *)
  0xc5; 0xfd; 0x6f; 0x84; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsp,544))) *)
  0xc5; 0xfd; 0xef; 0x84; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rsp,384))) *)
  0xc5; 0xcd; 0xef; 0xf0;  (* VPXOR (%_% ymm6) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xcd; 0xef; 0xb4; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm6) (%_% ymm6) (Memop Word256 (%% (rsp,704))) *)
  0xc5; 0xfd; 0x6f; 0x64; 0x24; 0x60;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rsp,96))) *)
  0xc5; 0xdd; 0xef; 0x94; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm2) (%_% ymm4) (Memop Word256 (%% (rsp,256))) *)
  0xc5; 0xfd; 0x6f; 0x84; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsp,576))) *)
  0xc5; 0xfd; 0xef; 0x84; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rsp,416))) *)
  0xc5; 0xed; 0xef; 0xd0;  (* VPXOR (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xed; 0xef; 0x94; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm2) (%_% ymm2) (Memop Word256 (%% (rsp,736))) *)
  0xc4; 0xc1; 0x5d; 0x73; 0xf0; 0x01;
                           (* VPSLLQ (%_% ymm4) (%_% ymm8) (Imm8 (word 1)) *)
  0xc4; 0xc1; 0x7d; 0x73; 0xd0; 0x3f;
                           (* VPSRLQ (%_% ymm0) (%_% ymm8) (Imm8 (word 63)) *)
  0xc5; 0xdd; 0xeb; 0xe0;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xe5; 0x73; 0xf7; 0x01;
                           (* VPSLLQ (%_% ymm3) (%_% ymm7) (Imm8 (word 1)) *)
  0xc5; 0xfd; 0x73; 0xd7; 0x3f;
                           (* VPSRLQ (%_% ymm0) (%_% ymm7) (Imm8 (word 63)) *)
  0xc5; 0xe5; 0xeb; 0xd8;  (* VPOR (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xfd; 0x73; 0xf6; 0x01;
                           (* VPSLLQ (%_% ymm0) (%_% ymm6) (Imm8 (word 1)) *)
  0xc5; 0xb5; 0x73; 0xd6; 0x3f;
                           (* VPSRLQ (%_% ymm9) (%_% ymm6) (Imm8 (word 63)) *)
  0xc4; 0xc1; 0x7d; 0xeb; 0xc1;
                           (* VPOR (%_% ymm0) (%_% ymm0) (%_% ymm9) *)
  0xc5; 0xdd; 0xef; 0xe2;  (* VPXOR (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0xe5; 0xef; 0xd9;  (* VPXOR (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc4; 0xc1; 0x7d; 0xef; 0xc0;
                           (* VPXOR (%_% ymm0) (%_% ymm0) (%_% ymm8) *)
  0xc5; 0xbd; 0x73; 0xf2; 0x01;
                           (* VPSLLQ (%_% ymm8) (%_% ymm2) (Imm8 (word 1)) *)
  0xc5; 0xed; 0x73; 0xd2; 0x3f;
                           (* VPSRLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 63)) *)
  0xc5; 0xbd; 0xeb; 0xd2;  (* VPOR (%_% ymm2) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0x55; 0xef; 0xf4;  (* VPXOR (%_% ymm14) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0x7d; 0xef; 0x8c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* VPXOR (%_% ymm9) (%_% ymm0) (Memop Word256 (%% (rsp,192))) *)
  0xc5; 0x7d; 0x7f; 0x8c; 0x24; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,800))) (%_% ymm9) *)
  0xc5; 0x1d; 0xef; 0xfc;  (* VPXOR (%_% ymm15) (%_% ymm12) (%_% ymm4) *)
  0xc5; 0x65; 0xef; 0x24; 0x24;
                           (* VPXOR (%_% ymm12) (%_% ymm3) (Memop Word256 (%% (rsp,0))) *)
  0xc5; 0x65; 0xef; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm8) (%_% ymm3) (Memop Word256 (%% (rsp,320))) *)
  0xc5; 0x7d; 0x7f; 0xb4; 0x24; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,832))) (%_% ymm14) *)
  0xc5; 0x15; 0xef; 0xf4;  (* VPXOR (%_% ymm14) (%_% ymm13) (%_% ymm4) *)
  0xc5; 0x25; 0xef; 0xec;  (* VPXOR (%_% ymm13) (%_% ymm11) (%_% ymm4) *)
  0xc5; 0x65; 0xef; 0x9c; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VPXOR (%_% ymm11) (%_% ymm3) (Memop Word256 (%% (rsp,160))) *)
  0xc5; 0xad; 0xef; 0xe4;  (* VPXOR (%_% ymm4) (%_% ymm10) (%_% ymm4) *)
  0xc5; 0x7d; 0xef; 0x54; 0x24; 0x20;
                           (* VPXOR (%_% ymm10) (%_% ymm0) (Memop Word256 (%% (rsp,32))) *)
  0xc5; 0xc5; 0xef; 0xd2;  (* VPXOR (%_% ymm2) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0xc5; 0x73; 0xf1; 0x01;
                           (* VPSLLQ (%_% ymm7) (%_% ymm1) (Imm8 (word 1)) *)
  0xc5; 0xf5; 0x73; 0xd1; 0x3f;
                           (* VPSRLQ (%_% ymm1) (%_% ymm1) (Imm8 (word 63)) *)
  0xc5; 0xc5; 0xeb; 0xc9;  (* VPOR (%_% ymm1) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0xcd; 0xef; 0xc9;  (* VPXOR (%_% ymm1) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xe5; 0xef; 0xbc; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm7) (%_% ymm3) (Memop Word256 (%% (rsp,480))) *)
  0xc5; 0xe5; 0xef; 0x9c; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm3) (%_% ymm3) (Memop Word256 (%% (rsp,640))) *)
  0xc5; 0xed; 0xef; 0x6c; 0x24; 0x40;
                           (* VPXOR (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rsp,64))) *)
  0xc5; 0x7d; 0xef; 0x8c; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm9) (%_% ymm0) (Memop Word256 (%% (rsp,352))) *)
  0xc5; 0xfd; 0xef; 0xb4; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm6) (%_% ymm0) (Memop Word256 (%% (rsp,512))) *)
  0xc5; 0xfd; 0xef; 0x84; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm0) (%_% ymm0) (Memop Word256 (%% (rsp,672))) *)
  0xc5; 0xfd; 0x7f; 0x2c; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm5) *)
  0xc5; 0xed; 0xef; 0xac; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* VPXOR (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rsp,224))) *)
  0xc5; 0xfd; 0x7f; 0xac; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,160))) (%_% ymm5) *)
  0xc5; 0xed; 0xef; 0xac; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rsp,384))) *)
  0xc5; 0xfd; 0x7f; 0xac; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,320))) (%_% ymm5) *)
  0xc5; 0xed; 0xef; 0xac; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm5) (%_% ymm2) (Memop Word256 (%% (rsp,544))) *)
  0xc5; 0xed; 0xef; 0x94; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm2) (%_% ymm2) (Memop Word256 (%% (rsp,704))) *)
  0xc5; 0xfd; 0x7f; 0xac; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,480))) (%_% ymm5) *)
  0xc5; 0xf5; 0xef; 0x6c; 0x24; 0x60;
                           (* VPXOR (%_% ymm5) (%_% ymm1) (Memop Word256 (%% (rsp,96))) *)
  0xc5; 0xfd; 0x7f; 0xac; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,640))) (%_% ymm5) *)
  0xc5; 0xf5; 0xef; 0xac; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm5) (%_% ymm1) (Memop Word256 (%% (rsp,256))) *)
  0xc5; 0xfd; 0x7f; 0x6c; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm5) *)
  0xc5; 0xf5; 0xef; 0xac; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm5) (%_% ymm1) (Memop Word256 (%% (rsp,416))) *)
  0xc5; 0xfd; 0x7f; 0xac; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,352))) (%_% ymm5) *)
  0xc5; 0xf5; 0xef; 0xac; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm5) (%_% ymm1) (Memop Word256 (%% (rsp,576))) *)
  0xc5; 0xfd; 0x7f; 0xac; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,512))) (%_% ymm5) *)
  0xc5; 0xf5; 0xef; 0x8c; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm1) (%_% ymm1) (Memop Word256 (%% (rsp,736))) *)
  0xc5; 0xfd; 0x7f; 0x4c; 0x24; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rsp,64))) (%_% ymm1) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd7; 0x1c;
                           (* VPSRLQ (%_% ymm1) (%_% ymm15) (Imm8 (word 28)) *)
  0xc4; 0xc1; 0x05; 0x73; 0xf7; 0x24;
                           (* VPSLLQ (%_% ymm15) (%_% ymm15) (Imm8 (word 36)) *)
  0xc5; 0x85; 0xeb; 0xc9;  (* VPOR (%_% ymm1) (%_% ymm15) (%_% ymm1) *)
  0xc5; 0xfd; 0x7f; 0x8c; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,576))) (%_% ymm1) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd6; 0x3d;
                           (* VPSRLQ (%_% ymm1) (%_% ymm14) (Imm8 (word 61)) *)
  0xc4; 0xc1; 0x0d; 0x73; 0xf6; 0x03;
                           (* VPSLLQ (%_% ymm14) (%_% ymm14) (Imm8 (word 3)) *)
  0xc5; 0x0d; 0xeb; 0xf9;  (* VPOR (%_% ymm15) (%_% ymm14) (%_% ymm1) *)
  0xc5; 0x7d; 0x7f; 0xbc; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,704))) (%_% ymm15) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd5; 0x17;
                           (* VPSRLQ (%_% ymm1) (%_% ymm13) (Imm8 (word 23)) *)
  0xc4; 0xc1; 0x15; 0x73; 0xf5; 0x29;
                           (* VPSLLQ (%_% ymm13) (%_% ymm13) (Imm8 (word 41)) *)
  0xc5; 0x15; 0xeb; 0xe9;  (* VPOR (%_% ymm13) (%_% ymm13) (%_% ymm1) *)
  0xc5; 0x7d; 0x7f; 0xac; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,672))) (%_% ymm13) *)
  0xc5; 0xf5; 0x73; 0xd4; 0x2e;
                           (* VPSRLQ (%_% ymm1) (%_% ymm4) (Imm8 (word 46)) *)
  0xc5; 0xdd; 0x73; 0xf4; 0x12;
                           (* VPSLLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 18)) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xfd; 0x7f; 0xa4; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,384))) (%_% ymm4) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd4; 0x3f;
                           (* VPSRLQ (%_% ymm1) (%_% ymm12) (Imm8 (word 63)) *)
  0xc4; 0xc1; 0x1d; 0x73; 0xf4; 0x01;
                           (* VPSLLQ (%_% ymm12) (%_% ymm12) (Imm8 (word 1)) *)
  0xc5; 0x1d; 0xeb; 0xe1;  (* VPOR (%_% ymm12) (%_% ymm12) (%_% ymm1) *)
  0xc5; 0x7d; 0x7f; 0xa4; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,416))) (%_% ymm12) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd3; 0x14;
                           (* VPSRLQ (%_% ymm1) (%_% ymm11) (Imm8 (word 20)) *)
  0xc4; 0xc1; 0x25; 0x73; 0xf3; 0x2c;
                           (* VPSLLQ (%_% ymm11) (%_% ymm11) (Imm8 (word 44)) *)
  0xc5; 0x25; 0xeb; 0xd9;  (* VPOR (%_% ymm11) (%_% ymm11) (%_% ymm1) *)
  0xc5; 0x7d; 0x7f; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,256))) (%_% ymm11) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd0; 0x36;
                           (* VPSRLQ (%_% ymm1) (%_% ymm8) (Imm8 (word 54)) *)
  0xc4; 0xc1; 0x3d; 0x73; 0xf0; 0x0a;
                           (* VPSLLQ (%_% ymm8) (%_% ymm8) (Imm8 (word 10)) *)
  0xc5; 0x3d; 0xeb; 0xc1;  (* VPOR (%_% ymm8) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0xf5; 0x73; 0xd7; 0x13;
                           (* VPSRLQ (%_% ymm1) (%_% ymm7) (Imm8 (word 19)) *)
  0xc5; 0xc5; 0x73; 0xf7; 0x2d;
                           (* VPSLLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 45)) *)
  0xc5; 0xc5; 0xeb; 0xf9;  (* VPOR (%_% ymm7) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0xf5; 0x73; 0xd3; 0x3e;
                           (* VPSRLQ (%_% ymm1) (%_% ymm3) (Imm8 (word 62)) *)
  0xc5; 0xe5; 0x73; 0xf3; 0x02;
                           (* VPSLLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 2)) *)
  0xc5; 0xe5; 0xeb; 0xd9;  (* VPOR (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xfd; 0x7f; 0x9c; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,736))) (%_% ymm3) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd2; 0x02;
                           (* VPSRLQ (%_% ymm1) (%_% ymm10) (Imm8 (word 2)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf2; 0x3e;
                           (* VPSLLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 62)) *)
  0xc5; 0x2d; 0xeb; 0xd1;  (* VPOR (%_% ymm10) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0x7d; 0x7f; 0x54; 0x24; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rsp,96))) (%_% ymm10) *)
  0xc5; 0xfd; 0x6f; 0x9c; 0x24; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsp,800))) *)
  0xc5; 0xd5; 0x73; 0xf3; 0x06;
                           (* VPSLLQ (%_% ymm5) (%_% ymm3) (Imm8 (word 6)) *)
  0xc5; 0xf5; 0x73; 0xd3; 0x3a;
                           (* VPSRLQ (%_% ymm1) (%_% ymm3) (Imm8 (word 58)) *)
  0xc5; 0xd5; 0xeb; 0xe9;  (* VPOR (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd1; 0x15;
                           (* VPSRLQ (%_% ymm1) (%_% ymm9) (Imm8 (word 21)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x2b;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 43)) *)
  0xc5; 0x35; 0xeb; 0xc9;  (* VPOR (%_% ymm9) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x7d; 0x7f; 0x8c; 0x24; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,800))) (%_% ymm9) *)
  0xc5; 0xf5; 0x73; 0xd6; 0x31;
                           (* VPSRLQ (%_% ymm1) (%_% ymm6) (Imm8 (word 49)) *)
  0xc5; 0xcd; 0x73; 0xf6; 0x0f;
                           (* VPSLLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 15)) *)
  0xc5; 0xcd; 0xeb; 0xf1;  (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xfd; 0x6f; 0x24; 0x24;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rsp,0))) *)
  0xc5; 0xe5; 0x73; 0xf4; 0x1c;
                           (* VPSLLQ (%_% ymm3) (%_% ymm4) (Imm8 (word 28)) *)
  0xc5; 0xf5; 0x73; 0xd4; 0x24;
                           (* VPSRLQ (%_% ymm1) (%_% ymm4) (Imm8 (word 36)) *)
  0xc5; 0xe5; 0xeb; 0xd9;  (* VPOR (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7d; 0x6f; 0x8c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsp,320))) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xf1; 0x19;
                           (* VPSLLQ (%_% ymm10) (%_% ymm9) (Imm8 (word 25)) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd1; 0x27;
                           (* VPSRLQ (%_% ymm1) (%_% ymm9) (Imm8 (word 39)) *)
  0xc5; 0x2d; 0xeb; 0xd1;  (* VPOR (%_% ymm10) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0xf5; 0x73; 0xd0; 0x03;
                           (* VPSRLQ (%_% ymm1) (%_% ymm0) (Imm8 (word 3)) *)
  0xc5; 0xfd; 0x73; 0xf0; 0x3d;
                           (* VPSLLQ (%_% ymm0) (%_% ymm0) (Imm8 (word 61)) *)
  0xc5; 0xfd; 0xeb; 0xc1;  (* VPOR (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0x7d; 0x6f; 0xac; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm13) (Memop Word256 (%% (rsp,352))) *)
  0xc4; 0xc1; 0x0d; 0x73; 0xf5; 0x27;
                           (* VPSLLQ (%_% ymm14) (%_% ymm13) (Imm8 (word 39)) *)
  0xc4; 0xc1; 0x1d; 0x73; 0xd5; 0x19;
                           (* VPSRLQ (%_% ymm12) (%_% ymm13) (Imm8 (word 25)) *)
  0xc4; 0x41; 0x0d; 0xeb; 0xf4;
                           (* VPOR (%_% ymm14) (%_% ymm14) (%_% ymm12) *)
  0xc5; 0xfd; 0x6f; 0xa4; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rsp,160))) *)
  0xc5; 0xf5; 0x73; 0xd4; 0x09;
                           (* VPSRLQ (%_% ymm1) (%_% ymm4) (Imm8 (word 9)) *)
  0xc5; 0xdd; 0x73; 0xf4; 0x37;
                           (* VPSLLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 55)) *)
  0xc5; 0xdd; 0xeb; 0xe1;  (* VPOR (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7d; 0x6f; 0xa4; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rsp,480))) *)
  0xc4; 0xc1; 0x25; 0x73; 0xf4; 0x15;
                           (* VPSLLQ (%_% ymm11) (%_% ymm12) (Imm8 (word 21)) *)
  0xc4; 0xc1; 0x75; 0x73; 0xd4; 0x2b;
                           (* VPSRLQ (%_% ymm1) (%_% ymm12) (Imm8 (word 43)) *)
  0xc5; 0x25; 0xeb; 0xd9;  (* VPOR (%_% ymm11) (%_% ymm11) (%_% ymm1) *)
  0xc5; 0xf5; 0x73; 0xd2; 0x08;
                           (* VPSRLQ (%_% ymm1) (%_% ymm2) (Imm8 (word 8)) *)
  0xc5; 0xed; 0x73; 0xf2; 0x38;
                           (* VPSLLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 56)) *)
  0xc5; 0xed; 0xeb; 0xd1;  (* VPOR (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xfd; 0x6f; 0x8c; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsp,640))) *)
  0xc5; 0xb5; 0x73; 0xd1; 0x25;
                           (* VPSRLQ (%_% ymm9) (%_% ymm1) (Imm8 (word 37)) *)
  0xc5; 0xf5; 0x73; 0xf1; 0x1b;
                           (* VPSLLQ (%_% ymm1) (%_% ymm1) (Imm8 (word 27)) *)
  0xc4; 0xc1; 0x75; 0xeb; 0xc9;
                           (* VPOR (%_% ymm1) (%_% ymm1) (%_% ymm9) *)
  0xc5; 0x7d; 0x6f; 0x4c; 0x24; 0x20;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rsp,32))) *)
  0xc4; 0xc1; 0x1d; 0x73; 0xd1; 0x2c;
                           (* VPSRLQ (%_% ymm12) (%_% ymm9) (Imm8 (word 44)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xf1; 0x14;
                           (* VPSLLQ (%_% ymm9) (%_% ymm9) (Imm8 (word 20)) *)
  0xc4; 0x41; 0x35; 0xeb; 0xcc;
                           (* VPOR (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0x7d; 0x6f; 0xac; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm13) (Memop Word256 (%% (rsp,512))) *)
  0xc4; 0xc1; 0x1d; 0x73; 0xd5; 0x38;
                           (* VPSRLQ (%_% ymm12) (%_% ymm13) (Imm8 (word 56)) *)
  0xc4; 0xc1; 0x15; 0x73; 0xf5; 0x08;
                           (* VPSLLQ (%_% ymm13) (%_% ymm13) (Imm8 (word 8)) *)
  0xc4; 0x41; 0x15; 0xeb; 0xec;
                           (* VPOR (%_% ymm13) (%_% ymm13) (%_% ymm12) *)
  0xc5; 0x7d; 0x6f; 0x64; 0x24; 0x40;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rsp,64))) *)
  0xc4; 0xc1; 0x05; 0x73; 0xd4; 0x32;
                           (* VPSRLQ (%_% ymm15) (%_% ymm12) (Imm8 (word 50)) *)
  0xc4; 0xc1; 0x1d; 0x73; 0xf4; 0x0e;
                           (* VPSLLQ (%_% ymm12) (%_% ymm12) (Imm8 (word 14)) *)
  0xc4; 0x41; 0x1d; 0xeb; 0xe7;
                           (* VPOR (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc5; 0x35; 0xdf; 0xbc; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VPANDN (%_% ymm15) (%_% ymm9) (Memop Word256 (%% (rsp,704))) *)
  0xc5; 0x05; 0xef; 0xfb;  (* VPXOR (%_% ymm15) (%_% ymm15) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,128))) (%_% ymm15) *)
  0xc4; 0x41; 0x55; 0xdf; 0xfa;
                           (* VPANDN (%_% ymm15) (%_% ymm5) (%_% ymm10) *)
  0xc5; 0x05; 0xef; 0xbc; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm15) (%_% ymm15) (Memop Word256 (%% (rsp,416))) *)
  0xc5; 0x7d; 0x7f; 0xbc; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,288))) (%_% ymm15) *)
  0xc5; 0x7d; 0x6f; 0xbc; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsp,576))) *)
  0xc4; 0x41; 0x05; 0xdf; 0xf8;
                           (* VPANDN (%_% ymm15) (%_% ymm15) (%_% ymm8) *)
  0xc5; 0x05; 0xef; 0xf9;  (* VPXOR (%_% ymm15) (%_% ymm15) (%_% ymm1) *)
  0xc5; 0x7d; 0x7f; 0xbc; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,448))) (%_% ymm15) *)
  0xc4; 0x41; 0x5d; 0xdf; 0xfe;
                           (* VPANDN (%_% ymm15) (%_% ymm4) (%_% ymm14) *)
  0xc5; 0x05; 0xef; 0x7c; 0x24; 0x60;
                           (* VPXOR (%_% ymm15) (%_% ymm15) (Memop Word256 (%% (rsp,96))) *)
  0xc5; 0x7d; 0x7f; 0xbc; 0x24; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,608))) (%_% ymm15) *)
  0xc5; 0x7d; 0x6f; 0xbc; 0x24; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsp,800))) *)
  0xc4; 0x41; 0x05; 0xdf; 0xfb;
                           (* VPANDN (%_% ymm15) (%_% ymm15) (%_% ymm11) *)
  0xc5; 0x05; 0xef; 0xbc; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VPXOR (%_% ymm15) (%_% ymm15) (Memop Word256 (%% (rsp,256))) *)
  0xc5; 0x7d; 0x7f; 0x3c; 0x24;
                           (* VMOVDQA (Memop Word256 (%% (rsp,0))) (%_% ymm15) *)
  0xc5; 0x7d; 0x6f; 0xbc; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsp,704))) *)
  0xc5; 0x05; 0xdf; 0xff;  (* VPANDN (%_% ymm15) (%_% ymm15) (%_% ymm7) *)
  0xc4; 0x41; 0x05; 0xef; 0xf9;
                           (* VPXOR (%_% ymm15) (%_% ymm15) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0xbc; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,160))) (%_% ymm15) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xfd;
                           (* VPANDN (%_% ymm15) (%_% ymm10) (%_% ymm13) *)
  0xc5; 0x05; 0xef; 0xfd;  (* VPXOR (%_% ymm15) (%_% ymm15) (%_% ymm5) *)
  0xc5; 0x7d; 0x7f; 0xbc; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,320))) (%_% ymm15) *)
  0xc5; 0x3d; 0xdf; 0xfe;  (* VPANDN (%_% ymm15) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x05; 0xef; 0xbc; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm15) (%_% ymm15) (Memop Word256 (%% (rsp,576))) *)
  0xc5; 0x7d; 0x7f; 0xbc; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,480))) (%_% ymm15) *)
  0xc5; 0x0d; 0xdf; 0xbc; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* VPANDN (%_% ymm15) (%_% ymm14) (Memop Word256 (%% (rsp,672))) *)
  0xc5; 0x05; 0xef; 0xfc;  (* VPXOR (%_% ymm15) (%_% ymm15) (%_% ymm4) *)
  0xc5; 0x7d; 0x7f; 0xbc; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,640))) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xdf; 0xfc;
                           (* VPANDN (%_% ymm15) (%_% ymm11) (%_% ymm12) *)
  0xc5; 0x05; 0xef; 0xbc; 0x24; 0x20; 0x03; 0x00; 0x00;
                           (* VPXOR (%_% ymm15) (%_% ymm15) (Memop Word256 (%% (rsp,800))) *)
  0xc5; 0x7d; 0x7f; 0x7c; 0x24; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rsp,32))) (%_% ymm15) *)
  0xc5; 0x45; 0xdf; 0xf8;  (* VPANDN (%_% ymm15) (%_% ymm7) (%_% ymm0) *)
  0xc5; 0x05; 0xef; 0xbc; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm15) (%_% ymm15) (Memop Word256 (%% (rsp,704))) *)
  0xc5; 0x7d; 0x7f; 0xbc; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,192))) (%_% ymm15) *)
  0xc5; 0x15; 0xdf; 0xbc; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VPANDN (%_% ymm15) (%_% ymm13) (Memop Word256 (%% (rsp,384))) *)
  0xc4; 0x41; 0x05; 0xef; 0xd2;
                           (* VPXOR (%_% ymm10) (%_% ymm15) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x94; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,352))) (%_% ymm10) *)
  0xc5; 0x4d; 0xdf; 0xd2;  (* VPANDN (%_% ymm10) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x41; 0x2d; 0xef; 0xc0;
                           (* VPXOR (%_% ymm8) (%_% ymm10) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x84; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,512))) (%_% ymm8) *)
  0xc5; 0x7d; 0x6f; 0x94; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rsp,672))) *)
  0xc5; 0x7d; 0x6f; 0xbc; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsp,736))) *)
  0xc4; 0x41; 0x2d; 0xdf; 0xc7;
                           (* VPANDN (%_% ymm8) (%_% ymm10) (%_% ymm15) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc6;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm14) *)
  0xc5; 0x7d; 0x7f; 0x84; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,672))) (%_% ymm8) *)
  0xc5; 0x7d; 0x6f; 0xb4; 0x24; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm14) (Memop Word256 (%% (rsp,832))) *)
  0xc4; 0x41; 0x1d; 0xdf; 0xc6;
                           (* VPANDN (%_% ymm8) (%_% ymm12) (%_% ymm14) *)
  0xc4; 0x41; 0x3d; 0xef; 0xc3;
                           (* VPXOR (%_% ymm8) (%_% ymm8) (%_% ymm11) *)
  0xc5; 0x7d; 0x7f; 0x44; 0x24; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rsp,64))) (%_% ymm8) *)
  0xc5; 0x7d; 0xdf; 0xc3;  (* VPANDN (%_% ymm8) (%_% ymm0) (%_% ymm3) *)
  0xc5; 0xbd; 0xef; 0xff;  (* VPXOR (%_% ymm7) (%_% ymm8) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0xbc; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,224))) (%_% ymm7) *)
  0xc5; 0x7d; 0x6f; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rsp,384))) *)
  0xc5; 0x7d; 0x6f; 0x84; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsp,416))) *)
  0xc4; 0xc1; 0x25; 0xdf; 0xf8;
                           (* VPANDN (%_% ymm7) (%_% ymm11) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0xef; 0xfd;
                           (* VPXOR (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0xbc; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,384))) (%_% ymm7) *)
  0xc5; 0x7d; 0x6f; 0xac; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm13) (Memop Word256 (%% (rsp,256))) *)
  0xc4; 0xc1; 0x65; 0xdf; 0xd9;
                           (* VPANDN (%_% ymm3) (%_% ymm3) (%_% ymm9) *)
  0xc5; 0xe5; 0xef; 0xd8;  (* VPXOR (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,256))) (%_% ymm3) *)
  0xc5; 0xbd; 0xdf; 0xc5;  (* VPANDN (%_% ymm0) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0xc1; 0x7d; 0xef; 0xdb;
                           (* VPXOR (%_% ymm3) (%_% ymm0) (%_% ymm11) *)
  0xc5; 0xfd; 0x7f; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,416))) (%_% ymm3) *)
  0xc5; 0xed; 0xdf; 0xf9;  (* VPANDN (%_% ymm7) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xc5; 0xef; 0xf6;  (* VPXOR (%_% ymm6) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xb4; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,544))) (%_% ymm6) *)
  0xc5; 0x7d; 0x7f; 0xfe;  (* VMOVDQA (%_% ymm6) (%_% ymm15) *)
  0xc5; 0x7d; 0x6f; 0x7c; 0x24; 0x60;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsp,96))) *)
  0xc4; 0xc1; 0x4d; 0xdf; 0xf7;
                           (* VPANDN (%_% ymm6) (%_% ymm6) (%_% ymm15) *)
  0xc4; 0xc1; 0x4d; 0xef; 0xfa;
                           (* VPXOR (%_% ymm7) (%_% ymm6) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0xbc; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,704))) (%_% ymm7) *)
  0xc5; 0xf5; 0xdf; 0x8c; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VPANDN (%_% ymm1) (%_% ymm1) (Memop Word256 (%% (rsp,576))) *)
  0xc5; 0xf5; 0xef; 0xd2;  (* VPXOR (%_% ymm2) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x94; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,576))) (%_% ymm2) *)
  0xc5; 0x95; 0xdf; 0xac; 0x24; 0x20; 0x03; 0x00; 0x00;
                           (* VPANDN (%_% ymm5) (%_% ymm13) (Memop Word256 (%% (rsp,800))) *)
  0xc4; 0xc1; 0x55; 0xef; 0xee;
                           (* VPXOR (%_% ymm5) (%_% ymm5) (%_% ymm14) *)
  0xc4; 0xe2; 0x7d; 0x59; 0x06;
                           (* VPBROADCASTQ (%_% ymm0) (Memop Quadword (%% (rsi,0))) *)
  0xc5; 0xd5; 0xef; 0xe8;  (* VPXOR (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc4; 0xc1; 0x0d; 0xdf; 0xf5;
                           (* VPANDN (%_% ymm6) (%_% ymm14) (%_% ymm13) *)
  0xc4; 0x41; 0x4d; 0xef; 0xf4;
                           (* VPXOR (%_% ymm14) (%_% ymm6) (%_% ymm12) *)
  0xc5; 0x7d; 0x7f; 0x74; 0x24; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rsp,96))) (%_% ymm14) *)
  0xc5; 0x85; 0xdf; 0xc4;  (* VPANDN (%_% ymm0) (%_% ymm15) (%_% ymm4) *)
  0xc5; 0xfd; 0xef; 0xb4; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* VPXOR (%_% ymm6) (%_% ymm0) (Memop Word256 (%% (rsp,736))) *)
  0xc5; 0xfd; 0x7f; 0xb4; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rsp,736))) (%_% ymm6) *)
  0x48; 0x83; 0xc6; 0x08;  (* ADD (% rsi) (Imm8 (word 8)) *)
  0x48; 0x83; 0xc0; 0x01;  (* ADD (% rax) (Imm8 (word 1)) *)
  0x48; 0x83; 0xf8; 0x18;  (* CMP (% rax) (Imm8 (word 24)) *)
  0x0f; 0x85; 0x39; 0xf9; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294965561)) *)
  0xc5; 0xfd; 0x6f; 0x0c; 0x24;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsp,0))) *)
  0xc5; 0xfd; 0x6f; 0x54; 0x24; 0x20;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsp,32))) *)
  0xc5; 0xfd; 0x6f; 0x5c; 0x24; 0x40;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsp,64))) *)
  0xc5; 0xd5; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xef; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x2f;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm5) *)
  0xc5; 0xfe; 0x7f; 0x8f; 0xc8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,200))) (%_% ymm1) *)
  0xc5; 0xfe; 0x7f; 0x97; 0x90; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,400))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0x58; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,600))) (%_% ymm3) *)
  0xc5; 0xfd; 0x6f; 0x44; 0x24; 0x60;
                           (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsp,96))) *)
  0xc5; 0xfd; 0x6f; 0x8c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsp,128))) *)
  0xc5; 0xfd; 0x6f; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsp,160))) *)
  0xc5; 0xfd; 0x6f; 0x9c; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsp,192))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc7; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x47; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x8f; 0xe8; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,232))) (%_% ymm1) *)
  0xc5; 0xfe; 0x7f; 0x97; 0xb0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,432))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0x78; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,632))) (%_% ymm3) *)
  0xc5; 0xfd; 0x6f; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsp,224))) *)
  0xc5; 0xfd; 0x6f; 0x8c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsp,256))) *)
  0xc5; 0xfd; 0x6f; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsp,288))) *)
  0xc5; 0xfd; 0x6f; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsp,320))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc7; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x47; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x8f; 0x08; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,264))) (%_% ymm1) *)
  0xc5; 0xfe; 0x7f; 0x97; 0xd0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,464))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0x98; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,664))) (%_% ymm3) *)
  0xc5; 0xfd; 0x6f; 0x84; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsp,352))) *)
  0xc5; 0xfd; 0x6f; 0x8c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsp,384))) *)
  0xc5; 0xfd; 0x6f; 0x94; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsp,416))) *)
  0xc5; 0xfd; 0x6f; 0x9c; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsp,448))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc7; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x47; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x8f; 0x28; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,296))) (%_% ymm1) *)
  0xc5; 0xfe; 0x7f; 0x97; 0xf0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,496))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0xb8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,696))) (%_% ymm3) *)
  0xc5; 0xfd; 0x6f; 0x84; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsp,480))) *)
  0xc5; 0xfd; 0x6f; 0x8c; 0x24; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsp,512))) *)
  0xc5; 0xfd; 0x6f; 0x94; 0x24; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsp,544))) *)
  0xc5; 0xfd; 0x6f; 0x9c; 0x24; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsp,576))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc7; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x8f; 0x48; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,328))) (%_% ymm1) *)
  0xc5; 0xfe; 0x7f; 0x97; 0x10; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,528))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0xd8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,728))) (%_% ymm3) *)
  0xc5; 0xfd; 0x6f; 0x84; 0x24; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsp,608))) *)
  0xc5; 0xfd; 0x6f; 0x8c; 0x24; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsp,640))) *)
  0xc5; 0xfd; 0x6f; 0x94; 0x24; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsp,672))) *)
  0xc5; 0xfd; 0x6f; 0x9c; 0x24; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsp,704))) *)
  0xc5; 0xfd; 0x6c; 0xe1;  (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x6d; 0xf1;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xed; 0x6c; 0xfb;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0x6d; 0x6d; 0xc3;  (* VPUNPCKHQDQ (%_% ymm8) (%_% ymm2) (%_% ymm3) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xc7; 0x20;
                           (* VPERM2I128 (%_% ymm0) (%_% ymm4) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xc8; 0x20;
                           (* VPERM2I128 (%_% ymm1) (%_% ymm6) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x5d; 0x46; 0xd7; 0x31;
                           (* VPERM2I128 (%_% ymm2) (%_% ymm4) (%_% ymm7) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xd8; 0x31;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm6) (%_% ymm8) (Imm8 (word 49)) *)
  0xc5; 0xfe; 0x7f; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x8f; 0x68; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,360))) (%_% ymm1) *)
  0xc5; 0xfe; 0x7f; 0x97; 0x30; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,560))) (%_% ymm2) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0xf8; 0x02; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,760))) (%_% ymm3) *)
  0xc5; 0xfd; 0x6f; 0x9c; 0x24; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsp,736))) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xd8; 0x00;
                           (* VEXTRACTI128 (%_% xmm0) (%_% ymm3) (Imm8 (word 0)) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xd9; 0x01;
                           (* VEXTRACTI128 (%_% xmm1) (%_% ymm3) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0x87; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVQ (Memop Quadword (%% (rdi,192))) (%_% xmm0) *)
  0xc4; 0xe3; 0xf9; 0x16; 0x87; 0x88; 0x01; 0x00; 0x00; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,392))) (%_% xmm0) (Imm8 (word 1)) *)
  0xc5; 0xf9; 0xd6; 0x8f; 0x50; 0x02; 0x00; 0x00;
                           (* VMOVQ (Memop Quadword (%% (rdi,592))) (%_% xmm1) *)
  0xc4; 0xe3; 0xf9; 0x16; 0x8f; 0x18; 0x03; 0x00; 0x00; 0x01;
                           (* VPEXTRQ (Memop Quadword (%% (rdi,792))) (%_% xmm1) (Imm8 (word 1)) *)
  0x48; 0x89; 0xec;        (* MOV (% rsp) (% rbp) *)
  0x5d;                    (* POP (% rbp) *)
  0xc3                     (* RET *)
];;

let sha3_keccak4_f1600_tmc = define_trimmed "sha3_keccak4_f1600_tmc" sha3_keccak4_f1600_mc;;

let SHA3_KECCAK4_F1600_EXEC = X86_MK_CORE_EXEC_RULE sha3_keccak4_f1600_tmc;;

(* ------------------------------------------------------------------------- *)
(* Additional definitions and tactics used in proof.                         *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_CORRECT = prove
  (`!rc_pointer:int64 bitstate_in:int64 A1 A2 A3 A4 pc:num stackpointer:int64.
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_tmc) (val stackpointer, 0x360) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_tmc) (val bitstate_in, 800) /\
  nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_tmc) (val rc_pointer, 192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in,800) (val rc_pointer,192) /\
  nonoverlapping_modulo (2 EXP 64) (val bitstate_in,800) (val stackpointer, 0x360) /\
  nonoverlapping_modulo (2 EXP 64) (val stackpointer, 800) (val rc_pointer,192)
  ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST sha3_keccak4_f1600_tmc) /\
              read RIP s = word (pc + 0x13) /\
              read RSP s = stackpointer /\
              C_ARGUMENTS [bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(bitstate_in,25) s = A1 /\
              wordlist_from_memory(word_add bitstate_in (word 200),25) s = A2 /\
              wordlist_from_memory(word_add bitstate_in (word 600),25) s = A4 /\
              wordlist_from_memory(word_add bitstate_in (word 400),25) s = A3)
             (\s. read RIP s = word(pc + 0xc1e) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A1 /\
                  wordlist_from_memory(word_add bitstate_in (word 200),25) s = keccak 24 A2 /\
                  wordlist_from_memory(word_add bitstate_in (word 400),25) s = keccak 24 A3 /\
                  wordlist_from_memory(word_add bitstate_in (word 600),25) s = keccak 24 A4)
           (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RBP; 
                      R8; R9; R10; R11; R12; R13; R14; R15; RDI; RSI] ,, 
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes (stackpointer, 0x360)],,
            MAYCHANGE [memory :> bytes (bitstate_in, 800)])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`rc_pointer:int64`; `bitstate_in:int64`;`A1:int64 list`;`A2:int64 list`;`A3:int64 list`;`A4:int64 list`] THEN
  MAP_EVERY X_GEN_TAC [`pc:num`;`stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  ASM_CASES_TAC
   `LENGTH(A1:int64 list) = 25 /\ LENGTH(A2:int64 list) = 25 /\
    LENGTH(A3:int64 list) = 25 /\ LENGTH(A4:int64 list) = 25`
  THENL
  ALL_TAC;
   [FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC);
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  (*** Set up the loop invariant ***)

  ENSURES_WHILE_PAUP_TAC `0` `24` `pc + 0x5d` `pc + 0x62d`
  `\i s.
      (read R8 s = i /\
       read RDI s = bitstate_in /\
       read RSP s = stackpointer /\
       read YMM5 s = (read (memory :> bytes64 (word_add bitstate_in (word 160))) s) /\
       read RBX s = (read (memory :> bytes64 (word_add bitstate_in (word 168))) s) /\
       read RCX s = (read (memory :> bytes64 (word_add bitstate_in (word 176))) s) /\
       read RDX s = (read (memory :> bytes64 (word_add bitstate_in (word 184))) s) /\
       read RBP s = (read (memory :> bytes64 (word_add bitstate_in (word 192))) s) /\
       read RSI s = word_add rc_pointer (word (8 * i)) /\
       wordlist_from_memory(rc_pointer,24) s = round_constants /\
       wordlist_from_memory(bitstate_in,25) s = 
          MAP2 (\(x:bool) (y:(64)word). (if x then (word_not y) else y)) (
          [false; true;  true;  false; false; 
          false; false; false; true;  false; 
          false; false; true;  false; false; 
          false; false; true;  false; false;
          true;  false; false; false; false]) (keccak (2*i) A))  /\
      (read ZF s <=> i = 12)` THEN
  REPEAT CONJ_TAC THENL 
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC; 
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 25)) s0` THEN

    X86_STEPS_TAC SHA3_KECCAK_F1600_EXEC (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    REPEAT CONJ_TAC THENL 
    [CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE;
    EXPAND_TAC "A" THEN
    PURE_ONCE_REWRITE_TAC[ARITH_RULE `2 * 0 = 0`] THEN
    REWRITE_TAC[keccak] THEN 
    REWRITE_TAC[MAP2]];

    (*** Preservation of the invariant including end condition code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `2 * i`; `2 * i + 1`] THEN
    MP_TAC(WORD_RULE
        `word_add (word (2 * i)) (word 1):int64 = word(2 * i + 1)`) THEN
    DISCH_TAC THEN

    CONV_TAC(RATOR_CONV(LAND_CONV
      (ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THENC
      ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN

    ASM_REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC; 
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN
    MP_TAC(ISPECL [`A:int64 list`; `2 * i`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN 
    REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2] THEN
    REWRITE_TAC[CONS_11] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (bitstate_in,8 * 25)) s0` THEN
      
    SUBGOAL_THEN
      `read (memory :> bytes64 (word_add rc_pointer (word(8 * i)))) s0 =
      EL i round_constants /\
      read (memory :> bytes64 (word_add rc_pointer (word(2 * 8 * i)))) s0 =
      EL (2 * i) round_constants /\
      read (memory :> bytes64 (word_add rc_pointer (word(16 * i)))) s0 =
      EL (2 * i) round_constants /\
      read (memory :> bytes64 (word_add (word_add rc_pointer (word(16 * i))) (word(8)))) s0 =
      EL (2 * i + 1) round_constants`
    ASSUME_TAC THENL
      [UNDISCH_TAC `i < 12` THEN SPEC_TAC(`i:num`,`i:num`) THEN
       CONV_TAC EXPAND_CASES_CONV THEN
       REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN 
       CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
       ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
       CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
       REWRITE_TAC[];
       ALL_TAC] THEN 

    X86_STEPS_TAC SHA3_KECCAK_F1600_EXEC (1--394) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
    [CONV_TAC WORD_RULE;
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `2 * (i + 1) = (2 * i + 1) + 1`] THEN
      REWRITE_TAC[keccak] THEN 
      FIRST_X_ASSUM(fun th ->
        REWRITE_TAC [SYM th]) THEN
      REWRITE_TAC[keccak_round] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
      REWRITE_TAC[round_constants; MAP2] THEN REWRITE_TAC[CONS_11] THEN                    
      REWRITE_TAC[WORD_XOR_NOT;WORD_ROL_NOT_SYM] THEN 
      REWRITE_TAC[WORD_NEG_EL_DEMORGAN;WORD_NOT_NOT] THEN
      REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC;

      REWRITE_TAC [WORD_BLAST `word_add x (word 18446744073709551594):int64 = 
              word_sub x (word 22)`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN 
      REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT; ARITH_RULE`22 < 2 EXP 64`] THEN
      CONJ_TAC THENL 
      [UNDISCH_TAC `i < 12` 
        THEN ARITH_TAC;
        ARITH_TAC]];

    (*** The trivial loop-back goal ***)
    
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC; 
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The tail of logical not operation and writeback ***)

    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC(RATOR_CONV(LAND_CONV
     (ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THENC
      ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    ASM_REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC; 
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc_pointer,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(bitstate_in,25) s:int64 list`] THEN
    MP_TAC(ISPECL [`A:int64 list`; `24`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN
    REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2] THEN
    REWRITE_TAC[CONS_11] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_NOT_NOT]]);;

let SHA3_KECCAK_F1600_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!rc_pointer:int64 bitstate_in:int64 A pc:num stackpointer:int64 returnaddress.
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_tmc) (val (word_sub stackpointer (word 256)), 256) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_tmc) (val bitstate_in, 200) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_tmc) (val rc_pointer, 192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val rc_pointer,192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val (word_sub stackpointer (word 256)), 264) /\
 nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 256)), 256) (val rc_pointer,192)
 ==> ensures x86
         (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_tmc) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(bitstate_in,25) s = A)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 200);
                     memory :> bytes(word_sub stackpointer (word 256),256)])`,
let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_STACK_TAC sha3_keccak_f1600_tmc
    (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_CORRECT)
  `[RBX; RBP; R12; R13; R14; R15]` 256);;

let SHA3_KECCAK_F1600_SUBROUTINE_CORRECT = time prove
 (`!rc_pointer:int64 bitstate_in:int64 A pc:num stackpointer:int64 returnaddress.
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_mc) (val (word_sub stackpointer (word 256)), 256) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_mc) (val bitstate_in, 200) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_mc) (val rc_pointer, 192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val rc_pointer,192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val (word_sub stackpointer (word 256)), 264) /\
 nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 256)), 256) (val rc_pointer,192)
 ==> ensures x86
         (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_mc) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(bitstate_in,25) s = A)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 200);
                     memory :> bytes(word_sub stackpointer (word 256),256)])`,
let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE 
    (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_NOIBT_SUBROUTINE_CORRECT)));;


(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let sha3_keccak_f1600_windows_mc = define_from_elf
  "sha3_keccak_f1600_windows_mc" "x86/sha3/sha3_keccak_f1600.obj";;

let sha3_keccak_f1600_windows_tmc = define_trimmed "sha3_keccak_f1600_windows_tmc" sha3_keccak_f1600_windows_mc;;

let SHA3_KECCAK_F1600_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A pc:num stackpointer:int64 returnaddress.
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_windows_tmc) (val (word_sub stackpointer (word 272)), 272) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_windows_tmc) (val bitstate_in, 200) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_windows_tmc) (val rc_pointer, 192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val rc_pointer,192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val (word_sub stackpointer (word 272)), 280) /\
 nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 272)), 272) (val rc_pointer,192)
 ==> ensures x86
         (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_windows_tmc) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(bitstate_in,25) s = A)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A)
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 200);
                     memory :> bytes(word_sub stackpointer (word 272),272)])`,
let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  WINDOWS_X86_WRAP_STACK_TAC
    sha3_keccak_f1600_windows_tmc sha3_keccak_f1600_tmc
    ((CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_CORRECT))
    `[RBX; RBP; R12; R13; R14; R15]` 256);;

let SHA3_KECCAK_F1600_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!rc_pointer:int64 bitstate_in:int64 A pc:num stackpointer:int64 returnaddress.
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_windows_mc) (val (word_sub stackpointer (word 272)), 272) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_windows_mc) (val bitstate_in, 200) /\
 nonoverlapping_modulo (2 EXP 64) (pc, LENGTH sha3_keccak_f1600_windows_mc) (val rc_pointer, 192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val rc_pointer,192) /\
 nonoverlapping_modulo (2 EXP 64) (val bitstate_in,200) (val (word_sub stackpointer (word 272)), 280) /\
 nonoverlapping_modulo (2 EXP 64) (val (word_sub stackpointer (word 272)), 272) (val rc_pointer,192)
 ==> ensures x86
         (\s. bytes_loaded s (word pc) (sha3_keccak_f1600_windows_mc) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [bitstate_in; rc_pointer] s /\
              wordlist_from_memory(rc_pointer,24) s = round_constants /\
              wordlist_from_memory(bitstate_in,25) s = A)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(bitstate_in,25) s = keccak 24 A)
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes (bitstate_in, 200);
                     memory :> bytes(word_sub stackpointer (word 272),272)])`,
let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE 
  (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_NOIBT_WINDOWS_SUBROUTINE_CORRECT)));;