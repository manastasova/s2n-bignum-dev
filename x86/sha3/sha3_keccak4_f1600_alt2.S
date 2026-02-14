// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3, batch of four independent operations
// Input a[100], rc[24], rho8, rho56; output a[100]
//
// The input/output argument is in effect four 25-element Keccak arrays
// a[0...24], a[25..49], a[50..74] and a[75..99], which could be considered
// as type a[25][4].
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-refaerence-3.0.pdf
//
//    extern void sha3_keccak4_f1600_alt2(uint64_t a[100], const uint64_t rc[24], const void* rho8, const void* rho56);
//
// Standard x86-64 ABI: RDI = a, RSI = rc, RDX = rho8, RCX = rho56
// Microsoft x64 ABI:   RCX = a, RDX = rc, R8 = rho8, R9 = rho56
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak4_f1600_alt2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak4_f1600_alt2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak4_f1600_alt2)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak4_f1600_alt2):
        CFI_START
       _CET_ENDBR

#if WINDOWS_ABI
    CFI_DEC_RSP(176)
    CFI_STACKSAVEU(xmm6,0)
    CFI_STACKSAVEU(xmm7,16)
    CFI_STACKSAVEU(xmm8,32)
    CFI_STACKSAVEU(xmm9,48)
    CFI_STACKSAVEU(xmm10,64)
    CFI_STACKSAVEU(xmm11,80)
    CFI_STACKSAVEU(xmm12,96)
    CFI_STACKSAVEU(xmm13,112)
    CFI_STACKSAVEU(xmm14,128)
    CFI_STACKSAVEU(xmm15,144)
    CFI_STACKSAVE(rdi,160)
    CFI_STACKSAVE(rsi,168)
    mov rdi, rcx
    mov rsi, rdx
    mov rdx, r8
    mov rcx, r9
#endif

    mov    r11, rsp
    and    rsp,0xffffffffffffffe0
    .cfi_register rsp, r11
    sub    rsp,0x300

        vmovdqu ymm3,YMMWORD PTR [rdi+0xc8]	
        vmovdqu ymm4,YMMWORD PTR [rdi+0x258]
        vmovdqu ymm0,YMMWORD PTR [rdi]
        vmovdqu ymm1,YMMWORD PTR [rdi+0x190]
        vpunpcklqdq ymm2,ymm0,ymm3
        vpunpckhqdq ymm0,ymm0,ymm3
        vpunpcklqdq ymm3,ymm1,ymm4
        vperm2i128 ymm7,ymm2,ymm3,0x20
        vpunpckhqdq ymm1,ymm1,ymm4
        vperm2i128 ymm3,ymm2,ymm3,0x31
        vmovdqu ymm4,YMMWORD PTR [rdi+0x278]
        vmovdqu YMMWORD PTR [rsp+0x120],ymm3
        vperm2i128 ymm3,ymm0,ymm1,0x31
        vmovdqu YMMWORD PTR [rsp+0x1e0],ymm7
        vperm2i128 ymm7,ymm0,ymm1,0x20
        vmovdqu ymm0,YMMWORD PTR [rdi+0x20]
        vmovdqu ymm1,YMMWORD PTR [rdi+0x1b0]
        vmovdqu YMMWORD PTR [rsp+0x140],ymm3
        vmovdqu ymm3,YMMWORD PTR [rdi+0xe8]
        vmovdqu YMMWORD PTR [rsp+0x100],ymm7
        vpunpcklqdq ymm2,ymm0,ymm3
        vpunpckhqdq ymm0,ymm0,ymm3
        vpunpcklqdq ymm3,ymm1,ymm4
        vperm2i128 ymm7,ymm2,ymm3,0x20
        vpunpckhqdq ymm1,ymm1,ymm4
        vperm2i128 ymm3,ymm2,ymm3,0x31
        vmovdqu ymm4,YMMWORD PTR [rdi+0x298]
        vperm2i128 ymm14,ymm0,ymm1,0x31
        vmovdqu YMMWORD PTR [rsp+0x160],ymm7
        vperm2i128 ymm7,ymm0,ymm1,0x20
        vmovdqu ymm0,YMMWORD PTR [rdi+0x40]
        vmovdqu ymm1,YMMWORD PTR [rdi+0x1d0]
        vmovdqu YMMWORD PTR [rsp+0x200],ymm3
        vmovdqu ymm3,YMMWORD PTR [rdi+0x108]
        vmovdqu ymm10,ymm14
        vmovdqu YMMWORD PTR [rsp+0x180],ymm7
        vpunpcklqdq ymm2,ymm0,ymm3
        vpunpckhqdq ymm0,ymm0,ymm3
        vpunpcklqdq ymm3,ymm1,ymm4
        vpunpckhqdq ymm1,ymm1,ymm4
        vperm2i128 ymm11,ymm2,ymm3,0x20
        vperm2i128 ymm3,ymm2,ymm3,0x31
        vperm2i128 ymm7,ymm0,ymm1,0x20
        vmovdqu YMMWORD PTR [rsp+0x2e0],ymm3
        vperm2i128 ymm8,ymm0,ymm1,0x31
        vmovdqu ymm3,YMMWORD PTR [rdi+0x128]
        vmovdqu ymm0,YMMWORD PTR [rdi+0x60]
        vmovdqu ymm1,YMMWORD PTR [rdi+0x1f0]
        vmovdqu YMMWORD PTR [rsp+0x220],ymm7
        vmovdqu ymm14,ymm11
        vmovdqu ymm4,YMMWORD PTR [rdi+0x2b8]
        vmovdqu ymm5,YMMWORD PTR [rdi+0x2f8]
        vpunpcklqdq ymm2,ymm0,ymm3
        vpunpckhqdq ymm0,ymm0,ymm3
        vpunpcklqdq ymm3,ymm1,ymm4
        vpunpckhqdq ymm1,ymm1,ymm4
        vmovdqu ymm4,YMMWORD PTR [rdi+0x2d8]
        vperm2i128 ymm15,ymm2,ymm3,0x20
        vperm2i128 ymm3,ymm2,ymm3,0x31
        vperm2i128 ymm7,ymm0,ymm1,0x20
        vperm2i128 ymm9,ymm0,ymm1,0x31
        vmovdqu YMMWORD PTR [rsp+0x1a0],ymm3
        vmovdqu ymm0,YMMWORD PTR [rdi+0x80]
        vmovdqu ymm3,YMMWORD PTR [rdi+0x148]
        vmovdqu ymm1,YMMWORD PTR [rdi+0x210]
        vmovdqu YMMWORD PTR [rsp+0x2c0],ymm7
        vpunpcklqdq ymm2,ymm0,ymm3
        vpunpckhqdq ymm0,ymm0,ymm3
        vpunpcklqdq ymm3,ymm1,ymm4
        vpunpckhqdq ymm1,ymm1,ymm4
        vperm2i128 ymm7,ymm2,ymm3,0x20
        vperm2i128 ymm13,ymm2,ymm3,0x31
        vperm2i128 ymm3,ymm0,ymm1,0x31
        vmovdqu YMMWORD PTR [rsp+0x2a0],ymm7
        vperm2i128 ymm7,ymm0,ymm1,0x20
        vmovdqu ymm0,YMMWORD PTR [rdi+0xa0]
        vmovdqu ymm1,YMMWORD PTR [rdi+0x230]
        vmovdqu YMMWORD PTR [rsp+0x260],ymm3
        vmovdqu ymm3,YMMWORD PTR [rdi+0x168]
        vpunpcklqdq ymm4,ymm1,ymm5
        vpunpckhqdq ymm1,ymm1,ymm5
        vmovdqu YMMWORD PTR [rsp+0x280],ymm7
        vpunpcklqdq ymm2,ymm0,ymm3
        vpunpckhqdq ymm0,ymm0,ymm3
        vperm2i128 ymm12,ymm2,ymm4,0x20
        vperm2i128 ymm3,ymm0,ymm1,0x20
        vperm2i128 ymm7,ymm2,ymm4,0x31
        vperm2i128 ymm4,ymm0,ymm1,0x31
        vmovq  xmm0,QWORD PTR [rdi+0x250]
        vmovq  xmm1,QWORD PTR [rdi+0xc0]
        vmovdqu YMMWORD PTR [rsp+0x1c0],ymm12
        vmovdqu YMMWORD PTR [rsp+0x240],ymm4
        vpinsrq xmm0,xmm0,QWORD PTR [rdi+0x318],0x1
        vpinsrq xmm1,xmm1,QWORD PTR [rdi+0x188],0x1
        vinserti128 ymm2,ymm1,xmm0,0x1
        mov r10, 0

Lsha3_keccak4_f1600_alt2:
	vmovdqu ymm4,YMMWORD PTR [rsp+0x180]
        vpxor  ymm0,ymm9,YMMWORD PTR [rsp+0x1c0]
        vmovdqu YMMWORD PTR [rsp+0x0],ymm9
        vmovdqu ymm9,ymm10
        vmovdqu ymm11,YMMWORD PTR [rsp+0x200]
        vmovdqu ymm12,YMMWORD PTR [rsp+0x2a0]
        vmovdqu YMMWORD PTR [rsp+0x40],ymm3
        vpxor  ymm1,ymm4,YMMWORD PTR [rsp+0x2e0]
        vmovdqu ymm10,YMMWORD PTR [rsp+0x120]
        vmovdqu YMMWORD PTR [rsp+0x20],ymm4
        vpxor  ymm12,ymm12,ymm3
        vmovdqu ymm6,YMMWORD PTR [rsp+0x100]
        vmovdqu ymm4,YMMWORD PTR [rsp+0x1a0]
        vmovdqu YMMWORD PTR [rsp+0xa0],ymm14
        vpxor  ymm0,ymm0,ymm1
        vpxor  ymm1,ymm11,ymm8
        vpxor  ymm11,ymm7,YMMWORD PTR [rsp+0x280]
        vmovdqu YMMWORD PTR [rsp+0x80],ymm10
        vpxor  ymm12,ymm12,ymm1
        vpxor  ymm1,ymm9,ymm15
        vmovdqu ymm3,YMMWORD PTR [rsp+0x220]
        vmovdqu YMMWORD PTR [rsp+0x60],ymm8
        vpxor  ymm11,ymm11,ymm1
        vpxor  ymm1,ymm14,YMMWORD PTR [rsp+0x2c0]
        vpxor  ymm12,ymm12,ymm6
        vmovdqu ymm8,YMMWORD PTR [rsp+0x140]
        vpxor  ymm11,ymm11,ymm10
        vpxor  ymm10,ymm13,YMMWORD PTR [rsp+0x240]
        vpxor  ymm3,ymm3,ymm4
        vmovdqu YMMWORD PTR [rsp+0xc0],ymm4
        vpsrlq ymm4,ymm12,0x3f
        vpsrlq ymm5,ymm11,0x3f
        vpxor  ymm0,ymm0,YMMWORD PTR [rsp+0x1e0]
        vpxor  ymm10,ymm10,ymm1
        vmovdqu ymm1,YMMWORD PTR [rsp+0x160]
        vpxor  ymm10,ymm10,ymm8
        vmovdqu ymm14,ymm1
        vpxor  ymm1,ymm2,YMMWORD PTR [rsp+0x260]
        vmovdqu YMMWORD PTR [rsp+0xe0],ymm14
        vpxor  ymm1,ymm1,ymm3
        vpsllq ymm3,ymm12,0x1
        vpor   ymm3,ymm3,ymm4
        vpsllq ymm4,ymm11,0x1
        vpxor  ymm1,ymm1,ymm14
        vpor   ymm4,ymm4,ymm5
        vpsrlq ymm14,ymm10,0x3f
        vpxor  ymm3,ymm3,ymm1
        vpsllq ymm5,ymm10,0x1
        vpxor  ymm4,ymm4,ymm0
        vpor   ymm5,ymm5,ymm14
        vpxor  ymm6,ymm4,ymm6
        vpxor  ymm5,ymm5,ymm12
        vpsrlq ymm12,ymm1,0x3f
        vpsllq ymm1,ymm1,0x1
        vpxor  ymm7,ymm5,ymm7
        vpxor  ymm9,ymm5,ymm9
        vpor   ymm1,ymm1,ymm12
        vpxor  ymm12,ymm3,YMMWORD PTR [rsp+0x1e0]
        vpxor  ymm1,ymm1,ymm11
        vpsrlq ymm11,ymm0,0x3f
        vpsllq ymm0,ymm0,0x1
        vpxor  ymm13,ymm1,ymm13
        vpxor  ymm8,ymm1,ymm8
        vpor   ymm0,ymm0,ymm11
        vpxor  ymm0,ymm0,ymm10
        vpxor  ymm10,ymm4,YMMWORD PTR [rsp+0x200]
        vpxor  ymm2,ymm0,ymm2
        vpsrlq ymm11,ymm10,0x14
        vpsllq ymm10,ymm10,0x2c
        vpor   ymm10,ymm10,ymm11
        vpxor  ymm11,ymm5,ymm15
        vpbroadcastq ymm15,QWORD PTR [rsi]
        vpsrlq ymm14,ymm11,0x15
        vpsllq ymm11,ymm11,0x2b
        vpor   ymm11,ymm11,ymm14
        vpandn ymm14,ymm10,ymm11
        vpxor  ymm14,ymm14,ymm15
        vpxor  ymm15,ymm14,ymm12
        vpsrlq ymm14,ymm13,0x2b
        vpsllq ymm13,ymm13,0x15
        vmovdqu YMMWORD PTR [rsp+0x1e0],ymm15
        vpor   ymm13,ymm13,ymm14
        vpandn ymm14,ymm11,ymm13
        vpxor  ymm15,ymm14,ymm10
        vpsrlq ymm14,ymm2,0x32
        vpsllq ymm2,ymm2,0xe
        vmovdqu YMMWORD PTR [rsp+0x100],ymm15
        vpor   ymm2,ymm2,ymm14
        vpandn ymm14,ymm13,ymm2
        vpxor  ymm11,ymm14,ymm11
        vmovdqu YMMWORD PTR [rsp+0x120],ymm11
        vpandn ymm11,ymm2,ymm12
        vpandn ymm12,ymm12,ymm10
        vpxor  ymm11,ymm11,ymm13
        vmovdqu YMMWORD PTR [rsp+0x140],ymm11
        vpxor  ymm11,ymm12,ymm2
        vpsrlq ymm2,ymm8,0x24
        vpsllq ymm8,ymm8,0x1c
        vmovdqu YMMWORD PTR [rsp+0x160],ymm11
        vpor   ymm8,ymm8,ymm2
        vpxor  ymm2,ymm0,YMMWORD PTR [rsp+0x220]
        vpsrlq ymm10,ymm2,0x2c
        vpsllq ymm2,ymm2,0x14
        vpor   ymm2,ymm2,ymm10
        vpxor  ymm10,ymm3,YMMWORD PTR [rsp+0x2e0]
        vpsrlq ymm11,ymm10,0x3d
        vpsllq ymm10,ymm10,0x3
        vpor   ymm10,ymm10,ymm11
        vpandn ymm11,ymm2,ymm10
        vpxor  ymm11,ymm11,ymm8
        vmovdqu YMMWORD PTR [rsp+0x180],ymm11
        vpxor  ymm11,ymm4,YMMWORD PTR [rsp+0x2a0]
        vpsrlq ymm12,ymm11,0x13
        vpsllq ymm11,ymm11,0x2d
        vpor   ymm11,ymm11,ymm12
        vpandn ymm12,ymm10,ymm11
        vpxor  ymm12,ymm12,ymm2
        vmovdqu YMMWORD PTR [rsp+0x200],ymm12
        vpsrlq ymm12,ymm7,0x3
        vpsllq ymm7,ymm7,0x3d
        vpor   ymm7,ymm7,ymm12
        vpandn ymm12,ymm11,ymm7
        vpxor  ymm10,ymm12,ymm10
        vpandn ymm12,ymm7,ymm8
        vpandn ymm8,ymm8,ymm2
        vpsrlq ymm2,ymm6,0x3f
        vpsllq ymm6,ymm6,0x1
        vpxor  ymm14,ymm12,ymm11
        vpor   ymm6,ymm6,ymm2
        vpsrlq ymm2,ymm9,0x3a
        vpxor  ymm12,ymm8,ymm7
        vpsllq ymm9,ymm9,0x6
        vmovdqu YMMWORD PTR [rsp+0x220],ymm12
        vpxor  ymm7,ymm0,YMMWORD PTR [rsp+0x260]
        vpor   ymm9,ymm9,ymm2
        vpxor  ymm2,ymm1,YMMWORD PTR [rsp+0x2c0]
        vpshufb ymm7,ymm7,YMMWORD PTR [rdx]
        vpsrlq ymm11,ymm2,0x27
        vpsllq ymm2,ymm2,0x19
        vpor   ymm11,ymm11,ymm2
        vpandn ymm2,ymm9,ymm11
        vpandn ymm8,ymm11,ymm7
        vpxor  ymm12,ymm2,ymm6
        vpxor  ymm2,ymm3,YMMWORD PTR [rsp+0x1c0]
        vpxor  ymm8,ymm8,ymm9
        vmovdqu YMMWORD PTR [rsp+0x2e0],ymm12
        vpsrlq ymm12,ymm2,0x2e
        vpsllq ymm2,ymm2,0x12
        vpor   ymm2,ymm12,ymm2
        vpandn ymm12,ymm7,ymm2
        vpxor  ymm15,ymm12,ymm11
        vpandn ymm11,ymm2,ymm6
        vpandn ymm6,ymm6,ymm9
        vpxor  ymm12,ymm11,ymm7
        vmovdqu YMMWORD PTR [rsp+0x2c0],ymm12
        vpxor  ymm12,ymm6,ymm2
        vpxor  ymm6,ymm0,YMMWORD PTR [rsp+0xe0]
        vpxor  ymm0,ymm0,YMMWORD PTR [rsp+0xc0]
        vmovdqu YMMWORD PTR [rsp+0x1a0],ymm12
        vpsrlq ymm2,ymm6,0x25
        vpsllq ymm6,ymm6,0x1b
        vpor   ymm2,ymm2,ymm6
        vpxor  ymm6,ymm3,YMMWORD PTR [rsp+0x20]
        vpxor  ymm3,ymm3,YMMWORD PTR [rsp+0x0]
        vpsrlq ymm7,ymm6,0x1c
        vpsllq ymm6,ymm6,0x24
        vpor   ymm7,ymm7,ymm6
        vpxor  ymm6,ymm4,YMMWORD PTR [rsp+0x60]
        vpxor  ymm4,ymm4,YMMWORD PTR [rsp+0x40]
        vpsrlq ymm12,ymm6,0x36
        vpsllq ymm6,ymm6,0xa
        vpor   ymm12,ymm12,ymm6
        vpxor  ymm6,ymm5,YMMWORD PTR [rsp+0x280]
        vpxor  ymm5,ymm5,YMMWORD PTR [rsp+0x80]
        vpandn ymm9,ymm7,ymm12
        vpsrlq ymm11,ymm6,0x31
        vpsllq ymm6,ymm6,0xf
        vpxor  ymm9,ymm9,ymm2
        vpor   ymm11,ymm11,ymm6
        vpandn ymm6,ymm12,ymm11
        vpxor  ymm6,ymm6,ymm7
        vmovdqu YMMWORD PTR [rsp+0x2a0],ymm6
        vpxor  ymm6,ymm1,YMMWORD PTR [rsp+0x240]
        vpxor  ymm1,ymm1,YMMWORD PTR [rsp+0xa0]
        vpshufb ymm6,ymm6,YMMWORD PTR [rcx]
        vpandn ymm13,ymm11,ymm6
        vpxor  ymm13,ymm13,ymm12
        vmovdqu YMMWORD PTR [rsp+0x280],ymm13
        vpandn ymm13,ymm6,ymm2
        vpandn ymm2,ymm2,ymm7
        vpxor  ymm2,ymm2,ymm6
        vpsrlq ymm6,ymm4,0x3e
        vpxor  ymm13,ymm13,ymm11
        vmovdqu YMMWORD PTR [rsp+0x260],ymm2
        vpsrlq ymm2,ymm5,0x2
        vpsllq ymm5,ymm5,0x3e
        vpor   ymm2,ymm2,ymm5
        vpsrlq ymm5,ymm1,0x9
        vpsllq ymm1,ymm1,0x37
        vpsllq ymm4,ymm4,0x2
        vpor   ymm1,ymm5,ymm1
        vpsrlq ymm5,ymm0,0x19
        vpor   ymm4,ymm6,ymm4
        vpsllq ymm0,ymm0,0x27
        vpor   ymm5,ymm5,ymm0
        vpandn ymm0,ymm1,ymm5
        vpxor  ymm0,ymm0,ymm2
        vmovdqu YMMWORD PTR [rsp+0x1c0],ymm0
        vpsrlq ymm0,ymm3,0x17
        vpsllq ymm3,ymm3,0x29
        vpor   ymm0,ymm0,ymm3
        vpandn ymm7,ymm0,ymm4
        vpandn ymm3,ymm5,ymm0
        vpxor  ymm7,ymm7,ymm5
        vpandn ymm5,ymm4,ymm2
        vpandn ymm2,ymm2,ymm1
        vpxor  ymm5,ymm5,ymm0
        vpxor  ymm3,ymm3,ymm1
        vpxor  ymm2,ymm2,ymm4
        vmovdqu YMMWORD PTR [rsp+0x240],ymm5

        add rsi, 8
        add r10, 1
        cmp r10, 0x18
        jne Lsha3_keccak4_f1600_alt2

        vmovdqu ymm4,YMMWORD PTR [rsp+0x1e0]
        vmovdqu ymm5,YMMWORD PTR [rsp+0x120]
        vmovdqu ymm0,YMMWORD PTR [rsp+0x100]
        vmovdqu ymm1,YMMWORD PTR [rsp+0x140]
        vmovdqu ymm12,YMMWORD PTR [rsp+0x1c0]
        vmovdqu YMMWORD PTR [rsp+0x1c0],ymm2
        vpunpcklqdq ymm2,ymm4,ymm0
        vpunpckhqdq ymm0,ymm4,ymm0
        vpunpcklqdq ymm4,ymm5,ymm1
        vpunpckhqdq ymm1,ymm5,ymm1
        vperm2i128 ymm6,ymm2,ymm4,0x20
        vperm2i128 ymm2,ymm2,ymm4,0x31
        vmovdqu ymm4,YMMWORD PTR [rsp+0x160]
        vperm2i128 ymm5,ymm0,ymm1,0x20
        vperm2i128 ymm0,ymm0,ymm1,0x31
        vmovdqu YMMWORD PTR [rdi+0x190],ymm2
        vmovdqu YMMWORD PTR [rdi+0x258],ymm0
        vmovdqu ymm0,YMMWORD PTR [rsp+0x180]
        vmovdqu YMMWORD PTR [rdi],ymm6
        vpunpcklqdq ymm2,ymm4,ymm0
        vpunpckhqdq ymm1,ymm4,ymm0
        vmovdqu ymm0,YMMWORD PTR [rsp+0x200]
        vmovdqu YMMWORD PTR [rdi+0xc8],ymm5
        vpunpcklqdq ymm4,ymm0,ymm10
        vpunpckhqdq ymm0,ymm0,ymm10
        vperm2i128 ymm6,ymm2,ymm4,0x20
        vperm2i128 ymm5,ymm1,ymm0,0x20
        vperm2i128 ymm2,ymm2,ymm4,0x31
        vmovdqu ymm4,YMMWORD PTR [rsp+0x220]
        vperm2i128 ymm1,ymm1,ymm0,0x31
        vmovdqu ymm0,YMMWORD PTR [rsp+0x2e0]
        vmovdqu YMMWORD PTR [rdi+0x1b0],ymm2
        vmovdqu YMMWORD PTR [rdi+0x278],ymm1
        vpunpcklqdq ymm2,ymm14,ymm4
        vpunpckhqdq ymm1,ymm14,ymm4
        vpunpcklqdq ymm4,ymm0,ymm8
        vpunpckhqdq ymm0,ymm0,ymm8
        vmovdqu YMMWORD PTR [rdi+0x20],ymm6
        vmovdqu YMMWORD PTR [rdi+0xe8],ymm5
        vperm2i128 ymm6,ymm2,ymm4,0x20
        vperm2i128 ymm5,ymm1,ymm0,0x20
        vperm2i128 ymm2,ymm2,ymm4,0x31
        vperm2i128 ymm1,ymm1,ymm0,0x31
        vmovdqu ymm4,YMMWORD PTR [rsp+0x2c0]
        vmovdqu ymm0,YMMWORD PTR [rsp+0x1a0]
        vmovdqu YMMWORD PTR [rdi+0x1d0],ymm2
        vmovdqu YMMWORD PTR [rdi+0x298],ymm1
        vpunpcklqdq ymm2,ymm15,ymm4
        vpunpckhqdq ymm1,ymm15,ymm4
        vpunpcklqdq ymm4,ymm0,ymm9
        vmovdqu YMMWORD PTR [rdi+0x108],ymm5
        vpunpckhqdq ymm0,ymm0,ymm9
        vmovdqu YMMWORD PTR [rdi+0x40],ymm6
        vperm2i128 ymm6,ymm2,ymm4,0x20
        vperm2i128 ymm2,ymm2,ymm4,0x31
        vperm2i128 ymm5,ymm1,ymm0,0x20
        vmovdqu ymm4,YMMWORD PTR [rsp+0x2a0]
        vperm2i128 ymm1,ymm1,ymm0,0x31
        vmovdqu ymm0,YMMWORD PTR [rsp+0x280]
        vmovdqu YMMWORD PTR [rdi+0x128],ymm5
        vmovdqu ymm5,YMMWORD PTR [rsp+0x260]
        vmovdqu YMMWORD PTR [rdi+0x1f0],ymm2
        vpunpcklqdq ymm2,ymm4,ymm0
        vpunpckhqdq ymm0,ymm4,ymm0
        vpunpcklqdq ymm4,ymm13,ymm5
        vmovdqu YMMWORD PTR [rdi+0x60],ymm6
        vperm2i128 ymm6,ymm2,ymm4,0x20
        vmovdqu YMMWORD PTR [rdi+0x2b8],ymm1
        vperm2i128 ymm2,ymm2,ymm4,0x31
        vpunpckhqdq ymm1,ymm13,ymm5
        vmovdqu YMMWORD PTR [rdi+0x80],ymm6
        vmovdqu ymm4,YMMWORD PTR [rsp+0x240]
        vperm2i128 ymm5,ymm0,ymm1,0x20
        vperm2i128 ymm0,ymm0,ymm1,0x31
        vmovdqu YMMWORD PTR [rdi+0x210],ymm2
        vpunpcklqdq ymm2,ymm12,ymm3
        vmovdqu YMMWORD PTR [rdi+0x2d8],ymm0
        vpunpckhqdq ymm0,ymm12,ymm3
        vpunpcklqdq ymm3,ymm7,ymm4
        vpunpckhqdq ymm1,ymm7,ymm4
        vmovdqu YMMWORD PTR [rdi+0x148],ymm5
        vperm2i128 ymm5,ymm2,ymm3,0x20
        vperm2i128 ymm2,ymm2,ymm3,0x31
        vmovdqu ymm3,YMMWORD PTR [rsp+0x1c0]
        vperm2i128 ymm4,ymm0,ymm1,0x20
        vperm2i128 ymm0,ymm0,ymm1,0x31
        vmovdqu YMMWORD PTR [rdi+0xa0],ymm5
        vextracti128 xmm15,ymm3,0x1
        vmovdqu YMMWORD PTR [rdi+0x168],ymm4
        vmovdqu YMMWORD PTR [rdi+0x230],ymm2
        vmovdqu YMMWORD PTR [rdi+0x2f8],ymm0
        vmovq QWORD PTR [rdi+0xc0],xmm3
        vmovhpd QWORD PTR [rdi+0x188],xmm3
        vmovq QWORD PTR [rdi+0x250],xmm15
        vmovhpd QWORD PTR [rdi+0x318],xmm15
        mov	rsp, r11
        .cfi_same_value r11
        .cfi_same_value rsp
        
#if WINDOWS_ABI
    CFI_STACKLOADU(xmm6,0)
    CFI_STACKLOADU(xmm7,16)
    CFI_STACKLOADU(xmm8,32)
    CFI_STACKLOADU(xmm9,48)
    CFI_STACKLOADU(xmm10,64)
    CFI_STACKLOADU(xmm11,80)
    CFI_STACKLOADU(xmm12,96)
    CFI_STACKLOADU(xmm13,112)
    CFI_STACKLOADU(xmm14,128)
    CFI_STACKLOADU(xmm15,144)
    CFI_STACKLOAD(rdi,160)
    CFI_STACKLOAD(rsi,168)
    CFI_INC_RSP(176)
#endif

    CFI_RET

S2N_BN_SIZE_DIRECTIVE(sha3_keccak4_f1600_alt2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif