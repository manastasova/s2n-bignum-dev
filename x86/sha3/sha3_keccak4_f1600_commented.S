// Copyright (c) 2017-2024 The OpenSSL Project Authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Written by Andy Polyakov, @dot-asm, initially for use in the OpenSSL
// project.

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3
// Input a[25], rc[24]; output a[25]
//
// Keccak-f1600 permutation operation is at the core of SHA3 and SHAKE 
// and is fully specified here:
//
//   https://keccak.team/files/Keccak-reference-3.0.pdf
//
//    extern void sha3_keccak4_f1600_commented(uint64_t a[25], const uint64_t rc[24]);
//
// Standard x86-64 ABI: RDI = a, RSI = rc
// Microsoft x64 ABI:   RCX = a, RDX = rc
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak4_f1600_commented)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak4_f1600_commented)
        .text    
        .align 32

S2N_BN_SYMBOL(sha3_keccak4_f1600_commented):
        _CET_ENDBR

#if WINDOWS_ABI
    push    rdi
    push    rsi
    mov     rdi, rcx
    mov     rsi, rdx
#endif

    push   rbp
    mov    rbp,rsp
    and    rsp,0xffffffffffffffe0
    sub    rsp,0x360

    // **** Bitstates Allocation **** //
    // ymm5     	A[0]	[state0[0], state1[0], state2[0], state3[0]]	    0x00, 0xC8, 0x190, 0x258
    // 0x0(%rsp)	A[1]	[state0[1], state1[1], state2[1], state3[1]]	    0x08, 0xD0, 0x198, 0x260
    // 0x20(%rsp)	A[2]	[state0[2], state1[2], state2[2], state3[2]]	    0x10, 0xD8, 0x1A0, 0x268
    // 0x40(%rsp)	A[3]	[state0[3], state1[3], state2[3], state3[3]]	    0x18, 0xE0, 0x1A8, 0x270
    // 0x60(%rsp)	A[4]	[state0[4], state1[4], state2[4], state3[4]]	    0x20, 0xE8, 0x1B0, 0x278
    // 0x80(%rsp)	A[5]	[state0[5], state1[5], state2[5], state3[5]]    	0x28, 0xF0, 0x1B8, 0x280
    // 0xa0(%rsp)	A[6]	[state0[6], state1[6], state2[6], state3[6]]    	0x30, 0xF8, 0x1C0, 0x288
    // 0xc0(%rsp)	A[7]	[state0[7], state1[7], state2[7], state3[7]]    	0x38, 0x100, 0x1C8, 0x290
    // 0xe0(%rsp)	A[8]	[state0[8], state1[8], state2[8], state3[8]]    	0x40, 0x108, 0x1D0, 0x298
    // 0x100(%rsp)	A[9]	[state0[9], state1[9], state2[9], state3[9]]    	0x48, 0x110, 0x1D8, 0x2A0
    // 0x120(%rsp)	A[10]	[state0[10], state1[10], state2[10], state3[10]]	0x50, 0x118, 0x1E0, 0x2A8
    // 0x140(%rsp)	A[11]	[state0[11], state1[11], state2[11], state3[11]]	0x58, 0x120, 0x1E8, 0x2B0
    // 0x160(%rsp)	A[12]	[state0[12], state1[12], state2[12], state3[12]]	0x60, 0x128, 0x1F0, 0x2B8
    // 0x180(%rsp)	A[13]	[state0[13], state1[13], state2[13], state3[13]]	0x68, 0x130, 0x1F8, 0x2C0
    // 0x1a0(%rsp)	A[14]	[state0[14], state1[14], state2[14], state3[14]]	0x70, 0x138, 0x200, 0x2C8
    // 0x1c0(%rsp)	A[15]	[state0[15], state1[15], state2[15], state3[15]]	0x78, 0x140, 0x208, 0x2D0
    // 0x1e0(%rsp)	A[16]	[state0[16], state1[16], state2[16], state3[16]]	0x80, 0x148, 0x210, 0x2D8
    // 0x200(%rsp)	A[17]	[state0[17], state1[17], state2[17], state3[17]]	0x88, 0x150, 0x218, 0x2E0
    // 0x220(%rsp)	A[18]	[state0[18], state1[18], state2[18], state3[18]]	0x90, 0x158, 0x220, 0x2E8
    // 0x240(%rsp)	A[19]	[state0[19], state1[19], state2[19], state3[19]]	0x98, 0x160, 0x228, 0x2F0
    // 0x260(%rsp)	A[20]	[state0[20], state1[20], state2[20], state3[20]]	0xA0, 0x168, 0x230, 0x2F8
    // 0x280(%rsp)	A[21]	[state0[21], state1[21], state2[21], state3[21]]	0xA8, 0x170, 0x238, 0x300
    // 0x2a0(%rsp)	A[22]	[state0[22], state1[22], state2[22], state3[22]]	0xB0, 0x178, 0x240, 0x308
    // 0x2c0(%rsp)	A[23]	[state0[23], state1[23], state2[23], state3[23]]	0xB8, 0x180, 0x248, 0x310
    // 0x2e0(%rsp)	A[24]	[state0[24], state1[24], state2[24], state3[24]]	0xC0, 0x188, 0x250, 0x318

    # Load 32 bytes from each of the 4 states
    vmovdqu ymm0,YMMWORD PTR [rdi]                   # load state0[0..3] (32 bytes from offset 0)
    vmovdqu ymm1,YMMWORD PTR [rdi+0xc8]              # load state1[0..3] (32 bytes from offset 200)
    vmovdqu ymm2,YMMWORD PTR [rdi+0x190]             # load state2[0..3] (32 bytes from offset 400)
    vmovdqu ymm3,YMMWORD PTR [rdi+0x258]             # load state3[0..3] (32 bytes from offset 600)

    # Interleave low and high qwords from ymm0 and ymm1
    vpunpcklqdq ymm4,ymm0,ymm1                       # ymm4 = [state0[0] | state1[0] | state0[2] | state1[2]]  
    vpunpckhqdq ymm5,ymm0,ymm1                       # ymm5 = [state0[1] | state1[1] | state0[3] | state1[3]] 

    # Interleave low and high qwords from ymm2 and ymm3
    vpunpcklqdq ymm6,ymm2,ymm3                       # ymm6 = [state2[0] | state3[0] | state2[2] | state3[2]]
    vpunpckhqdq ymm7,ymm2,ymm3                       # ymm7 = [state2[1] | state3[1] | state2[3] | state3[3]]

    # Permute 128-bit lanes to complete the interleave
    vperm2i128 ymm0,ymm4,ymm6,0x20                   # ymm0 = [state0[0] | state1[0] | state2[0] | state3[0]]
    vperm2i128 ymm2,ymm4,ymm6,0x31                   # ymm2 = [state0[2] | state1[2] | state2[2] | state3[2]]
    vperm2i128 ymm1,ymm5,ymm7,0x20                   # ymm1 = [state0[1] | state1[1] | state2[1] | state3[1]]
    vperm2i128 ymm3,ymm5,ymm7,0x31                   # ymm3 = [state0[3] | state1[3] | state2[3] | state3[3]]

    # Store results
    vmovdqa ymm5,ymm0                                # store states [0] -> ymm5
    vmovdqa YMMWORD PTR [rsp],ymm1                   # store states [1] -> memory 
    vmovdqa YMMWORD PTR [rsp+0x20],ymm2              # store states [2] -> memory 
    vmovdqa YMMWORD PTR [rsp+0x40],ymm3              # store states [3] -> memory

    # Load 32 bytes from each of the 4 states (starting at offset 32)
    vmovdqu ymm0,YMMWORD PTR [rdi+0x20]              # load state0[4..7] (32 bytes from offset 32)
    vmovdqu ymm1,YMMWORD PTR [rdi+0xe8]              # load state1[4..7] (32 bytes from offset 232)
    vmovdqu ymm2,YMMWORD PTR [rdi+0x1b0]             # load state2[4..7] (32 bytes from offset 432)
    vmovdqu ymm3,YMMWORD PTR [rdi+0x278]             # load state3[4..7] (32 bytes from offset 632)

    # Interleave low and high qwords from ymm0 and ymm1
    vpunpcklqdq ymm4,ymm0,ymm1                       # ymm4 = [state0[4] | state1[4] | state0[6] | state1[6]]
    vpunpckhqdq ymm6,ymm0,ymm1                       # ymm6 = [state0[5] | state1[5] | state0[7] | state1[7]]


    # Interleave low and high qwords from ymm2 and ymm3
    vpunpcklqdq ymm7, ymm2, ymm3                     # ymm7 = [state2[4] | state3[4] | state2[6] | state3[6]]
    vpunpckhqdq ymm8, ymm2, ymm3                     # ymm8 = [state2[5] | state3[5] | state2[7] | state3[7]]


    # Permute 128-bit lanes to complete the interleave
    vperm2i128  ymm0, ymm4, ymm7, 0x20               # ymm0 = [state0[4] | state1[4] | state2[4] | state3[4]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31               # ymm2 = [state0[6] | state1[6] | state2[6] | state3[6]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20               # ymm1 = [state0[5] | state1[5] | state2[5] | state3[5]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31               # ymm3 = [state0[7] | state1[7] | state2[7] | state3[7]]

    # Store results
    vmovdqa    [rsp+0x60], ymm0                      # store states [4] --> memory
    vmovdqa    [rsp+0x80], ymm1                      # store states [5] --> memory
    vmovdqa    [rsp+0xa0], ymm2                      # store states [6] --> memory
    vmovdqa    [rsp+0xc0], ymm3                      # store states [7] --> memory

    # Load 32 bytes from each of the 4 states (starting at offset 64)
    vmovdqu     ymm0, [rdi+0x40]                     # load state0[8..11] (32 bytes from offset 64)
    vmovdqu     ymm1, [rdi+0x108]                    # load state1[8..11] (32 bytes from offset 264)
    vmovdqu     ymm2, [rdi+0x1d0]                    # load state2[8..11] (32 bytes from offset 464)
    vmovdqu     ymm3, [rdi+0x298]                    # load state3[8..11] (32 bytes from offset 664)

    # Interleave low and high qwords from ymm0 and ymm1
    vpunpcklqdq ymm4, ymm0, ymm1                     # ymm4 = [state0[8] | state1[8] | state0[10] | state1[10]]
    vpunpckhqdq ymm6, ymm0, ymm1                     # ymm6 = [state0[9] | state1[9] | state0[11] | state1[11]]

    # Interleave low and high qwords from ymm2 and ymm3
    vpunpcklqdq ymm7, ymm2, ymm3                     # ymm7 = [state2[8] | state3[8] | state2[10] | state3[10]]
    vpunpckhqdq ymm8, ymm2, ymm3                     # ymm8 = [state2[9] | state3[9] | state2[11] | state3[11]]

    # Permute 128-bit lanes to complete the interleave
    vperm2i128  ymm0, ymm4, ymm7, 0x20               # ymm0 = [state0[8] | state1[8] | state2[8] | state3[8]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31               # ymm2 = [state0[10] | state1[10] | state2[10] | state3[10]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20               # ymm1 = [state0[9] | state1[9] | state2[9] | state3[9]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31               # ymm3 = [state0[11] | state1[11] | state2[11] | state3[11]]

    # Store results
    vmovdqa    [rsp+0xe0], ymm0                      # store states [8] --> memory
    vmovdqa    [rsp+0x100], ymm1                     # store states [9] --> memory
    vmovdqa    [rsp+0x120], ymm2                     # store states [10] --> memory
    vmovdqa    [rsp+0x140], ymm3                     # store states [11] --> memory


    # Load 32 bytes from each of the 4 states (starting at offset 96)
    vmovdqu     ymm0, [rdi+0x60]                     # load state0[12..15] (32 bytes from offset 96)
    vmovdqu     ymm1, [rdi+0x128]                    # load state1[12..15] (32 bytes from offset 296)
    vmovdqu     ymm2, [rdi+0x1f0]                    # load state2[12..15] (32 bytes from offset 496)
    vmovdqu     ymm3, [rdi+0x2b8]                    # load state3[12..15] (32 bytes from offset 696)

    # Interleave low and high qwords from ymm0 and ymm1
    vpunpcklqdq ymm4, ymm0, ymm1                     # ymm4 = [state0[12] | state1[12] | state0[14] | state1[14]]
    vpunpckhqdq ymm6, ymm0, ymm1                     # ymm6 = [state0[13] | state1[13] | state0[15] | state1[15]]

    # Interleave low and high qwords from ymm2 and ymm3
    vpunpcklqdq ymm7, ymm2, ymm3                     # ymm7 = [state2[12] | state3[12] | state2[14] | state3[14]]
    vpunpckhqdq ymm8, ymm2, ymm3                     # ymm8 = [state2[13] | state3[13] | state2[15] | state3[15]]

    # Permute 128-bit lanes to complete the interleave
    vperm2i128  ymm0, ymm4, ymm7, 0x20               # ymm0 = [state0[12] | state1[12] | state2[12] | state3[12]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31               # ymm2 = [state0[14] | state1[14] | state2[14] | state3[14]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20               # ymm1 = [state0[13] | state1[13] | state2[13] | state3[13]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31               # ymm3 = [state0[15] | state1[15] | state2[15] | state3[15]]

    # Store results
    vmovdqa    [rsp+0x160], ymm0                     # store states [12] --> memory
    vmovdqa    [rsp+0x180], ymm1                     # store states [13] --> memory
    vmovdqa    [rsp+0x1a0], ymm2                     # store states [14] --> memory
    vmovdqa    [rsp+0x1c0], ymm3                     # store states [15] --> memory

    # Load 32 bytes from each of the 4 states (starting at offset 128)
    vmovdqu     ymm0, [rdi+0x80]                     # load state0[16..19] (32 bytes from offset 128)
    vmovdqu     ymm1, [rdi+0x148]                    # load state1[16..19] (32 bytes from offset 328)
    vmovdqu     ymm2, [rdi+0x210]                    # load state2[16..19] (32 bytes from offset 528)
    vmovdqu     ymm3, [rdi+0x2d8]                    # load state3[16..19] (32 bytes from offset 728)

    # Interleave low and high qwords from ymm0 and ymm1
    vpunpcklqdq ymm4, ymm0, ymm1                     # ymm4 = [state0[16] | state1[16] | state0[18] | state1[18]]
    vpunpckhqdq ymm6, ymm0, ymm1                     # ymm6 = [state0[17] | state1[17] | state0[19] | state1[19]]

    # Interleave low and high qwords from ymm2 and ymm3
    vpunpcklqdq ymm7, ymm2, ymm3                     # ymm7 = [state2[16] | state3[16] | state2[18] | state3[18]]
    vpunpckhqdq ymm8, ymm2, ymm3                     # ymm8 = [state2[17] | state3[17] | state2[19] | state3[19]]

    # Permute 128-bit lanes to complete the interleave
    vperm2i128  ymm0, ymm4, ymm7, 0x20                # ymm0 = [state0[16] | state1[16] | state2[16] | state3[16]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31                # ymm2 = [state0[18] | state1[18] | state2[18] | state3[18]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20                # ymm1 = [state0[17] | state1[17] | state2[17] | state3[17]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31                # ymm3 = [state0[19] | state1[19] | state2[19] | state3[19]]

    # Store results
    vmovdqa    [rsp+0x1e0], ymm0                      # store states [16] --> memory
    vmovdqa    [rsp+0x200], ymm1                      # store states [17] --> memory
    vmovdqa    [rsp+0x220], ymm2                      # store states [18] --> memory
    vmovdqa    [rsp+0x240], ymm3                      # store states [19] --> memory

    # Load 32 bytes from each of the 4 states (starting at offset 160)
    vmovdqu     ymm0, [rdi+0xa0]                      # load state0[20..23] (32 bytes from offset 160)
    vmovdqu     ymm1, [rdi+0x168]                     # load state1[20..23] (32 bytes from offset 360)
    vmovdqu     ymm2, [rdi+0x230]                     # load state2[20..23] (32 bytes from offset 560)
    vmovdqu     ymm3, [rdi+0x2f8]                     # load state3[20..23] (32 bytes from offset 760)

    # Interleave low and high qwords from ymm0 and ymm1
    vpunpcklqdq ymm4, ymm0, ymm1                      # ymm4 = [state0[20] | state1[20] | state0[22] | state1[22]]
    vpunpckhqdq ymm6, ymm0, ymm1                      # ymm6 = [state0[21] | state1[21] | state0[23] | state1[23]]

    # Interleave low and high qwords from ymm2 and ymm3
    vpunpcklqdq ymm7, ymm2, ymm3                      # ymm7 = [state2[20] | state3[20] | state2[22] | state3[22]]
    vpunpckhqdq ymm8, ymm2, ymm3                      # ymm8 = [state2[21] | state3[21] | state2[23] | state3[23]]

    # Permute 128-bit lanes to complete the interleave
    vperm2i128  ymm0, ymm4, ymm7, 0x20                # ymm0 = [state0[20] | state1[20] | state2[20] | state3[20]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31                # ymm2 = [state0[22] | state1[22] | state2[22] | state3[22]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20                # ymm1 = [state0[21] | state1[21] | state2[21] | state3[21]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31                # ymm3 = [state0[23] | state1[23] | state2[23] | state3[23]]

    # Store results
    vmovdqa    [rsp+0x260], ymm0                      # store states [20] --> memory
    vmovdqa    [rsp+0x280], ymm1                      # store states [21] --> memory
    vmovdqa    [rsp+0x2a0], ymm2                      # store states [22] --> memory
    vmovdqa    [rsp+0x2c0], ymm3                      # store states [23] --> memory

    # load states [24] ---> 192
    vmovq       xmm1, [rdi+0xc0]
    vpinsrq     xmm1, xmm1, [rdi+0x188], 0x1
    vmovq       xmm2, [rdi+0x250]
    vpinsrq     xmm2, xmm2, [rdi+0x318], 0x1
    vinserti128 ymm3, ymm1, xmm2, 0x1
    vmovdqa     [rsp+0x2e0], ymm3


    mov    rax,0x0

    .keccak_loop:

    // Theta step
    # ymm5                                              # state A[0]
    vmovdqa    ymm12, [rsp+0x80]                        # state A[5]
    vmovdqa    ymm13, [rsp+0x120]                       # state A[10]
    vmovdqa    ymm11, [rsp+0x1c0]                       # state A[15]
    vmovdqa    ymm10, [rsp+0x260]                       # state A[20]
    vpxor      ymm1, ymm5, ymm12                        # A[0] xor A[5]
    vpxor      ymm0, ymm13, ymm11                       # A[10] xor A[15]
    vpxor      ymm1, ymm1, ymm0                         # (A[0] xor A[5]) xor (A[10] xor A[15])
    vpxor      ymm1, ymm1, ymm10                        # A[20] xor (A[0] xor A[5] xor A[10] xor A[15]) = C[0]
             
    vmovdqa    ymm4, [rsp+0x0]                          # state A[1]
    vmovdqa    ymm6, [rsp+0x1e0]                        # state A[16]
    vpxor      ymm8, ymm4, [rsp+0xa0]                   # A[6] xor A[1]
    vpxor      ymm0, ymm6, [rsp+0x140]                  # A[11] xor A[16]
    vpxor      ymm8, ymm8, ymm0                         # (A[11] xor A[16]) xor (A[6] xor A[1])
    vpxor      ymm8, ymm8, [rsp+0x280]                  # A[21] xor (A[11] xor A[16] xor A[6] xor A[1]) = C[1]
             
    vmovdqa    ymm0, [rsp+0x20]                         # state A[2]
    vpxor      ymm7, ymm0, [rsp+0xc0]                   # A[7] xor A[2]
    vmovdqa    ymm14, [rsp+0x200]                       # state A[17]
    vpxor      ymm0, ymm14, [rsp+0x160]                 # A[12] xor A[17]
    vpxor      ymm7, ymm7, ymm0                         # (A[12] xor A[17]) xor (A[7] xor A[2])
    vpxor      ymm7, ymm7, [rsp+0x2a0]                  # A[22] xor (A[12] xor A[17] xor A[7] xor A[2]) = C[2]
             
    vmovdqa    ymm3, [rsp+0x40]                         # state A[3]
    vpxor      ymm6, ymm3, [rsp+0xe0]                   # A[8] xor A[3]
    vmovdqa    ymm0, [rsp+0x220]                        # state A[18]
    vpxor      ymm0, ymm0, [rsp+0x180]                  # A[13] xor A[18]
    vpxor      ymm6, ymm6, ymm0                         # (A[13] xor A[18]) xor (A[8] xor A[3])
    vpxor      ymm6, ymm6, [rsp+0x2c0]                  # A[23] xor (A[13] xor A[18] xor A[8] xor A[3]) = C[3]
             
    vmovdqa    ymm4, [rsp+0x60]                         # state A[4]
    vpxor      ymm2, ymm4, [rsp+0x100]                  # A[9] xor A[4]
    vmovdqa    ymm0, [rsp+0x240]                        # state A[19]
    vpxor      ymm0, ymm0, [rsp+0x1a0]                  # A[14] xor A[19]
    vpxor      ymm2, ymm2, ymm0                         # (A[14] xor A[19]) xor (A[9] xor A[4])
    vpxor      ymm2, ymm2, [rsp+0x2e0]                  # A[24] xor (A[14] xor A[19] xor A[9] xor A[4]) = C[4]

    // C[0]	ymm1	A[0] xor A[5] xor A[10] xor A[15] xor A[20]
    // C[1]	ymm8	A[1] xor A[6] xor A[11] xor A[16] xor A[21]
    // C[2]	ymm7	A[2] xor A[7] xor A[12] xor A[17] xor A[22]
    // C[3]	ymm6	A[3] xor A[8] xor A[13] xor A[18] xor A[23]
    // C[4]	ymm2	A[4] xor A[9] xor A[14] xor A[19] xor A[24]


    vpsllq     ymm4, ymm8, 0x1                          # C[1] << 1
    vpsrlq     ymm0, ymm8, 0x3f                         # D[0] --> shift left C[0]
    vpor       ymm4, ymm4, ymm0                         # completing rotation
              
    vpsllq     ymm3, ymm7, 0x1                          # C[2] << 1
    vpsrlq     ymm0, ymm7, 0x3f                         # right shift for rotation
    vpor       ymm3, ymm3, ymm0                         # completing rotation
              
    vpsllq     ymm0, ymm6, 0x1                          # C[3] << 1
    vpsrlq     ymm9, ymm6, 0x3f                         # right shift for rotation
    vpor       ymm0, ymm0, ymm9                         # completing rotation
              
    vpxor      ymm4, ymm4, ymm2                         # D[0] = C[4] xor C[1]<<1
    vpxor      ymm3, ymm3, ymm1                         # D[1] = C[0] xor C[2]<<1
    vpxor      ymm0, ymm0, ymm8                         # D[2] = C[1] xor C[3]<<1

    // D[0]	ymm4	C[4] xor ROT(C[1], 1)	C[4] XOR left rotation of C[1] by 1 bit
    // D[1]	ymm3	C[0] xor ROT(C[2], 1)	C[0] XOR left rotation of C[2] by 1 bit
    // D[2]	ymm0	C[1] xor ROT(C[3], 1)	C[1] XOR left rotation of C[3] by 1 bit
    // D[3]	ymm2	C[2] xor ROT(C[4], 1)	C[2] XOR left rotation of C[4] by 1 bit
    // D[4]	ymm1	C[3] xor ROT(C[0], 1)	C[3] XOR left rotation of C[0] by 1 bit

    vpsllq     ymm8, ymm2, 0x1                          # C[4] <<< 1
    vpsrlq     ymm2, ymm2, 0x3f                         # right shift for rotation
    vpor       ymm2, ymm8, ymm2                         # completing rotation

    vpxor      ymm14, ymm5, ymm4                        # A[0] xor D[0]

    vpxor      ymm9, ymm0, YMMWORD PTR [rsp+0xc0]       # A[7] xor D[2]
    vmovdqa    YMMWORD PTR [rsp+0x320], ymm9            # store A[7] READY

    vpxor      ymm15, ymm12, ymm4                       # A[5] xor D[0] keep A[5] in ymm15 READY
    vpxor      ymm12, ymm3, YMMWORD PTR [rsp+0x0]       # A[1] xor D[1] keep A[1] in ymm12 READY
    vpxor      ymm8, ymm3 , YMMWORD PTR [rsp+0x140]     # A[11] xor D[1] keep A[11] in ymm8 READY

    vmovdqa    YMMWORD PTR [rsp+0x340], ymm14           # store A[0] READY

    vpxor      ymm14, ymm13, ymm4                       # A[10] xor D[0] keep A[10] in ymm14 READY
    vpxor      ymm13, ymm11, ymm4                       # A[15] xor D[0] keep A[15] in ymm13 READY
    vpxor      ymm11, ymm3, YMMWORD PTR [rsp+0xa0]      # A[6] xor D[1] keep A[6] in ymm11 READY
    vpxor      ymm4, ymm10, ymm4                        # A[20] xor D[0] keep A[20] in ymm4 READY
    vpxor      ymm10, ymm0, YMMWORD PTR [rsp+0x20]      # A[2] xor D[2] keep A[2] in ymm10 READY

    vpxor      ymm2, ymm7, ymm2                         # D[3] = C[2] xor C[4]<<<1

    vpsllq     ymm7, ymm1, 0x1                          # C[0] <<< 1 (for rotation)
    vpsrlq     ymm1, ymm1, 0x3f                         # C[0] >> 63 (for rotation)
    vpor       ymm1, ymm7, ymm1                         # C[0] = C[0] <<< 1

    vpxor      ymm1, ymm6, ymm1                         # D[4] = C[3] xor C[0] <<< 1

    vpxor      ymm7, ymm3, YMMWORD PTR [rsp+0x1e0]      # A[16] xor D[1] keep A[16] in ymm7 READY
    vpxor      ymm3, ymm3, YMMWORD PTR [rsp+0x280]      # A[21] xor D[1] keep A[21] in ymm3 READY
    vpxor      ymm5, ymm2, YMMWORD PTR [rsp+0x40]       # A[3] xor D[3]
    vpxor      ymm9, ymm0, YMMWORD PTR [rsp+0x160]      # A[12] xor D[2] keep A[12] in ymm9 READY
    vpxor      ymm6, ymm0, YMMWORD PTR [rsp+0x200]      # A[17] xor D[2] keep A[17] in ymm6 READY
    vpxor      ymm0, ymm0, YMMWORD PTR [rsp+0x2a0]      # A[22] xor D[2] keep A[22] in ymm0 READY

    vmovdqa    YMMWORD PTR [rsp+0x0], ymm5              # store A[3] READY
     
    vpxor      ymm5, ymm2, YMMWORD PTR [rsp+0xe0]       # A[8] xor D[3]
    vmovdqa    YMMWORD PTR [rsp+0xa0], ymm5             # store A[8] READY
    vpxor      ymm5, ymm2, YMMWORD PTR [rsp+0x180]      # A[13] xor D[3]
    vmovdqa    YMMWORD PTR [rsp+0x140], ymm5            # store A[13] READY
    vpxor      ymm5, ymm2, YMMWORD PTR [rsp+0x220]      # A[18] xor D[3] 
    vpxor      ymm2, ymm2, YMMWORD PTR [rsp+0x2c0]      # A[23] xor D[3] keep A[23] in ymm2 READY
    vmovdqa    YMMWORD PTR [rsp+0x1e0], ymm5            # store A[18] xor D[3] READY
    vpxor      ymm5, ymm1, YMMWORD PTR [rsp+0x60]       # A[4] xor D[4]
    vmovdqa    YMMWORD PTR [rsp+0x280], ymm5            # store A[4] READY
    vpxor      ymm5, ymm1, YMMWORD PTR [rsp+0x100]      # A[9] xor D[4]
    vmovdqa    YMMWORD PTR [rsp+0x20], ymm5             # store A[9] READY
    vpxor      ymm5, ymm1, YMMWORD PTR [rsp+0x1a0]      # A[14] xor D[4]
    vmovdqa    YMMWORD PTR [rsp+0x160], ymm5            # store A[14] READY
    vpxor      ymm5, ymm1, YMMWORD PTR [rsp+0x240]      # A[19] xor D[4] keep 
    vmovdqa   YMMWORD PTR [rsp+0x200], ymm5             # Store A[19] READY
    vpxor      ymm1, ymm1, YMMWORD PTR [rsp+0x2e0]      # A[24] xor D[4]
    vmovdqa    YMMWORD PTR [rsp+0x40], ymm1             # store A[24] READY

    // A'[0]	0x340(rsp)	A[0] XOR D[0]	Stored to stack
    // A'[1]	ymm12	    A[1] XOR D[1]	Kept in register
    // A'[2]	ymm10	    A[2] XOR D[2]	Kept in register
    // A'[3]	0x0(rsp)	A[3] XOR D[3]	Stored to stack
    // A'[4]	0x280(rsp)	A[4] XOR D[4]	Stored to stack
    // A'[5]	ymm15	    A[5] XOR D[0]	Kept in register
    // A'[6]	ymm11	    A[6] XOR D[1]	Kept in register
    // A'[7]	0x320(rsp)	A[7] XOR D[2]	Stored to stack
    // A'[8]	0xa0(rsp)	A[8] XOR D[3]	Stored to stack
    // A'[9]	0x20(rsp)	A[9] XOR D[4]	Stored to stack
    // A'[10]	ymm14   	A[10] XOR D[0]	Kept in register
    // A'[11]	ymm8	    A[11] XOR D[1]	Kept in register
    // A'[12]	ymm9	    A[12] XOR D[2]	Kept in register
    // A'[13]	0x140(rsp)	A[13] XOR D[3]	Stored to stack
    // A'[14]	0x160(rsp)	A[14] XOR D[4]	Stored to stack
    // A'[15]	ymm13   	A[15] XOR D[0]	Kept in register
    // A'[16]	ymm7	    A[16] XOR D[1]	Kept in register
    // A'[17]	ymm6	    A[17] XOR D[2]	Kept in register
    // A'[18]	0x1e0(rsp)	A[18] XOR D[3]	Stored to stack
    // A'[19]	0x200(rsp)	A[19] XOR D[4]	Stored to stack
    // A'[20]	ymm4	    A[20] XOR D[0]	Kept in register
    // A'[21]	ymm3	    A[21] XOR D[1]	Kept in register
    // A'[22]	ymm0	    A[22] XOR D[2]	Kept in register
    // A'[23]	ymm2	    A[23] XOR D[3]	Kept in register
    // A'[24]	0x40(rsp)	A[24] XOR D[4]	Stored to stack

    vpsrlq     ymm1, ymm15, 0x1c                   # Shift right A'[5] by 28 bits into ymm1
    vpsllq     ymm15, ymm15, 0x24                  # Shift left A'[5] by 36 bits
    vpor       ymm1, ymm15, ymm1                   # Combine to perform ROL 36 on A'[5]
    vmovdqa    YMMWORD PTR [rsp+0x240], ymm1       # Store A'[5]<<<36 for rho step (will be used as B[19] in chi step)

    vpsrlq     ymm1, ymm14, 0x3d                   # Shift right A'[10] by 61 bits into ymm1
    vpsllq     ymm14, ymm14, 0x3                   # Shift left A'[10] by 3 bits
    vpor       ymm15, ymm14, ymm1                  # Combine to perform ROL 3 on A'[10]
    vmovdqa    YMMWORD PTR [rsp+0x2c0], ymm15      # Store A'[10]<<<3 for rho step (will be used as B[23] in chi step)

    vpsrlq     ymm1, ymm13, 0x17                   # Shift right A'[15] by 23 bits into ymm1
    vpsllq     ymm13, ymm13, 0x29                  # Shift left A'[15] by 41 bits
    vpor       ymm13, ymm13, ymm1                  # Combine to perform ROL 41 on A'[15]
    vmovdqa    YMMWORD PTR [rsp+0x2a0], ymm13      # Store A'[15]<<<41 for rho step (will be used as B[22] in chi step)

    vpsrlq     ymm1, ymm4, 0x2e                    # Shift right A'[20] by 46 bits into ymm1
    vpsllq     ymm4, ymm4, 0x12                    # Shift left A'[20] by 18 bits
    vpor       ymm4, ymm4, ymm1                    # Combine to perform ROL 18 on A'[20]
    vmovdqa    YMMWORD PTR [rsp+0x180], ymm4       # Store A'[20]<<<18 for rho step (will be used as B[16] in chi step)

    vpsrlq     ymm1, ymm12, 0x3f                   # Shift right A'[1] by 63 bits into ymm1
    vpsllq     ymm12, ymm12, 0x1                   # Shift left A'[1] by 1 bit
    vpor       ymm12, ymm12, ymm1                  # Combine to perform ROL 1 on A'[1]
    vmovdqa    YMMWORD PTR [rsp+0x1a0], ymm12      # Store A'[1]<<<1 for rho step (will be used as B[14] in chi step)

    vpsrlq     ymm1, ymm11, 0x14                   # Shift right A'[6] by 20 bits into ymm1
    vpsllq     ymm11, ymm11, 0x2c                  # Shift left A'[6] by 44 bits
    vpor       ymm11, ymm11, ymm1                  # Combine to perform ROL 44 on A'[6]
    vmovdqa    YMMWORD PTR [rsp+0x100], ymm11      # Store A'[6]<<<44 for rho step (will be used as B[9] in chi step)

    vpsrlq     ymm1, ymm8, 0x36                    # Shift right A'[11] by 54 bits into ymm1
    vpsllq     ymm8, ymm8, 0xa                     # Shift left A'[11] by 10 bits
    vpor       ymm8, ymm8, ymm1                    # Combine to perform ROL 10 on A'[11] (will be used as B[7] in chi step)
            
    vpsrlq     ymm1, ymm7, 0x13                    # Shift right A'[16] by 19 bits into ymm1
    vpsllq     ymm7, ymm7, 0x2d                    # Shift left A'[16] by 45 bits
    vpor       ymm7, ymm7, ymm1                    # Combine to perform ROL 45 on A'[16] (will be used as B[5] in chi step)
            
    vpsrlq     ymm1, ymm3, 0x3e                    # Shift right A'[21] by 62 bits into ymm1
    vpsllq     ymm3, ymm3, 0x2                     # Shift left A'[21] by 2 bits
    vpor       ymm3, ymm3, ymm1                    # Combine to perform ROL 2 on A'[21]
    vmovdqa    YMMWORD PTR [rsp+0x2e0], ymm3       # Store A'[21]<<<2 for rho step (will be used as B[24] in chi step)

    vpsrlq ymm1,ymm10,0x2
    vpsllq     ymm10, ymm10, 0x3e                  # Shift left A'[2] by 62 bits
    vpor       ymm10, ymm10, ymm1                  # Combine to perform ROL 62 on A'[2]
    vmovdqa    YMMWORD PTR [rsp+0x60], ymm10       # Store A'[2]<<<62 for rho step (will be used as B[4] in chi step)

    vmovdqa    ymm3, YMMWORD PTR [rsp+0x320]       # Load A'[7] from stack
    vpsllq     ymm5, ymm3, 0x6                     # Shift left A'[7] by 6 bits
    vpsrlq     ymm1, ymm3, 0x3a                    # Shift right A'[7] by 58 bits
    vpor       ymm5, ymm5, ymm1                    # Combine to perform ROL 6 on A'[7] (will be used as B[3] in chi step)

    vpsrlq     ymm1, ymm9, 0x15                    # Shift right A'[12] by 21 bits into ymm1
    vpsllq     ymm9, ymm9, 0x2b                    # Shift left A'[12] by 43 bits
    vpor       ymm9, ymm9, ymm1                    # Combine to perform ROL 43 on A'[12]
    vmovdqa    YMMWORD PTR [rsp+0x320], ymm9       # Store A'[12]<<<43 for rho step (will be used as B[17] in chi step)

    vpsrlq     ymm1, ymm6, 0x31                    # Shift right A'[17] by 49 bits into ymm1
    vpsllq     ymm6, ymm6, 0xf                     # Shift left A'[17] by 15 bits
    vpor       ymm6, ymm6, ymm1                    # Combine to perform ROL 15 on A'[17] (will be used as B[11] in chi step)

    vmovdqa    ymm4, YMMWORD PTR [rsp+0x0]         # Load A'[3] from stack
    vpsllq     ymm3, ymm4, 0x1c                    # Shift left A'[3] by 28 bits
    vpsrlq     ymm1, ymm4, 0x24                    # Shift right A'[3] by 36 bits
    vpor       ymm3, ymm3, ymm1                    # Combine to perform ROL 28 on A'[3] (will be used as B[18] in chi step)

    vmovdqa    ymm9, YMMWORD PTR [rsp+0x140]       # Load A'[13] from stack
    vpsllq     ymm10, ymm9, 0x19                   # Shift left A'[13] by 25 bits
    vpsrlq     ymm1, ymm9, 0x27                    # Shift right A'[13] by 39 bits
    vpor       ymm10, ymm10, ymm1                  # Combine to perform ROL 25 on A'[13] (will be used as B[8] in chi step)

    vpsrlq     ymm1, ymm0, 0x3                     # Shift right A'[22] by 3 bits into ymm1
    vpsllq     ymm0, ymm0, 0x3d                    # Shift left A'[22] by 61 bits
    vpor       ymm0, ymm0, ymm1                    # Combine to perform ROL 61 on A'[22] (will be used as B[20] in chi step)

    vmovdqa    ymm13, YMMWORD PTR [rsp+0x160]      # Load A'[14] from stack
    vpsllq     ymm14, ymm13, 0x27                  # Shift left A'[14] by 39 bits
    vpsrlq     ymm12, ymm13, 0x19                  # Shift right A'[14] by 25 bits
    vpor       ymm14, ymm14, ymm12                 # Combine to perform ROL 39 on A'[14] (will be used as B[2] in chi step)

    vmovdqa    ymm4, YMMWORD PTR [rsp+0xa0]        # Load A'[8] from stack
    vpsrlq     ymm1, ymm4, 0x9                     # Shift right A'[8] by 9 bits
    vpsllq     ymm4, ymm4, 0x37                    # Shift left A'[8] by 55 bits
    vpor       ymm4, ymm4, ymm1                    # Combine to perform ROL 55 on A'[8] (will be used as B[1] in chi step)

    vmovdqa    ymm12, YMMWORD PTR [rsp+0x1e0]      # Load A'[18] from stack
    vpsllq     ymm11, ymm12, 0x15                  # Shift left A'[18] by 21 bits
    vpsrlq     ymm1, ymm12, 0x2b                   # Shift right A'[18] by 43 bits
    vpor       ymm11, ymm11, ymm1                  # Combine to perform ROL 21 on A'[18] (will be used as B[15] in chi step)

    vpsrlq     ymm1, ymm2, 0x8                     # Shift right A'[23] by 8 bits into ymm1
    vpsllq     ymm2, ymm2, 0x38                    # Shift left A'[23] by 56 bits
    vpor       ymm2, ymm2, ymm1                    # Combine to perform ROL 56 on A'[23] (will be used as B[10] in chi step)

    vmovdqa    ymm1, YMMWORD PTR [rsp+0x280]       # Load A'[4] from stack
    vpsrlq     ymm9, ymm1, 0x25                    # Shift right A'[4] by 37 bits
    vpsllq     ymm1, ymm1, 0x1b                    # Shift left A'[4] by 27 bits
    vpor       ymm1, ymm1, ymm9                    # Combine to perform ROL 27 on A'[4] (will be used as B[6] in chi step)

    vmovdqa    ymm9, YMMWORD PTR [rsp+0x20]        # Load A'[9] from stack
    vpsrlq     ymm12, ymm9, 0x2c                   # Shift right A'[9] by 44 bits
    vpsllq     ymm9, ymm9, 0x14                    # Shift left A'[9] by 20 bits
    vpor       ymm9, ymm9, ymm12                   # Combine to perform ROL 20 on A'[9] (will be used as B[12] in chi step)

    vmovdqa    ymm13, YMMWORD PTR [rsp+0x200]      # Load A'[19] from stack
    vpsrlq     ymm12, ymm13, 0x38                  # Shift right A'[19] by 56 bits
    vpsllq     ymm13, ymm13, 0x8                   # Shift left A'[19] by 8 bits
    vpor       ymm13, ymm13, ymm12                 # Combine to perform ROL 8 on A'[19] (will be used as B[13] in chi step)

    vmovdqa    ymm12, YMMWORD PTR [rsp+0x40]       # Load A'[24] from stack
    vpsrlq     ymm15, ymm12, 0x32                  # Shift right A'[24] by 50 bits
    vpsllq     ymm12, ymm12, 0xe                   # Shift left A'[24] by 14 bits
    vpor       ymm12, ymm12, ymm15                 # Combine to perform ROL 14 on A'[24] (will be used as B[21] in chi step)

    // B[0]	    A'[0]	None	In ymm5 initially, stored to 0x340(rsp)	B[0,0] = A'[0,0]
    // B[1]	    A'[8]	55	    In ymm4	B[1,0] = A'[1,1]
    // B[2]	    A'[14]	39	    In ymm14	B[2,0] = A'[2,2]
    // B[3]	    A'[7]	6	    In ymm5	B[3,0] = A'[3,3]
    // B[4]	    A'[2]	62	    0x60(rsp)	B[4,0] = A'[4,4]
    // B[5]	    A'[16]	45	    In ymm7	B[0,1] = A'[3,0]
    // B[6]	    A'[4]	27	    In ymm1	B[1,1] = A'[4,1]
    // B[7]	    A'[11]	10	    In ymm8	B[2,1] = A'[0,2]
    // B[8]	    A'[13]	25	    In ymm10	B[3,1] = A'[1,3]
    // B[9]	    A'[6]	44	    0x100(rsp)	B[4,1] = A'[2,4]
    // B[10]	A'[23]	56	    In ymm2	B[0,2] = A'[1,0]
    // B[11]	A'[17]	15	    In ymm6	B[1,2] = A'[2,1]
    // B[12]	A'[9]	20	    In ymm9	B[2,2] = A'[3,2]
    // B[13]	A'[19]	8	    In ymm13	B[3,2] = A'[4,3]
    // B[14]	A'[1]	1	    0x1a0(rsp)	B[4,2] = A'[0,4]
    // B[15]	A'[18]	21	    In ymm11	B[0,3] = A'[4,0]
    // B[16]	A'[20]	18	    0x180(rsp)	B[1,3] = A'[0,1]
    // B[17]	A'[12]	43	    0x320(rsp)	B[2,3] = A'[1,2]
    // B[18]	A'[3]	28	    In ymm3	B[3,3] = A'[2,3]
    // B[19]	A'[5]	36	    0x240(rsp)	B[4,3] = A'[3,4]
    // B[20]	A'[22]	61	    In ymm0	B[0,4] = A'[2,0]
    // B[21]	A'[24]	14	    In ymm12	B[1,4] = A'[3,1]
    // B[22]	A'[15]	41	    0x2a0(rsp)	B[2,4] = A'[4,2]
    // B[23]	A'[10]	3	    0x2c0(rsp)	B[3,4] = A'[0,3]
    // B[24]	A'[21]	2	    0x2e0(rsp)	B[4,4] = A'[1,4]

    vpandn     ymm15, ymm9, YMMWORD PTR [rsp+0x2c0] # ~B[12](A'[9]<<<20) & B[23](A'[10]<<<3) -> ymm15
    vpxor      ymm15, ymm15, ymm3                   # ymm15 ^ B[18](A'[3]<<<28) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0x80], ymm15        # Store A[5] (for next round)

    vpandn     ymm15, ymm5, ymm10                    # ~B[3](A'[7]<<<6) & B[4](A'[2]<<<62) -> ymm15
    vpxor      ymm15, ymm15, YMMWORD PTR [rsp+0x1a0] # ymm15 ^ B[14](A'[1]<<<1) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0x120], ymm15        # Store A[10] (for next round)

    vmovdqa    ymm15, YMMWORD PTR [rsp+0x240]       # Load B[19](A'[5]<<<36) into ymm15
    vpandn     ymm15, ymm15, ymm8                   # ~B[19](A'[5]<<<36) & B[7](A'[11]<<<10) -> ymm15
    vpxor      ymm15, ymm15, ymm1                   # ymm15 ^ B[6](A'[4]<<<27) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0x1c0], ymm15       # Store A[15] (for next round)

    vpandn     ymm15, ymm4, ymm14                   # ~B[1](A'[8]<<<55) & B[2](A'[14]<<<39) -> ymm15
    vpxor      ymm15, ymm15, YMMWORD PTR [rsp+0x60] # ymm15 ^ B[4](A'[2]<<<62) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0x260], ymm15       # Store A[20] (for next round)

    vmovdqa    ymm15, YMMWORD PTR [rsp+0x320]       # Load B[17](A'[12]<<<43) into ymm15
    vpandn     ymm15, ymm15, ymm11                  # ~B[17](A'[12]<<<43) & B[15](A'[18]<<<21) -> ymm15
    vpxor      ymm15, ymm15, YMMWORD PTR [rsp+0x100]# ymm15 ^ B[9](A'[6]<<<44) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0x0], ymm15         # Store A[1] (for next round)

    vmovdqa    ymm15, YMMWORD PTR [rsp+0x2c0]       # Load B[23](A'[10]<<<3) into ymm15
    vpandn     ymm15, ymm15, ymm7                   # ~B[23](A'[10]<<<3) & B[5](A'[16]<<<45) -> ymm15
    vpxor      ymm15, ymm15, ymm9                   # ymm15 ^ B[12](A'[9]<<<20) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0xa0], ymm15        # Store A[6] (for next round)

    vpandn     ymm15, ymm10, ymm13                  # ~B[4](A'[2]<<<62) & B[13](A'[19]<<<8) -> ymm15
    vpxor      ymm15, ymm15, ymm5                   # ymm15 ^ B[3](A'[7]<<<6) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0x140], ymm15       # Store A[11] (for next round)

    vpandn     ymm15, ymm8, ymm6                    # ~B[7](A'[11]<<<10) & B[11](A'[17]<<<15) -> ymm15
    vpxor      ymm15, ymm15, YMMWORD PTR [rsp+0x240]# ymm15 ^ B[19](A'[5]<<<36) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0x1e0], ymm15       # Store A[16] (for next round)

    vpandn     ymm15, ymm14, YMMWORD PTR [rsp+0x2a0]# ~B[2](A'[14]<<<39) & B[22](A'[15]<<<41) -> ymm15
    vpxor      ymm15, ymm15, ymm4                   # ymm15 ^ B[1](A'[8]<<<55) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0x280], ymm15       # Store A[21] (for next round)

    vpandn     ymm15, ymm11, ymm12                   # ~B[15](A'[18]<<<21) & B[21](A'[24]<<<14) -> ymm15
    vpxor      ymm15, ymm15, YMMWORD PTR [rsp+0x320] # ymm15 ^ B[17](A'[12]<<<43) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0x20], ymm15         # Store A[2] (for next round)

    vpandn     ymm15, ymm7, ymm0                     # ~B[5](A'[16]<<<45) & B[20](A'[22]<<<61) -> ymm15
    vpxor      ymm15, ymm15, YMMWORD PTR [rsp+0x2c0] # ymm15 ^ B[23](A'[10]<<<3) -> ymm15
    vmovdqa    YMMWORD PTR [rsp+0xc0], ymm15         # Store A[7] (for next round)

    vpandn     ymm15, ymm13, YMMWORD PTR [rsp+0x180] # ~B[13](A'[19]<<<8) & B[16](A'[20]<<<18) -> ymm15
    vpxor      ymm10, ymm15, ymm10                   # ymm15 ^ B[4](A'[2]<<<62) -> ymm10
    vmovdqa    YMMWORD PTR [rsp+0x160], ymm10        # Store A[12] (for next round)

    vpandn     ymm10, ymm6, ymm2                     # ~B[11](A'[17]<<<15) & B[10](A'[23]<<<56) -> ymm10
    vpxor      ymm8, ymm10, ymm8                     # ymm10 ^ B[7](A'[11]<<<10) -> ymm8
    vmovdqa    YMMWORD PTR [rsp+0x200], ymm8         # Store A[17] (for next round)

    vmovdqa    ymm10, YMMWORD PTR [rsp+0x2a0]       # Load B[22](A'[15]<<<41) into ymm10
    vmovdqa    ymm15, YMMWORD PTR [rsp+0x2e0]       # Load B[24](A'[21]<<<2) into ymm15
    vpandn     ymm8, ymm10, ymm15                   # ~B[22](A'[15]<<<41) & B[24](A'[21]<<<2) -> ymm8
    vpxor      ymm8, ymm8, ymm14                    # ymm8 ^ B[2](A'[14]<<<39) -> ymm8
    vmovdqa    YMMWORD PTR [rsp+0x2a0], ymm8        # Store A[22] (for next round)

    vmovdqa    ymm14, YMMWORD PTR [rsp+0x340]       # Load B[0](A'[0]) into ymm14
    vpandn     ymm8, ymm12, ymm14                   # ~B[21](A'[24]<<<14) & B[0](A'[0]) -> ymm8
    vpxor      ymm8, ymm8, ymm11                    # ymm8 ^ B[15](A'[18]<<<21) -> ymm8
    vmovdqa    YMMWORD PTR [rsp+0x40], ymm8         # Store A[3] (for next round)

    vpandn     ymm8, ymm0, ymm3                     # ~B[20](A'[22]<<<61) & B[18](A'[3]<<<28) -> ymm8
    vpxor      ymm7, ymm8, ymm7                     # ymm8 ^ B[5](A'[16]<<<45) -> ymm7
    vmovdqa    YMMWORD PTR [rsp+0xe0], ymm7         # Store A[8] (for next round)

    vmovdqa    ymm11, YMMWORD PTR [rsp+0x180]       # Load B[16](A'[20]<<<18) into ymm11
    vmovdqa    ymm8, YMMWORD PTR [rsp+0x1a0]        # Load B[14](A'[1]<<<1) into ymm8
    vpandn     ymm7, ymm11, ymm8                    # ~B[16](A'[20]<<<18) & B[14](A'[1]<<<1) -> ymm7
    vpxor      ymm7, ymm7, ymm13                    # ymm7 ^ B[13](A'[19]<<<8) -> ymm7
    vmovdqa    YMMWORD PTR [rsp+0x180], ymm7        # Store A[13] (for next round)
    vmovdqa    ymm13, YMMWORD PTR [rsp+0x100]       # Load B[9](A'[6]<<<44) into ymm13

    vpandn     ymm3, ymm3, ymm9                     # ~B[18](A'[3]<<<28) & B[12](A'[9]<<<20) -> ymm3
    vpxor      ymm3, ymm3, ymm0                     # ymm3 ^ B[20](A'[22]<<<61) -> ymm3
    vmovdqa    YMMWORD PTR [rsp+0x100], ymm3        # Store A[9] (for next round)

    vpandn     ymm0, ymm8, ymm5                     # ~B[14](A'[1]<<<1) & B[3](A'[7]<<<6) -> ymm0
    vpxor      ymm3, ymm0, ymm11                    # ymm0 ^ B[16](A'[20]<<<18) -> ymm3
    vmovdqa    YMMWORD PTR [rsp+0x1a0], ymm3        # Store A[14] (for next round)

    vpandn     ymm7, ymm2, ymm1                     # ~B[6](A'[4]<<<27) & B[10](A'[23]<<<56) -> ymm7
    vpxor      ymm6, ymm7, ymm6                     # ymm7 ^ B[11](A'[17]<<<15) -> ymm6
    vmovdqa    YMMWORD PTR [rsp+0x220], ymm6        # Store A[18] (for next round)

    vmovdqa    ymm6, ymm15                          # Copy B[24](A'[21]<<<2) to ymm6
    vmovdqa    ymm15, YMMWORD PTR [rsp+0x60]        # Load B[4](A'[2]<<<62) into ymm15
    vpandn     ymm6, ymm6, ymm15                    # ~B[24](A'[21]<<<2) & B[4](A'[2]<<<62) -> ymm6
    vpxor      ymm7, ymm6, ymm10                    # ymm6 ^ B[22](A'[15]<<<41) -> ymm7
    vmovdqa    YMMWORD PTR [rsp+0x2c0], ymm7        # Store A[23] (for next round)

    vpandn     ymm1, ymm1, YMMWORD PTR [rsp+0x240]  # ~B[6](A'[4]<<<27) & B[19](A'[5]<<<36) -> ymm1
    vpxor      ymm2, ymm1, ymm2                     # ymm1 ^ B[10](A'[23]<<<56) -> ymm2
    vmovdqa    YMMWORD PTR [rsp+0x240], ymm2        # Store A[19] (for next round)

    vpandn     ymm5, ymm13, YMMWORD PTR [rsp+0x320] # ~B[9](A'[6]<<<44) & B[17](A'[12]<<<43) -> ymm5
    vpxor      ymm5, ymm5, ymm14                    # ymm5 ^ B[0](A'[0]) -> ymm5
    vpbroadcastq ymm0, QWORD PTR [rsi]              # Load round constant into ymm0

    vpxor      ymm5, ymm5, ymm0                     # XOR with round constant (iota step) - A[0] for next round

    vpandn     ymm6, ymm14, ymm13                   # ~B[0](A'[0]) & B[9](A'[6]<<<44) -> ymm6
    vpxor      ymm14, ymm6, ymm12                   # ymm6 ^ B[21](A'[24]<<<14) -> ymm14
    vmovdqa    YMMWORD PTR [rsp+0x60], ymm14        # Store A[4] (for next round)

    vpandn     ymm0, ymm15, ymm4                    # ~B[4](A'[2]<<<62) & B[1](A'[8]<<<55) -> ymm0
    vpxor      ymm6, ymm0, YMMWORD PTR [rsp+0x2e0]  # ymm0 ^ B[24](A'[21]<<<2) -> ymm6
    vmovdqa    YMMWORD PTR [rsp+0x2e0], ymm6        # Store A[24] (for next round)

    add    rsi,0x8
    add    rax,0x1
    cmp    rax,0x18
    jne    .keccak_loop

    # First group (states 0-3)
    // vmovdqa ymm0, ymm5                          # Load A[0] from register [state0[0] | state1[0] | state2[0] | state3[0]]
    vmovdqa    ymm1, YMMWORD PTR [rsp+0x0]         # Load A[1] [state0[1] | state1[1] | state2[1] | state3[1]]
    vmovdqa    ymm2, YMMWORD PTR [rsp+0x20]        # Load A[2] [state0[2] | state1[2] | state2[2] | state3[2]]
    vmovdqa    ymm3, YMMWORD PTR [rsp+0x40]        # Load A[3] [state0[3] | state1[3] | state2[3] | state3[3]]

    # Unpack to group by state
    vpunpcklqdq ymm4, ymm5, ymm1                   # [state0[0] | state0[1] | state2[0] | state2[1]]
    vpunpckhqdq ymm6, ymm5, ymm1                   # [state1[0] | state1[1] | state3[0] | state3[1]]
    vpunpcklqdq ymm7, ymm2, ymm3                   # [state0[2] | state0[3] | state2[2] | state2[3]]
    vpunpckhqdq ymm8, ymm2, ymm3                   # [state1[2] | state1[3] | state3[2] | state3[3]]

    # Permute 128-bit lanes to complete un-interleave
    vperm2i128  ymm5, ymm4, ymm7, 0x20             # [state0[0] | state0[1] | state0[2] | state0[3]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20             # [state1[0] | state1[1] | state1[2] | state1[3]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31             # [state2[0] | state2[1] | state2[2] | state2[3]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31             # [state3[0] | state3[1] | state3[2] | state3[3]]

    # Store back to memory in consecutive format
    vmovdqu    YMMWORD PTR [rdi], ymm5             # Store state0[0..3]
    vmovdqu    YMMWORD PTR [rdi+0xc8], ymm1        # Store state1[0..3]
    vmovdqu    YMMWORD PTR [rdi+0x190], ymm2       # Store state2[0..3]
    vmovdqu    YMMWORD PTR [rdi+0x258], ymm3       # Store state3[0..3]

    # Second group (states 4-7)
    vmovdqa    ymm0, YMMWORD PTR [rsp+0x60]        # Load A[4] [state0[4] | state1[4] | state2[4] | state3[4]]
    vmovdqa    ymm1, YMMWORD PTR [rsp+0x80]        # Load A[5] [state0[5] | state1[5] | state2[5] | state3[5]]
    vmovdqa    ymm2, YMMWORD PTR [rsp+0xa0]        # Load A[6] [state0[6] | state1[6] | state2[6] | state3[6]]
    vmovdqa    ymm3, YMMWORD PTR [rsp+0xc0]        # Load A[7] [state0[7] | state1[7] | state2[7] | state3[7]]

    # Unpack to group by state
    vpunpcklqdq ymm4, ymm0, ymm1                   # [state0[4] | state0[5] | state2[4] | state2[5]]
    vpunpckhqdq ymm6, ymm0, ymm1                   # [state1[4] | state1[5] | state3[4] | state3[5]]
    vpunpcklqdq ymm7, ymm2, ymm3                   # [state0[6] | state0[7] | state2[6] | state2[7]]
    vpunpckhqdq ymm8, ymm2, ymm3                   # [state1[6] | state1[7] | state3[6] | state3[7]]

    # Permute 128-bit lanes to complete un-interleave
    vperm2i128  ymm0, ymm4, ymm7, 0x20            # [state0[4] | state0[5] | state0[6] | state0[7]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20            # [state1[4] | state1[5] | state1[6] | state1[7]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31            # [state2[4] | state2[5] | state2[6] | state2[7]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31            # [state3[4] | state3[5] | state3[6] | state3[7]]

    # Store back to memory
    vmovdqu    YMMWORD PTR [rdi+0x20], ymm0       # Store state0[4..7]
    vmovdqu    YMMWORD PTR [rdi+0xe8], ymm1       # Store state1[4..7]
    vmovdqu    YMMWORD PTR [rdi+0x1b0], ymm2      # Store state2[4..7]
    vmovdqu    YMMWORD PTR [rdi+0x278], ymm3      # Store state3[4..7]

    # Third group (states 8-11)
    vmovdqa    ymm0, YMMWORD PTR [rsp+0xe0]       # Load A[8] [state0[8] | state1[8] | state2[8] | state3[8]]
    vmovdqa    ymm1, YMMWORD PTR [rsp+0x100]      # Load A[9] [state0[9] | state1[9] | state2[9] | state3[9]]
    vmovdqa    ymm2, YMMWORD PTR [rsp+0x120]      # Load A[10] [state0[10] | state1[10] | state2[10] | state3[10]]
    vmovdqa    ymm3, YMMWORD PTR [rsp+0x140]      # Load A[11] [state0[11] | state1[11] | state2[11] | state3[11]]

    # Unpack to group by state
    vpunpcklqdq ymm4, ymm0, ymm1                  # [state0[8] | state0[9] | state2[8] | state2[9]]
    vpunpckhqdq ymm6, ymm0, ymm1                  # [state1[8] | state1[9] | state3[8] | state3[9]]
    vpunpcklqdq ymm7, ymm2, ymm3                  # [state0[10] | state0[11] | state2[10] | state2[11]]
    vpunpckhqdq ymm8, ymm2, ymm3                  # [state1[10] | state1[11] | state3[10] | state3[11]]

    # Permute 128-bit lanes to complete un-interleave
    vperm2i128  ymm0, ymm4, ymm7, 0x20            # [state0[8] | state0[9] | state0[10] | state0[11]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20            # [state1[8] | state1[9] | state1[10] | state1[11]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31            # [state2[8] | state2[9] | state2[10] | state2[11]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31            # [state3[8] | state3[9] | state3[10] | state3[11]]

    # Store back to memory
    vmovdqu    YMMWORD PTR [rdi+0x40], ymm0       # Store state0[8..11]
    vmovdqu    YMMWORD PTR [rdi+0x108], ymm1      # Store state1[8..11]
    vmovdqu    YMMWORD PTR [rdi+0x1d0], ymm2      # Store state2[8..11]
    vmovdqu    YMMWORD PTR [rdi+0x298], ymm3      # Store state3[8..11]

    # Fourth group (states 12-15)
    vmovdqa    ymm0, YMMWORD PTR [rsp+0x160]      # Load A[12] [state0[12] | state1[12] | state2[12] | state3[12]]
    vmovdqa    ymm1, YMMWORD PTR [rsp+0x180]      # Load A[13] [state0[13] | state1[13] | state2[13] | state3[13]]
    vmovdqa    ymm2, YMMWORD PTR [rsp+0x1a0]      # Load A[14] [state0[14] | state1[14] | state2[14] | state3[14]]
    vmovdqa    ymm3, YMMWORD PTR [rsp+0x1c0]      # Load A[15] [state0[15] | state1[15] | state2[15] | state3[15]]

    # Unpack to group by state
    vpunpcklqdq ymm4, ymm0, ymm1                  # [state0[12] | state0[13] | state2[12] | state2[13]]
    vpunpckhqdq ymm6, ymm0, ymm1                  # [state1[12] | state1[13] | state3[12] | state3[13]]
    vpunpcklqdq ymm7, ymm2, ymm3                  # [state0[14] | state0[15] | state2[14] | state2[15]]
    vpunpckhqdq ymm8, ymm2, ymm3                  # [state1[14] | state1[15] | state3[14] | state3[15]]

    # Permute 128-bit lanes to complete un-interleave
    vperm2i128  ymm0, ymm4, ymm7, 0x20            # [state0[12] | state0[13] | state0[14] | state0[15]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20            # [state1[12] | state1[13] | state1[14] | state1[15]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31            # [state2[12] | state2[13] | state2[14] | state2[15]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31            # [state3[12] | state3[13] | state3[14] | state3[15]]

    # Store back to memory
    vmovdqu    YMMWORD PTR [rdi+0x60], ymm0       # Store state0[12..15]
    vmovdqu    YMMWORD PTR [rdi+0x128], ymm1      # Store state1[12..15]
    vmovdqu    YMMWORD PTR [rdi+0x1f0], ymm2      # Store state2[12..15]
    vmovdqu    YMMWORD PTR [rdi+0x2b8], ymm3      # Store state3[12..15]

    # Fifth group (states 16-19)
    vmovdqa    ymm0, YMMWORD PTR [rsp+0x1e0]      # Load A[16] [state0[16] | state1[16] | state2[16] | state3[16]]
    vmovdqa    ymm1, YMMWORD PTR [rsp+0x200]      # Load A[17] [state0[17] | state1[17] | state2[17] | state3[17]]
    vmovdqa    ymm2, YMMWORD PTR [rsp+0x220]      # Load A[18] [state0[18] | state1[18] | state2[18] | state3[18]]
    vmovdqa    ymm3, YMMWORD PTR [rsp+0x240]      # Load A[19] [state0[19] | state1[19] | state2[19] | state3[19]]

    # Unpack to group by state
    vpunpcklqdq ymm4, ymm0, ymm1                  # [state0[16] | state0[17] | state2[16] | state2[17]]
    vpunpckhqdq ymm6, ymm0, ymm1                  # [state1[16] | state1[17] | state3[16] | state3[17]]
    vpunpcklqdq ymm7, ymm2, ymm3                  # [state0[18] | state0[19] | state2[18] | state2[19]]
    vpunpckhqdq ymm8, ymm2, ymm3                  # [state1[18] | state1[19] | state3[18] | state3[19]]

    # Permute 128-bit lanes to complete un-interleave
    vperm2i128  ymm0, ymm4, ymm7, 0x20            # [state0[16] | state0[17] | state0[18] | state0[19]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20            # [state1[16] | state1[17] | state1[18] | state1[19]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31            # [state2[16] | state2[17] | state2[18] | state2[19]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31            # [state3[16] | state3[17] | state3[18] | state3[19]]

    # Store back to memory
    vmovdqu    YMMWORD PTR [rdi+0x80], ymm0       # Store state0[16..19]
    vmovdqu    YMMWORD PTR [rdi+0x148], ymm1      # Store state1[16..19]
    vmovdqu    YMMWORD PTR [rdi+0x210], ymm2      # Store state2[16..19]
    vmovdqu    YMMWORD PTR [rdi+0x2d8], ymm3      # Store state3[16..19]

    # Sixth group (states 20-23)
    vmovdqa    ymm0, YMMWORD PTR [rsp+0x260]      # Load A[20] [state0[20] | state1[20] | state2[20] | state3[20]]
    vmovdqa    ymm1, YMMWORD PTR [rsp+0x280]      # Load A[21] [state0[21] | state1[21] | state2[21] | state3[21]]
    vmovdqa    ymm2, YMMWORD PTR [rsp+0x2a0]      # Load A[22] [state0[22] | state1[22] | state2[22] | state3[22]]
    vmovdqa    ymm3, YMMWORD PTR [rsp+0x2c0]      # Load A[23] [state0[23] | state1[23] | state2[23] | state3[23]]

    # Unpack to group by state
    vpunpcklqdq ymm4, ymm0, ymm1                  # [state0[20] | state0[21] | state2[20] | state2[21]]
    vpunpckhqdq ymm6, ymm0, ymm1                  # [state1[20] | state1[21] | state3[20] | state3[21]]
    vpunpcklqdq ymm7, ymm2, ymm3                  # [state0[22] | state0[23] | state2[22] | state2[23]]
    vpunpckhqdq ymm8, ymm2, ymm3                  # [state1[22] | state1[23] | state3[22] | state3[23]]

    # Permute 128-bit lanes to complete un-interleave
    vperm2i128  ymm0, ymm4, ymm7, 0x20            # [state0[20] | state0[21] | state0[22] | state0[23]]
    vperm2i128  ymm1, ymm6, ymm8, 0x20            # [state1[20] | state1[21] | state1[22] | state1[23]]
    vperm2i128  ymm2, ymm4, ymm7, 0x31            # [state2[20] | state2[21] | state2[22] | state2[23]]
    vperm2i128  ymm3, ymm6, ymm8, 0x31            # [state3[20] | state3[21] | state3[22] | state3[23]]

    # Store back to memory
    vmovdqu    YMMWORD PTR [rdi+0xa0], ymm0       # Store state0[20..23]
    vmovdqu    YMMWORD PTR [rdi+0x168], ymm1      # Store state1[20..23]
    vmovdqu    YMMWORD PTR [rdi+0x230], ymm2      # Store state2[20..23]
    vmovdqu    YMMWORD PTR [rdi+0x2f8], ymm3      # Store state3[20..23]

    # Handle the last elements (states 24)
    vmovdqa    ymm3, YMMWORD PTR [rsp+0x2e0]      # Load A[24] [state0[24] | state1[24] | state2[24] | state3[24]]

    # Extract and store each state's element 24
    vextracti128 xmm0, ymm3, 0x0                  # Extract [state0[24] | state1[24]]
    vextracti128 xmm1, ymm3, 0x1                  # Extract [state2[24] | state3[24]]
    vmovq      QWORD PTR [rdi+0xc0], xmm0         # Store state0[24]
    vpextrq    QWORD PTR [rdi+0x188], xmm0, 0x1   # Store state1[24]
    vmovq      QWORD PTR [rdi+0x250], xmm1        # Store state2[24]
    vpextrq    QWORD PTR [rdi+0x318], xmm1, 0x1   # Store state3[24]

    mov    rsp,rbp
    pop    rbp

#if WINDOWS_ABI
    pop    rsi
    pop    rdi
#endif

    ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif
