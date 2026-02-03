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
//    extern void sha3_keccak4_f1600_alt(uint64_t a[100], const uint64_t rc[24], const void* rho8, const void* rho56);
//
// Standard x86-64 ABI: RDI = a, RSI = rc, RDX = rho8, RCX = rho56
// Microsoft x64 ABI:   RCX = a, RDX = rc, R8 = rho8, R9 = rho56
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak4_f1600_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha3_keccak4_f1600_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak4_f1600_alt)
        .text
        .balign 32

S2N_BN_SYMBOL(sha3_keccak4_f1600_alt):
        CFI_START
      _CET_ENDBR
		mov	r11, rsp
        and    rsp,0xffffffffffffffe0
        sub    rsp,0x340

// **** Bitstates Allocation Map on Stack (CORRECTED) **** //
// 0x0(%rsp)      A[0]  (A[0][0])	[state0[0], state1[0], state2[0], state3[0]]
// 0x20(%rsp)	    A[1]  (A[1][0])	[state0[1], state1[1], state2[1], state3[1]]
// 0x40(%rsp)	    A[2]  (A[2][0])	[state0[2], state1[2], state2[2], state3[2]]
// 0x60(%rsp)	    A[3]  (A[3][0])	[state0[3], state1[3], state2[3], state3[3]]
// 0x80(%rsp)	    A[4]  (A[4][0])	[state0[4], state1[4], state2[4], state3[4]]
// 0xa0(%rsp)	    A[5]  (A[0][1])	[state0[5], state1[5], state2[5], state3[5]]
// ymm12     	    A[6]  (A[1][1])	[state0[6], state1[6], state2[6], state3[6]]
// 0xc0(%rsp)	    A[7]  (A[2][1])	[state0[7], state1[7], state2[7], state3[7]]
// 0xe0(%rsp)	    A[8]  (A[3][1])	[state0[8], state1[8], state2[8], state3[8]]
// 0x100(%rsp)	    A[9]  (A[4][1])	[state0[9], state1[9], state2[9], state3[9]]
// 0x120(%rsp)	    A[10] (A[0][2])	[state0[10], state1[10], state2[10], state3[10]]
// 0x140(%rsp)	    A[11] (A[1][2])	[state0[11], state1[11], state2[11], state3[11]]
// ymm10     	    A[12] (A[2][2])	[state0[12], state1[12], state2[12], state3[12]]
// 0x160(%rsp)	    A[13] (A[3][2])	[state0[13], state1[13], state2[13], state3[13]]
// 0x180(%rsp)	    A[14] (A[4][2])	[state0[14], state1[14], state2[14], state3[14]]
// 0x1a0(%rsp)	    A[15] (A[0][3])	[state0[15], state1[15], state2[15], state3[15]]
// ymm13     	    A[16] (A[1][3])	[state0[16], state1[16], state2[16], state3[16]]
// 0x1c0(%rsp)	    A[17] (A[2][3])	[state0[17], state1[17], state2[17], state3[17]]
// ymm3             A[18] (A[3][3])	[state0[18], state1[18], state2[18], state3[18]]
// 0x1e0(%rsp)      A[19] (A[4][3])	[state0[19], state1[19], state2[19], state3[19]]
// ymm15     	    A[20] (A[0][4])	[state0[20], state1[20], state2[20], state3[20]]
// ymm14     	    A[21] (A[1][4])	[state0[21], state1[21], state2[21], state3[21]]
// ymm8     	    A[22] (A[2][4])	[state0[22], state1[22], state2[22], state3[22]]
// 0x200(%rsp)	    A[23] (A[3][4])	[state0[23], state1[23], state2[23], state3[23]]
// ymm6     	    A[24] (A[4][4])	[state0[24], state1[24], state2[24], state3[24]]

// Load 32 bytes from each of the 4 states (A[0-3])
vmovdqu ymm4,[rdi]                            // Load state0[0, 1, 2, 3] (32 bytes from Input (%rdi) offsets: 0x00)
vpunpcklqdq ymm2,ymm4,[rdi+0xc8]              // ymm2 = [state0[0] | state1[0] | state0[2] | state1[2]]
vpunpckhqdq ymm0,ymm4,[rdi+0xc8]              // ymm0 = [state0[1] | state1[1] | state0[3] | state1[3]]
vmovdqu ymm4,[rdi+0x190]                      // Load state2[0, 1, 2, 3] (32 bytes from Input (%rdi) offsets: 0x190)
vpunpckhqdq ymm1,ymm4,[rdi+0x258]             // ymm1 = [state2[1] | state3[1] | state2[3] | state3[3]]
vpunpcklqdq ymm3,ymm4,[rdi+0x258]             // ymm3 = [state2[0] | state3[0] | state2[2] | state3[2]]
vperm2i128 ymm4,ymm0,ymm1,0x20                // A1 = ymm4 = [state0[1] | state1[1] | state2[1] | state3[1]]
vperm2i128 ymm14,ymm2,ymm3,0x20               // A0 = ymm14 = [state0[0] | state1[0] | state2[0] | state3[0]]
vmovdqu [rsp+0x20],ymm4                      // store A[1] -> on stack
vperm2i128 ymm4,ymm2,ymm3,0x31                // A2 = ymm4 = [state0[2] | state1[2] | state2[2] | state3[2]]
vmovdqu [rsp+0x40],ymm4                      // store A[2] -> on stack
vperm2i128 ymm4,ymm0,ymm1,0x31                // A3 = ymm4 = [state0[3] | state1[3] | state2[3] | state3[3]]
vmovdqu [rsp+0x60],ymm4                      // store A[3] -> on stack

// Load, Interleave, and Store 32 bytes from each of the 4 states (A[4-7])
vmovdqu ymm4,[rdi+0x20]
vpunpcklqdq ymm2,ymm4,[rdi+0xe8]
vpunpckhqdq ymm0,ymm4,[rdi+0xe8]
vmovdqu ymm4,[rdi+0x1b0]
vpunpcklqdq ymm3,ymm4,[rdi+0x278]
vpunpckhqdq ymm1,ymm4,[rdi+0x278]
vperm2i128 ymm4,ymm2,ymm3,0x20
vperm2i128 ymm12,ymm2,ymm3,0x31
vmovdqu [rsp+0x80],ymm4                      // store A[4] -> on stack
vperm2i128 ymm4,ymm0,ymm1,0x20
vmovdqu [rsp+0xa0],ymm4                      // store A[5] -> on stack
vperm2i128 ymm4,ymm0,ymm1,0x31
vmovdqu [rsp+0xc0],ymm4                      // store A[7] -> on stack

// Load, Interleave, and Store 32 bytes from each of the 4 states (A[8-11])
vmovdqu ymm4,[rdi+0x40]
vpunpcklqdq ymm2,ymm4,[rdi+0x108]
vpunpckhqdq ymm0,ymm4,[rdi+0x108]
vmovdqu ymm4,[rdi+0x1d0]
vpunpcklqdq ymm3,ymm4,[rdi+0x298]
vpunpckhqdq ymm1,ymm4,[rdi+0x298]
vperm2i128 ymm4,ymm2,ymm3,0x20
vmovdqu [rsp+0xe0],ymm4                      // store A[8] -> on stack
vperm2i128 ymm4,ymm0,ymm1,0x20
vmovdqu [rsp+0x100],ymm4                      // store A[9] -> on stack
vperm2i128 ymm4,ymm2,ymm3,0x31
mov    rax,QWORD PTR [rdi+0xc0]               // Load state0[24] into rax
vmovdqu [rsp+0x120],ymm4                      // store A[10] -> on stack
vperm2i128 ymm4,ymm0,ymm1,0x31
vmovdqu [rsp+0x140],ymm4                      // store A[11] -> on stack

// Load, Interleave, and Store 32 bytes from each of the 4 states (A[12-15])
vmovdqu ymm4,[rdi+0x60]
vpunpckhqdq ymm0,ymm4,[rdi+0x128]
vpunpcklqdq ymm2,ymm4,[rdi+0x128]
vmovdqu ymm4,[rdi+0x1f0]
mov    QWORD PTR [rsp+0x0],rax              // store state0[24] -> on stack (part of A[24])
vpunpcklqdq ymm3,ymm4,[rdi+0x2b8]
vpunpckhqdq ymm1,ymm4,[rdi+0x2b8]
mov    rax,QWORD PTR [rdi+0x188]              // Load state1[24] into rax
vperm2i128 ymm10,ymm2,ymm3,0x20
vperm2i128 ymm2,ymm2,ymm3,0x31
vperm2i128 ymm4,ymm0,ymm1,0x20
vmovdqu [rsp+0x180],ymm2                      // store A[14] -> on stack
vperm2i128 ymm2,ymm0,ymm1,0x31
vmovdqu [rsp+0x160],ymm4                      // store A[13] -> on stack

// Load, Interleave, and Store 32 bytes from each of the 4 states (A[16-19])
vmovdqu ymm4,[rdi+0x80]
vpunpckhqdq ymm0,ymm4,[rdi+0x148]
vmovdqu [rsp+0x1a0],ymm2                      // store A[15] -> on stack
vmovdqu ymm4,[rdi+0x210]
vmovdqu ymm2,[rdi+0x80]
vpunpcklqdq ymm3,ymm4,[rdi+0x2d8]
vpunpcklqdq ymm2,ymm2,[rdi+0x148]
vpunpckhqdq ymm1,ymm4,[rdi+0x2d8]
vperm2i128 ymm13,ymm2,ymm3,0x20
vperm2i128 ymm3,ymm2,ymm3,0x31
vperm2i128 ymm4,ymm0,ymm1,0x20
vperm2i128 ymm2,ymm0,ymm1,0x31

// Load, Interleave, and Store 32 bytes from each of the 4 states (A[20-23])
vmovdqu ymm1,[rdi+0x230]
vpunpckhqdq ymm1,ymm1,[rdi+0x2f8]
vmovdqu [rsp+0x1c0],ymm4                      // store A[17] -> on stack
vmovdqu ymm4,[rdi+0xa0]
vpunpckhqdq ymm0,ymm4,[rdi+0x168]
vmovdqu [rsp+0x1e0],ymm2                      // store A[18] -> on stack
vmovdqu ymm4,[rdi+0x230]
vmovdqu ymm2,[rdi+0xa0]
vpunpcklqdq ymm4,ymm4,[rdi+0x2f8]
vpunpcklqdq ymm2,ymm2,[rdi+0x168]
vperm2i128 ymm5,ymm0,ymm1,0x20
vperm2i128 ymm15,ymm2,ymm4,0x20
vperm2i128 ymm8,ymm2,ymm4,0x31
vperm2i128 ymm2,ymm0,ymm1,0x31
vmovdqu [rsp+0x200],ymm2                      // store A[23] -> on stack

// Load A[24] from each of the 4 states
// A[24] is the last element (only 8 bytes per state)
// mov    rax,QWORD PTR [rdi+0xc0]               // Load state0[24] into rax
// mov    QWORD PTR [rsp+0x0],rax              // store state0[24] -> on stack (part of A[24])
// mov    rax,QWORD PTR [rdi+0x188]              // Load state1[24] into rax
// mov    QWORD PTR [rsp+0x8],rax              // store state1[24] -> on stack (part of A[24])
// mov    rax,QWORD PTR [rdi+0x250]              // Load state2[24] into rax
// mov    QWORD PTR [rsp+0x10],rax              // store state2[24] -> on stack (part of A[24])
// mov    rax,QWORD PTR [rdi+0x318]              // Load state3[24] into rax
// mov    QWORD PTR [rsp+0x18],rax              // store state3[24] -> on stack (part of A[24])

vmovq  xmm1,[rdi+0xc0]                        // Load state0[24] into lower 64 bits of xmm1
vpinsrq xmm1,xmm1,[rdi+0x188],0x1             // Insert state1[24] into upper 64 bits of xmm1 = [state0[24] | state1[24]]
vmovq  xmm2,[rdi+0x250]                       // Load state2[24] into lower 64 bits of xmm2
vpinsrq xmm2,xmm2,[rdi+0x318],0x1             // Insert state3[24] into upper 64 bits of xmm2 = [state2[24] | state3[24]]
vinserti128 ymm6,ymm1,xmm2,0x1                // Interleave into ymm3 = A[24] = [state0[24] | state1[24] | state2[24] | state3[24]]
vmovdqu [rsp+0x0],ymm6                      // store A[24] -> on stack

vmovdqu	ymm6, [rsp+0x0]
vmovdqu	[rsp+0x0], ymm14
vmovdqu	ymm14, ymm5
	mov r10, 0

   Lsha3_keccak4_f1600_alt:
	# ===== ROUND i: THETA STEP - Computing C[x] = A[x][0] ^ A[x][1] ^ A[x][2] ^ A[x][3] ^ A[x][4] =====
	
	vpxor	ymm0, ymm15, [rsp+0x1a0]              # A[20] xor A[15] (A[0][4] xor A[0][3])
	vpxor	ymm9, ymm13, ymm14                     # A[16] xor A[21] (A[1][3] xor A[1][4])
	vmovdqu	ymm4, [rsp+0xa0]                      # load A[5] (A[0][1])
	vpxor	ymm2, ymm4, [rsp+0x120]                # A[5] xor A[10] (A[0][1] xor A[0][2])
	vpxor	ymm7, ymm8, [rsp+0x1c0]                # A[22] xor A[17] (A[2][4] xor A[2][3])
	vpxor	ymm5, ymm3, [rsp+0x200]                # A[18] xor A[23] (A[3][3] xor A[3][4])
	vmovdqu	ymm4, [rsp+0xe0]                      # load A[8] (A[3][1])
	vpxor	ymm1, ymm6, [rsp+0x1e0]                # A[24] xor A[19] (A[4][4] xor A[4][3])
	vpxor	ymm2, ymm2, ymm0                       # (A[5] xor A[10]) xor (A[20] xor A[15])
	vpxor	ymm0, ymm12, [rsp+0x140]               # A[6] xor A[11] (A[1][1] xor A[1][2])
	vpxor	ymm2, ymm2, [rsp+0x0]                # C[0] = A[0] xor A[5] xor A[10] xor A[15] xor A[20]
	vpxor	ymm9, ymm9, ymm0                       # (A[16] xor A[21]) xor (A[6] xor A[11])
	vpxor	ymm0, ymm10, [rsp+0xc0]               # A[12] xor A[7] (A[2][2] xor A[2][1])
	vpxor	ymm9, ymm9, [rsp+0x20]                # C[1] = A[1] xor A[6] xor A[11] xor A[16] xor A[21]
	vpxor	ymm7, ymm7, ymm0                       # (A[22] xor A[17]) xor (A[12] xor A[7])
	vpsllq	ymm11, ymm9, 1                         # C[1] << 1 (for ROL(C[1], 1))
	vpxor	ymm0, ymm4, [rsp+0x160]                # A[8] xor A[13] (A[3][1] xor A[3][2])
	vmovdqu	ymm4, [rsp+0x100]                      # load A[9] (A[4][1])
	vpxor	ymm7, ymm7, [rsp+0x40]                # C[2] = A[2] xor A[7] xor A[12] xor A[17] xor A[22]
	vpxor	ymm5, ymm5, ymm0                       # (A[18] xor A[23]) xor (A[8] xor A[13])
	vpxor	ymm0, ymm4, [rsp+0x180]                # A[9] xor A[14] (A[4][1] xor A[4][2])
	vpxor	ymm5, ymm5, [rsp+0x60]                # C[3] = A[3] xor A[8] xor A[13] xor A[18] xor A[23]
	vpsllq	ymm4, ymm7, 1                          # C[2] << 1 (for ROL(C[2], 1))
	vpxor	ymm1, ymm1, ymm0                       # (A[24] xor A[19]) xor (A[9] xor A[14])
	vpsrlq	ymm0, ymm9, 63                         # C[1] >> 63 (for ROL(C[1], 1))
	vpxor	ymm1, ymm1, [rsp+0x80]                # C[4] = A[4] xor A[9] xor A[14] xor A[19] xor A[24]
	
	# ===== THETA STEP - Computing D[x] = C[x-1] ^ ROL(C[x+1], 1) =====
	
	vpor	ymm11, ymm11, ymm0                     # ROL(C[1], 1) = (C[1] << 1) | (C[1] >> 63)
	vpsrlq	ymm0, ymm7, 63                         # C[2] >> 63 (for ROL(C[2], 1))
	vpor	ymm4, ymm4, ymm0                       # ROL(C[2], 1) = (C[2] << 1) | (C[2] >> 63)
	vpsrlq	ymm0, ymm5, 63                         # C[3] >> 63 (for ROL(C[3], 1))
	vpxor	ymm11, ymm11, ymm1                     # D[0] = C[4] xor ROL(C[1], 1)
	vmovdqu	[rsp+0x240], ymm0                      # temp store C[3] >> 63
	vpsllq	ymm0, ymm5, 1                          # C[3] << 1 (for ROL(C[3], 1))
	vpxor	ymm4, ymm4, ymm2                       # D[1] = C[0] xor ROL(C[2], 1)
	vpxor	ymm15, ymm11, ymm15                    # A'[20] = D[0] xor A[20] (A'[0][4])
	vpor	ymm0, ymm0, [rsp+0x240]                # ROL(C[3], 1) = (C[3] << 1) | (C[3] >> 63)
	vpxor	ymm12, ymm4, ymm12                     # A'[6] = D[1] xor A[6] (A'[1][1])
	vpxor	ymm13, ymm4, ymm13                     # A'[16] = D[1] xor A[16] (A'[1][3])
	vpxor	ymm0, ymm0, ymm9                       # D[2] = C[1] xor ROL(C[3], 1)
	vpsrlq	ymm9, ymm1, 63                         # C[4] >> 63 (for ROL(C[4], 1))
	vpsllq	ymm1, ymm1, 1                          # C[4] << 1 (for ROL(C[4], 1))
	vpxor	ymm10, ymm0, ymm10                     # A'[12] = D[2] xor A[12] (A'[2][2])
	vpxor	ymm8, ymm0, ymm8                       # A'[22] = D[2] xor A[22] (A'[2][4])
	vpor	ymm1, ymm1, ymm9                       # ROL(C[4], 1) = (C[4] << 1) | (C[4] >> 63)
	vpbroadcastq ymm9, QWORD PTR [rsi]            # load round constant RC[i]
	vpxor	ymm1, ymm1, ymm7                       # D[3] = C[2] xor ROL(C[4], 1)
	vpsrlq	ymm7, ymm2, 63                         # C[0] >> 63 (for ROL(C[0], 1))
	vpsllq	ymm2, ymm2, 1                          # C[0] << 1 (for ROL(C[0], 1))
	vpxor	ymm3, ymm1, ymm3                       # A'[18] = D[3] xor A[18] (A'[3][3])
	vpor	ymm2, ymm2, ymm7                       # ROL(C[0], 1) = (C[0] << 1) | (C[0] >> 63)
	
	# ===== RHO and PI STEPS - B[y][(2*x+3*y)%5] = ROL(A'[x][y], r[x][y]) =====
	
	vpsrlq	ymm7, ymm12, 20                        # A'[6] >> 20 (for rho rotation)
	vpsllq	ymm12, ymm12, 44                       # A'[6] << 44 (for rho rotation)
	vpxor	ymm2, ymm2, ymm5                       # D[4] = C[3] xor ROL(C[0], 1)
	vpxor	ymm5, ymm11, [rsp+0x0]               # A'[0] = D[0] xor A[0] (A'[0][0])
	vpor	ymm12, ymm12, ymm7                     # B[1][1] = ROL(A'[6], 44) (rho+pi step)
	vpsrlq	ymm7, ymm10, 21                        # A'[12] >> 21 (for rho rotation)
	vpxor	ymm6, ymm2, ymm6                       # A'[24] = D[4] xor A[24] (A'[4][4])
	vpsllq	ymm10, ymm10, 43                       # A'[12] << 43 (for rho rotation)
	
	# ===== CHI STEP - A''[x][y] = B[x][y] ^ (~B[x+1][y] & B[x+2][y]) =====
	
	vpor	ymm10, ymm10, ymm7                     # B[2][2] = ROL(A'[12], 43) (rho+pi step)
	vpandn	ymm7, ymm12, ymm10                     # ~B[1][1] & B[2][2] (chi step preparation)
	vpxor	ymm7, ymm7, ymm9                       # B[0][0] xor (~B[1][1] & B[2][2]) xor RC[i]
	vpxor	ymm9, ymm7, ymm5                       # A''[0] = B[0][0] xor (~B[1][0] & B[2][0]) xor RC[i]
	vpsrlq	ymm7, ymm3, 43                         # A'[18] >> 43 (for rho rotation)
	vmovdqu	[rsp+0x0], ymm9                      # store A''[0] (new A[0][0])
	vpsllq	ymm3, ymm3, 21                         # A'[18] << 21 (for rho rotation)
	vpor	ymm3, ymm3, ymm7                       # B[3][3] = ROL(A'[18], 21) (rho+pi step)
	vpandn	ymm7, ymm10, ymm3                      # ~B[2][2] & B[3][3] (chi step)
	vpxor	ymm9, ymm7, ymm12                      # A''[1] = B[1][1] xor (~B[2][2] & B[3][3])
	vpsrlq	ymm7, ymm6, 50                         # A'[24] >> 50 (for rho rotation)
	vpsllq	ymm6, ymm6, 14                         # A'[24] << 14 (for rho rotation)
	vmovdqu	[rsp+0x320], ymm9                       # store A''[1] (temp B result)
	vpor	ymm6, ymm6, ymm7                       # B[4][4] = ROL(A'[24], 14) (rho+pi step)
	vpandn	ymm7, ymm3, ymm6                       # ~B[3][3] & B[4][4] (chi step)
	vpxor	ymm10, ymm7, ymm10                     # A''[2] = B[2][2] xor (~B[3][3] & B[4][4])
	vpandn	ymm7, ymm6, ymm5                       # ~B[4][4] & B[0][0] (chi step)
	vpandn	ymm5, ymm5, ymm12                      # ~B[0][0] & B[1][1] (chi step)
	vpxor	ymm3, ymm7, ymm3                       # A''[3] = B[3][3] xor (~B[4][4] & B[0][0])
	vpxor	ymm6, ymm5, ymm6                       # A''[4] = B[4][4] xor (~B[0][0] & B[1][1])
	vmovdqu	[rsp+0x300], ymm10                      # store A''[2]
	vmovdqu	[rsp+0x2e0], ymm3                       # store A''[3]
	
	# ===== RHO+PI+CHI for second row (A[x][1]) =====
	
	vpxor	ymm3, ymm1, [rsp+0x60]                # A'[3] = D[3] xor A[3]
	vmovdqu	[rsp+0x2c0], ymm6                       # store A''[4]
	vpsrlq	ymm5, ymm3, 36                         # A'[3] >> 36 (for rho rotation)
	vpsllq	ymm3, ymm3, 28                         # A'[3] << 28 (for rho rotation)
	vpor	ymm3, ymm3, ymm5                       # B[0][1] = ROL(A'[3], 28) (rho+pi: A[3] -> B[0][1])
	vpxor	ymm5, ymm2, [rsp+0x100]                # A'[9] = D[4] xor A[9]
	vpsrlq	ymm6, ymm5, 44                         # A'[9] >> 44 (for rho rotation)
	vpsllq	ymm5, ymm5, 20                         # A'[9] << 20 (for rho rotation)
	vpor	ymm5, ymm5, ymm6                       # B[1][1] = ROL(A'[9], 20) (rho+pi: A[9] -> B[1][1])
	vpxor	ymm6, ymm11, [rsp+0x120]               # A'[10] = D[0] xor A[10]
	vpsrlq	ymm7, ymm6, 61                         # A'[10] >> 61 (for rho rotation)
	vpsllq	ymm6, ymm6, 3                          # A'[10] << 3 (for rho rotation)
	vpor	ymm6, ymm6, ymm7                       # B[2][1] = ROL(A'[10], 3) (rho+pi: A[10] -> B[2][1])
	vpandn	ymm7, ymm5, ymm6                       # ~B[1][1] & B[2][1] (chi step)
	vpxor	ymm10, ymm7, ymm3                      # A''[5] = B[0][1] xor (~B[1][1] & B[2][1])
	vpsrlq	ymm7, ymm13, 19                        # A'[16] >> 19
	vpsllq	ymm13, ymm13, 45                       # A'[16] << 45 (for rho rotation)
	vmovdqu	[rsp+0x2a0], ymm10                      # store A''[5]
	vpor	ymm13, ymm13, ymm7                     # B[3][1] = ROL(A'[16], 45) (rho+pi)
	vpsrlq	ymm7, ymm8, 3                          # A'[22] >> 3 (for rho rotation)
	vpsllq	ymm8, ymm8, 61                         # A'[22] << 61 (for rho rotation)
	vpandn	ymm10, ymm6, ymm13                     # ~B[2][1] & B[3][1] (chi step)
	vpor	ymm8, ymm8, ymm7                       # B[4][1] = ROL(A'[22], 61) (rho+pi)
	vpxor	ymm10, ymm10, ymm5                     # A''[6] = B[1][1] xor (~B[2][1] & B[3][1])
	vpandn	ymm7, ymm13, ymm8                      # ~B[3][1] & B[4][1] (chi step)
	vpxor	ymm12, ymm7, ymm6                      # A''[7] = B[2][1] xor (~B[3][1] & B[4][1])
	vpandn	ymm6, ymm8, ymm3                       # ~B[4][1] & B[0][1] (chi step)
	vpandn	ymm3, ymm3, ymm5                       # ~B[0][1] & B[1][1] (chi step)
	vpxor	ymm7, ymm6, ymm13                      # A''[8] = B[3][1] xor (~B[4][1] & B[0][1])
	vpxor	ymm8, ymm3, ymm8                       # A''[9] = B[4][1] xor (~B[0][1] & B[1][1])
	vmovdqu	[rsp+0x280], ymm12                      # store A''[7]
	vmovdqu	[rsp+0x260], ymm7                       # store A''[8]
	vmovdqu	[rsp+0x100], ymm8                      # store A''[9]
	
	# ===== RHO+PI+CHI for third row (A[x][2]) =====
	
	vpxor	ymm3, ymm4, [rsp+0x20]                # A'[16] = D[1] xor A[16]
	vpsrlq	ymm5, ymm3, 63                         # A'[16] >> 63 (for rho rotation)
	vpsllq	ymm3, ymm3, 1                          # A'[16] << 1 (for rho rotation)
	vpor	ymm3, ymm3, ymm5                       # B[0][2] = ROL(A'[16], 1) (rho+pi)
	vpxor	ymm5, ymm0, [rsp+0xc0]                # A'[7] = D[2] xor A[7]
	vpsrlq	ymm6, ymm5, 58                         # A'[7] >> 58 (for rho rotation)
	vpsllq	ymm5, ymm5, 6                          # A'[7] << 6 (for rho rotation)
	vpor	ymm5, ymm5, ymm6                       # B[1][2] = ROL(A'[7], 6) (rho+pi)
	vpxor	ymm6, ymm1, [rsp+0x160]                # A'[13] = D[3] xor A[13]
	vpsrlq	ymm7, ymm6, 39                         # A'[13] >> 39 (for rho rotation)
	vpsllq	ymm6, ymm6, 25                         # A'[13] << 25 (for rho rotation)
	vpor	ymm6, ymm6, ymm7                       # B[2][2] = ROL(A'[13], 25) (rho+pi)
	vpandn	ymm7, ymm5, ymm6                       # ~B[1][2] & B[2][2] (chi step)
	vpxor	ymm8, ymm7, ymm3                       # A''[10] = B[0][2] xor (~B[1][2] & B[2][2])
	vpxor	ymm7, ymm2, [rsp+0x1e0]                # A'[19] = D[4] xor A[19]
	vmovdqu	[rsp+0xc0], ymm8                      # store A''[10]
	vpshufb	ymm7, ymm7, [rdx]                      # B[3][2] = ROL(A'[19], 8) using byte shuffle
	vpandn	ymm8, ymm6, ymm7                       # ~B[2][2] & B[3][2] (chi step)
	vpxor	ymm13, ymm8, ymm5                      # A''[11] = B[1][2] xor (~B[2][2] & B[3][2])
	vpsrlq	ymm8, ymm15, 46                        # A'[20] >> 46 (for rho rotation)
	vmovdqu	[rsp+0x1e0], ymm13                     # store A''[11]
	vpsllq	ymm15, ymm15, 18                       # A'[20] << 18 (for rho rotation)
	vpor	ymm15, ymm15, ymm8                     # B[4][2] = ROL(A'[20], 18) (rho+pi)
	vpxor	ymm8, ymm4, [rsp+0x140]                # A'[11] = D[1] xor A[11]
	vpxor	ymm4, ymm4, ymm14                      # (temp computation for later)
	vpandn	ymm9, ymm7, ymm15                      # ~B[3][2] & B[4][2] (chi step)
	vpxor	ymm9, ymm9, ymm6                       # A''[12] = B[2][2] xor (~B[3][2] & B[4][2])
	vpandn	ymm6, ymm15, ymm3                      # ~B[4][2] & B[0][2] (chi step)
	vpandn	ymm3, ymm3, ymm5                       # ~B[0][2] & B[1][2] (chi step)
	vpxor	ymm15, ymm3, ymm15                     # A''[14] = B[4][2] xor (~B[0][2] & B[1][2])
	vpxor	ymm12, ymm6, ymm7                      # A''[13] = B[3][2] xor (~B[4][2] & B[0][2])
	
	# ===== RHO+PI+CHI for fourth row (A[x][3]) =====
	
	vpxor	ymm3, ymm2, [rsp+0x80]                # A'[4] = D[4] xor A[4]
	vmovdqu	[rsp+0x120], ymm12                     # store A''[13]
	vpxor	ymm12, ymm1, [rsp+0x200]               # A'[23] = D[3] xor A[23]
	vpxor	ymm1, ymm1, [rsp+0xe0]                # A'[8] = D[3] xor A[8]
	vpxor	ymm2, ymm2, [rsp+0x180]                # A'[14] = D[4] xor A[14]
	vpsrlq	ymm5, ymm3, 37                         # A'[4] >> 37 (for rho rotation)
	vpshufb	ymm12, ymm12, [rcx]                    # B[3][3] = ROL(A'[23], 56) using byte shuffle
	vpsllq	ymm3, ymm3, 27                         # A'[4] << 27 (for rho rotation)
	vpor	ymm3, ymm3, ymm5                       # B[0][3] = ROL(A'[4], 27) (rho+pi)
	vpxor	ymm5, ymm11, [rsp+0xa0]               # A'[5] = D[0] xor A[5]
	vpxor	ymm11, ymm11, [rsp+0x1a0]              # A'[15] = D[0] xor A[15]
	vpsrlq	ymm6, ymm5, 28                         # A'[5] >> 28 (for rho rotation)
	vpsllq	ymm5, ymm5, 36                         # A'[5] << 36 (for rho rotation)
	vpor	ymm5, ymm5, ymm6                       # B[1][3] = ROL(A'[5], 36) (rho+pi)
	vpsrlq	ymm6, ymm8, 54                         # A'[11] >> 54 (for rho rotation)
	vpsllq	ymm8, ymm8, 10                         # A'[11] << 10 (for rho rotation)
	vpor	ymm8, ymm8, ymm6                       # B[2][3] = ROL(A'[11], 10) (rho+pi)
	vpandn	ymm6, ymm5, ymm8                       # ~B[1][3] & B[2][3] (chi step)
	vpxor	ymm7, ymm6, ymm3                       # A''[15] = B[0][3] xor (~B[1][3] & B[2][3])
	vpxor	ymm6, ymm0, [rsp+0x1c0]                # A'[17] = D[2] xor A[17]
	vpxor	ymm0, ymm0, [rsp+0x40]                # A'[2] = D[2] xor A[2]
	vmovdqu	[rsp+0x240], ymm7                      # store A''[15]
	vpsrlq	ymm7, ymm6, 49                         # A'[17] >> 49 (for rho rotation)
	vpsllq	ymm6, ymm6, 15                         # A'[17] << 15 (for rho rotation)
	vpor	ymm6, ymm6, ymm7                       # B[4][3] = ROL(A'[17], 15) (rho+pi)
	vpandn	ymm13, ymm6, ymm12                     # ~B[4][3] & B[3][3] (chi step)
	vpandn	ymm7, ymm8, ymm6                       # ~B[2][3] & B[4][3] (chi step)
	vpxor	ymm13, ymm13, ymm8                     # A''[17] = B[2][3] xor (~B[4][3] & B[3][3])
	vpandn	ymm8, ymm12, ymm3                      # ~B[3][3] & B[0][3] (chi step)
	vpandn	ymm3, ymm3, ymm5                       # ~B[0][3] & B[1][3] (chi step)
	vpxor	ymm3, ymm3, ymm12                      # A''[18] = B[3][3] xor (~B[0][3] & B[1][3])
	vpxor	ymm8, ymm8, ymm6                       # A''[19] = B[4][3] xor (~B[3][3] & B[0][3])
	vpxor	ymm7, ymm7, ymm5                       # A''[16] = B[1][3] xor (~B[2][3] & B[4][3])
	vmovdqu	[rsp+0x1c0], ymm13                     # store A''[17]
	vmovdqu	[rsp+0x140], ymm3                      # store A''[18]
	
	# ===== RHO+PI+CHI for fifth row (A[x][4]) =====
	
	vpsrlq	ymm3, ymm0, 2                          # A'[2] >> 2 (for rho rotation)
	vpsllq	ymm0, ymm0, 62                         # A'[2] << 62 (for rho rotation)
	vmovdqu	ymm13, [rsp+0x280]                      # load A''[7]
	vpor	ymm0, ymm0, ymm3                       # B[0][4] = ROL(A'[2], 62) (rho+pi)
	vpsrlq	ymm3, ymm1, 9                          # A'[8] >> 9 (for rho rotation)
	vpxor	ymm13, ymm13, [rsp+0x300]               # A''[7] xor A''[2] (C[2] computation start)
	vpsllq	ymm1, ymm1, 55                         # A'[8] << 55 (for rho rotation)
	vpor	ymm1, ymm1, ymm3                       # B[1][4] = ROL(A'[8], 55) (rho+pi)
	vpsrlq	ymm3, ymm2, 25                         # A'[14] >> 25 (for rho rotation)
	vpsllq	ymm2, ymm2, 39                         # A'[14] << 39 (for rho rotation)
	vpor	ymm2, ymm2, ymm3                       # B[2][4] = ROL(A'[14], 39) (rho+pi)
	vpsrlq	ymm3, ymm11, 23                        # A'[15] >> 23 (for rho rotation)
	vpsllq	ymm11, ymm11, 41                       # A'[15] << 41 (for rho rotation)
	vpandn	ymm5, ymm1, ymm2                       # ~B[1][4] & B[2][4] (chi step)
	vpor	ymm11, ymm11, ymm3                     # B[3][4] = ROL(A'[15], 41) (rho+pi)
	vpxor	ymm5, ymm5, ymm0                       # A''[20] = B[0][4] xor (~B[1][4] & B[2][4])
	vpandn	ymm3, ymm2, ymm11                      # ~B[2][4] & B[3][4] (chi step)
	vpxor	ymm6, ymm3, ymm1                       # A''[21] = B[1][4] xor (~B[2][4] & B[3][4])
	vpsrlq	ymm3, ymm4, 62                         # (temp) >> 62 (for rho rotation)
	vpsllq	ymm4, ymm4, 2                          # (temp) << 2 (for rho rotation)
	vmovdqu	ymm12, ymm6                            # copy A''[21]
	vpor	ymm4, ymm4, ymm3                       # B[4][4] = ROL(A'[21], 2) (rho+pi)
	vmovdqu	[rsp+0x220], ymm12                       # store A''[21]
	vpandn	ymm6, ymm11, ymm4                      # ~B[3][4] & B[4][4] (chi step)
	vpxor	ymm6, ymm6, ymm2                       # A''[22] = B[2][4] xor (~B[3][4] & B[4][4])
	vpandn	ymm2, ymm4, ymm0                       # ~B[4][4] & B[0][4] (chi step)
	vpandn	ymm0, ymm0, ymm1                       # ~B[0][4] & B[1][4] (chi step)
	vpxor	ymm14, ymm2, ymm11                     # A''[23] = B[3][4] xor (~B[4][4] & B[0][4])
	vmovdqu	ymm2, [rsp+0x260]                       # load A''[8]
	vpxor	ymm0, ymm0, ymm4                       # A''[24] = B[4][4] xor (~B[0][4] & B[1][4])
	
	# ===== ROUND i+1: THETA STEP - Computing C[x] for next round =====
	
	vpxor	ymm1, ymm5, [rsp+0x240]                # A''[20] xor A''[15] (C[0] computation)
	vmovdqu	ymm11, [rsp+0xc0]                     # load A''[10]
	vpxor	ymm11, ymm11, [rsp+0x2a0]               # A''[10] xor A''[5] (C[0] computation)
	vmovdqu	ymm3, ymm14                            # copy A''[23]
	vpxor	ymm14, ymm10, [rsp+0x320]               # A''[6] xor A''[1] (C[1] computation)
	vpxor	ymm11, ymm11, ymm1                     # (A''[20] xor A''[15]) xor (A''[10] xor A''[5])
	vpxor	ymm1, ymm7, [rsp+0x1e0]                # A''[16] xor A''[11] (C[1] computation)
	vpxor	ymm11, ymm11, [rsp+0x0]              # C[0] = A''[0] xor A''[5] xor A''[10] xor A''[15] xor A''[20]
	vpxor	ymm14, ymm14, ymm1                     # (A''[6] xor A''[1]) xor (A''[16] xor A''[11])
	vpxor	ymm1, ymm9, [rsp+0x1c0]                # A''[12] xor A''[17] (C[2] computation)
	vpxor	ymm14, ymm14, ymm12                    # C[1] = A''[1] xor A''[6] xor A''[11] xor A''[16] xor A''[21]
	vpxor	ymm12, ymm2, [rsp+0x2e0]                # A''[8] xor A''[3] (C[3] computation)
	vpxor	ymm2, ymm0, ymm15                      # A''[24] xor A''[14] (C[4] computation)
	vmovdqu	[rsp+0x200], ymm3                      # store A''[23]
	vpxor	ymm13, ymm13, ymm1                     # (A''[7] xor A''[2]) xor (A''[12] xor A''[17])
	vpxor	ymm1, ymm8, ymm3                       # A''[19] xor A''[23] (C[3] computation)
	vpxor	ymm12, ymm12, ymm1                     # (A''[8] xor A''[3]) xor (A''[19] xor A''[23])
	vpsrlq	ymm3, ymm14, 63                        # C[1] >> 63 (for ROL)
	vpxor	ymm13, ymm13, ymm6                     # C[2] = A''[2] xor A''[7] xor A''[12] xor A''[17] xor A''[22]
	vmovdqu	ymm1, [rsp+0x100]                      # load A''[9]
	vpxor	ymm1, ymm1, [rsp+0x2c0]                 # A''[9] xor A''[4] (C[4] computation)
	vpsllq	ymm4, ymm13, 1                         # C[2] << 1 (for ROL)
	vpxor	ymm12, ymm12, [rsp+0x120]              # C[3] = A''[3] xor A''[8] xor A''[13] xor A''[18] xor A''[23]
	vpxor	ymm1, ymm1, ymm2                       # (A''[24] xor A''[14]) xor (A''[9] xor A''[4])
	vpsllq	ymm2, ymm14, 1                         # C[1] << 1 (for ROL)
	vpxor	ymm1, ymm1, [rsp+0x140]                # C[4] = A''[4] xor A''[9] xor A''[14] xor A''[19] xor A''[24]
	vpor	ymm2, ymm2, ymm3                       # ROL(C[1], 1)
	vpsrlq	ymm3, ymm13, 63                        # C[2] >> 63 (for ROL)
	vpor	ymm4, ymm4, ymm3                       # ROL(C[2], 1)
	vpsrlq	ymm3, ymm12, 63                        # C[3] >> 63 (for ROL)
	vpxor	ymm2, ymm2, ymm1                       # D[0] = C[4] xor ROL(C[1], 1)
	vmovdqu	[rsp+0x20], ymm3                      # temp store C[3] >> 63
	vpsllq	ymm3, ymm12, 1                         # C[3] << 1 (for ROL)
	vpxor	ymm4, ymm4, ymm11                      # D[1] = C[0] xor ROL(C[2], 1)
	vpxor	ymm5, ymm2, ymm5                       # A'''[20] = D[0] xor A''[20]
	vpor	ymm3, ymm3, [rsp+0x20]                # ROL(C[3], 1)
	vpxor	ymm10, ymm4, ymm10                     # A'''[6] = D[1] xor A''[6]
	vpxor	ymm7, ymm4, ymm7                       # A'''[16] = D[1] xor A''[16]
	vpxor	ymm14, ymm3, ymm14                     # D[2] = C[1] xor ROL(C[3], 1)
	vpsrlq	ymm3, ymm1, 63                         # C[4] >> 63 (for ROL)
	vpsllq	ymm1, ymm1, 1                          # C[4] << 1 (for ROL)
	vpxor	ymm9, ymm14, ymm9                      # A'''[12] = D[2] xor A''[12]
	vpxor	ymm6, ymm14, ymm6                      # A'''[22] = D[2] xor A''[22]
	vpor	ymm1, ymm1, ymm3                       # ROL(C[4], 1)
	vpsrlq	ymm3, ymm11, 63                        # C[0] >> 63 (for ROL)
	vpsllq	ymm11, ymm11, 1                        # C[0] << 1 (for ROL)
	vpxor	ymm1, ymm1, ymm13                      # D[3] = C[2] xor ROL(C[4], 1)
	vpbroadcastq ymm13, QWORD PTR [rsi+8]         # load round constant RC[i+1]
	vpor	ymm11, ymm3, ymm11                     # ROL(C[0], 1)
	vpxor	ymm8, ymm1, ymm8                       # A'''[19] = D[3] xor A''[19]
	vpxor	ymm3, ymm2, [rsp+0x0]                # A'''[0] = D[0] xor A''[0]
	vpxor	ymm11, ymm11, ymm12                    # D[4] = C[3] xor ROL(C[0], 1)
	
	# ===== ROUND i+1: RHO and PI STEPS =====
	
	vpsrlq	ymm12, ymm10, 20                       # A'''[6] >> 20
	vpsllq	ymm10, ymm10, 44                       # A'''[6] << 44
	vpxor	ymm0, ymm11, ymm0                      # A'''[24] = D[4] xor A''[24]
	vpor	ymm10, ymm12, ymm10                    # B[1][1] = ROL(A'''[6], 44)
	vpsrlq	ymm12, ymm9, 21                        # A'''[12] >> 21
	vpsllq	ymm9, ymm9, 43                         # A'''[12] << 43
	vpor	ymm9, ymm12, ymm9                      # B[2][2] = ROL(A'''[12], 43)
	vpandn	ymm12, ymm10, ymm9                     # ~B[1][1] & B[2][2] (chi step)
	vpxor	ymm12, ymm12, ymm13                    # B[0][0] xor (~B[1][1] & B[2][2]) xor RC[i+1]
	vpxor	ymm12, ymm12, ymm3                     # A''''[0] = B[0][0] xor (~B[1][0] & B[2][0]) xor RC[i+1]
	vmovdqu	[rsp+0x0], ymm12                     # store A''''[0] (for next iteration)
	vpsrlq	ymm12, ymm8, 43                        # A'''[19] >> 43
	vpsllq	ymm8, ymm8, 21                         # A'''[19] << 21
	vpor	ymm8, ymm12, ymm8                      # B[3][3] = ROL(A'''[19], 21)
	vpandn	ymm12, ymm9, ymm8                      # ~B[2][2] & B[3][3] (chi step)
	vpxor	ymm12, ymm12, ymm10                    # A''''[1] = B[1][1] xor (~B[2][2] & B[3][3])
	vmovdqu	[rsp+0x20], ymm12                     # store A''''[1] (for next iteration)
	vpsrlq	ymm12, ymm0, 50                        # A'''[24] >> 50
	vpsllq	ymm0, ymm0, 14                         # A'''[24] << 14
	vpor	ymm0, ymm12, ymm0                      # B[4][4] = ROL(A'''[24], 14)
	vpandn	ymm12, ymm8, ymm0                      # ~B[3][3] & B[4][4] (chi step)
	vpxor	ymm9, ymm12, ymm9                      # A''''[2] = B[2][2] xor (~B[3][3] & B[4][4])
	vmovdqu	[rsp+0x40], ymm9                      # store A''''[2] (for next iteration)
	vpandn	ymm9, ymm0, ymm3                       # ~B[4][4] & B[0][0] (chi step)
	vpandn	ymm3, ymm3, ymm10                      # ~B[0][0] & B[1][1] (chi step)
	vpxor	ymm0, ymm3, ymm0                       # A''''[4] = B[4][4] xor (~B[0][0] & B[1][1])
	vpxor	ymm3, ymm1, [rsp+0x2e0]                 # A'''[3] = D[3] xor A''[3]
	vpxor	ymm9, ymm9, ymm8                       # A''''[3] = B[3][3] xor (~B[4][4] & B[0][0])
	vpxor	ymm8, ymm11, [rsp+0x100]               # A'''[9] = D[4] xor A''[9]
	vmovdqu	[rsp+0x60], ymm9                      # store A''''[3] (for next iteration)
	vpxor	ymm9, ymm2, [rsp+0xc0]                # A'''[10] = D[0] xor A''[10]
	vmovdqu	[rsp+0x80], ymm0                      # store A''''[4] (for next iteration)
	
	# ===== Continue RHO+PI+CHI for remaining rows (similar pattern) =====
	
	vpsrlq	ymm0, ymm3, 36                         # A'''[3] >> 36
	vpsllq	ymm3, ymm3, 28                         # A'''[3] << 28
	vpor	ymm0, ymm0, ymm3                       # B[0][1] = ROL(A'''[3], 28)
	vpsrlq	ymm3, ymm8, 44                         # A'''[9] >> 44
	vpsllq	ymm8, ymm8, 20                         # A'''[9] << 20
	vpor	ymm3, ymm3, ymm8                       # B[1][1] = ROL(A'''[9], 20)
	vpsrlq	ymm8, ymm9, 61                         # A'''[10] >> 61
	vpsllq	ymm9, ymm9, 3                          # A'''[10] << 3
	vpor	ymm8, ymm8, ymm9                       # B[2][1] = ROL(A'''[10], 3)
	vpandn	ymm9, ymm3, ymm8                       # ~B[1][1] & B[2][1] (chi step)
	vpxor	ymm9, ymm9, ymm0                       # A''''[5] = B[0][1] xor (~B[1][1] & B[2][1])
	vmovdqu	[rsp+0xa0], ymm9                      # store A''''[5] (for next iteration)
	vpsrlq	ymm9, ymm7, 19                         # A'''[16] >> 19
	vpsllq	ymm7, ymm7, 45                         # A'''[16] << 45
	vpor	ymm7, ymm9, ymm7                       # B[3][1] = ROL(A'''[16], 45)
	vpsrlq	ymm9, ymm6, 3                          # A'''[22] >> 3
	vpsllq	ymm6, ymm6, 61                         # A'''[22] << 61
	vpandn	ymm12, ymm8, ymm7                      # ~B[2][1] & B[3][1] (chi step)
	vpor	ymm6, ymm9, ymm6                       # B[4][1] = ROL(A'''[22], 61)
	vpxor	ymm12, ymm12, ymm3                     # A''''[6] = B[1][1] xor (~B[2][1] & B[3][1])
	vpandn	ymm9, ymm7, ymm6                       # ~B[3][1] & B[4][1] (chi step)
	vpxor	ymm8, ymm9, ymm8                       # A''''[7] = B[2][1] xor (~B[3][1] & B[4][1])
	vmovdqu	[rsp+0xc0], ymm8                      # store A''''[7] (for next iteration)
	vpandn	ymm8, ymm6, ymm0                       # ~B[4][1] & B[0][1] (chi step)
	vpandn	ymm0, ymm0, ymm3                       # ~B[0][1] & B[1][1] (chi step)
	vpxor	ymm3, ymm4, [rsp+0x320]                 # A'''[1] = D[1] xor A''[1]
	vpxor	ymm0, ymm0, ymm6                       # A''''[9] = B[4][1] xor (~B[0][1] & B[1][1])
	vpxor	ymm6, ymm14, [rsp+0x280]                # A'''[7] = D[2] xor A''[7]
	vpxor	ymm8, ymm8, ymm7                       # A''''[8] = B[3][1] xor (~B[4][1] & B[0][1])
	vmovdqu	[rsp+0x100], ymm0                      # store A''''[9] (for next iteration)
	vpsrlq	ymm0, ymm3, 63                         # A'''[1] >> 63
	vpsllq	ymm3, ymm3, 1                          # A'''[1] << 1
	vmovdqu	[rsp+0xe0], ymm8                      # store A''''[8] (for next iteration)
	vpor	ymm0, ymm0, ymm3                       # B[0][2] = ROL(A'''[1], 1)
	vpsrlq	ymm3, ymm6, 58                         # A'''[7] >> 58
	vpsllq	ymm6, ymm6, 6                          # A'''[7] << 6
	vpor	ymm3, ymm3, ymm6                       # B[1][2] = ROL(A'''[7], 6)
	vpxor	ymm6, ymm1, [rsp+0x120]                # A'''[13] = D[3] xor A''[13]
	vpsrlq	ymm7, ymm6, 39                         # A'''[13] >> 39
	vpsllq	ymm6, ymm6, 25                         # A'''[13] << 25
	vpor	ymm7, ymm7, ymm6                       # B[2][2] = ROL(A'''[13], 25)
	vpandn	ymm6, ymm3, ymm7                       # ~B[1][2] & B[2][2] (chi step)
	vpxor	ymm9, ymm6, ymm0                       # A''''[10] = B[0][2] xor (~B[1][2] & B[2][2])
	vpxor	ymm6, ymm11, [rsp+0x140]               # A'''[11] = D[4] xor A''[11]
	vmovdqu	[rsp+0x120], ymm9                      # store A''''[10] (for next iteration)
	vpshufb	ymm6, ymm6, [rdx]                      # B[3][2] = ROL(A'''[11], 8) using byte shuffle
	vpandn	ymm8, ymm7, ymm6                       # ~B[2][2] & B[3][2] (chi step)
	vpxor	ymm10, ymm8, ymm3                      # A''''[11] = B[1][2] xor (~B[2][2] & B[3][2])
	vpsrlq	ymm8, ymm5, 46                         # A'''[20] >> 46
	vmovdqu	[rsp+0x140], ymm10                     # store A''''[11] (for next iteration)
	vpsllq	ymm5, ymm5, 18                         # A'''[20] << 18
	vpor	ymm5, ymm8, ymm5                       # B[4][2] = ROL(A'''[20], 18)
	vpandn	ymm10, ymm6, ymm5                      # ~B[3][2] & B[4][2] (chi step)
	vpxor	ymm10, ymm10, ymm7                     # A''''[12] = B[2][2] xor (~B[3][2] & B[4][2])
	vpandn	ymm7, ymm5, ymm0                       # ~B[4][2] & B[0][2] (chi step)
	vpandn	ymm0, ymm0, ymm3                       # ~B[0][2] & B[1][2] (chi step)
	vpxor	ymm0, ymm0, ymm5                       # A''''[14] = B[4][2] xor (~B[0][2] & B[1][2])
	vpxor	ymm9, ymm7, ymm6                       # A''''[13] = B[3][2] xor (~B[4][2] & B[0][2])
	vmovdqu	[rsp+0x180], ymm0                      # store A''''[14] (for next iteration)
	vpxor	ymm0, ymm11, [rsp+0x2c0]                # A'''[4] = D[4] xor A''[4]
	vpxor	ymm11, ymm11, ymm15                    # A'''[14] = D[4] xor A''[14]
	vmovdqu	[rsp+0x160], ymm9                      # store A''''[13] (for next iteration)
	vpsrlq	ymm5, ymm0, 37                         # A'''[4] >> 37
	vpsllq	ymm0, ymm0, 27                         # A'''[4] << 27
	vpor	ymm5, ymm5, ymm0                       # B[0][3] = ROL(A'''[4], 27)
	vpxor	ymm0, ymm2, [rsp+0x2a0]                 # A'''[5] = D[0] xor A''[5]
	vpxor	ymm2, ymm2, [rsp+0x240]                # A'''[15] = D[0] xor A''[15]
	vpsrlq	ymm6, ymm0, 28                         # A'''[5] >> 28
	vpsllq	ymm0, ymm0, 36                         # A'''[5] << 36
	vpor	ymm6, ymm6, ymm0                       # B[1][3] = ROL(A'''[5], 36)
	vpxor	ymm0, ymm4, [rsp+0x1e0]                # A'''[11] = D[1] xor A''[11]
	vpxor	ymm4, ymm4, [rsp+0x220]                  # A'''[21] = D[1] xor A''[21]
	vpsrlq	ymm3, ymm0, 54                         # A'''[11] >> 54
	vpsllq	ymm0, ymm0, 10                         # A'''[11] << 10
	vpor	ymm3, ymm3, ymm0                       # B[2][3] = ROL(A'''[11], 10)
	vpandn	ymm0, ymm6, ymm3                       # ~B[1][3] & B[2][3] (chi step)
	vpxor	ymm0, ymm0, ymm5                       # A''''[15] = B[0][3] xor (~B[1][3] & B[2][3])
	vmovdqu	[rsp+0x1a0], ymm0                      # store A''''[15] (for next iteration)
	vpxor	ymm0, ymm14, [rsp+0x1c0]               # A'''[17] = D[2] xor A''[17]
	vpxor	ymm14, ymm14, [rsp+0x300]               # A'''[2] = D[2] xor A''[2]
	vpsrlq	ymm7, ymm0, 49                         # A'''[17] >> 49
	vpsllq	ymm0, ymm0, 15                         # A'''[17] << 15
	vpor	ymm7, ymm7, ymm0                       # B[4][3] = ROL(A'''[17], 15)
	vpxor	ymm0, ymm1, [rsp+0x200]                # A'''[23] = D[3] xor A''[23]
	vpxor	ymm1, ymm1, [rsp+0x260]                 # A'''[8] = D[3] xor A''[8]
	vpandn	ymm13, ymm3, ymm7                      # ~B[2][3] & B[4][3] (chi step)
	vpshufb	ymm0, ymm0, [rcx]                      # B[3][3] = ROL(A'''[23], 56) using byte shuffle
	vpxor	ymm13, ymm13, ymm6                     # A''''[16] = B[1][3] xor (~B[2][3] & B[4][3])
	vpandn	ymm8, ymm7, ymm0                       # ~B[4][3] & B[3][3] (chi step)
	vpxor	ymm3, ymm8, ymm3                       # A''''[17] = B[2][3] xor (~B[4][3] & B[3][3])
	vmovdqu	[rsp+0x1c0], ymm3                      # store A''''[17] (for next iteration)
	vpandn	ymm3, ymm0, ymm5                       # ~B[3][3] & B[0][3] (chi step)
	vpandn	ymm5, ymm5, ymm6                       # ~B[0][3] & B[1][3] (chi step)
	vpxor	ymm6, ymm5, ymm0                       # A''''[18] = B[3][3] xor (~B[0][3] & B[1][3])
	vpsrlq	ymm0, ymm1, 9                          # A'''[8] >> 9
	vpxor	ymm3, ymm3, ymm7                       # A''''[19] = B[4][3] xor (~B[3][3] & B[0][3])
	vmovdqu	[rsp+0x1e0], ymm6                      # store A''''[18] (for next iteration)
	vpsllq	ymm1, ymm1, 55                         # A'''[8] << 55
	vpsrlq	ymm6, ymm14, 2                         # A'''[2] >> 2
	vpor	ymm1, ymm0, ymm1                       # B[1][4] = ROL(A'''[8], 55)
	vpsrlq	ymm0, ymm11, 25                        # A'''[14] >> 25
	vpsllq	ymm11, ymm11, 39                       # A'''[14] << 39
	vpsllq	ymm14, ymm14, 62                       # A'''[2] << 62
	vpor	ymm11, ymm0, ymm11                     # B[2][4] = ROL(A'''[14], 39)
	vpsrlq	ymm0, ymm2, 23                         # A'''[15] >> 23
	vpor	ymm6, ymm6, ymm14                      # B[0][4] = ROL(A'''[2], 62)
	vpsllq	ymm2, ymm2, 41                         # A'''[15] << 41
	vpandn	ymm15, ymm1, ymm11                     # ~B[1][4] & B[2][4] (chi step)
	vpor	ymm2, ymm0, ymm2                       # B[3][4] = ROL(A'''[15], 41)
	vpxor	ymm15, ymm15, ymm6                     # A''''[20] = B[0][4] xor (~B[1][4] & B[2][4])
	vpandn	ymm0, ymm11, ymm2                      # ~B[2][4] & B[3][4] (chi step)
	vpxor	ymm14, ymm0, ymm1                      # A''''[21] = B[1][4] xor (~B[2][4] & B[3][4])
	vpsrlq	ymm0, ymm4, 62                         # A'''[21] >> 62
	vpsllq	ymm4, ymm4, 2                          # A'''[21] << 2
	vpor	ymm4, ymm0, ymm4                       # B[4][4] = ROL(A'''[21], 2)
	vpandn	ymm0, ymm4, ymm6                       # ~B[4][4] & B[0][4] (chi step)
	vpandn	ymm8, ymm2, ymm4                       # ~B[3][4] & B[4][4] (chi step)
	vpandn	ymm6, ymm6, ymm1                       # ~B[0][4] & B[1][4] (chi step)
	vpxor	ymm2, ymm0, ymm2                       # A''''[23] = B[3][4] xor (~B[4][4] & B[0][4])
	vpxor	ymm8, ymm8, ymm11                      # A''''[22] = B[2][4] xor (~B[3][4] & B[4][4])
	vpxor	ymm6, ymm6, ymm4                       # A''''[24] = B[4][4] xor (~B[0][4] & B[1][4])
	vmovdqu	[rsp+0x200], ymm2                      # store A''''[23] (for next iteration)

	# ===== LOOP CONTROL =====
	
	add rsi, 16                                    # advance round constant pointer by 2 rounds
	add r10, 2                                     # increment loop counter by 2
	cmp r10, 0x18                                  # compare with 24 (0x18 = 24 rounds)
	jne	Lsha3_keccak4_f1600_alt                    # if not done, continue to next iteration

	// Load A[1], A[3], save A[21], load A[0], A[2] for deinterleaving
	vmovdqu	ymm4, [rsp+0x20]
	vmovdqu	ymm11, ymm14
	vmovdqu	ymm5, [rsp+0x60]
	vmovdqu	ymm14, [rsp+0x0]
	vmovdqu	ymm1, [rsp+0x40]
	// Load, De-interleave, and Store 32 bytes to each of the 4 states (A[0-3])
	vpunpcklqdq	ymm2, ymm14, ymm4
	vpunpckhqdq	ymm0, ymm14, ymm4
	vpunpcklqdq	ymm4, ymm1, ymm5
	vperm2i128	ymm7, ymm2, ymm4, 32
	vperm2i128	ymm2, ymm2, ymm4, 49
	vpunpckhqdq	ymm1, ymm1, ymm5
	vmovdqu	ymm4, [rsp+0x80]
	vmovdqu	[rdi+0x190], ymm2
	vperm2i128	ymm5, ymm0, ymm1, 32
	vperm2i128	ymm0, ymm0, ymm1, 49
	vmovdqu	ymm2, [rsp+0xa0]
	vmovdqu	[rdi+0x258], ymm0
	vpunpcklqdq	ymm1, ymm4, ymm2
	vpunpckhqdq	ymm0, ymm4, ymm2
	vmovdqu	[rdi+0xc8], ymm5
	vmovdqu	ymm4, [rsp+0xc0]
	vmovdqu	[rdi+0x0], ymm7
	// Load, De-interleave, and Store 32 bytes to each of the 4 states (A[4-7])
	vmovdqu	ymm7, [rsp+0x140]
	vpunpcklqdq	ymm2, ymm12, ymm4
	vpunpckhqdq	ymm12, ymm12, ymm4
	vperm2i128	ymm5, ymm1, ymm2, 32
	vperm2i128	ymm4, ymm0, ymm12, 32
	vperm2i128	ymm1, ymm1, ymm2, 49
	vmovdqu	[rdi+0x20], ymm5
	vperm2i128	ymm0, ymm0, ymm12, 49
	vmovdqu	ymm5, [rsp+0x120]
	vmovdqu	[rdi+0xe8], ymm4
	vmovdqu	ymm4, [rsp+0xe0]
	vmovdqu	[rdi+0x1b0], ymm1
	vmovdqu	ymm1, [rsp+0x100]
	vmovdqu	[rdi+0x278], ymm0
	// Load, De-interleave, and Store 32 bytes to each of the 4 states (A[8-11])
	vpunpckhqdq	ymm0, ymm5, ymm7
	vpunpcklqdq	ymm2, ymm4, ymm1
	vpunpckhqdq	ymm1, ymm4, ymm1
	vpunpcklqdq	ymm4, ymm5, ymm7
	vperm2i128	ymm7, ymm2, ymm4, 32
	vperm2i128	ymm5, ymm1, ymm0, 32
	vperm2i128	ymm2, ymm2, ymm4, 49
	vmovdqu	[rdi+0x40], ymm7
	vperm2i128	ymm1, ymm1, ymm0, 49
	vmovdqu	ymm7, [rsp+0x1a0]
	vmovdqu	[rdi+0x108], ymm5
	vmovdqu	ymm5, [rsp+0x180]
	vmovdqu	[rdi+0x1d0], ymm2
	// Load, De-interleave, and Store 32 bytes to each of the 4 states (A[12-15])
	vpunpcklqdq	ymm2, ymm10, ymm9
	vpunpcklqdq	ymm4, ymm5, ymm7
	vpunpckhqdq	ymm0, ymm5, ymm7
	vmovdqu	[rdi+0x298], ymm1
	vpunpckhqdq	ymm1, ymm10, ymm9
	vperm2i128	ymm7, ymm2, ymm4, 32
	vperm2i128	ymm2, ymm2, ymm4, 49
	vperm2i128	ymm5, ymm1, ymm0, 32
	vmovdqu	ymm4, [rsp+0x1c0]
	vperm2i128	ymm1, ymm1, ymm0, 49
	vmovdqu	[rdi+0x1f0], ymm2
	vpunpcklqdq	ymm0, ymm13, ymm4
	vpunpckhqdq	ymm13, ymm13, ymm4
	vmovdqu	ymm4, [rsp+0x1e0]
	vmovdqu	[rdi+0x2b8], ymm1
	vmovdqu	[rdi+0x60], ymm7
	// Load, De-interleave, and Store 32 bytes to each of the 4 states (A[16-19])
	vpunpcklqdq	ymm1, ymm3, ymm4
	vpunpckhqdq	ymm3, ymm3, ymm4
	vmovdqu	[rdi+0x128], ymm5
	vperm2i128	ymm4, ymm0, ymm1, 32
	vperm2i128	ymm2, ymm13, ymm3, 32
	vperm2i128	ymm0, ymm0, ymm1, 49
	vmovdqu	[rdi+0x80], ymm4
	vperm2i128	ymm13, ymm13, ymm3, 49
	vmovdqu	[rdi+0x148], ymm2
	vmovdqu	ymm4, [rsp+0x200]
	vmovdqu	[rdi+0x210], ymm0
	// Load, De-interleave, and Store 32 bytes to each of the 4 states (A[20-23])
	vpunpcklqdq	ymm0, ymm15, ymm11
	vpunpckhqdq	ymm15, ymm15, ymm11
	vpunpcklqdq	ymm1, ymm8, ymm4
	vpunpckhqdq	ymm8, ymm8, ymm4
	vmovq   QWORD PTR [rdi+0xc0], xmm6
	vperm2i128	ymm3, ymm0, ymm1, 32
	vperm2i128	ymm2, ymm15, ymm8, 32
	vperm2i128	ymm0, ymm0, ymm1, 49
	vmovhpd	QWORD PTR [rdi+0x188], xmm6
	vperm2i128	ymm15, ymm15, ymm8, 49
	vextracti128	xmm6, ymm6, 0x1
	vmovdqu	[rdi+0x2d8], ymm13
	vmovdqu	[rdi+0xa0], ymm3
	vmovdqu	[rdi+0x168], ymm2
	vmovdqu	[rdi+0x230], ymm0
	vmovdqu	[rdi+0x2f8], ymm15
	// Store A[24] (last element) to each of the 4 states (8 bytes each)
	vmovq	QWORD PTR [rdi+0x250], xmm6
	vmovhpd [rdi+0x318], xmm6

	mov	rsp, r11
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc

S2N_BN_SIZE_DIRECTIVE(sha3_keccak4_f1600_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif