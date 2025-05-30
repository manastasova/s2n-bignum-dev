// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Triple modulo p_256k1, z := (3 * x) mod p_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_triple_p256k1(uint64_t z[static 4],
//                                     const uint64_t x[static 4]);
//
// The input x can be any 4-digit bignum, not necessarily reduced modulo
// p_256k1, and the result is always fully reduced, z = (3 * x) mod p_256k1.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_triple_p256k1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_triple_p256k1)
        .text

#define z %rdi
#define x %rsi

// Main digits of intermediate results

#define d0 %r8
#define d1 %r9
#define d2 %r10
#define d3 %r11

// Quotient estimate = top of product + 1

#define q %rdx

// Other temporary variables and their short version

#define a %rax
#define c %rcx

#define ashort %eax
#define qshort %edx

S2N_BN_SYMBOL(bignum_triple_p256k1):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// First do the multiplication by 3, getting z = [h; d3; ...; d0]
// but immediately form the quotient estimate q = h + 1

        xorl    ashort, ashort

        movq    (x), q
        movq    q, d0
        adcxq   q, q
        adoxq   q, d0
        movq    8(x), q
        movq    q, d1
        adcxq   q, q
        adoxq   q, d1
        movq    16(x), q
        movq    q, d2
        adcxq   q, q
        adoxq   q, d2
        movq    24(x), q
        movq    q, d3
        adcxq   q, q
        adoxq   q, d3

// For this limited range a simple quotient estimate of q = h + 1 works, where
// h = floor(z / 2^256). Then -p_256k1 <= z - q * p_256k1 < p_256k1.

        movl    $1, qshort
        adcxq   a, q
        adoxq   a, q

// Initial subtraction of z - q * p_256k1, actually by adding q * 4294968273.

        movq    $4294968273, c
        xorq    a, a
        imulq   c, q
        addq    q, d0
        adcq    a, d1
        adcq    a, d2
        adcq    a, d3

// With z = 2^256 * h + l, the underlying result z' is actually
// (2^256 * h + l) - q * (2^256 - 4294968273) = (l + q * 4294968273) - 2^256
// so carry-clear <=> z' is negative. Correct by subtracting in that case.
// In any case, write final result to z as we go.

        cmovcq  a, c

        subq    c, d0
        movq    d0, (z)
        sbbq    a, d1
        movq    d1, 8(z)
        sbbq    a, d2
        movq    d2, 16(z)
        sbbq    a, d3
        movq    d3, 24(z)

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
