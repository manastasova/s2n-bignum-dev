// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square modulo p_25519, z := (x^2) mod p_25519
// Input x[4]; output z[4]
//
//    extern void bignum_sqr_p25519_alt(uint64_t z[static 4],
//                                      const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sqr_p25519_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sqr_p25519_alt)
        .text

#define z %rdi
#define x %rsi

// Re-use input pointer later for constant

#define d %rsi
#define c %rcx

#define dshort %esi

// Macro for the key "multiply and add to (c,h,l)" step, for square term

#define combadd1(c,h,l,numa)                    \
        movq    numa, %rax ;                      \
        mulq    %rax;                            \
        addq    %rax, l ;                         \
        adcq    %rdx, h ;                         \
        adcq    $0, c

// A short form where we don't expect a top carry

#define combads(h,l,numa)                       \
        movq    numa, %rax ;                      \
        mulq    %rax;                            \
        addq    %rax, l ;                         \
        adcq    %rdx, h

// A version doubling before adding, for non-square terms

#define combadd2(c,h,l,numa,numb)               \
        movq    numa, %rax ;                      \
        mulq     numb;                 \
        addq    %rax, %rax ;                       \
        adcq    %rdx, %rdx ;                       \
        adcq    $0, c ;                           \
        addq    %rax, l ;                         \
        adcq    %rdx, h ;                         \
        adcq    $0, c

S2N_BN_SYMBOL(bignum_sqr_p25519_alt):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Save more registers to play with

        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15

// Result term 0

        movq    (x), %rax
        mulq    %rax

        movq    %rax, %r8
        movq    %rdx, %r9
        xorq    %r10, %r10

// Result term 1

       xorq    %r11, %r11
       combadd2(%r11,%r10,%r9,(x),8(x))

// Result term 2

        xorq    %r12, %r12
        combadd1(%r12,%r11,%r10,8(x))
        combadd2(%r12,%r11,%r10,(x),16(x))

// Result term 3

        xorq    %r13, %r13
        combadd2(%r13,%r12,%r11,(x),24(x))
        combadd2(%r13,%r12,%r11,8(x),16(x))

// Result term 4

        xorq    %r14, %r14
        combadd2(%r14,%r13,%r12,8(x),24(x))
        combadd1(%r14,%r13,%r12,16(x))

// Result term 5

        xorq    %r15, %r15
        combadd2(%r15,%r14,%r13,16(x),24(x))

// Result term 6

        combads(%r15,%r14,24(x))

// Now we have the full 8-digit product 2^256 * h + l where
// h = [%r15,%r14,%r13,%r12] and l = [%r11,%r10,%r9,%r8]
// and this is == 38 * h + l (mod p_25519)

        movl    $38, dshort

        movq    %r12, %rax
        mulq    d
        addq    %rax, %r8
        adcq    %rdx, %r9
        sbbq    c, c

        movq    %r13, %rax
        mulq    d
        subq    c, %rdx
        addq    %rax, %r9
        adcq    %rdx, %r10
        sbbq    c, c

        movq    %r14, %rax
        mulq    d
        subq    c, %rdx
        addq    %rax, %r10
        adcq    %rdx, %r11
        sbbq    c, c

        movq    %r15, %rax
        mulq    d
        subq    c, %rdx
        xorq    c, c
        addq    %rax, %r11
        movq    %rdx, %r12
        adcq    c, %r12

// Now we have reduced to 5 digits, 2^255 * h + l = [%r12,%r11,%r10,%r9,%r8]
// Use q = h + 1 as the initial quotient estimate, either right or 1 too big.

        shldq   $1, %r11, %r12
        leaq    1(%r12), %rax
        movl    $19, dshort
        bts     $63, %r11
        imulq   d, %rax
        addq    %rax, %r8
        adcq    c, %r9
        adcq    c, %r10
        adcq    c, %r11

// Now the effective answer is 2^256 * (CF - 1) + [u3,u2,u1,u0]
// So we correct if CF = 0 by subtracting 19, either way masking to
// 255 bits, i.e. by effectively adding p_25519 to the "full" answer

        sbbq    %rax, %rax
        notq    %rax
        andq    d, %rax
        subq    %rax, %r8
        sbbq    c, %r9
        sbbq    c, %r10
        sbbq    c, %r11
        btr     $63, %r11

// Write everything back

        movq    %r8, (z)
        movq    %r9, 8(z)
        movq    %r10, 16(z)
        movq    %r11, 24(z)

// Restore registers and return

        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
