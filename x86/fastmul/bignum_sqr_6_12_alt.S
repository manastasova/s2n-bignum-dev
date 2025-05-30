// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square, z := x^2
// Input x[6]; output z[12]
//
//    extern void bignum_sqr_6_12_alt(uint64_t z[static 12],
//                                    const uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sqr_6_12_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sqr_6_12_alt)
        .text

// Input arguments

#define z rdi
#define x rsi

// Other variables used as a rotating 3-word window to add terms to

#define t0 r8
#define t1 r9
#define t2 r10

// Additional temporaries for local windows to share doublings

#define u0 rcx
#define u1 r11

// Macro for the key "multiply and add to (c,h,l)" step

#define combadd(c,h,l,numa,numb)                \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, 0

// Set up initial window (c,h,l) = numa * numb

#define combaddz(c,h,l,numa,numb)               \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        xor     c, c;                           \
        mov     l, rax;                         \
        mov     h, rdx

// Doubling step (c,h,l) = 2 * (c,hh,ll) + (0,h,l)

#define doubladd(c,h,l,hh,ll)                   \
        add     ll, ll;                         \
        adc     hh, hh;                         \
        adc     c, c;                           \
        add     l, ll;                          \
        adc     h, hh;                          \
        adc     c, 0

// Square term incorporation (c,h,l) += numba^2

#define combadd1(c,h,l,numa)                    \
        mov     rax, numa;                      \
        mul     rax;                            \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, 0

// A short form where we don't expect a top carry

#define combads(h,l,numa)                       \
        mov     rax, numa;                      \
        mul     rax;                            \
        add     l, rax;                         \
        adc     h, rdx

// A version doubling directly before adding, for single non-square terms

#define combadd2(c,h,l,numa,numb)               \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     rax, rax;                       \
        adc     rdx, rdx;                       \
        adc     c, 0;                           \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, 0

S2N_BN_SYMBOL(bignum_sqr_6_12_alt):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Result term 0

        mov     rax, [x]
        mul     rax

        mov     [z], rax
        mov     t0, rdx
        xor     t1, t1

// Result term 1

        xor     t2, t2
        combadd2(t2,t1,t0,[x],[x+8])
        mov     [z+8], t0

// Result term 2

        xor     t0, t0
        combadd1(t0,t2,t1,[x+8])
        combadd2(t0,t2,t1,[x],[x+16])
        mov     [z+16], t1

// Result term 3

        combaddz(t1,u1,u0,[x],[x+24])
        combadd(t1,u1,u0,[x+8],[x+16])
        doubladd(t1,t0,t2,u1,u0)
        mov     [z+24], t2

// Result term 4

        combaddz(t2,u1,u0,[x],[x+32])
        combadd(t2,u1,u0,[x+8],[x+24])
        doubladd(t2,t1,t0,u1,u0)
        combadd1(t2,t1,t0,[x+16])
        mov     [z+32], t0

// Result term 5

        combaddz(t0,u1,u0,[x],[x+40])
        combadd(t0,u1,u0,[x+8],[x+32])
        combadd(t0,u1,u0,[x+16],[x+24])
        doubladd(t0,t2,t1,u1,u0)
        mov     [z+40], t1

// Result term 6

        combaddz(t1,u1,u0,[x+8],[x+40])
        combadd(t1,u1,u0,[x+16],[x+32])
        doubladd(t1,t0,t2,u1,u0)
        combadd1(t1,t0,t2,[x+24])
        mov     [z+48], t2

// Result term 7

        combaddz(t2,u1,u0,[x+16],[x+40])
        combadd(t2,u1,u0,[x+24],[x+32])
        doubladd(t2,t1,t0,u1,u0)
        mov     [z+56], t0

// Result term 8

        xor     t0, t0
        combadd2(t0,t2,t1,[x+24],[x+40])
        combadd1(t0,t2,t1,[x+32])
        mov     [z+64], t1

// Result term 9

        xor     t1, t1
        combadd2(t1,t0,t2,[x+32],[x+40])
        mov     [z+72], t2

// Result term 10

        combads(t1,t0,[x+40])
        mov     [z+80], t0

// Result term 11

        mov     [z+88], t1

// Return

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
