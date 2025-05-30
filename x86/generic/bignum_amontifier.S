// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compute "amontification" constant z :== 2^{128k} (congruent mod m)
// Input m[k]; output z[k]; temporary buffer t[>=k]
//
//    extern void bignum_amontifier(uint64_t k, uint64_t *z, const uint64_t *m,
//                                  uint64_t *t);
//
// This is called "amontifier" because any other value x can now be mapped into
// the almost-Montgomery domain with an almost-Montgomery multiplication by z.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = m, RCX = t
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = m, R9 = t
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_amontifier)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_amontifier)
        .text

#define k rdi
#define z rsi

// These two inputs get moved to different places since RCX and RDX are special

#define m r12
#define t r13

// Other variables
// Matters that c is RCX as CL=lo(c) is assumed in shifts

#define i rbx
#define j rbp
#define a rax
#define c rcx
#define h r11
#define l r10
#define b r9
#define n r8

// Some aliases for the values b and n

#define q r8
#define r r9

#define ashort eax
#define ishort ebx
#define jshort ebp
#define qshort r8d


S2N_BN_SYMBOL(bignum_amontifier):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Save some additional registers for use, copy args out of RCX and RDX

        push    rbp
        push    rbx
        push    r12
        push    r13

        mov     m, rdx
        mov     t, rcx

// If k = 0 the whole operation is trivial

        test    k, k
        jz      bignum_amontifier_end

// Copy the input m into the temporary buffer t. The temporary register
// c matters since we want it to hold the highest digit, ready for the
// normalization phase.

        xor     i, i
bignum_amontifier_copyinloop:
        mov     c, [m+8*i]
        mov     [t+8*i], c
        inc     i
        cmp     i, k
        jc      bignum_amontifier_copyinloop

// Do a rather stupid but constant-time digit normalization, conditionally
// shifting left (k-1) times based on whether the top word is zero.
// With careful binary striding this could be O(k*log(k)) instead of O(k^2)
// while still retaining the constant-time style.
// The "neg c" sets the zeroness predicate (~CF) for the entire inner loop

        mov     i, k
        dec     i
        jz      bignum_amontifier_normalized
bignum_amontifier_normloop:
        xor     j, j
        mov     h, k
        neg     c
        mov     ashort, 0
bignum_amontifier_shufloop:
        mov     c, a
        mov     a, [t+8*j]
        cmovc   c, a
        mov     [t+8*j], c
        inc     j
        dec     h
        jnz     bignum_amontifier_shufloop
        dec     i
        jnz     bignum_amontifier_normloop

// We now have the top digit nonzero, assuming the input was nonzero,
// and as per the invariant of the loop above, c holds that digit. So
// now just count c's leading zeros and shift t bitwise that many bits.
// Note that we don't care about the result of bsr for zero inputs so
// the simple xor-ing with 63 is safe.

bignum_amontifier_normalized:

        bsr     c, c
        xor     c, 63

        xor     b, b
        xor     i, i
bignum_amontifier_bitloop:
        mov     a, [t+8*i]
        mov     j, a
        shld    a, b, cl
        mov     [t+8*i],a
        mov     b, j
        inc     i
        cmp     i, k
        jc      bignum_amontifier_bitloop

// Let h be the high word of n, which in all the in-scope cases is >= 2^63.
// Now successively form q = 2^i div h and r = 2^i mod h as i goes from
// 64 to 126. We avoid just using division out of constant-time concerns
// (at the least we would need to fix up h = 0 for out-of-scope inputs) and
// don't bother with Newton-Raphson, since this stupid simple loop doesn't
// contribute much of the overall runtime at typical sizes.

        mov     h, [t+8*k-8]
        mov     qshort, 1
        mov     r, h
        neg     r
        mov     ishort, 62
bignum_amontifier_estloop:

        add     q, q
        mov     a, h
        sub     a, r
        cmp     r, a    // CF <=> r < h - r <=> 2 * r < h
        sbb     a, a
        not     a       // a = bitmask(2 * r >= h)
        sub     q, a
        add     r, r
        and     a, h
        sub     r, a
        dec     i
        jnz     bignum_amontifier_estloop

// Strictly speaking the above loop doesn't quite give the true remainder
// and quotient in the special case r = h = 2^63, so fix it up. We get
// q = 2^63 - 1 and r = 2^63 and really want q = 2^63 and r = 0. This is
// supererogatory, because the main property of q used below still holds
// in this case unless the initial m = 1, and then anyway the overall
// specification (congruence modulo m) holds degenerately. But it seems
// nicer to get a "true" quotient and remainder.

        inc     r
        cmp     h, r
        adc     q, 0

// So now we have q and r with 2^126 = q * h + r (imagining r = 0 in the
// fixed-up case above: note that we never actually use the computed
// value of r below and so didn't adjust it). And we can assume the ranges
// q <= 2^63 and r < h < 2^64.
//
// The idea is to use q as a first quotient estimate for a remainder
// of 2^{p+62} mod n, where p = 64 * k. We have, splitting n into the
// high and low parts h and l:
//
// 2^{p+62} - q * n = 2^{p+62} - q * (2^{p-64} * h + l)
//                  = 2^{p+62} - (2^{p-64} * (q * h) + q * l)
//                  = 2^{p+62} - 2^{p-64} * (2^126 - r) - q * l
//                  = 2^{p-64} * r - q * l
//
// Note that 2^{p-64} * r < 2^{p-64} * h <= n
// and also  q * l < 2^63 * 2^{p-64} = 2^{p-1} <= n
// so |diff| = |2^{p-64} * r - q * l| < n.
//
// If in fact diff >= 0 then it is already 2^{p+62} mod n.
// otherwise diff + n is the right answer.
//
// To (maybe?) make the computation slightly easier we actually flip
// the sign and compute d = q * n - 2^{p+62}. Then the answer is either
// -d (when negative) or n - d; in either case we effectively negate d.
// This negating tweak in fact spoils the result for cases where
// 2^{p+62} mod n = 0, when we get n instead. However the only case
// where this can happen is m = 1, when the whole spec holds trivially,
// and actually the remainder of the logic below works anyway since
// the latter part of the code only needs a congruence for the k-digit
// result, not strict modular reduction (the doublings will maintain
// the non-strict inequality).

        xor     c, c
        xor     i, i
bignum_amontifier_mulloop:
        mov     rax, [t+8*i]
        mul     q
        add     rax, c
        adc     rdx, 0
        mov     [z+8*i], rax
        mov     c, rdx
        inc     i
        cmp     i, k
        jc      bignum_amontifier_mulloop

// Now c is the high word of the product, so subtract 2^62
// and then turn it into a bitmask in q = h

        mov     rax, 0x4000000000000000
        sub     c, a
        sbb     q, q
        not     q

// Now do [c] * n - d for our final answer

        xor     c, c
        xor     i, i
bignum_amontifier_remloop:
        mov     a, [t+8*i]
        and     a, q
        neg     c
        sbb     a, [z+8*i]
        sbb     c, c
        mov     [z+8*i], a
        inc     i
        cmp     i, k
        jc      bignum_amontifier_remloop

// Now still need to do a couple of modular doublings to get us all the
// way up to 2^{p+64} == r from initial 2^{p+62} == r (mod n).

        xor     c, c
        xor     j, j
        xor     b, b
bignum_amontifier_dubloop1:
        mov     a, [z+8*j]
        shrd    c, a, 63
        neg     b
        sbb     c, [t+8*j]
        sbb     b, b
        mov     [z+8*j],c
        mov     c, a
        inc     j
        cmp     j, k
        jc      bignum_amontifier_dubloop1
        shr     c, 63
        add     c, b
        xor     j, j
        xor     b, b
bignum_amontifier_corrloop1:
        mov     a, [t+8*j]
        and     a, c
        neg     b
        adc     a, [z+8*j]
        sbb     b, b
        mov     [z+8*j], a
        inc     j
        cmp     j, k
        jc      bignum_amontifier_corrloop1

// This is not exactly the same: we also copy output to t giving the
// initialization t_1 = r == 2^{p+64} mod n for the main loop next.

        xor     c, c
        xor     j, j
        xor     b, b
bignum_amontifier_dubloop2:
        mov     a, [z+8*j]
        shrd    c, a, 63
        neg     b
        sbb     c, [t+8*j]
        sbb     b, b
        mov     [z+8*j],c
        mov     c, a
        inc     j
        cmp     j, k
        jc      bignum_amontifier_dubloop2
        shr     c, 63
        add     c, b
        xor     j, j
        xor     b, b
bignum_amontifier_corrloop2:
        mov     a, [t+8*j]
        and     a, c
        neg     b
        adc     a, [z+8*j]
        sbb     b, b
        mov     [z+8*j], a
        mov     [t+8*j], a
        inc     j
        cmp     j, k
        jc      bignum_amontifier_corrloop2

// We then successively generate (k+1)-digit values satisfying
// t_i == 2^{p+64*i} mod n, each of which is stored in h::t. Finish
// initialization by zeroing h initially

        xor     h, h

// Then if t_i = 2^{p} * h + l
// we have t_{i+1} == 2^64 * t_i
//         = (2^{p+64} * h) + (2^64 * l)
//        == r * h + l<<64
// Do this k more times so we end up == 2^{128*k+64}, one more than we want
//
// Writing B = 2^{64k}, the possible correction of adding r, which for
// a (k+1)-digit result is equivalent to subtracting q = 2^{64*(k+1)} - r
// would give the overall worst-case value minus q of
// [ B * (B^k - 1) + (B - 1) * r ] - [B^{k+1} - r]
// = B * (r - 1) < B^{k+1} so we keep inside k+1 digits as required.
//
// This implementation makes the shift implicit by starting b with the
// "previous" digit (initially 0) to offset things by 1.

        mov     i, k
bignum_amontifier_modloop:
        xor     b, b
        mov     n, k
        xor     j, j
        xor     c, c
bignum_amontifier_cmaloop:
        adc     c, b
        sbb     l, l
        mov     rax, [z+8*j]
        mul     h
        sub     rdx, l
        add     rax, c
        mov     b, [t+8*j]
        mov     [t+8*j], rax
        mov     c, rdx
        inc     j
        dec     n
        jnz     bignum_amontifier_cmaloop
        adc     b, c
        mov     h, b

        sbb     l, l

        xor     j, j
        xor     c, c
bignum_amontifier_oaloop:
        mov     a, [t+8*j]
        mov     b, [z+8*j]
        and     b, l
        neg     c
        adc     a, b
        sbb     c, c
        mov     [t+8*j], a
        inc     j
        cmp     j, k
        jc      bignum_amontifier_oaloop
        sub     h, c

        dec     i
        jnz     bignum_amontifier_modloop

// Now do one almost-Montgomery reduction w.r.t. the original m
// which lops off one 2^64 from the congruence and, with the usual
// almost-Montgomery correction, gets us back inside k digits for
// the end result.

        mov     a, [m]
        mov     c, a
        mov     b, a
        shl     c, 2
        sub     b, c
        xor     b, 2
        mov     c, b
        imul    c, a
        mov     ashort, 2
        add     a, c
        add     c, 1
        imul    b, a
        imul    c, c
        mov     ashort, 1
        add     a, c
        imul    b, a
        imul    c, c
        mov     ashort, 1
        add     a, c
        imul    b, a
        imul    c, c
        mov     ashort, 1
        add     a, c
        imul    b, a

        mov     c, [t]
        imul    b, c

        mov     rax, [m]
        mul     b
        add     rax, c
        mov     c, rdx
        mov     jshort, 1
        mov     n, k
        dec     n
        jz      bignum_amontifier_montend

bignum_amontifier_montloop:
        adc     c, [t+8*j]
        sbb     l, l
        mov     rax, [m+8*j]
        mul     b
        sub     rdx, l
        add     rax, c
        mov     [t+8*j-8], rax
        mov     c, rdx
        inc     j
        dec     n
        jnz     bignum_amontifier_montloop
bignum_amontifier_montend:
        adc     h, c
        sbb     l, l
        mov     [t+8*k-8], h

        xor     j, j
        xor     c, c
bignum_amontifier_osloop:
        mov     a, [t+8*j]
        mov     b, [m+8*j]
        and     b, l
        neg     c
        sbb     a, b
        sbb     c, c
        mov     [z+8*j], a
        inc     j
        cmp     j, k
        jc      bignum_amontifier_osloop

 bignum_amontifier_end:
        pop     r13
        pop     r12
        pop     rbx
        pop     rbp

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
