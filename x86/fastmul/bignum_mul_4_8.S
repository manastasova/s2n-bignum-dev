// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[4], y[4]; output z[8]
//
//    extern void bignum_mul_4_8(uint64_t z[static 8], const uint64_t x[static 4],
//                               const uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mul_4_8)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mul_4_8)
        .text

// These are actually right

#define z rdi
#define x rsi

// Copied in or set up

#define y rcx

// A zero register

#define zero rbp
#define zeroe ebp

// Add in x[i] * rdx to the (i,i+1) position with the register window
// Would be nice to have conditional expressions reg[i], reg[i+1] ...

.macro mulpadd arg1,arg2
        mulx    rbx, rax, [x+8*\arg2]
.if ((\arg1 + \arg2) % 4 == 0)
        adcx    r8, rax
        adox    r9, rbx
.elseif ((\arg1 + \arg2) % 4 == 1)
        adcx    r9, rax
        adox    r10, rbx
.elseif ((\arg1 + \arg2) % 4 == 2)
        adcx    r10, rax
        adox    r11, rbx
.elseif ((\arg1 + \arg2) % 4 == 3)
        adcx    r11, rax
        adox    r8, rbx
.endif

.endm


// Add in the whole j'th row

.macro addrow arg1
        mov     rdx, [y+8*\arg1]
        xor     zeroe, zeroe

        mulpadd \arg1, 0

.if (\arg1 % 4 == 0)
        mov     [z+8*\arg1],r8
.elseif (\arg1 % 4 == 1)
        mov     [z+8*\arg1],r9
.elseif (\arg1 % 4 == 2)
        mov     [z+8*\arg1],r10
.elseif (\arg1 % 4 == 3)
        mov     [z+8*\arg1],r11
.endif

        mulpadd \arg1, 1
        mulpadd \arg1, 2

.if (\arg1 % 4 == 0)
        mulx    r8, rax, [x+24]
        adcx    r11, rax
        adox    r8, zero
        adcx    r8, zero
.elseif (\arg1 % 4 == 1)
        mulx    r9, rax, [x+24]
        adcx    r8, rax
        adox    r9, zero
        adcx    r9, zero
.elseif (\arg1 % 4 == 2)
        mulx    r10, rax, [x+24]
        adcx    r9, rax
        adox    r10, zero
        adcx    r10, zero
.elseif (\arg1 % 4 == 3)
        mulx    r11, rax, [x+24]
        adcx    r10, rax
        adox    r11, zero
        adcx    r11, zero
.endif

.endm



S2N_BN_SYMBOL(bignum_mul_4_8):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save more registers to play with

        push    rbp
        push    rbx

// Copy y into a safe register to start with

        mov     y, rdx

// Zero a register, which also makes sure we don't get a fake carry-in

        xor     zeroe, zeroe

// Do the zeroth row, which is a bit different
// Write back the zero-zero product and then accumulate
// r8,r11,r10,r9 as y[0] * x from 1..4

        mov     rdx, [y]

        mulx    r9, r8, [x]
        mov     [z], r8

        mulx    r10, rbx, [x+8]
        adcx    r9, rbx

        mulx    r11, rbx, [x+16]
        adcx    r10, rbx

        mulx    r8, rbx, [x+24]
        adcx    r11, rbx
        adcx    r8, zero

// Now all the other rows in a uniform pattern

        addrow  1
        addrow  2
        addrow  3

// Now write back the additional columns

        mov     [z+32], r8
        mov     [z+40], r9
        mov     [z+48], r10
        mov     [z+56], r11

// Restore registers and return

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
