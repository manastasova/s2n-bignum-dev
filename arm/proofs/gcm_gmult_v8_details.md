# GCM GMULT V8: Detailed Explanation of Specifications and Proofs

This document walks through every specification and proof in the formal
verification of `gcm_gmult_v8`, explaining the mathematical ideas, design
decisions, and proof techniques in detail.

---

## Table of Contents

1. [NIST SP 800-38D Specification](#1-nist-sp-800-38d-specification)
2. [Equivalence A: NIST to Polynomial Algebra](#2-equivalence-a-nist-to-polynomial-algebra)
3. [Equivalence B: P(x) to Q(x) Ideal Mapping](#3-equivalence-b-px-to-qx-ideal-mapping)
4. [Equivalence C: polyval_dot to gcm_gmult_spec](#4-equivalence-c-polyval_dot-to-gcm_gmult_spec)
5. [Equivalence D: gcm_gmult_spec to ARM Assembly](#5-equivalence-d-gcm_gmult_spec-to-arm-assembly)

---

## 1. NIST SP 800-38D Specification

### 1.1 What is GHASH?

GHASH is the authentication component of AES-GCM (Galois/Counter Mode),
the most widely deployed authenticated encryption scheme. It performs
multiplication in the finite field GF(2^128), defined by the irreducible
polynomial P(x) = x^128 + x^7 + x^2 + x + 1.

The NIST standard SP 800-38D (November 2007) defines two algorithms:
- **Algorithm 1** (Section 6.3): multiplication of two 128-bit blocks X * Y
- **Algorithm 2** (Section 6.4): GHASH_H, the iterated hash function

### 1.2 How Algorithm 1 works

Algorithm 1 is a **shift-and-XOR loop**, the binary polynomial equivalent
of schoolbook multiplication with online modular reduction:

```
Input: two 128-bit blocks X and Y
Output: X * Y in GF(2^128)

1. Let Z_0 = 0^128, V_0 = Y
2. For i = 0 to 127:
   a. If x_i = 1:  Z_{i+1} = Z_i XOR V_i     (accumulate partial product)
      else:         Z_{i+1} = Z_i
   b. If LSB(V_i) = 1:  V_{i+1} = (V_i >> 1) XOR R    (reduce overflow)
      else:              V_{i+1} = V_i >> 1
3. Return Z_128
```

Step 2a scans the bits of X one at a time. When x_i is 1, it XORs the
current power of Y (stored in V) into the accumulator Z. This is exactly
binary polynomial multiplication.

Step 2b maintains the invariant that V_i = Y * x^i mod P(x). Shifting V
right by 1 multiplies it by x in GF(2^128) (because of the reversed bit
convention). When the low bit falls off (overflow), the reduction
constant R = 0xE1 || 0^120 is XORed in to reduce back modulo P(x).

### 1.3 The NIST bit ordering

The most subtle aspect of the NIST spec is its **non-standard bit ordering**.
NIST numbers the bits of a 128-bit block as x_0, x_1, ..., x_127 where:
- x_0 is the **MSB** of byte 0
- x_7 is the **LSB** of byte 0
- x_8 is the MSB of byte 1
- etc.

This is the opposite of the natural polynomial convention where bit 0 is
the coefficient of x^0 (the constant term, the LSB).

In HOL Light's `int128` word type, bit 0 is the LSB of byte 0. The mapping
between NIST and HOL Light bit positions is:

```
NIST bit i  =  HOL Light bit (8 * (i DIV 8) + 7 - i MOD 8)
```

This is a **per-byte bit reversal**: within each byte the bit order is
flipped, but the byte order is preserved. The function
`bit_reverse_per_byte` (= `word_reversefields 8 o word_reversefields 1`)
implements this conversion.

### 1.4 Where the spec lives

**File:** `arm/proofs/utils/gcm_gmult_v8_nist.ml` (lines 1-99)

### 1.5 The HOL Light definitions, one by one

#### `nist_bit` — NIST bit accessor

```ocaml
let nist_bit = new_definition
  `nist_bit (x:int128) (i:num) =
   bit (8 * (i DIV 8) + 7 - i MOD 8) x`;;
```

This implements the NIST-to-HOL bit mapping formula. For any NIST bit
position i, it computes the corresponding HOL Light bit position and
reads it from the 128-bit word x.

Examples:
- `nist_bit x 0` = `bit 7 x` (MSB of byte 0)
- `nist_bit x 7` = `bit 0 x` (LSB of byte 0)
- `nist_bit x 8` = `bit 15 x` (MSB of byte 1)
- `nist_bit x 127` = `bit 120 x` (LSB of byte 15)

I used `new_definition` (a non-recursive definitional mechanism in HOL
Light) because `nist_bit` is a simple function with no recursion.

#### `nist_lsb` — NIST's LSB_1(V)

```ocaml
let nist_lsb = new_definition
  `nist_lsb (v:int128) = bit 120 v`;;
```

NIST's "rightmost bit" is bit x_127, which maps to HOL bit 120. This is
the bit that determines whether reduction is needed in step 2b of
Algorithm 1.

#### `nist_shr1` — NIST right shift

```ocaml
let nist_shr1 = new_definition
  `nist_shr1 (v:int128) : int128 =
   (word_of_bits
     {k | k < 128 /\
          (if k MOD 8 < 7 then bit (k + 1) v
           else if k = 7 then F
           else bit (k - 15) v)} : int128)`;;
```

This is the most complex definition because the NIST right shift does
not correspond to any standard word operation in HOL Light. In the NIST
bit ordering, "shift right by 1" means every bit x_i becomes x_{i-1}
and x_0 is cleared. But in HOL Light's bit ordering, this translates to
a non-trivial bit permutation.

I used `word_of_bits`, which constructs a word from a **set** of bit
positions. For each HOL Light bit position k (0 through 127), the
definition specifies where the bit comes from:

- **k MOD 8 < 7** (not at a byte boundary MSB): The bit comes from
  position k+1, which is the "next" bit in NIST order within the same
  byte. This handles the common case of shifting within a byte.

- **k = 7** (byte 0's MSB = NIST bit x_0): This becomes 0 (false),
  since the NIST shift pushes a 0 into the MSB position.

- **k MOD 8 = 7 and k > 7** (other byte MSBs): The bit comes from
  position k-15. This is the cross-byte carry: NIST bit x_{8n} comes
  from x_{8n+1}, which after the per-byte bit reversal is at HOL
  position (8n + 7) - 15 = 8(n-1) + 0, i.e., the LSB of the previous byte.

**Design choice:** I used `word_of_bits` instead of trying to express
`nist_shr1` using combinations of `word_shl`, `word_ushr`, `word_and`,
etc. The set-based definition is more readable and directly corresponds
to the specification, even though it's less "computational."

#### `ghash_R` — Reduction constant

```ocaml
let ghash_R = new_definition
  `ghash_R : int128 = word 0xE1`;;
```

The NIST reduction constant R = 11100001 || 0^120. In the NIST bit
ordering, the first byte has bits 1,1,1,0,0,0,0,1. In HOL Light's byte
representation, byte 0 is 0xE1 = 225. Since all other bytes are 0,
R is simply `word 225` (or equivalently `word 0xE1`).

#### `ghash_mul_loop` — Algorithm 1 loop body

```ocaml
let ghash_mul_loop = define
  `ghash_mul_loop (z:int128) (v:int128) (x:int128) 0 = z /\
   ghash_mul_loop z v x (SUC n) =
     let i = 128 - SUC n in
     let z' = if nist_bit x i then word_xor z v else z in
     let v' = if nist_lsb v
              then word_xor (nist_shr1 v) ghash_R
              else nist_shr1 v in
     ghash_mul_loop z' v' x n`;;
```

This is the recursive loop. I used HOL Light's `define` for recursive
definitions. Key design choices:

- **Countdown from 128 to 0** instead of counting up from 0 to 127.
  HOL Light's induction principle works on `SUC n`, so counting down is
  more natural. The bit index is computed as `i = 128 - SUC n`.

- **All NIST operations used directly**: `nist_bit`, `nist_lsb`,
  `nist_shr1`, `ghash_R`. No simplification or conversion to polynomial
  operations. This ensures the definition is a faithful transcription of
  the standard.

- **Functional style**: no mutable state. Each loop iteration takes the
  current (z, v, x) and the remaining count n, returns the final z.

#### `nist_ghash_mul` — Algorithm 1 top level

```ocaml
let nist_ghash_mul = new_definition
  `nist_ghash_mul (x:int128) (y:int128) : int128 =
   ghash_mul_loop (word 0) y x 128`;;
```

Start with Z_0 = 0, V_0 = Y, process all 128 bits of X. This directly
implements NIST's "return Z_128."

#### `nist_ghash` — Algorithm 2 (GHASH_H)

```ocaml
let nist_ghash = define
  `nist_ghash (h:int128) (acc:int128) [] = acc /\
   nist_ghash h acc (CONS x xs) =
     nist_ghash h (nist_ghash_mul (word_xor acc x) h) xs`;;
```

The iterated GHASH: given a hash key H, an accumulator, and a list of
128-bit blocks, XOR each block with the accumulator then multiply by H.
Uses `define` for the recursive list structure.

### 1.6 The reduction constant R

The reduction constant R = 0xE1 is derived from the irreducible polynomial
P(x) = x^128 + x^7 + x^2 + x + 1.

In GF(2^128), we have `x^128 = x^7 + x^2 + x + 1 (mod P(x))`. So when
the V-step multiplies by x and the result overflows 128 bits (the x^128
term appears), we subtract (= XOR in GF(2)) the low part of P(x) to
reduce back.

The low part is `x^7 + x^2 + x + 1`. In NIST bit ordering:
- x^7 → NIST bit 7 → byte 0, position 0 (LSB) → HOL bit 0
- x^2 → NIST bit 2 → byte 0, position 5 → HOL bit 5
- x^1 → NIST bit 1 → byte 0, position 6 → HOL bit 6
- x^0 → NIST bit 0 → byte 0, position 7 (MSB) → HOL bit 7

So byte 0 = `11100001` in binary = **0xE1**. All other bytes are 0.
Hence R = 0xE1 || 0^120 = `word 225`.

After per-byte bit reversal, R becomes 0x87 = 135 = `10000111` in binary.
This is `x^7 + x^2 + x + 1` in natural polynomial order — exactly the
low-order terms of P(x). The proof confirms this as `BYTE_BITREV_GHASH_R`.

### 1.7 The schoolbook specification: `ghash_reduce(word_pmul a b)`

The NIST Algorithm 1 (Horner evaluation) is one way to multiply in
GF(2^128). The alternative is the **schoolbook approach**: compute the
full polynomial product first, then reduce modulo P(x) afterwards.

This is expressed as `ghash_reduce(word_pmul a b)` using definitions
from John Harrison's `ghash.ml` library:

#### `word_pmul` — Full polynomial (carry-less) multiplication

```
word_pmul (a:int128) (b:int128) : 256 word
```

Takes two 128-bit inputs, produces a **256-bit** result. This is
carry-less multiplication — exactly like schoolbook long multiplication
but with XOR instead of addition (no carries in GF(2)).

For example, multiplying `x^3 + x + 1` by `x^2 + 1`:

```
         1 0 1 1       (A = x^3 + x + 1)
       x 0 1 0 1       (B = x^2 + 1)
       ---------
         1 0 1 1       A * bit 0 of B (= A * 1)
       0 0 0 0         A * bit 1 of B (= A * 0, shifted left 1)
     1 0 1 1           A * bit 2 of B (= A * 1, shifted left 2)
   0 0 0 0             A * bit 3 of B (= A * 0, shifted left 3)
   -------------
   0 1 0 0 1 1 1       XOR all rows = x^5 + x^4 + x^2 + x + 1
```

The result can be up to 254 bits (two 127-degree polynomials multiplied).
No reduction happens here — it's the raw product.

This is what the ARM `PMULL` instruction computes in hardware.

#### `ghash_reduce1` — One pass of Barrett reduction

```
ghash_reduce1 x =
  word_xor (word_subword x (0,128))           (* low 128 bits *)
           (word_pmul (word_ushr x 128)        (* high bits *)
                      (word 135))              (* 0x87 = x^7+x^2+x+1 *)
```

In polynomial terms: if x = hi * x^128 + lo, then since
`x^128 = x^7 + x^2 + x + 1 (mod P)`:

```
x mod P = lo + hi * (x^7 + x^2 + x + 1)
        = lo XOR pmul(hi, 0x87)
```

One pass takes a ~254-bit input and produces a ~134-bit output
(128 bits from lo, plus up to 7 more from the pmul with 0x87).

#### `ghash_reduce` — Two passes = full reduction

```
ghash_reduce x = word_zx(ghash_reduce1(ghash_reduce1(x)))
```

- **First pass**: 256-bit → ~134-bit (folds upper 128 bits down)
- **Second pass**: ~134-bit → 128-bit (folds remaining ~6 high bits down)
- **`word_zx`**: Truncates 256-bit to 128-bit (safe because after two
  passes the upper bits are all zero — proved as `R2_HIGH_ZERO`)

#### Horner vs schoolbook: same result, different algorithms

| | NIST Algorithm 1 (Horner) | ghash_reduce(word_pmul) (Schoolbook) |
|---|---|---|
| How it works | One bit at a time, reduce every step | Full multiply, then reduce |
| Intermediate size | Always 128 bits | Up to 256 bits |
| When reduction happens | At every step (V-step XOR with R) | Once at the end (ghash_reduce) |
| Speed | 128 sequential steps | One wide multiply + 2 reduction passes |
| Hardware needed | Just shift + XOR | Wide carry-less multiplier (PMULL) |

Both compute the same result because reduction can happen at any point:
`(a mod P) + (b mod P) = (a + b) mod P` in any ring. Horner reduces
at every step; schoolbook accumulates everything then reduces once.

**Where it lives:** `ghash.ml` (John Harrison's library, pre-existing).
We did not write these definitions — we proved they equal the NIST spec.

### 1.8 Design principles for the NIST specification

1. **Faithful transcription**: Every definition mirrors the NIST standard
   exactly. I did not optimize, simplify, or reorder anything. The per-byte
   bit reversal is handled in the definitions themselves, not abstracted away.

2. **Separation of spec and proof**: The NIST definitions (lines 1-99) are
   pure specification with no proof content. The proof that this matches
   polynomial algebra is in the separate NIST_GHASH_EQ_GHASH_REDUCE theorem and its lemmas.

3. **HOL Light idioms**: I used `new_definition` for non-recursive
   functions and `define` for recursive ones, following standard HOL Light
   practice.

---

## 2. Equivalence A: NIST to Polynomial Algebra

### 2.1 What we need to prove

The goal is:

```
NIST_GHASH_EQ_GHASH_REDUCE:
  forall x y : int128.
    bit_reverse_per_byte(nist_ghash_mul x y) =
    ghash_reduce(word_pmul (bit_reverse_per_byte x) (bit_reverse_per_byte y))
```

In words: if you take the NIST multiplication result, apply per-byte bit
reversal (converting from NIST bit order to polynomial bit order), you
get the same result as: converting both inputs to polynomial order,
multiplying them as polynomials (`word_pmul`), and reducing modulo P(x)
(`ghash_reduce`).

`ghash_reduce` and `word_pmul` are from John Harrison's `ghash.ml`
library, which provides the GF(2^128) polynomial arithmetic foundation.

### 2.2 Proof structure: three stages

The proof decomposes into three stages:

```
brp(nist_ghash_mul x y)
  = poly_mul_loop 0 (brp y) (brp x) 128           [Stage 1: NIST_LOOP_AS_POLY_LOOP]
  = ghash_reduce(word_pmul (brp x) (brp y))        [Stage 2: POLY_LOOP_EQ_GHASH_REDUCE]
```

#### Stage 1: Pull brp through the NIST loop (NIST_LOOP_AS_POLY_LOOP)

```
NIST_LOOP_AS_POLY_LOOP:
  brp(ghash_mul_loop z v x n) = poly_mul_loop (brp z) (brp v) (brp x) n
```

where `brp` = `bit_reverse_per_byte` and `poly_mul_loop` is a
"natural order" version of the loop that shifts LEFT and XORs with 0x87
(instead of shifting right and XORing with 0xE1).

The two loops side by side:

```
NIST loop (ghash_mul_loop):              Natural loop (poly_mul_loop):
  Z' = if nist_bit x i                    Z' = if bit i x
       then xor z v else z                     then xor z v else z
  V' = if nist_lsb v                      V' = if bit 127 v
       then xor(nist_shr1 v)(0xE1)             then xor(word_shl v 1)(0x87)
       else nist_shr1 v                         else word_shl v 1
```

Every operation in the NIST loop has a natural-order equivalent. The
per-byte bit reversal `brp` converts between them.

**Proof technique:** Induction on the loop counter n. At each step,
we show brp commutes with every operation using four key lemmas:

| Lemma | Statement | Proof |
|-------|-----------|-------|
| `NIST_BIT_AS_NATURAL` | `nist_bit x i = bit i (brp x)` | Arithmetic on the bit-index formula |
| `NIST_SHR1_AS_SHL` | `brp(nist_shr1 v) = word_shl(brp v) 1` | `WORD_BLAST` (128-bit BDD) |
| `BYTE_BITREV_XOR` | `brp(word_xor a b) = word_xor(brp a)(brp b)` | `WORD_BLAST` |
| `BYTE_BITREV_GHASH_R` | `brp(word 0xE1) = word 0x87` | `WORD_REDUCE_CONV` (concrete computation) |

The most important is `NIST_BIT_AS_NATURAL`: NIST bit i of x equals
natural bit i of brp(x). This is the fundamental property of per-byte
bit reversal — it makes the bit numbering match up index-for-index, so
the loop scan reads the same values in the same order on both sides.

The induction step works as follows:

```
brp(ghash_mul_loop z v x (SUC n))
= brp(ghash_mul_loop z' v' x n)                    [expand NIST loop]
= poly_mul_loop (brp z') (brp v') (brp x) n        [induction hypothesis]
= poly_mul_loop (brp z)' (brp v)' (brp x) n        [push brp through z',v']
= poly_mul_loop (brp z) (brp v) (brp x) (SUC n)    [fold natural loop]
```

The third step uses all four commutation lemmas to transform brp(z')
and brp(v') into the natural-loop updates of (brp z) and (brp v).

**Result of Stage 1:**

```
NIST_GHASH_MUL_BYTREV_EQ_POLY_LOOP:
  brp(nist_ghash_mul x y) = poly_mul_loop (word 0) (brp y) (brp x) 128
```

#### Stage 2: Natural-order loop = ghash_reduce(word_pmul) (POLY_LOOP_EQ_GHASH_REDUCE)

```
POLY_LOOP_EQ_GHASH_REDUCE:
  poly_mul_loop (word 0) y x 128 = ghash_reduce(word_pmul x y)
```

Both sides are 128-bit words computing `poly(x) * poly(y) mod P(x)`,
but in completely different ways: the LHS is a 128-step sequential loop,
the RHS is a full 256-bit multiply followed by two reduction passes.

**Proof strategy: uniqueness.** Instead of showing identical intermediate
values (impossible since the algorithms work so differently), we show:

1. The loop output is congruent to `poly(x) * poly(y)` modulo P(x)
2. `ghash_reduce(word_pmul x y)` is congruent to `poly(x) * poly(y)` modulo P(x)
3. Both are 128-bit words
4. By `CONG_MOD_GHASH_IMP_WORD_EQ`: two 128-bit words congruent mod P(x) are equal

Step 2 follows directly from Harrison's library (`POLY_EQUIV_GHASH_REDUCE`
+ `POLY_OF_WORD_PMUL_2N`).

Step 4 works because P(x) is irreducible of degree 128: each equivalence
class mod P(x) contains exactly one polynomial of degree < 128. Two
128-bit words represent polynomials of degree ≤ 127, so if they're in
the same class, they must be identical.

Step 1 is the hard part, requiring three sub-lemmas:

##### POLY_SHL_XOR_CONG_MOD_GHASH: the shift-and-reduce step preserves congruence

```
POLY_SHL_XOR_CONG_MOD_GHASH:
  poly(V_update(v)) ≡ x * poly(v)  (mod P)
```

The V-update (shift left by 1, conditionally XOR with 0x87) is congruent
to multiplication by x modulo P(x).

**Case 1: bit 127 of v = 0 (no overflow).**

If the MSB is 0, then poly(v) has degree ≤ 126, so x * poly(v) has
degree ≤ 127, which fits in 128 bits. Therefore `word_shl v 1` represents
`x * poly(v)` exactly — no modular reduction needed. The proof uses the
degree bound to show HOL Light's 128-bit word_shl doesn't truncate anything.

**Case 2: bit 127 of v = 1 (overflow).**

The MSB is 1, so poly(v) has degree 127 and x * poly(v) has degree 128,
which overflows 128 bits. HOL Light's `word_shl v 1` drops the x^128
term (truncated to 128 bits). The XOR with 0x87 adds back
`x^7 + x^2 + x + 1`.

So V_update represents:

```
x * poly(v) - x^128 + (x^7 + x^2 + x + 1)
= x * poly(v) - P(x)                          [since P = x^128 + x^7+x^2+x+1]
≡ x * poly(v)  (mod P)                        [subtracting P doesn't change residue]
```

The formal proof provides the quotient witness `ring_1 bool_poly` (we
subtracted exactly one copy of P).

##### POLY_LOOP_HORNER_CONG_MOD_GHASH: inductive congruence for the whole loop

```
POLY_LOOP_HORNER_CONG_MOD_GHASH:
  poly(poly_mul_loop z v x n) ≡ poly(z) + partial_poly(x,n) * poly(v)  (mod P)
```

where `partial_poly x n` is the Horner evaluation of the first n bits:
`b_{n-1} * x^{n-1} + b_{n-2} * x^{n-2} + ... + b_0`.

**Proof by induction on n:**

*Base case (n=0):* `poly_mul_loop z v x 0 = z` and `partial_poly x 0 = 0`.
So `poly(z) ≡ poly(z) + 0 * poly(v)`. Trivial.

*Inductive step (n → n+1):* The loop does one iteration:
1. Z' = if bit_n(x) then z XOR v else z (accumulate)
2. V' = V_update(v) (shift and reduce)
3. Result = poly_mul_loop z' v' x n (continue for n more steps)

By induction hypothesis applied to the remaining n steps:

```
poly(result) ≡ poly(z') + partial_poly(x,n) * poly(v')  (mod P)
```

We need to show this equals `poly(z) + partial_poly(x,n+1) * poly(v)`.

Using POLY_SHL_XOR_CONG_MOD_GHASH: `poly(v') ≡ x * poly(v) (mod P)`.

Using the Horner recurrence: `partial_poly(x,n+1) = partial_poly(x,n) * x + bit_n(x)`.

Substituting and applying ring algebra (distributivity, commutativity,
the mod_ghash congruence rules) transforms the IH into the target.

##### PARTIAL_POLY_128: Horner evaluation = poly_of_word

```
PARTIAL_POLY_128:
  partial_poly x 128 = poly_of_word x
```

After processing all 128 bits, the Horner partial polynomial equals the
polynomial represented by the 128-bit word x.

**Proof approach:**

1. Define a word-level Horner construction `word_horner x n` that builds
   up a 128-bit word bit by bit

2. Prove `WORD_HORNER_BIT`: the bit characterization
   `bit k (word_horner x n) ⟺ k < n ∧ bit(128-n+k) x`

3. Prove `WORD_HORNER_128`: `word_horner x 128 = x` (from the bit
   characterization with n=128)

4. Prove `PARTIAL_POLY_AS_WORD_HORNER`:
   `partial_poly x n = poly_of_word(word_horner x n)` by induction,
   using `WORD_HORNER_BIT127_F` (no overflow since the Horner intermediate
   always has bit 127 = F for n ≤ 127)

5. Compose: `partial_poly x 128 = poly_of_word(word_horner x 128) = poly_of_word x`

##### Putting Stage 2 together

1. From POLY_LOOP_HORNER_CONG_MOD_GHASH with n=128, z=0, and PARTIAL_POLY_128:
   `poly(poly_mul_loop 0 y x 128) ≡ poly(x) * poly(y) (mod P)`

2. From POLY_EQUIV_GHASH_REDUCE + POLY_OF_WORD_PMUL_2N:
   `poly(ghash_reduce(word_pmul x y)) ≡ poly(x) * poly(y) (mod P)`

3. Both are congruent to the same thing, both are 128-bit words.

4. By CONG_MOD_GHASH_IMP_WORD_EQ: `poly_mul_loop 0 y x 128 = ghash_reduce(word_pmul x y)`.

#### Stage 3: Composition (NIST_GHASH_EQ_GHASH_REDUCE)

```
brp(nist_ghash_mul x y)
  = poly_mul_loop 0 (brp y) (brp x) 128           [Stage 1]
  = ghash_reduce(word_pmul (brp x) (brp y))        [Stage 2]
```

Two rewrites. Done.

### 2.3 Key insight

The proof separates two concerns:

1. **Bit ordering** (Stage 1): The per-byte bit reversal `brp` is a
   homomorphism — it commutes with XOR, converts NIST shifts to polynomial
   shifts, and converts the NIST reduction constant to the polynomial one.
   This is proved at the word level using `WORD_BLAST`.

2. **Algorithm equivalence** (Stage 2): Horner evaluation with online
   reduction computes the same result as schoolbook multiplication with
   final reduction. This is proved at the polynomial algebra level using
   modular congruence + uniqueness (`CONG_MOD_GHASH_IMP_WORD_EQ`).

---

## 3. Equivalence B: P(x) to Q(x) Ideal Mapping

### 3.1 The problem

GHASH works with the polynomial P(x) = x^128 + x^7 + x^2 + x + 1,
but the ARM assembly implements POLYVAL, which works with the "reflected"
polynomial Q(x) = x^128 + x^127 + x^126 + x^121 + 1.

These are related by Q(x) = x^128 * P(1/x): reversing the coefficients
of P gives Q. The assembly uses Q because ARM's PMULL instruction
computes carry-less multiplication in the natural bit order, and the
POLYVAL convention avoids needing per-byte bit reversal at runtime.

We need to prove that reducing modulo P (via `ghash_reduce`) and
reducing modulo Q (via `polyval_reduce_prop3`) give results related
by bit-reversal.

### 3.2 What we proved

```
GHASH_POLYVAL_BRIDGE_CORE:
  forall a b : int128.
    (poly(bitrev(ghash_reduce(pmul a b))) * x^127 ==
     poly(bitrev a) * poly(bitrev b))  (mod Q)

GHASH_POLYVAL_BRIDGE_RHS:
  forall a b : int128.
    (poly(bitrev a) * poly(bitrev b) ==
     poly(ghash_twist(polyval_dot(bitrev a, bitrev b))) * x^127)  (mod Q)

GHASH_POLYVAL_BRIDGE:
  forall a b : int128.
    bitrev(ghash_reduce(pmul a b)) =
    ghash_twist(polyval_dot(bitrev a, bitrev b))
```

### 3.3 The mathematical idea

Given `c = ghash_reduce(pmul a b)`, we know `poly(c) ≡ poly(a)*poly(b) (mod P)`.

The key insight: the polynomial coefficient reversal map `poly_revn 254`
sends elements of ideal{P} to elements of ideal{Q}. Specifically:

```
poly_revn 254(k * P) = (poly_revn 126 k) * Q
```

for any polynomial k with degree ≤ 126.

This identity follows from the decomposition P = x^128 + poly(0x87):
- `poly_revn 254(k * x^128) = poly_revn 126(k)` (shift reversal)
- `poly_revn 254(k * poly(0x87)) = poly(bitrev k) * poly(bitrev 0x87)` (product reversal)
- These reassemble as `poly_revn 126(k) * (1 + x * poly(bitrev 0x87)) = poly_revn 126(k) * Q`

### 3.4 The proof infrastructure

This was the hardest part of the entire verification. The main lemma is
`POLY_REVN_MUL_GHASH`, and building up to it required ~20 supporting lemmas:

- **GHASH_POLY_EQ_X128_PLUS_POLY87**: Decompose P(x) = x^128 + poly(word 0x87).
  Proved by coefficient-level analysis using GHASH_POLY_COEFF_AT_0_1_2_7_128.

- **MUL_U128_WORD**: `poly(w) * x^128 = poly(shl(zx w : 256) 128)`.
  Connects polynomial multiplication by x^128 to a 256-bit word shift.
  Proved using bit-level proof via BIT_WORD_PMUL_ALT with SET_EQ_LEMMA
  for the singleton set characterization.

- **POLY_REVN254_OF_SHL128_EQ_REVN126**: `poly_revn 254(poly(shl(zx w) 128)) = poly_revn 126(poly w)`.
  Reversing a shifted polynomial removes the shift. Proved at the
  coefficient level via the poly_revn definition.

- **POLY_VAR_MUL_REVN126_EQ_BITREV**: `~bit 127 w ==> x * poly(ushr(bitrev w) 1) = poly(bitrev w)`.
  Multiplying by x undoes the right-shift from poly_revn 126.
  Proved using POLY_OF_WORD_PMUL_2N + NSUM_DELTA.

- **PMUL_135_BIT_NORMALIZE**: `bit k (word_pmul hi (word 135:256 word):256 word) <=>
  bit k (word_pmul hi (word 135:int128):256 word)`.
  Type normalization lemma for word_pmul with argument 135. HOL Light's
  `GSYM POLY_OF_WORD_PMUL_2N` can create word_pmul at wider types; this
  lemma normalizes the bit-level behavior. Proved as a trivial identity
  since both sides have identical bit semantics.

- **PMUL_2EXP127_BIT_NORMALIZE**: `bit k (word_pmul(zx w)(word(2^127)):512 word) <=>
  bit k (shl(zx w) 127:256 word)`. Type normalization for multiplication
  by 2^127 (= x^127). The 512-bit word_pmul result has the same bits as
  a 256-bit shift. Proved by expanding BIT_WORD_PMUL_ALT, characterizing
  `bit j (word(2^127))` as `j = 127` via DIV_EXP, then case-splitting
  on k ranges with set equality proofs using IN_SING.

- **REDUCE1_QUOTIENT**: `poly(x) + poly(reduce1(x)) = poly(hi) * P`
  where `hi = word_subword(x)(128,128)`. Gives the explicit quotient
  for one pass of Barrett reduction. Uses GHASH_POLY_EQ_X128_PLUS_LOW,
  MUL_U128_WORD, and PMUL_135_BIT_NORMALIZE for the word_pmul type
  normalization, with char-2 cancellation (a + a = 0).

- **REDUCE_SUM_EQ_QUOTIENT_MUL**: `poly(pmul a b) + poly(ghash_reduce(pmul a b)) =
  poly(quotient_xor) * ghash_poly`. Combines two applications of
  REDUCE1_QUOTIENT with INST_TYPE for handling type variables from
  POLY_GHASH_REDUCE_EQ_R2.

- **R2_HIGH_ZERO**: After two passes of reduce1, the upper 128 bits
  are zero. Uses GHASH_REDUCE1_HI (which gives a formula for the high
  bits) applied twice, combined with USHR121_SMALL, USHR126_SMALL,
  USHR127_SMALL (by WORD_BLAST) to show the cascading shifts clear
  all bits.

- **QUOTIENT_BIT127**: The explicit quotient word w = xor(hi1, hi2)
  satisfies ~bit 127 w, i.e., has degree ≤ 126. Follows from
  BIT255_PMUL_128 (bit 255 of pmul is F) and BIT255_REDUCE1_PMUL
  (bit 255 of reduce1(pmul) is F).

- **POLY_OF_WORD_SHL_ZX_127**: `poly(shl(zx w) 127) = poly(w) * x^127`.
  Uses POLY_VAR_POW_OF_WORD + PMUL_2EXP127_BIT_NORMALIZE to bridge
  the type mismatch between the 512-bit word_pmul and 256-bit shift.

- **POLY_REVN_254_AS_MUL**: `poly_revn 254(poly w) = poly(bitrev w) * x^127`.
  Composition of POLY_REVN_254_WORD128 + POLY_OF_WORD_SHL_ZX_127.
  Central to GHASH_POLYVAL_BRIDGE_CORE's ideal membership proof.

### 3.5 Assembly of the final proof

**GHASH_POLYVAL_BRIDGE_CORE** proof:

1. REDUCE_SUM_EQ_QUOTIENT_MUL gives (after swapping ring_add args via RING_ADD_SYM):
   `ring_add(poly(pmul a b))(poly(ghash_reduce(pmul a b))) = ring_mul(poly(quotient_xor))(ghash_poly)`

2. Apply poly_revn 254 via POLY_REVN_MUL_GHASH (using QUOTIENT_BIT127 for the degree bound):
   `poly_revn 254(ring_add ...) = ring_mul(poly_revn 126(quotient_xor))(polyval_poly)`

3. Expand cong/mod_polyval to ideal membership. Need:
   `ring_add(poly(bitrev(ghash_reduce))*x^127)(poly(bitrev a)*poly(bitrev b)) ∈ ideal{polyval_poly}`

4. Establish `poly_revn 254(poly(pmul a b)) = poly(bitrev a)*poly(bitrev b)` via
   POLY_REVN_254_PMUL + POLY_OF_WORD_PMUL_2N (handles the word_pmul type widening).

5. Rewrite the goal using GSYM of step 4 and POLY_REVN_254_AS_MUL to match
   the hypothesis from step 1-2. Show the result is `Q_quotient * polyval_poly`
   which is in ideal{polyval_poly} via ring_divides + RING_MUL_SYM.

**GHASH_POLYVAL_BRIDGE_RHS** proof:

1. From GHASH_TWIST_CORRECT: `poly(ghash_twist h) ≡ x * poly(h) (mod Q)`
2. Multiply both sides by x^127 via MOD_POLYVAL_MUL:
   `poly(ghash_twist(polyval_dot ...)) * x^127 ≡ poly(polyval_dot ...) * x^128 (mod Q)`
3. From POLYVAL_DOT_CORRECT: `poly(polyval_dot a b) * x^128 ≡ poly(a)*poly(b) (mod Q)`
4. Chain via MOD_POLYVAL_TRANS.

**GHASH_POLYVAL_BRIDGE** (the word-level equality):

1. GHASH_POLYVAL_BRIDGE_CORE: `bitrev(ghash_reduce) * x^127 ≡ bitrev(a)*bitrev(b) (mod Q)`
2. GHASH_POLYVAL_BRIDGE_RHS: `bitrev(a)*bitrev(b) ≡ ghash_twist(polyval_dot) * x^127 (mod Q)`
3. MOD_POLYVAL_TRANS: `bitrev(ghash_reduce) * x^127 ≡ ghash_twist(polyval_dot) * x^127 (mod Q)`
4. MOD_POLYVAL_CANCEL_VARPOW (n=127): cancel x^127, giving the word equality.

---

## 4. Equivalence C: polyval_dot to gcm_gmult_spec

### 4.1 What gcm_gmult_spec is

`gcm_gmult_spec` is an **instruction-level specification** that mirrors
exactly what the 27 ARM NEON instructions compute. It implements:
1. Byte-swap the input (REV64)
2. Karatsuba carry-less multiplication using 3 PMULL/PMULL2 instructions
3. Two-phase Barrett reduction modulo Q(x) using shifts and XORs
4. Byte-swap the output (REV64)

**File:** `arm/proofs/utils/gcm_gmult_v8_spec.ml`

### 4.2 What polyval_dot is

`polyval_dot a b` (from nebeid's `ghash_spec.ml`) computes:
1. Full carry-less multiplication: `word_pmul a b`
2. Prop 3 reduction: `polyval_reduce_prop3(word_pmul a b)`

It satisfies: `poly(polyval_dot a b) * x^128 ≡ poly(a) * poly(b) (mod Q)`

### 4.3 The proof (GCM_GMULT_SPEC_EQ_POLYVAL_DOT)

We need to show:

```
gcm_gmult_spec xi h (word_zx(karatsuba_mid H)) =
word_reversefields 8 (polyval_dot (word_reversefields 8 xi) H)
```

Both sides compute the same 256-bit product and reduce it mod Q, but
using different code paths:
- `gcm_gmult_spec` uses the Karatsuba recombination from the assembly
  instructions (EXT, EOR patterns) and a two-phase Barrett reduction
- `polyval_dot` uses direct Karatsuba (PMUL_KARATSUBA) and Gueron's
  Proposition 3 reduction

**Proof decomposition** (WORD_BLAST at 256 bits was infeasible):

1. **KARATSUBA_LIMBS** (4 lemmas, WORD_BLAST): Extract the four 64-bit
   limbs of the 256-bit Karatsuba product. Each is a 64-bit WORD_BLAST
   (128 BDD variables).

2. **KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS** (WORD_BLAST): Show the spec's Karatsuba
   recombination produces the same limbs B, C as Prop 3.

3. **BARRETT_REDUCTION_EQ_PROP3_REDUCTION** (WORD_BLAST on 4 × 64 = 256 vars): Show the
   spec's two-phase Barrett reduction equals Prop 3's reduction on
   the same four limbs. This was the largest single WORD_BLAST, barely
   fitting in the BDD capacity.

4. **Composition**: Wire everything together with abbreviations and
   rewrites.

---

## 5. Equivalence D: gcm_gmult_spec to ARM Assembly

### 5.1 The assembly

`gcm_gmult_v8` is 27 ARM NEON instructions implementing GCM-GHASH
multiplication. It uses:
- `REV64` for byte swapping
- `PMULL`/`PMULL2` for carry-less multiplication (Karatsuba with 3 multiplies)
- `EXT`, `EOR` for Karatsuba recombination
- Shift + XOR sequences for two-phase Barrett reduction

### 5.2 The proof (GCM_GMULT_V8_EXEC_CORRECT)

The ARM simulation proof steps through all 27 instructions using
`MAP_EVERY` with a custom `GCM_SIMD_SIMPLIFY_TAC` at each step.

The main challenge was **REV64 term explosion**: the `word_reversefields`
operation on 128-bit SIMD registers creates ~40KB terms that bog down
subsequent symbolic execution. Three SIMD simplification rules were
developed to handle this:

1. Lower 64-bit lane of REV64
2. Upper 64-bit lane of REV64
3. Full 128-bit REV64 round-trip

These rules eagerly simplify the REV64 output before the next
instruction is symbolically executed, keeping term sizes manageable.

### 5.3 Subroutine wrapper

`GCM_GMULT_V8_SUBROUTINE_CORRECT` wraps the execution correctness
for the ARM subroutine calling convention (X30 return address, etc.).

---

## Summary: The Complete Chain

```
NIST Algorithm 1 (gcm_gmult_v8_nist.ml, lines 1-99)
   |
   | bit_reverse_per_byte commutes with all NIST operations
   | (NIST_LOOP_AS_POLY_LOOP, NIST_V_UPDATE_AS_POLY_SHL, NIST_Z_UPDATE_AS_POLY_XOR — by induction + WORD_BLAST)
   |
   | shift-and-XOR loop = ghash_reduce(word_pmul)
   | (POLY_LOOP_EQ_GHASH_REDUCE — by CONG_MOD_GHASH_IMP_WORD_EQ uniqueness)
   |
   v
ghash_reduce(word_pmul(brp x, brp y))                    [NIST_GHASH_EQ_GHASH_REDUCE]
   |
   | poly_revn 254 maps ideal{P} → ideal{Q}
   | (POLY_REVN_MUL_GHASH — the ideal mapping lemma)
   |
   | explicit quotient from 2× REDUCE1_QUOTIENT
   | + degree bound from R2_HIGH_ZERO + QUOTIENT_BIT127
   |
   v
ghash_twist(polyval_dot(bitrev a, bitrev b))              [GHASH_POLYVAL_BRIDGE]
   |
   | Karatsuba limb extraction (KARATSUBA_LIMBS — WORD_BLAST)
   | Reduction equivalence (BARRETT_REDUCTION_EQ_PROP3_REDUCTION — WORD_BLAST 256 vars)
   |
   v
gcm_gmult_spec                                            [GCM_GMULT_SPEC_EQ_POLYVAL_DOT]
   |
   | 27-step ARM simulation (MAP_EVERY + GCM_SIMD_SIMPLIFY_TAC)
   |
   v
gcm_gmult_v8 assembly (27 NEON instructions)              [GCM_GMULT_V8_EXEC_CORRECT]
```

**Zero CHEAT_TAC. Complete end-to-end formal verification.**

---

## Attribution: Who Did What

### John Harrison (AWS) — GF(2)[x] foundation

John Harrison built the mathematical foundation that everything rests on.
His `ghash.ml` library provides:

| What | Description |
|------|-------------|
| `bool_poly` | The polynomial ring GF(2)[x] formalized in HOL Light |
| `poly_of_word` | Converts a machine word to a polynomial (bit i = coefficient of x^i) |
| `ghash_poly` | P(x) = x^128 + x^7 + x^2 + x + 1, the GHASH irreducible polynomial |
| `ghash_reduce`, `ghash_reduce1` | Barrett reduction modulo P(x) |
| `word_pmul` | Carry-less (polynomial) multiplication on machine words |
| `mod_ghash` | Congruence relation modulo P(x) |
| `POLY_EQUIV_GHASH_REDUCE` | `ghash_reduce` output is congruent to its input mod P(x) |
| `CONG_MOD_GHASH_IMP_WORD_EQ` | Two 128-bit words congruent mod P(x) are equal |
| `POLY_OF_WORD_PMUL_2N` | `poly(word_pmul a b) = poly(a) * poly(b)` |
| `POLY_OF_WORD_XOR` | `poly(xor a b) = poly(a) + poly(b)` |
| Irreducibility of P(x) | Used in `CONG_MOD_GHASH_IMP_WORD_EQ` uniqueness argument |

We used these as a **black box** — we never modified `ghash.ml`, only
imported and applied its theorems.

### Nevine Ebeid (nebeid) — POLYVAL infrastructure and algebraic specs

Nevine built the POLYVAL side and the algebraic specification that
connects GHASH to POLYVAL:

| What | Description |
|------|-------------|
| `polyval_poly` | Q(x) = x^128 + x^127 + x^126 + x^121 + 1 |
| `polyval_reduce_prop3` | Gueron's Proposition 3 reduction modulo Q(x) |
| `mod_polyval` | Congruence relation modulo Q(x) |
| `polyval_dot` | POLYVAL dot product: `pmul` then `polyval_reduce_prop3` |
| `ghash_twist` | Multiplication by x modulo Q(x) |
| `POLYVAL_DOT_CORRECT` | `poly(polyval_dot a b) * x^128 ≡ poly(a) * poly(b) (mod Q)` |
| `GHASH_TWIST_CORRECT` | `poly(ghash_twist h) ≡ x * poly(h) (mod Q)` |
| `POLYVAL_REDUCE_PROP3_CORRECT` | Prop 3 reduction is correct mod Q(x) |
| `PMUL_KARATSUBA` | 3-multiply Karatsuba decomposition of `word_pmul` |
| `MOD_POLYVAL_CANCEL_VARPOW` | Two 128-bit words congruent mod Q(x) are equal |
| `MOD_POLYVAL_CANCEL_VARPOW` | Can cancel x^n from both sides of a mod Q congruence |
| `GHASH_REDUCE1_HI` | Formula for high bits after one reduction pass |
| `ghash_polyval_acc`, `h_power`, `htable` | Batched GHASH specification |

These provide the **target** that the assembly implements. Nevine's work
establishes that `polyval_dot` and `ghash_twist` correctly implement
field arithmetic modulo Q(x), and that Karatsuba decomposition is valid.

### Our work (manastasova) — The complete verification chain

We built everything needed to connect the NIST standard to Nevine's
algebraic specifications, and from those specifications to the ARM assembly:

**Equivalence A: NIST ↔ polynomial algebra** (~52 theorems)

| What | Description |
|------|-------------|
| `nist_bit`, `nist_lsb`, `nist_shr1`, `ghash_R` | NIST bit-level operations |
| `ghash_mul_loop`, `nist_ghash_mul`, `nist_ghash` | NIST Algorithms 1 and 2 |
| `poly_mul_loop`, `partial_poly`, `word_horner` | Natural-order loop + Horner evaluation |
| `NIST_LOOP_AS_POLY_LOOP` | Per-byte bit reversal commutes with the NIST loop |
| `POLY_SHL_XOR_CONG_MOD_GHASH` | Shift-and-reduce step preserves congruence mod P(x) |
| `POLY_LOOP_HORNER_CONG_MOD_GHASH` | Inductive loop congruence |
| `PARTIAL_POLY_128` | Horner evaluation = poly_of_word |
| `POLY_LOOP_EQ_GHASH_REDUCE` | Horner loop = ghash_reduce(word_pmul) |
| **`NIST_GHASH_EQ_GHASH_REDUCE`** | **NIST Algorithm 1 = ghash_reduce(word_pmul(brp x, brp y))** |

**Equivalence B: P(x) ↔ Q(x) ideal mapping** (~30 theorems)

| What | Description |
|------|-------------|
| `GHASH_POLY_EQ_X128_PLUS_POLY87` | P(x) = x^128 + poly(0x87) |
| `MUL_U128_WORD` | poly(w) * x^128 as a word operation |
| `POLY_REVN126_EQ_USHR_BITREV`, `POLY_REVN254_OF_SHL128_EQ_REVN126` | Coefficient reversal identities |
| `POLY_VAR_MUL_REVN126_EQ_BITREV` | x * poly_revn_126(k) = poly(bitrev k) |
| `PMUL_135_BIT_NORMALIZE` | word_pmul type normalization for ×135 |
| `PMUL_2EXP127_BIT_NORMALIZE` | word_pmul type normalization for ×2^127 |
| `REDUCE1_QUOTIENT` | Explicit quotient from Barrett reduction |
| `REDUCE_SUM_EQ_QUOTIENT_MUL` | Two-pass quotient for ghash_reduce |
| `R2_HIGH_ZERO` | Two reduction passes clear all high bits |
| `QUOTIENT_BIT127` | Quotient has degree ≤ 126 |
| `POLY_OF_WORD_SHL_ZX_127` | poly(shl(zx w) 127) = poly(w) * x^127 |
| `POLY_REVN_254_AS_MUL` | poly_revn 254(poly w) = poly(bitrev w) * x^127 |
| **`POLY_REVN_MUL_GHASH`** | **poly_revn 254(k*P) = poly_revn_126(k) * Q** |
| **`GHASH_POLYVAL_BRIDGE_CORE`** | **bitrev(c) * x^127 ≡ bitrev(a) * bitrev(b) (mod Q)** |
| **`GHASH_POLYVAL_BRIDGE_RHS`** | **bitrev(a) * bitrev(b) ≡ ghash_twist(polyval_dot) * x^127 (mod Q)** |
| **`GHASH_POLYVAL_BRIDGE`** | **bitrev(ghash_reduce(pmul a b)) = ghash_twist(polyval_dot(bitrev a, bitrev b))** |

**Equivalence C: polyval_dot ↔ gcm_gmult_spec** (~10 theorems)

| What | Description |
|------|-------------|
| `gcm_gmult_spec` | Instruction-level specification of the ARM code |
| `KARATSUBA_LIMB_0_63/64_127/128_191/192_255` | 64-bit limb extraction from Karatsuba product |
| `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS` | Spec's Karatsuba recombination = Prop 3's limbs |
| `BARRETT_REDUCTION_EQ_PROP3_REDUCTION` | Spec's Barrett reduction = Prop 3's reduction |
| **`GCM_GMULT_SPEC_EQ_POLYVAL_DOT`** | **gcm_gmult_spec = rev8(polyval_dot(rev8 xi, H))** |

**Equivalence D: gcm_gmult_spec ↔ ARM assembly** (~5 theorems)

| What | Description |
|------|-------------|
| SIMD simplification rules (3) | Handle REV64 term explosion |
| **`GCM_GMULT_V8_EXEC_CORRECT`** | **27-step ARM simulation proof** |
| **`GCM_GMULT_V8_SUBROUTINE_CORRECT`** | **Subroutine calling convention wrapper** |

### Summary

| Author | Contribution | Theorems |
|--------|-------------|----------|
| John Harrison | GF(2)[x] polynomial ring foundation | ~15 key theorems in `ghash.ml` |
| Nevine Ebeid | POLYVAL, Prop 3, Karatsuba, algebraic specs | ~15 key theorems across 4 files |
| manastasova | NIST spec + all 4 equivalence proofs + assembly proof | ~130 theorems/definitions across 3 files |

The division: Harrison provided the **mathematical foundation**, Nevine
provided the **algebraic target specifications**, and we built the
**complete verification chain** from the NIST standard through all
intermediate layers down to the ARM assembly — with zero CHEAT_TAC.
