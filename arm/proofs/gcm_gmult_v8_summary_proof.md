# GCM GMULT V8: Full Proof Chain from NIST Spec to ARM Implementation

## Overview

This document describes the complete formal verification chain connecting
the NIST SP 800-38D GHASH multiplication specification to the ARM NEON
`gcm_gmult_v8` assembly implementation. Every layer is connected by a
formally proved HOL Light theorem, with **zero CHEAT_TAC** remaining.

The chain has five layers connected by four equivalence proofs:

```
NIST SP 800-38D Algorithm 1             (bit-level shift-and-XOR loop)
        |
        |  NIST Horner loop = schoolbook multiply + reduce mod P(x)
        |  (NIST_GHASH_EQ_GHASH_REDUCE)                        [this work]
        v
Polynomial algebra mod P(x)             (poly_of_word, ghash_reduce, word_pmul)
        |
        |  GHASH reduction (mod P) = POLYVAL reduction (mod Q) under bit-reversal
        |  (GHASH_REDUCE_BITREV_EQ_POLYVAL_DOT                 [this work]
        |   + POLYVAL_DOT_CORRECT, GHASH_TWIST_CORRECT)        [pre-existing]
        v
polyval_dot / polyval_reduce_prop3      (Gueron's Prop 3 reduction mod Q(x))
        |
        |  Assembly instruction-level spec = POLYVAL algebraic spec
        |  (GCM_GMULT_SPEC_EQ_POLYVAL_DOT)                     [this work]
        v
gcm_gmult_spec                          (ARM instruction-level spec)
        |
        |  27-step ARM simulation: assembly = instruction-level spec
        |  (GCM_GMULT_V8_EXEC_CORRECT)                         [this work]
        v
gcm_gmult_v8 assembly                   (27 NEON instructions)
```

---

## Components

| Component | Status |
|-----------|--------|
| **GF(2)[x] foundation** (`ghash.ml`: bool_poly, poly_of_word, P(x), ghash_reduce, irreducibility) | Pre-existing |
| **POLYVAL infrastructure** (`polyval.ml`: Q(x), polyval_reduce_prop3) | Pre-existing |
| **Prop 3 correctness** (`polyval_prop3_proof.ml`: POLYVAL_REDUCE_PROP3_CORRECT) | Pre-existing |
| **Karatsuba decomposition** (`karatsuba_pmul_proof.ml`: PMUL_KARATSUBA) | Pre-existing |
| **GHASH algebraic spec** (`ghash_spec.ml`: polyval_dot, ghash_polyval_acc, htable, twist) | Pre-existing |
| **P(x) <-> Q(x) algebraic specifications** (POLYVAL_DOT_CORRECT, GHASH_TWIST_CORRECT) | Pre-existing |
| **GHASH-POLYVAL reflection equivalence** (GHASH_REDUCE_BITREV_CONG_MOD_POLYVAL (GHASH_POLYVAL_BRIDGE_CORE), GHASH_REDUCE_BITREV_EQ_POLYVAL_DOT (GHASH_POLYVAL_BRIDGE)) | This work |
| **gcm_gmult_spec = polyval_dot** (GCM_GMULT_SPEC_EQ_POLYVAL_DOT) | This work |
| **Implementation spec** (`gcm_gmult_v8_spec.ml`: gcm_gmult_spec, SIMD lemmas, test vectors) | This work |
| **ARM assembly = gcm_gmult_spec** (`gcm_gmult_v8.ml`: GCM_GMULT_V8_EXEC_CORRECT) | This work |
| **NIST Algorithm 1 transcription** (`gcm_gmult_v8_nist.ml`: nist_ghash_mul, nist_ghash) | This work |
| **NIST Algorithm 1 = polynomial algebra** (NIST_GHASH_EQ_GHASH_REDUCE + all supporting lemmas) | This work |

---

## Files and their roles

### Pre-existing

| File | Role |
|------|------|
| `common/ghash.ml` | GF(2)[x] polynomial ring, P(x) = x^128+x^7+x^2+x+1, `ghash_reduce`, `ghash_reduce1`, `mod_ghash`, `MOD_GHASH_REFL/SYM/TRANS/ADD/MUL`, `POLY_EQUIV_GHASH_REDUCE`, irreducibility |
| `common/polyval.ml` | Q(x) = x^128+x^127+x^126+x^121+1, `polyval_reduce_prop3`, `mod_polyval` |
| `common/polyval_prop3_proof.ml` | `POLYVAL_REDUCE_PROP3_CORRECT`: prop3 result * x^128 = input (mod Q) |
| `common/karatsuba_pmul_proof.ml` | `PMUL_KARATSUBA`: 3-PMULL Karatsuba = word_pmul |
| `common/ghash_spec.ml` | `polyval_dot`, `ghash_polyval_acc`, batched GHASH, htable predicates, twist, `POLYVAL_DOT_CORRECT`, `GHASH_TWIST_CORRECT` |

### This work

| File | Role |
|------|------|
| `arm/proofs/utils/gcm_gmult_v8_spec.ml` | `gcm_gmult_spec`: implementation-level spec mirroring ARM instructions (Karatsuba + 2-phase Barrett reduction + byte reversal) |
| `arm/proofs/gcm_gmult_v8.ml` | ARM simulation proof: 27-step `MAP_EVERY` with SIMD simplification. Loads `gcm_gmult_v8_nist.ml` to ensure the full chain is verified. |
| `arm/proofs/utils/gcm_gmult_v8_nist.ml` | NIST Algorithm 1 definitions + all mathematical equivalence proofs (NIST = polynomial algebra, GHASH-POLYVAL reflection, gcm_gmult_spec = polyval_dot) |

### How the proof chain is verified

The proofs are split across two files, each with a clear responsibility:

```
gcm_gmult_v8.ml proves:
    assembly = gcm_gmult_spec                           (ARM simulation)

gcm_gmult_v8_nist.ml proves:
    gcm_gmult_spec = polyval_dot                        (spec = algebraic spec)
    polyval_dot ↔ ghash_reduce  (via bit-reversal)      (GHASH-POLYVAL reflection)
    ghash_reduce(word_pmul) = nist_ghash_mul             (NIST = polynomial algebra)
```

Running `make generic/gcm_gmult_v8.correct` loads `gcm_gmult_v8.ml`,
which loads `gcm_gmult_v8_nist.ml` via `needs`. HOL Light checks
**every proof in both files**, verifying the complete chain from NIST
Algorithm 1 down to the ARM assembly. No single theorem needs to state
the entire end-to-end equivalence — each theorem connects adjacent
layers, and HOL Light verifies every link.

---

## ARM Assembly = gcm_gmult_spec (Equivalence D)

### GCM_GMULT_V8_EXEC_CORRECT

```
forall xi_ptr htable_ptr xi h hhl pc.
  nonoverlapping constraints ==>
  ensures arm
    (precondition: code at pc, inputs in memory)
    (postcondition: PC = pc+108, mem[xi_ptr] = gcm_gmult_spec xi h hhl)
    (frame: ABI-allowed changes)
```

Proved by simulating all 27 ARM NEON instructions using `MAP_EVERY`
with per-step `GCM_SIMD_SIMPLIFY_TAC` to manage REV64 byte-level
term expansion. Three SIMD simplification rules handle REV64 on
lower lane, upper lane, and full 128-bit register.

### GCM_GMULT_V8_SUBROUTINE_CORRECT

Wraps the execution correctness for the ARM subroutine calling convention
(X30 return address, callee-saved registers).

---

## gcm_gmult_spec = polyval_dot (Equivalence C: GCM_GMULT_SPEC_EQ_POLYVAL_DOT)

### Statement

```
forall xi h : int128.
  let H = byteswap128 h in
  gcm_gmult_spec xi h (word_zx(karatsuba_mid H)) =
  word_reversefields 8 (polyval_dot (word_reversefields 8 xi) H)
```

This says: the ARM implementation spec, given the accumulator `xi` and
hash table entry `h`, produces the same result as `polyval_dot` applied
in the natural polynomial byte order.

### Proof strategy

Direct WORD_BLAST on the full equation was infeasible (carry-less
multiplication creates exponential BDDs for 256+ Boolean variables).
The proof was decomposed into modular lemmas:

#### Step 1: KARATSUBA_LIMB_0_63 / 64_127 / 128_191 / 192_255 (4 lemmas, by WORD_BLAST)

Extract the four 64-bit limbs of the 256-bit Karatsuba product.

#### Step 2: KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS (by WORD_BLAST)

The spec's Karatsuba recombination `xm'` has halves equaling Prop 3's
limbs B and C.

#### Step 3: BARRETT_REDUCTION_EQ_PROP3_REDUCTION (by WORD_BLAST on 4 x 64 = 256 Boolean vars)

The spec's two-phase Barrett reduction and Prop 3's reduction produce
identical results on the same four 64-bit limbs.

#### Step 4: Composition

Expand both sides, abbreviate Karatsuba pmull results, align operand
orders, and close with BARRETT_REDUCTION_EQ_PROP3_REDUCTION.

---

## GHASH-POLYVAL Reflection Equivalence (Equivalence B)

This is the deepest mathematical result: it connects the two different
polynomial representations used in GHASH (mod P) and POLYVAL (mod Q),
proving that GHASH reduction and POLYVAL reduction are equivalent
under bit-reversal.

### Background

GHASH uses P(x) = x^128 + x^7 + x^2 + x + 1 (the NIST polynomial).
POLYVAL uses Q(x) = x^128 + x^127 + x^126 + x^121 + 1 (the "reflected" polynomial).

These are related by: Q(x) = x^128 * P(1/x), i.e., Q is the bit-reversal of P.
The bit-reversal map `poly_revn 254` sends ideal{P} to ideal{Q}, which is the
core of the equivalence proof.

### Top-level theorems

```
GHASH_REDUCE_BITREV_CONG_MOD_POLYVAL (GHASH_POLYVAL_BRIDGE_CORE):
  forall a b : int128.
    (poly(bitrev(ghash_reduce(pmul a b))) * x^127 ==
     poly(bitrev a) * poly(bitrev b))  (mod Q)

GHASH_REDUCE_BITREV_EQ_POLYVAL_DOT (GHASH_POLYVAL_BRIDGE):
  forall a b : int128.
    word_reversefields 1 (ghash_reduce(word_pmul a b)) =
    ghash_twist(polyval_dot (word_reversefields 1 a) (word_reversefields 1 b))
```

`GHASH_REDUCE_BITREV_CONG_MOD_POLYVAL (GHASH_POLYVAL_BRIDGE_CORE)` is the polynomial congruence: bit-reversing a
mod-P reduction result gives a mod-Q result (up to the x^127 twist factor).

`GHASH_REDUCE_BITREV_EQ_POLYVAL_DOT (GHASH_POLYVAL_BRIDGE)` is the word-level consequence: bit-reversing `ghash_reduce`
equals `ghash_twist(polyval_dot)`, connecting the two reduction algorithms.

### Proof structure

The proof of GHASH_REDUCE_BITREV_CONG_MOD_POLYVAL (GHASH_POLYVAL_BRIDGE_CORE) required building an extensive algebraic
infrastructure to show that `poly_revn 254` maps ideal{P} into ideal{Q}.

#### Key lemma: POLY_REVN_MUL_GHASH (the ideal mapping)

```
POLY_REVN_MUL_GHASH:
  ~bit 127 w ==>
  poly_revn 254 (ring_mul bool_poly (poly_of_word w) ghash_poly) =
  ring_mul bool_poly (poly_revn 126 (poly_of_word w)) polyval_poly
```

This says: for any quotient polynomial `k = poly(w)` with degree <= 126,
`poly_revn 254(k * P) = (poly_revn 126 k) * Q`. In other words, reversing the
coefficients maps elements of ideal{P} to elements of ideal{Q}.

**Proof of POLY_REVN_MUL_GHASH:**

1. Decompose P: `ghash_poly = x^128 + poly(0x87)` (GHASH_POLY_EQ_X128_PLUS_POLY87)
2. Distribute: `k * P = k * x^128 + k * poly(0x87)` (RING_ADD_LDISTRIB)
3. Shift reversal: `poly_revn 254(k * x^128) = poly_revn 126(k)` (POLY_REVN254_OF_SHL128_EQ_REVN126 + MUL_U128_WORD)
4. Product reversal: `poly_revn 254(k * poly(0x87)) = poly(bitrev w) * poly(bitrev 0x87)` (POLY_REVN_254_PMUL)
5. Factor: `total = poly_revn 126(k) * (1 + x * poly(bitrev 0x87)) = poly_revn 126(k) * Q` (Q_AS_ONE_PLUS_U_REV_LOW + POLY_VAR_MUL_REVN126_EQ_BITREV)

#### Explicit quotient from ghash_reduce

```
REDUCE1_QUOTIENT:
  poly(x) + poly(ghash_reduce1(x)) = poly(word_subword x (128,128)) * ghash_poly
```

This gives the explicit quotient for one pass of Barrett reduction: the upper
128 bits of the input. Two passes yield the full quotient for `ghash_reduce`.

```
R2_HIGH_ZERO:
  word_ushr(ghash_reduce1(ghash_reduce1(pmul a b)))(128) = word 0
```

After two passes, the result's upper bits are zero. This uses GHASH_REDUCE1_HI
twice with WORD_BLAST to show the cascading shifts clear all high bits.

```
QUOTIENT_BIT127:
  ~bit 127 (word_xor(word_subword T (128,128))(word_subword(ghash_reduce1 T)(128,128)))
```

The quotient word has degree <= 126 (bit 127 = F), satisfying POLY_REVN_MUL_GHASH's
hypothesis.

#### Assembly of GHASH_REDUCE_BITREV_CONG_MOD_POLYVAL (GHASH_POLYVAL_BRIDGE_CORE)

1. From `REDUCE1_QUOTIENT` applied twice + char-2 cancellation:
   `ring_add(poly T)(poly r2) = ring_mul(poly w)(ghash_poly)` where `w = xor(hi1, hi2)`
2. From `POLY_GHASH_REDUCE_EQ_R2` + `R2_HIGH_ZERO`:
   `poly(ghash_reduce T) = poly(r2)` (truncation preserves polynomial since high bits = 0)
3. Hence: `ring_add(poly(ghash_reduce T))(poly T) = ring_mul(poly w)(ghash_poly)`
4. Apply `poly_revn 254` to both sides:
   - LHS: `ring_add(poly_revn 254(poly c))(poly_revn 254(poly T))` (POLY_REVN_ADD)
   - `= ring_add(poly(bitrev c) * x^127)(poly(bitrev a) * poly(bitrev b))` (POLY_REVN_254_WORD128 + POLY_REVN_254_PMUL)
   - RHS: `ring_mul(poly_revn 126(poly w))(polyval_poly)` (POLY_REVN_MUL_GHASH + QUOTIENT_BIT127)
   - which is in `ideal{polyval_poly}`
5. So `(poly(bitrev c) * x^127 == poly(bitrev a) * poly(bitrev b)) mod_polyval`

#### Derivation of GHASH_REDUCE_BITREV_EQ_POLYVAL_DOT (GHASH_POLYVAL_BRIDGE) from GHASH_REDUCE_BITREV_CONG_MOD_POLYVAL (GHASH_POLYVAL_BRIDGE_CORE)

Both `bitrev(ghash_reduce(pmul a b))` and `ghash_twist(polyval_dot(bitrev a, bitrev b))`
are 128-bit words satisfying the same polynomial congruence mod Q (multiplied by x^127).
By `MOD_POLYVAL_CANCEL_VARPOW`, congruent words mod Q are equal, giving the word equality.

### Supporting lemmas for the GHASH-POLYVAL reflection equivalence

| Lemma | Statement | Proof technique |
|-------|-----------|-----------------|
| `GHASH_POLY_EQ_X128_PLUS_POLY87` | P = x^128 + poly(0x87) | GHASH_POLY_COEFF_AT_0_1_2_7_128 + bit-level case analysis |
| `GHASH_POLY_COEFF_AT_0_1_2_7_128` | ghash_poly(m) <=> m one in {128,7,2,1,0} | RING_SUM_CLAUSES + BOOL_POLY_POW_COEFF |
| `POLY_OF_WORD2_EQ_POLY_VAR` | poly(word 2:int128) = poly_var | FUN_EQ + monomial_var + one_INDUCT |
| `POLY_REVN126_EQ_USHR_BITREV` | poly_revn 126(poly w) = poly(ushr(bitrev w) 1) | FUN_EQ + poly_revn definition + BIT_WORD_USHR/REVERSEFIELDS |
| `POLY_VAR_MUL_REVN126_EQ_BITREV` | ~bit 127 w ==> x * poly(ushr(bitrev w) 1) = poly(bitrev w) | POLY_OF_WORD_PMUL_2N + NSUM_DELTA + BIT_WORD_USHR |
| `POLY_REVN254_OF_SHL128_EQ_REVN126` | poly_revn 254(poly(shl(zx w) 128:256)) = poly_revn 126(poly w) | FUN_EQ + BIT_WORD_SHL/ZX |
| `MUL_U128_WORD` | poly(w) * x^128 = poly(shl(zx w:256) 128) | NSUM_DELTA + BIT_WORD_PMUL_ALT + BIT_TRIVIAL |
| `POLY_OF_WORD_SURJ_128` | bounded-degree bool_poly element = poly_of_word(w) with ~bit 127 w | word_of_bits + ONE_FUN_EQ |
| `WORD_USHR_128_AS_ZX_SUBWORD` | word_ushr x 128 = word_zx(word_subword x (128,128)) | WORD_EQ_BITS_ALT + BIT_WORD_USHR/ZX/SUBWORD |
| `BIT255_PMUL_128` | ~bit 255 (word_pmul a b : 256 word) | BIT_WORD_PMUL_ALT + BIT_TRIVIAL |
| `BIT255_REDUCE1_PMUL` | ~bit 255 (ghash_reduce1(word_pmul a b)) | BIT_WORD_XOR + BIT_WORD_SUBWORD + degree bound |
| `QUOTIENT_BIT127` | ~bit 127 (xor hi1 hi2) | BIT255_PMUL_128 + BIT255_REDUCE1_PMUL |
| `POLY_GHASH_REDUCE_EQ_R2` | poly(ghash_reduce(pmul a b)) = poly(reduce1(reduce1(pmul a b))) | R2_HIGH_ZERO + BIT_WORD_USHR |
| `R2_HIGH_ZERO` | word_ushr(reduce1(reduce1(pmul a b)))(128) = word 0 | GHASH_REDUCE1_HI x2 + USHR_SMALL lemmas (WORD_BLAST) |
| `WORD_JOIN_SUBWORDS_256` | x:256 = word_join(subword(128,128))(subword(0,128)) | WORD_EQ_BITS_ALT + BIT_WORD_JOIN |
| `REDUCE1_QUOTIENT` | poly(x) + poly(reduce1 x) = poly(subword(128,128)) * P | GHASH_POLY_EQ_X128_PLUS_POLY87 + MUL_U128_WORD + POLY_OF_WORD_PMUL_2N + char-2 cancellation |
| `ONE_FUN_EQ` | f = g <=> f one = g one (for type 1) | one_INDUCT |
| `BIT_TRIVIAL_128` | 128 <= i ==> ~bit i (w:int128) | BIT_TRIVIAL + DIMINDEX_128 |
| `BOOL_POLY_ZERO_ALL_COEFFS_FALSE` | ~(ring_0 bool_poly m) | BOOL_POLY_ZERO + poly_0 + COND_ID |

---

## NIST Algorithm 1 = Polynomial algebra (Equivalence A: NIST_GHASH_EQ_GHASH_REDUCE)

### Top-level theorem

```
NIST_GHASH_EQ_GHASH_REDUCE:
  forall x y : int128.
    bit_reverse_per_byte(nist_ghash_mul x y) =
    ghash_reduce(word_pmul (bit_reverse_per_byte x) (bit_reverse_per_byte y))
```

This says: the NIST Algorithm 1 multiplication (shift-and-XOR loop),
after per-byte bit reversal to convert from NIST bit ordering to
natural polynomial bit ordering, equals the polynomial product reduced
by `ghash_reduce` (= reduction mod P(x) = x^128 + x^7 + x^2 + x + 1).

### NIST definitions

| Definition | Description |
|------------|-------------|
| `nist_bit x i` | NIST bit accessor: maps NIST bit i to HOL Light bit `8*(i DIV 8) + 7 - i MOD 8` |
| `nist_lsb v` | NIST LSB_1(V) = bit 120 in HOL Light (= bit 127 in polynomial order) |
| `nist_shr1 v` | NIST right-shift by 1 (handles per-byte bit boundary crossing) |
| `ghash_R` | Reduction constant R = 0xE1 (= 11100001 || 0^120) |
| `ghash_mul_loop z v x n` | Algorithm 1 loop body (n steps remaining) |
| `nist_ghash_mul x y` | Algorithm 1: X * Y = `ghash_mul_loop (word 0) y x 128` |
| `nist_ghash h acc xs` | Algorithm 2: GHASH_H(X) = iterated XOR-then-multiply |
| `bit_reverse_per_byte x` | Per-byte bit reversal = `word_reversefields 8 (word_reversefields 1 x)` |
| `poly_mul_loop z v x n` | Natural-order version of the loop (shift + conditional XOR with 0x87) |
| `partial_poly x n` | Horner evaluation of x's bits (= poly_of_word(x) after 128 steps) |
| `word_horner x n` | Word-level version of partial_poly (used for the Horner identity proof) |

### Proof structure

The proof decomposes into three stages:

#### Stage 1: NIST loop -> polynomial-order loop (NIST_LOOP_AS_POLY_LOOP)

```
NIST_LOOP_AS_POLY_LOOP:
  forall n z v x.
    bit_reverse_per_byte(ghash_mul_loop z v x n) =
    poly_mul_loop (brp z) (brp v) (brp x) n
```

Proved by induction on `n` using NIST_BIT_AS_NATURAL, NIST_SHR1_AS_SHL,
NIST_V_UPDATE_AS_POLY_SHL, NIST_Z_UPDATE_AS_POLY_XOR.

#### Stage 2: Polynomial-order loop -> ghash_reduce(word_pmul) (POLY_LOOP_EQ_GHASH_REDUCE)

```
POLY_LOOP_EQ_GHASH_REDUCE:
  forall x y : int128.
    poly_mul_loop (word 0) y x 128 = ghash_reduce(word_pmul x y)
```

Both sides are 128-bit words congruent to `poly(x) * poly(y) (mod P)`.
Since they're congruent and both are 128-bit words, `CONG_MOD_GHASH_IMP_WORD_EQ`
gives the word equality.

The key sub-lemmas are POLY_SHL_XOR_CONG_MOD_GHASH (V-step preserves congruence
mod P), POLY_LOOP_HORNER_CONG_MOD_GHASH (inductive loop congruence), and
PARTIAL_POLY_128 (Horner evaluation = poly_of_word).

#### Stage 3: Composition (NIST_GHASH_EQ_GHASH_REDUCE)

Trivial rewrite composition of Stages 1 and 2.

---

## Test vectors

Four formally proved test vectors validate `gcm_gmult_spec` in HOL Light:
- Zero input -> zero output (GCM_GMULT_TEST_ZERO)
- NIST SP 800-38D Test Case 2 derived values (GCM_GMULT_TEST_1)
- Mixed bit patterns (GCM_GMULT_TEST_2)
- All-ones inputs (GCM_GMULT_TEST_3)

Additional runtime tests in `test.c` validate the assembly against a
C reference implementation of NIST Algorithm 1 using the NIST test vector
and random inputs.

---

## Summary of proof techniques

| Technique | Where used |
|-----------|-----------|
| `WORD_BLAST` / BDD | Karatsuba limbs, Barrett/Prop3 reduction equivalence, byte-reversal XOR, USHR_SMALL lemmas |
| `WORD_EQ_BITS_ALT` (bit-level) | WORD_ZX_SHL_XOR_OVERFLOW, WORD_JOIN_SUBWORDS_256, WORD_USHR_128_AS_ZX_SUBWORD |
| Induction on loop counter | NIST_LOOP_AS_POLY_LOOP, POLY_LOOP_HORNER_CONG_MOD_GHASH, WORD_HORNER_BIT, PARTIAL_POLY_AS_WORD_HORNER |
| `MOD_GHASH_TRANS/ADD/MUL` | POLY_SHL_XOR_CONG_MOD_GHASH, POLY_LOOP_STEP_CONG_MOD_GHASH, POLY_LOOP_EQ_GHASH_REDUCE |
| `MOD_POLYVAL_TRANS/CANCEL_VARPOW` | GHASH_REDUCE_BITREV_EQ_POLYVAL_DOT (GHASH_POLYVAL_BRIDGE) from GHASH_REDUCE_BITREV_CONG_MOD_POLYVAL (GHASH_POLYVAL_BRIDGE_CORE) |
| `poly_revn` coefficient analysis | POLY_REVN254_OF_SHL128_EQ_REVN126, POLY_REVN126_EQ_USHR_BITREV, POLY_REVN_MUL_GHASH |
| `NSUM_DELTA` for convolution | MUL_U128_WORD, POLY_VAR_MUL_REVN126_EQ_BITREV |
| `GHASH_REDUCE1_HI` cascading | R2_HIGH_ZERO (two-pass degree bound) |
| Ring algebra (`RING_ADD_LDISTRIB`, etc.) | POLY_REVN_MUL_GHASH, REDUCE_SUM_EQ_QUOTIENT_MUL |
| `POLY_OF_WORD_ZX` (cross-size) | POLY_GHASH_REDUCE_EQ_R2, POLY_OF_WORD_ZX_128_256 |
| `MESON_TAC` (ring algebra) | BOOL_POLY_MUL_ASSOC_COMM, BOOL_POLY_ADD_CANCEL |
| ARM simulation (`MAP_EVERY`) | GCM_GMULT_V8_EXEC_CORRECT |

---

## Total proof effort

- **~75 theorems** proved across 3 files (plus ~20 in interactive sessions)
- **0 CHEAT_TAC** remaining
- **0 new_axiom** added
- **4 equivalence proofs** connecting 5 abstraction layers
- **End-to-end verification**: NIST SP 800-38D Algorithm 1 = ARM assembly output
- Key mathematical contribution: the **GHASH-POLYVAL reflection equivalence**
  via the `poly_revn` ideal mapping from P(x) to Q(x), establishing that
  bit-reversal of GF(2^128) elements converts between the two standard
  polynomial bases used in GHASH and POLYVAL
