# GCM GMULT V8: Full Proof Chain from NIST Spec to ARM Implementation

## Overview

This document describes the complete formal verification chain connecting
the NIST SP 800-38D GHASH multiplication specification to the ARM NEON
`gcm_gmult_v8` assembly implementation. Every layer is connected by a
formally proved HOL Light theorem, with **zero CHEAT_TAC** remaining.

The chain has five layers connected by four bridges:

```
NIST SP 800-38D Algorithm 1            (bit-level shift-and-XOR loop)
        |  Bridge A  (manastasova: BRIDGE_A)
        v
Polynomial algebra mod P(x)            (poly_of_word, ghash_reduce, word_pmul)
        |  Bridge B  (nebeid: POLYVAL_DOT_CORRECT + GHASH_TWIST_CORRECT)
        v
polyval_dot / polyval_reduce_prop3     (Gueron's Prop 3 reduction mod Q(x))
        |  Bridge C  (manastasova: GCM_GMULT_POLYVAL_DOT)
        v
gcm_gmult_spec                         (ARM instruction-level spec)
        |  Bridge D  (manastasova: GCM_GMULT_V8_EXEC_CORRECT)
        v
gcm_gmult_v8 assembly                  (27 NEON instructions)
```

---

## Attribution

| Component | Author | Status |
|-----------|--------|--------|
| **GF(2)[x] foundation** (`ghash.ml`: bool_poly, poly_of_word, P(x), ghash_reduce, irreducibility) | John Harrison (AWS) | Complete |
| **POLYVAL infrastructure** (`polyval.ml`: Q(x), polyval_reduce_prop3) | nebeid | Complete |
| **Prop 3 correctness** (`polyval_prop3_proof.ml`: POLYVAL_REDUCE_PROP3_CORRECT) | nebeid | Complete |
| **Karatsuba decomposition** (`karatsuba_pmul_proof.ml`: PMUL_KARATSUBA) | nebeid | Complete |
| **GHASH algebraic spec** (`ghash_spec.ml`: polyval_dot, ghash_polyval_acc, htable, twist) | nebeid | Complete |
| **Bridge B: P(x) <-> Q(x)** (POLYVAL_DOT_CORRECT, GHASH_TWIST_CORRECT) | nebeid | Complete |
| **Bridge C: polyval_dot <-> gcm_gmult_spec** (GCM_GMULT_POLYVAL_DOT) | manastasova | Complete |
| **Implementation spec** (`gcm_gmult_v8_spec.ml`: gcm_gmult_spec, SIMD lemmas, test vectors) | manastasova | Complete |
| **Bridge D: ARM simulation** (`gcm_gmult_v8.ml`: GCM_GMULT_V8_EXEC_CORRECT) | manastasova | Complete |
| **NIST Algorithm 1 transcription** (`gcm_gmult_v8_nist.ml`: nist_ghash_mul, nist_ghash) | manastasova | Complete |
| **Bridge A: NIST <-> polynomial algebra** (BRIDGE_A + all supporting lemmas) | manastasova | Complete |

---

## Files and their roles

### Pre-existing (from nebeid's ghash-polyval branch)

| File | Role |
|------|------|
| `common/ghash.ml` | GF(2)[x] polynomial ring, P(x) = x^128+x^7+x^2+x+1, `ghash_reduce`, `ghash_reduce1`, `mod_ghash`, `MOD_GHASH_REFL/SYM/TRANS/ADD/MUL`, `POLY_EQUIV_GHASH_REDUCE`, irreducibility |
| `common/polyval.ml` | Q(x) = x^128+x^127+x^126+x^121+1, `polyval_reduce_prop3`, `mod_polyval` |
| `common/polyval_prop3_proof.ml` | `POLYVAL_REDUCE_PROP3_CORRECT`: prop3 result * x^128 = input (mod Q) |
| `common/karatsuba_pmul_proof.ml` | `PMUL_KARATSUBA`: 3-PMULL Karatsuba = word_pmul |
| `common/ghash_spec.ml` | `polyval_dot`, `ghash_polyval_acc`, batched GHASH, htable predicates, twist, `POLYVAL_DOT_CORRECT`, `GHASH_TWIST_CORRECT` |

### Created in this work

| File | Role |
|------|------|
| `arm/proofs/utils/gcm_gmult_v8_spec.ml` | `gcm_gmult_spec`: implementation-level spec mirroring ARM instructions (Karatsuba + 2-phase Barrett reduction + byte reversal) |
| `arm/proofs/gcm_gmult_v8.ml` | ARM simulation proof: 27-step `MAP_EVERY` with SIMD simplification |
| `arm/proofs/utils/gcm_gmult_v8_nist.ml` | NIST Algorithm 1 definitions + Bridge A (full) + Bridge C (`GCM_GMULT_POLYVAL_DOT`) |

---

## Bridge D: ARM Assembly -> gcm_gmult_spec

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

## Bridge C: gcm_gmult_spec -> polyval_dot (GCM_GMULT_POLYVAL_DOT)

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

#### Step 1: KARATSUBA_LIMBS (4 lemmas, by WORD_BLAST)

Extract the four 64-bit limbs (A, B, C, D) of the 256-bit Karatsuba product
`T = word_xor(word_xor(word_zx xl)(word_shl(word_zx mid) 64))(word_shl(word_zx xh) 128)`:

| Lemma | Result |
|-------|--------|
| `KARATSUBA_LIMB_A` | `word_subword T (0,64) = word_subword xl (0,64)` |
| `KARATSUBA_LIMB_B` | `word_subword T (64,64) = word_xor (word_subword xl (64,64)) (word_subword mid (0,64))` |
| `KARATSUBA_LIMB_C` | `word_subword T (128,64) = word_xor (word_subword xh (0,64)) (word_subword mid (64,64))` |
| `KARATSUBA_LIMB_D` | `word_subword T (192,64) = word_subword xh (64,64)` |

#### Step 2: SPEC_XM_PRIME_AS_ABCD (by WORD_BLAST)

The spec's Karatsuba recombination `xm'` has halves equaling Prop 3's
limbs B and C. This bridges the two different Karatsuba recombination
strategies (spec uses EXT/EOR, Prop 3 uses direct XOR).

#### Step 3: REDUCTION_EQUIV (by WORD_BLAST on 4 x 64 = 256 Boolean vars)

The spec's two-phase Barrett reduction and Prop 3's reduction produce
identical results on the same four 64-bit limbs:

```
forall a b c d : 64 word.
  spec_two_phase_reduction(a,b,c,d) = prop3_reduction(a,b,c,d)
```

Key insight: `phase1_lo = wa_lo XOR b = V` (Prop 3's V), so the
two reduction phases compute exactly the same intermediate values.

#### Step 4: Composition

1. Expand both sides with `PMUL_KARATSUBA` + `KARATSUBA_LIMBS` + `PMUL_W_64_128`
2. Abbreviate the 3 Karatsuba pmull results (xl, xh, xm) using `ABBREV_TAC`
3. Align operand orders with `WORD_PMUL_SYM`
4. Apply `SPEC_XM_PRIME_AS_ABCD` to rewrite xm' halves
5. Apply `REDUCTION_EQUIV` to equate the reduction arrangements
6. Close with beta-reductions

---

## Bridge B: polyval_dot -> Polynomial algebra (nebeid)

### Key theorems (from `ghash_spec.ml`)

| Theorem | Statement |
|---------|-----------|
| `POLYVAL_DOT_CORRECT` | `poly(polyval_dot a b) * x^128 = poly(a) * poly(b) (mod Q(x))` |
| `GHASH_TWIST_CORRECT` | GHASH = byte_reverse(POLYVAL(twist(byte_reverse(H)), ...)) |
| `MOD_POLYVAL_WORD_EQ` | Congruent 128-bit words mod Q(x) are equal |

These connect the POLYVAL computation (mod Q(x)) to GHASH (mod P(x))
via the bit-reflection relationship between the two polynomials.

---

## Bridge A: NIST Algorithm 1 -> Polynomial algebra (BRIDGE_A)

### Top-level theorem

```
BRIDGE_A:
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

### Bridge A proof structure

The proof decomposes into three stages:

#### Stage 1: NIST loop -> polynomial-order loop (LOOP_BRP)

```
LOOP_BRP:
  forall n z v x.
    bit_reverse_per_byte(ghash_mul_loop z v x n) =
    poly_mul_loop (brp z) (brp v) (brp x) n
```

Proved by induction on `n` using:
- `NIST_BIT_AS_NATURAL`: NIST bit i of x = natural bit i of brp(x)
- `NIST_SHR1_AS_SHL`: brp(nist_shr1 v) = word_shl(brp v) 1
- `V_STEP_BRP`: brp of V-update = if bit 127 then xor(shl,0x87) else shl
- `Z_STEP_BRP`: brp of Z-update = conditional XOR by natural bit

#### Stage 2: Polynomial-order loop -> ghash_reduce(word_pmul) (POLY_MUL_LOOP_CORRECT)

```
POLY_MUL_LOOP_CORRECT:
  forall x y : int128.
    poly_mul_loop (word 0) y x 128 = ghash_reduce(word_pmul x y)
```

Both sides are 128-bit words congruent to `poly(x) * poly(y) (mod P)`:
- The loop side uses `POLY_MUL_LOOP_CONG` (from `LOOP_INVARIANT`)
- The ghash_reduce side uses `POLY_EQUIV_GHASH_REDUCE` + `POLY_OF_WORD_PMUL_2N`

Since they're congruent and both are 128-bit words, `MOD_GHASH_WORD_EQ`
gives the word equality.

#### Stage 3: Composition (BRIDGE_A)

```
BRIDGE_A = NIST_GHASH_MUL_AS_POLY_LOOP + POLY_MUL_LOOP_CORRECT
```

Trivial rewrite composition of Stages 1 and 2.

### Key lemmas for Stage 2 (the hard part)

#### V_STEP_CONG: V-step preserves congruence mod P(x)

```
V_STEP_CONG:
  forall v : int128.
    (poly_of_word(if bit 127 v then word_xor(word_shl v 1)(word 0x87)
                  else word_shl v 1) ==
     ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v))
    (mod_ghash)
```

This is the core inductive step: the V-update (shift left by 1, XOR with
0x87 if overflow) is congruent to multiplication by the polynomial variable
u modulo P(x).

**Proof approach** (two cases):

- **False case** (`~bit 127 v`): No overflow, so `poly_of_word(word_shl v 1) = u * poly_of_word(v)`
  exactly. Uses `SHL_1_POLY_FALSE` which goes through `WORD_PMUL_POLY` + `POLY_OF_WORD_OF_POLY`
  with the degree bound `POLY_DEG_MUL_V_U_BOUND` (degree < 128 when bit 127 is false).

- **True case** (`bit 127 v`): Overflow by one bit. The quotient witness is `ring_1 bool_poly`.
  The proof uses `WORD_ZX_SHL_XOR_OVERFLOW` at 256 bits to show that the truncated shift
  and the full shift differ by exactly `x^128` at bit position 128. Then:
  - `poly(V_step) + u*poly(v) = x^128 + poly(0x87)` (via `POLY_OF_SHL_ZX`, `POLY_OF_WORD_X128`)
  - `x^128 + poly(0x87) = ghash_poly` (via `GHASH_POLY_AS_SUM`)
  - So `ghash_poly` divides the difference, giving the congruence with quotient 1.

**Supporting lemmas for V_STEP_CONG:**

| Lemma | Statement | Proof technique |
|-------|-----------|-----------------|
| `POLY_VAR_IN_BOOL_POLY` | `poly_var bool_ring one IN ring_carrier bool_poly` | Direct from `POLY_VAR` |
| `RING_MUL_POLY_VAR` | `u * poly_of_word(v) IN ring_carrier bool_poly` | `RING_MUL` |
| `WORD_CLZ_GE_1` | `~bit 127 v ==> 1 <= word_clz v` | `WORD_CLZ_EQ_0` |
| `POLY_DEG_MUL_V_U_BOUND` | `~bit 127 v ==> poly_deg(u * poly(v)) < 128` | `POLY_DEG_MUL_LE` + `POLY_DEG_VAR` + CLZ bound |
| `WORD_SHL_1_AS_OF_POLY` | `word_shl v 1 = word_of_poly(poly(v) * u)` | `WORD_PMUL_POLY` + `WORD_PMUL_POW2` |
| `SHL_1_POLY_FALSE` | `~bit 127 v ==> poly(shl v 1) = u * poly(v)` | `POLY_OF_WORD_OF_POLY` + degree bound |
| `ODD_1_DIV_2EXP` | `ODD(1 DIV 2^n) <=> (n = 0)` | Case split + `DIV_LT` |
| `WORD_ZX_SHL_XOR_OVERFLOW` | `word_xor(zx(shl v 1):256)(shl(zx v:256) 1) = if bit 127 v then shl(word 1) 128 else word 0` | `WORD_EQ_BITS_ALT` + bit-by-bit case analysis |
| `POLY_OF_WORD_X128` | `poly(word_shl (word 1:256) 128) = u^128` | `POLY_VAR_POW_OF_WORD` |
| `POLY_OF_WORD_ZX_128_256` | `poly(word_zx(w:int128):256) = poly(w)` | `POLY_OF_WORD_ZX` |
| `POLY_OF_WORD_2_256` | `poly(word 2 : 256 word) = u` | `POLY_VAR_POW_OF_WORD` at n=1 |
| `POLY_OF_SHL_ZX` | `poly(shl(zx v:256) 1) = u * poly(v)` | `WORD_PMUL_POLY` + `POLY_OF_WORD_OF_POLY` at 256 bits |
| `GHASH_POLY_AS_SUM` | `ghash_poly = u^128 + poly(word 0x87)` | `GHASH_POLY_OF_WORD` + `POLY_OF_WORD_XOR` |
| `RING_ADD_ACB` | `(A+B)+C = (A+C)+B` in any ring | `RING_ADD_ASSOC` + `RING_ADD_SYM` |

#### LOOP_INVARIANT: Inductive loop congruence

```
LOOP_INVARIANT:
  forall n z v x : int128. n <= 128 ==>
    (poly_of_word(poly_mul_loop z v x n) ==
     ring_add bool_poly (poly_of_word z)
       (ring_mul bool_poly (partial_poly x n) (poly_of_word v)))
    (mod_ghash)
```

Proved by induction on `n`. The base case is trivial (0 = 0 + 0*v).
The inductive step uses `LOOP_STEP_CONG` which shows the IH's RHS
is congruent to the target RHS, then chains via `MOD_GHASH_TRANS`.

**Supporting lemmas for LOOP_INVARIANT:**

| Lemma | Statement | Proof technique |
|-------|-----------|-----------------|
| `DISTRIB_LEMMA` | `(1 + u*pp) * pv = pv + (u*pp)*pv` | `RING_ADD_RDISTRIB` + `RING_MUL_LID` |
| `ASSOC_COMM_LEMMA` | `(u*pp)*pv = pp*(u*pv)` | `RING_MUL_SYM` + `RING_MUL_ASSOC` |
| `ADD_ASSOC_LEMMA` | `a + (b + c) = (a + b) + c` | `RING_ADD_ASSOC` |
| `LOOP_STEP_CONG` | IH's RHS == target RHS (mod P) | Case split on bit_i + ring algebra + `V_STEP_CONG` + `MOD_GHASH_ADD/MUL` |

#### PARTIAL_POLY_128: Horner evaluation = poly_of_word

```
PARTIAL_POLY_128:
  forall x : int128. partial_poly x 128 = poly_of_word x
```

The partial polynomial built by Horner evaluation of x's bits (MSB to LSB)
after 128 steps equals `poly_of_word x`.

**Proof approach:**

1. Define `word_horner x n` (word-level Horner construction):
   `word_horner x 0 = word 0`,
   `word_horner x (SUC n) = word_xor (if bit(128-SUC n) x then word 1 else word 0) (word_shl (word_horner x n) 1)`

2. Prove `WORD_HORNER_BIT`: bit-level characterization by induction:
   `bit k (word_horner x n) <=> k < n /\ bit(128-n+k) x`

3. Prove `WORD_HORNER_128`: `word_horner x 128 = x`
   (from WORD_HORNER_BIT with n=128: bit k = bit k x for all k < 128)

4. Prove `PARTIAL_POLY_AS_WORD_HORNER`: `partial_poly x n = poly_of_word(word_horner x n)`
   by induction, using `SHL_1_POLY_FALSE` (no overflow since `WORD_HORNER_BIT127_F`
   shows bit 127 is always false for n <= 127)

5. Compose: `partial_poly x 128 = poly_of_word(word_horner x 128) = poly_of_word x`

#### Uniqueness mod P(x)

| Lemma | Statement | Proof technique |
|-------|-----------|-----------------|
| `GHASH_POLY_NONZERO` | `ghash_poly <> ring_0 bool_poly` | `POLY_DEG_GHASH_POLY` (degree 128 <> degree 0) |
| `GHASH_DIVIDES_LOW_DEG` | `ghash_poly divides p /\ deg p < 128 ==> p = 0` | Degree argument: `deg(ghash_poly * q) >= 128` |
| `MOD_GHASH_WORD_EQ` | `(poly(x) == poly(y)) mod_ghash ==> x = y` | `POLY_OF_WORD_INJ` + `GHASH_DIVIDES_LOW_DEG` |

---

## Test vectors

Four formally proved test vectors validate `gcm_gmult_spec`:
- Zero input -> zero output
- NIST SP 800-38D Test Case 2 derived values
- Mixed bit patterns
- All-ones inputs

The NIST test case was also used to validate `GCM_GMULT_POLYVAL_DOT`
by concrete evaluation of both sides.

---

## Complete theorem inventory

### Bridge A (`gcm_gmult_v8_nist.ml`) -- manastasova

| # | Theorem | Type |
|---|---------|------|
| 1 | `NIST_BIT_AS_NATURAL` | NIST-to-natural bit mapping |
| 2 | `NIST_LSB_AS_NATURAL` | NIST LSB = bit 127 of brp |
| 3 | `BRP_GHASH_R` | brp(0xE1) = 0x87 |
| 4 | `NIST_HOL_BIT_BOUND` | Arithmetic helper |
| 5 | `SUB_8Q_PLUS_7` | Arithmetic helper |
| 6 | `EIGHT_MUL_SUB` | Arithmetic helper |
| 7 | `NIST_SHR1_BIT` | nist_shr1 shifts NIST bits right by 1 |
| 8 | `BRP_XOR` | brp distributes over XOR |
| 9 | `NIST_SHR1_AS_SHL` | brp(nist_shr1 v) = word_shl(brp v) 1 |
| 10 | `V_STEP_BRP` | V-update through brp |
| 11 | `Z_STEP_BRP` | Z-update through brp |
| 12 | `LOOP_BRP` | NIST loop through brp = poly loop |
| 13 | `BRP_ZERO` | brp(0) = 0 |
| 14 | `NIST_GHASH_MUL_AS_POLY_LOOP` | brp(nist_mul) = poly_loop |
| 15 | `BOOL_POLY_MUL_EQ` | ring_mul bool_poly = poly_mul bool_ring |
| 16 | `BOOL_POLY_ZERO_EQ` | ring_0 bool_poly = poly_0 bool_ring |
| 17 | `GHASH_POLY_NONZERO` | ghash_poly <> 0 |
| 18 | `GHASH_DIVIDES_LOW_DEG` | ghash_poly | p, deg p < 128 => p = 0 |
| 19 | `MOD_GHASH_WORD_EQ` | Congruent 128-bit words are equal |
| 20 | `KARATSUBA_LIMB_A/B/C/D` | 256-bit Karatsuba limb extractions |
| 21 | `SPEC_XM_PRIME_AS_ABCD` | xm' halves = Karatsuba B,C |
| 22 | `REDUCTION_EQUIV` | Spec reduction = Prop3 reduction |
| 23 | `GCM_GMULT_POLYVAL_DOT` | **Bridge C** |
| 24 | `POLY_VAR_IN_BOOL_POLY` | poly_var membership |
| 25 | `RING_MUL_POLY_VAR` | u*poly(v) membership |
| 26 | `WORD_CLZ_GE_1` | ~bit 127 => CLZ >= 1 |
| 27 | `POLY_DEG_MUL_V_U_BOUND` | degree of u*poly(v) < 128 |
| 28 | `WORD_SHL_1_AS_OF_POLY` | shl v 1 = word_of_poly(poly(v)*u) |
| 29 | `SHL_1_POLY_FALSE` | ~bit 127 => poly(shl v 1) = u*poly(v) |
| 30 | `ODD_1_DIV_2EXP` | ODD(1 DIV 2^n) <=> n=0 |
| 31 | `WORD_ZX_SHL_XOR_OVERFLOW` | 256-bit overflow identity |
| 32 | `POLY_OF_WORD_X128` | poly(shl (word 1:256) 128) = u^128 |
| 33 | `POLY_OF_WORD_ZX_128_256` | poly(zx w:256) = poly(w:128) |
| 34 | `POLY_OF_WORD_2_256` | poly(word 2:256) = u |
| 35 | `POLY_OF_SHL_ZX` | poly(shl(zx v:256) 1) = u*poly(v) |
| 36 | `GHASH_POLY_AS_SUM` | ghash_poly = u^128 + poly(0x87) |
| 37 | `RING_ADD_ACB` | Ring AC: (A+B)+C = (A+C)+B |
| 38 | `V_STEP_CONG` | **V-step congruence mod P** |
| 39 | `WORD_HORNER_BIT` | Bit characterization of word_horner |
| 40 | `WORD_HORNER_128` | word_horner x 128 = x |
| 41 | `WORD_HORNER_BIT127_F` | bit 127 (word_horner x n) = F for n<=127 |
| 42 | `PARTIAL_POLY_AS_WORD_HORNER` | partial_poly = poly(word_horner) |
| 43 | `PARTIAL_POLY_128` | **partial_poly x 128 = poly_of_word x** |
| 44 | `PARTIAL_POLY_IN_CARRIER` | partial_poly membership |
| 45 | `DISTRIB_LEMMA` | (1+u*pp)*pv = pv + (u*pp)*pv |
| 46 | `ASSOC_COMM_LEMMA` | (u*pp)*pv = pp*(u*pv) |
| 47 | `ADD_ASSOC_LEMMA` | a+(b+c) = (a+b)+c |
| 48 | `LOOP_STEP_CONG` | IH RHS == target RHS (mod P) |
| 49 | `LOOP_INVARIANT` | **Loop inductive congruence** |
| 50 | `POLY_MUL_LOOP_CONG` | poly(loop 0 y x 128) == poly(x)*poly(y) |
| 51 | `POLY_MUL_LOOP_CORRECT` | **loop = ghash_reduce(word_pmul)** |
| 52 | `BRIDGE_A` | **brp(nist_mul) = ghash_reduce(pmul(brp,brp))** |

### Bridge C+D (`gcm_gmult_v8_spec.ml` + `gcm_gmult_v8.ml`) -- manastasova

| Theorem | Description |
|---------|-------------|
| `GCM_GMULT_POLYVAL_DOT` | Bridge C: gcm_gmult_spec = rev8(polyval_dot) |
| `GCM_GMULT_V8_EXEC_CORRECT` | Bridge D: ARM assembly = gcm_gmult_spec |
| `GCM_GMULT_V8_SUBROUTINE_CORRECT` | Bridge D (subroutine wrapper) |
| `SIMD_SIMPLIFY_RULES` (3) | REV64 simplification for SIMD simulation |
| `WORD_INSERT_AS_JOIN_1/2` | Word insert bridging lemmas |
| `KAR_SUBWORD_LEMMA` | Karatsuba middle term subword identity |
| Test vectors (4) | Concrete validation of gcm_gmult_spec |

---

## Summary of proof techniques

| Technique | Where used |
|-----------|-----------|
| `WORD_BLAST` / BDD | KARATSUBA_LIMBS, SPEC_XM_PRIME_AS_ABCD, REDUCTION_EQUIV, BRP_XOR, NIST_SHR1_AS_SHL |
| `WORD_EQ_BITS_ALT` (bit-level) | WORD_ZX_SHL_XOR_OVERFLOW, WORD_HORNER_BIT |
| Induction on loop counter | LOOP_BRP, LOOP_INVARIANT, WORD_HORNER_BIT, PARTIAL_POLY_AS_WORD_HORNER |
| `MOD_GHASH_TRANS/ADD/MUL` | V_STEP_CONG, LOOP_STEP_CONG, POLY_MUL_LOOP_CORRECT |
| Quotient witness | V_STEP_CONG (witness = ring_1 for true case) |
| Degree argument | MOD_GHASH_WORD_EQ, SHL_1_POLY_FALSE |
| `POLY_OF_WORD_OF_POLY` roundtrip | SHL_1_POLY_FALSE, POLY_OF_SHL_ZX |
| `POLY_OF_WORD_ZX` (cross-size) | POLY_OF_WORD_ZX_128_256, POLY_OF_SHL_ZX |
| `MESON_TAC` (ring algebra) | ASSOC_COMM_LEMMA, LOOP_INVARIANT inductive step |
| ARM simulation (`MAP_EVERY`) | GCM_GMULT_V8_EXEC_CORRECT |
| `ABBREV_TAC` (term management) | GCM_GMULT_POLYVAL_DOT |

---

## Total proof effort

- **~55 theorems** proved across 3 files
- **0 CHEAT_TAC** remaining
- **4 bridges** connecting 5 abstraction layers
- **End-to-end verification**: NIST SP 800-38D Algorithm 1 = ARM assembly output
