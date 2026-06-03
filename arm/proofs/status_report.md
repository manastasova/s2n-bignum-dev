# Status Report

## Conference Presentation — CAW 2026

Presented **"Verification Accelerates: Speeding up AWS's ML-KEM & ML-DSA via
Optimized and Formally Verified SHA-3"** at CAW 2026 (colocated with Eurocrypt
2026). Ref: <https://caw.cryptanalysis.fun/>

## AES-256-GCM Tail Verification

Working on a parametrized strategy to generalize the proofs for aes256-gcm for
the tail (the different block sizes). The idea is to have the machine code
proven equivalent to `ghash_polyval_acc` (proving the ciphertext correctness is
straightforward so it's not discussed) through the equivalence sequence:

```
machine code == karatsuba_2blocks == karatsuba_Nblocks
             == word_reversefields 8
                  (polyval_reduce_prop3
                    (   word_pmul (word_reversefields 8 (word_xor xi ct1)) (polyval_dot h h)
                    XOR word_pmul (word_reversefields 8 ct2)               h))
             == ghash_polyval_acc h xi [ct1; ct2]
```

The whole chain is closed by one tactic, `GCM_NBLOCK_GHASH_STEP_TAC`, which
strings the steps together: reach the assembly-shaped `karatsuba_2blocks` spec
via symbolic simulation; rewrite it into the generic list form with the
arity-adapter lemma `GHASH_2BLOCK_AS_NBLOCK`; convert the Karatsuba form to the
GHASH polynomial by applying the per-N bridge
`GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC` (a specialization of the once-proven
bridge `GHASH_NBLOCK_KARATSUBA_EQ_PROP3`); and finish the XOR-AC equality with
the custom conversion `bubble_sort_conv`.

The idea of the parametrization is that only the per-N pieces are regenerated
per block count, while the hard reasoning — the
`GHASH_NBLOCK_KARATSUBA_EQ_PROP3` — is proven once and reused for every N.

---

### Details about tactics

*(maybe not for the report but interesting to see in the channel)*

**Main / new tactics used for the transformations**

- **`GCM_NBLOCK_GHASH_STEP_TAC`** — top-level closer performing the entire
  `machine code → ghash_polyval_acc` chain for the GHASH conjunct.
- **`GHASH_<N>BLOCK_AS_NBLOCK`** — arity adapter (positional spec → generic list
  spec).
- **`GHASH_<N>BLOCK_KARATSUBA_EQ_POLYVAL_ACC`** — per-N bridge (karatsuba form →
  field polynomial), specialized from the inductive
  `GHASH_NBLOCK_KARATSUBA_EQ_PROP3`.
- **`bubble_sort_conv`** — custom XOR associativity/commutativity normalizer
  that closes the final equality.

**Proven ONCE** (shared, reused for every N — all the hard reasoning)

- `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` — inductive bridge "generic Karatsuba =
  GHASH polynomial" (the core theorem).
- `GHASH_POLYVAL_ACC_BATCHED` — inductive "list-form GHASH = Horner/pmul sum."
- GF(2¹²⁸) ring algebra: `POLYVAL_DOT_CORRECT`, the `MOD_POLYVAL_*` family.
- `POLYVAL_DOT_H4_EQ_LOCAL` + `H5/H6/H7/H8_EQ` (symmetric h-power normalizers),
  `INSERT_IDEM`/`INSERT_SUBWORD`, `bubble_sort_conv` (+ helpers) — now hoisted
  into the shared helpers.
- Generic spec `ghash_Nblock_karatsuba` + list plumbing; the AES model; the
  simulator framework (`ARM_STEPS_TAC`, `GCM_ENC_SIMPLIFY_TAC`,
  `ABBREV_FINAL_XI_TAC`, the `GCM_NBLOCK_*_NORMALIZE_TAC` family,
  `GCM_NBLOCK_CT_STEP_TAC`).

**Proven PER block count N** (cheap specializations + one real proof)

- `ghash_<N>block_karatsuba` — positional spec mirroring the N-block assembly.
- `GHASH_<N>BLOCK_AS_NBLOCK` — arity adapter (cheap `REWRITE`+`BETA`).
- `GHASH_<N>BLOCK_KARATSUBA_EQ_POLYVAL_ACC` — per-N bridge (thin `SPEC` of
  `…_EQ_PROP3`).
- `GHASH_POLYVAL_ACC_N` — fixed-length unrolling of `…_BATCHED`.
- `<N>_blocks_prelooptail_mc` + `<N>_BLOCKS_PRELOOP_TAIL_EXEC` — machine code
  blob + EXEC rule.
- `GCM_CT1..CTN_STEP_TAC`, `GCM_<N>BLOCK_GHASH_STEP_TAC` — closure tactics scaled
  to N.
- `<N>_BLOCKS_PRELOOP_TAIL_CORRECT` — the only expensive per-N item: a fresh
  symbolic-execution proof of the new `.o` (per-N step ranges, s13/ct
  abbreviations, N-way conjunction). Unavoidable because the code is
  branchless/unrolled — no loop to induct over, so each program is verified on
  its own.
