# Plan — two-block AES-256-GCM preloop-tail correctness proof

## Goal

Prove the ARM assembly function that processes **two** 16-byte blocks
(32 bytes total) through the aws-lc `aesv8_gcm_8x_enc_256` kernel is
functionally correct against the `ghash_polyval_acc` + `aes256_block_enc`
spec — i.e. the two-block analogue of the now-complete
`ONE_BLOCK_PRELOOP_TAIL_CORRECT` in
`one_block_aes256_gcm_preloop_tail_direct.ml`.

## Inputs already in place

Reusable from the one-block proof and the existing library:

- `aes256_block_enc` — spec for 14-round AES-256 single-block encrypt
  (common/aes.ml). Used unchanged.
- `polyval_dot`, `polyval_reduce_prop3`, `ghash_polyval_acc`, `karatsuba_mid`
  — `common/ghash_spec.ml`.
- **`GHASH_POLYVAL_ACC_2`** (`common/ghash_spec.ml:702`) — the **key** 2-block
  Horner-unrolling lemma:
  ```
  ghash_polyval_acc h a [b; c] =
    polyval_reduce_prop3
      (word_xor (word_pmul (word_xor a b) (polyval_dot h h))
                (word_pmul c h))
  ```
  This folds the two-iteration Horner loop into a single Prop3 reduction of
  two 256-bit pmul results XORed together — exactly the shape the assembly
  computes when it runs `Loop_mod2x_v8`.
- From `gcm_gmult_v8_nist.ml`:
  - `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS` — Karatsuba mid recombination ↔ Prop3 limb form.
  - `BARRETT_REDUCTION_EQ_PROP3_REDUCTION` — two-phase Barrett ↔ Prop3 final.
  - `PMUL_KARATSUBA`, `KARATSUBA_LIMBS`, `PMUL_W_64_128`.
- From the direct 1-block closure:
  - `ABBREV_ALL_PMUL_TAC`, `PMUL_ARG_SORT_CONV`, `ABBREV_PMUL_HALVES_TAC`.
  - `DOUBLE_SUBWORD_JOIN`, `DOUBLE_SUBWORD_JOIN_HI`, `BYTESWAP128_SUBWORD_LO/HI`,
    `HALFSWAP_XOR`, `REV8_JOIN_FOLD`, `WORD_SWAP_HALVES_INVOLUTION`.
  - `GCM_ENC_SIMPLIFY_TAC`, SIMD REV64 lane-fold lemmas.

## What's missing (prerequisites)

1. **The two-block assembly file.** No
   `two_block_aes256_gcm_preloop_tail.S` exists in `arm/aes-gcm/` yet.
   First step: extract it from aws-lc's `aesv8_gcm_8x_enc_256` kernel
   analogously to the one-block extraction — keep INIT + 2 CTR counters
   + AES rounds on v0,v1 + `Loop_mod2x_v8` body + store → return. The
   commented-out blocks in the 1-block .S file are the guide: un-comment
   the v1 counter/AES path and the first Loop_mod2x_v8 iteration.
2. **Htable layout for two blocks.** The kernel uses 3 slots:
   - `Htable[0]` = h_hi (= byteswap128 h halves)
   - `Htable[1]` = h_lo
   - `Htable[2]` = h_xor (= h_hi xor h_lo, precomputed mid)
   - `Htable[6]`/`Htable[7]` = **h² = polyval_dot h h** (hi/lo)
   - `Htable[8]` = h²_hi xor h²_lo (Karatsuba-mid of h²)
   The `Loop_mod2x_v8` loads ALL of these. The postcondition hypothesis
   must add: `word_subword h2k (0,64) = karatsuba_mid h2` where
   `h2 = polyval_dot h h`.
3. **Two-block preloop-tail spec.** Add
   `two_block_preloop_tail_enc_spec` to a new
   `utils/two_block_preloop_tail_spec.ml`, returning `(ct1, ct2, new_xi)`
   where `new_xi = ghash_polyval_acc h (reversefields xi)
   [reversefields ct1; reversefields ct2]` (via reversefields 8 wrapping
   as in 1-block proof).

## Strategy

### Phase 1 — extract & set up (1-2 days)

1. Produce `arm/aes-gcm/two_block_aes256_gcm_preloop_tail.S` and its
   `.o` via the existing toolchain. Count instructions; expect roughly
   150-180 steps (≈65 prologue/AES + ≈60 mod2x GHASH + epilogue).
2. Add `two_block_preloop_tail_enc_spec` (spec in the `polyval_dot` /
   `ghash_polyval_acc` form, not `gcm_gmult_spec`).
3. Create `two_block_aes256_gcm_preloop_tail_direct.ml` by copying
   `one_block_aes256_gcm_preloop_tail_direct.ml` as a starting template.
   Reuse all helper lemmas/tactics verbatim.
4. Generate `one_block_prelooptail_2_mc` analogue via
   `define_assert_from_elf` on the new `.o`.

### Phase 2 — symbolic simulation (3-5 days)

1. Adapt the `ARM_STEPS_TAC` blocks:
   - Steps 1-19 prologue: identical to 1-block (uses same stack layout).
   - Steps 20-N AES-on-v0+v1: interleaved AES rounds for two counters.
     Need to abbreviate `ct0` and `ct1` AFTER the final XOR with rk14,
     plus corresponding `s13_0`, `s13_1`.
   - Steps for mod2x GHASH: the loop loads `Htable[0..2]` for h and
     `Htable[6..8]` for h². Expect 4 pmul instructions (2 low, 2 high,
     2 mid) plus 2-round Barrett reduction (same as 1-block).
   - Final store + return: two `STR Q8` into `out_ptr` and `out_ptr+16`.
2. Apply `GCM_ENC_SIMPLIFY_TAC` after each step to collapse EOR/AESE
   patterns (reuse 1-block's tactic unchanged).
3. Abbreviate `ct0`, `ct1`, `s13_0`, `s13_1` before diving into GHASH
   to keep term sizes manageable.

### Phase 3 — GHASH closure (2-3 days)

This is where the 2-block proof diverges meaningfully from 1-block:

1. **Unfold `ghash_polyval_acc` on a 2-element list** and apply
   `GHASH_POLYVAL_ACC_2`. This collapses the Horner iteration to
   `polyval_reduce_prop3 (word_xor (word_pmul (acc ⊕ ct1) (h²))
                                    (word_pmul ct2 h))`.
2. Apply `PMUL_KARATSUBA` + `KARATSUBA_LIMBS` to **both** pmuls —
   this will produce 6 half-mults (3 for `(acc⊕ct1)*h²`, 3 for
   `ct2*h`). `ABBREV_ALL_PMUL_TAC` will name them `pm0..pm5`.
3. Apply `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS` for the mid-recombination.
4. Apply `BARRETT_REDUCTION_EQ_PROP3_REDUCTION` for the final reduction
   — identical shape to 1-block since after the xor'd pmul, the
   reduction is a single Prop3 call.
5. **Reuse the full 14-step closure chain** from the 1-block direct
   proof (see `memory/project_preloop_direct_closure.md`): abbrev
   halves → collapse pmK duplicates → derive primed-var equalities →
   r1/t/u/r2 fold chain → final `WORD_BLAST`. The chain is insensitive
   to whether there are 2 pmul clusters instead of 1, but expect **more**
   primed variables to collapse (pm0..pm11 range instead of pm0..pm5).
6. The `h²` argument `polyval_dot h h` is opaque; the proof needs
   only that `h² = polyval_dot h h` and that `Htable[8]_lo =
   karatsuba_mid h²`. No need to unfold `polyval_dot`.

### Phase 4 — verification & cleanup (1 day)

1. Step through the new direct proof tactic-by-tactic via MCP. Do NOT
   batch-load. After each ARM_STEPS block, check term sizes remain
   under ~30KB.
2. Once closure succeeds, load the full file end-to-end once to
   confirm.
3. Document any divergences from the 1-block chain in a fresh memory
   note.

## Risks & mitigations

- **Closure-chain scale blowup.** With 2 pmul clusters and 2 ct's, the
  goal after Karatsuba/Barrett unfolding could be 50-80KB (vs 23KB for
  1-block). Mitigation: abbreviate `ct0` AND `ct1` early, and add a
  third `ABBREV_ALL_PMUL_TAC` pass if needed. If `ABBREV_PMUL_HALVES_TAC`
  generates too many primed variants, pre-sort pmuls by their
  `word_xor (acc ⊕ ct1) h²` vs `ct2 h` shape to keep them semantically
  grouped.
- **Mod2x interleaving.** The assembly interleaves the two GHASH
  multiplications for latency-hiding. The mid-pmul arguments may appear
  in a form that doesn't obviously match `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS`.
  If so, add a sort/normalize pass using `PMUL_ARG_SORT_CONV` before
  the Karatsuba recombine.
- **Possible new lemma:** if the two Barrett reductions are interleaved
  (one per pmul) rather than done on the xor'd result, `GHASH_POLYVAL_ACC_2`
  may not apply directly. Check the assembly's reduction order early in
  Phase 2 — if interleaved, prove a variant of `GHASH_POLYVAL_ACC_2`
  that matches the interleaved form, or prove an additional lemma that
  "sum-of-reductions = reduction-of-sum" for the Prop3 case.
- **Aliasing/nonoverlapping:** 2 blocks means `in_ptr,32`, `out_ptr,32`
  instead of `,16`. Update every `nonoverlapping` clause and the
  `MAYCHANGE [memory :> bytes(out_ptr,32); ...]`. Mechanical but
  error-prone — copy 1-block MAYCHANGE and `sed s/,16/,32/g` the
  relevant ones.

## Estimated effort

- Phase 1: 1-2 days (mostly assembly extraction & toolchain).
- Phase 2: 3-5 days (symbolic simulation; longest if mod2x interleaving
  surprises us).
- Phase 3: 2-3 days (GHASH closure; the 1-block chain transfers, but
  2x the pmul count means 2x the collapse work).
- Phase 4: 1 day.
- **Total: ~10 days of focused work.**

## First concrete action

Get the `.S` file and spec in place (Phase 1, steps 1-3). Without
those we can't even set a goal to simulate against.

---

# Looking ahead: parameterizing the closure as `GHASH_CLOSE_N_TAC`

Once 2-block works using the same hand-written chain as 1-block, build
a meta-tactic so 3-block, 4-block, ... drop to ~2-3 days each
(assembly extraction + simulation + one-line closure call).

## Scope of applicability

The 1-block proof reveals a recipe whose steps are mostly N-agnostic:
- **All helper lemmas/tactics scale unchanged**:
  `ABBREV_ALL_PMUL_TAC`, `ABBREV_PMUL_HALVES_TAC`,
  `KARATSUBA_{RECOMBINE_EQ_PROP3_LIMBS, LIMBS}`,
  `BARRETT_REDUCTION_EQ_PROP3_REDUCTION`, `PMUL_KARATSUBA`,
  `PMUL_W_64_128`, `DOUBLE_SUBWORD_JOIN`/`_HI`, `WORD_SUBWORD_XOR`,
  `WORD_REVERSEFIELDS_XOR_8_128`, the SIMD folds, `GCM_ENC_SIMPLIFY_TAC`.
- **The Horner-unrolling lemma generalizes**: `GHASH_POLYVAL_ACC_N`
  for any N can be proved by induction from `GHASH_POLYVAL_ACC_2` +
  `GHASH_POLYVAL_ACC_APPEND` + polyval linearity. One parameterized
  lemma, not N copies.
- **The closure chain** (pmK-duplicate collapse → r1/t/u/r2
  abbreviation → `WORD_BLAST`) scales mechanically: N blocks produce
  ~3N pmuls and ~6N half-names, chain gets longer but structure is
  identical.

What does **not** scale:
- Each tail length is a **separate function** in aws-lc's cascade
  (`.L256_enc_blocks_less_than_N` for N=1..7), so each needs its own
  `~150-step` `ARM_STEPS_TAC` simulation and its own correctness
  theorem. The 8-block bulk loop is a separate induction proof that
  uses the 8-block straight-line result as its body lemma.
- `WORD_BLAST` cost grows roughly quadratically in nested term size;
  somewhere around N=4-5 we may need extra abbreviation passes
  between Horner iterations (abbreviate the XOR'd accumulator at each
  step) before the final blast.

## Signature

```ocaml
GHASH_CLOSE_N_TAC : int -> tactic
```

Takes block count `n`. Precondition on the goal state when called:
`ghash_polyval_acc` has been unfolded, `GHASH_POLYVAL_ACC_N` applied,
`PMUL_KARATSUBA` + `KARATSUBA_LIMBS` + `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS`
+ `BARRETT_REDUCTION_EQ_PROP3_REDUCTION` have run. At that point the
goal is a pure boolean word equation over `3n` pmuls.

## Internal structure

```ocaml
let GHASH_CLOSE_N_TAC (n:int) : tactic =
  ABBREV_ALL_PMUL_TAC THEN                  (* pm0 .. pm_{3n-1} *)
  REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_ARG_SORT_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  ABBREV_ALL_PMUL_TAC THEN                  (* second pass for fold outputs *)
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI] THEN

  ABBREV_PMUL_HALVES_TAC THEN               (* x{ll,lh,hl,hh,ml,mh}+primes *)

  COLLAPSE_PMUL_DUPLICATES_TAC THEN         (* auto-derive pmI = pmJ from
                                               xor/reversefields arg-equality;
                                               propagates to hypotheses *)

  COLLAPSE_PRIMED_HALVES_TAC THEN           (* xml''=xhl etc. via
                                               ASM_MESON[] over half-subword eqs *)

  ASM_REWRITE_TAC[] THEN
  SIMPLIFY_ZERO_SUBWORDS_TAC THEN           (* word_subword (word 0) = word 0
                                               + WORD_XOR_0 + WORD_XOR_ASSOC *)

  REPEAT_N n REDUCTION_ROUND_TAC THEN       (* <-- the only n-dependent step *)

  CONV_TAC WORD_BLAST
```

## The only n-parameterized piece: `REDUCTION_ROUND_TAC`

Each round is what the `r1/t/u` + `r2/u2` part of the 1-block proof
was, generalized. One round per Horner iteration; each shrinks the
nested-shift depth by one. After `n` rounds the goal is 500–700 bytes
regardless of starting nested depth, and `WORD_BLAST` finishes.

```ocaml
let REDUCTION_ROUND_TAC : tactic = fun (asl,w) ->
  (* 1. Find the freshest variable appearing inside the remaining
        shl-nest (xll at round 0, u at round 1, u2 at round 2, ...).   *)
  let v = pick_innermost_var asl w in

  (* 2. Abbreviate r_k = shl63 v xor shl62 v xor shl57 v. *)
  let rk = fresh_name asl "r" in
  ABBREV_TAC (mk_eq(rk, shl_xor_triple v)) THEN

  (* 3. Prove the two fold lemmas RL_k, RH_k (quantified over y). *)
  DERIVE_SHL_SUBWORD_FOLDS_TAC rk v THEN

  (* 4. Rewrite goal with RL_k / RH_k. *)
  USE_THEN ("RL"^string_of_int k) (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN ("RH"^string_of_int k) (fun th -> REWRITE_TAC[th]) THEN

  (* 5. Abbreviate the new inner shift arg:
        t_{k+1} = <LHS inner>,  u_{k+1} = <RHS inner>.                   *)
  ABBREV_NEW_INNER_TAC k THEN

  (* 6. Prove t_{k+1} = u_{k+1} via WORD_BLAST on expanded forms
        and SUBST_ALL_TAC.                                               *)
  EQUATE_INNER_TAC k
```

## What makes this tractable to implement

1. **`COLLAPSE_PMUL_DUPLICATES_TAC`** — walks pmul hypotheses,
   pattern-matches `word_pmul X₁ Y₁ = pmI` against
   `word_pmul X₂ Y₂ = pmJ`, and when `X₁ = X₂` and `Y₁ = Y₂` modulo
   the fixed rewrite set
   `[WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR; karatsuba_mid]`,
   synthesizes `pmI = pmJ` via `BINOP_TAC + AP_THM_TAC + AP_TERM_TAC`
   + `ASM_REWRITE_TAC[...]`, then applies
   `RULE_ASSUM_TAC(REWRITE_RULE[...])` to propagate.

   The one hard case hit in 1-block (pm5=pm4 where Y args differ by
   `h1k_lo = karatsuba_mid h`) is handled with
   `BINOP_TAC THENL [...; ASM_REWRITE_TAC[karatsuba_mid]]`.

2. **`COLLAPSE_PRIMED_HALVES_TAC`** — collects
   `word_subword pmK (ofs,64) = xNN` hypotheses, groups by `(pmK, ofs)`,
   emits the conjunction `x₁ = x₂ /\ ...` from same-LHS pairs,
   discharges with `ASM_MESON_TAC[]` (fast because each follows from
   two same-LHS equalities).

3. **`pick_innermost_var`** — at round k the variable is the unique
   unresolved one inside `word_shl (word_zx v) 63`. Use `find_term`
   over the goal for that pattern.

4. **`DERIVE_SHL_SUBWORD_FOLDS_TAC`** — emits two `SUBGOAL_THEN`
   statements templated on `v` and `r_k`, each closed by
   `GEN_TAC THEN EXPAND_TAC r_k THEN CONV_TAC WORD_BLAST`. Templates
   are built once via `mk_forall`/`mk_comb` against a fixed
   `:64 word` / `:128 word` schema.

5. **Unit-form fold lemmas** are needed at each round too
   (`... xor sub_shl63 (... xor sub_shl57)` with no trailing `y`),
   produced analogously. The 1-block proof had two of these; per-round
   we need both (0,64) and (64,64) variants.

## Sanity check before coding the tactic

Do the 2-block proof **by hand** first using the same 1-block pattern.
If it takes exactly two `REDUCTION_ROUND` iterations and nothing else
new, parameterization is justified. If 2-block requires a new kind of
step not predicted here (e.g. a cross-pmul-cluster equality), that
becomes the 7th helper in the tactic.

## Cost estimate

- Write `GHASH_CLOSE_N_TAC` once 2-block is done: 1–1.5 days. The
  biggest sub-piece is `COLLAPSE_PMUL_DUPLICATES_TAC`; the others are
  mechanical templating.
- Each subsequent N-block proof thereafter: ~2–3 days total
  (assembly extraction + `ARM_STEPS_TAC` simulation + one-line call
  `GHASH_CLOSE_N_TAC n`).
- 8-block bulk loop: separate project using the 8-block straight-line
  result as its loop-body lemma (induction on block count).

## Recommended order

1. 2-block hand-written (this plan's Phase 1–4).
2. 3-block hand-written — if it works *without* any new lemma,
   strong evidence the recipe parameterizes cleanly.
3. Extract `GHASH_CLOSE_N_TAC` from the common structure of 2- and
   3-block closures.
4. N = 4, 5, 6, 7 using the meta-tactic.
5. 8-block bulk loop induction proof.
