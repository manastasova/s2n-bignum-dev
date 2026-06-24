# N-Block AES-GCM `preloop_tail` Proofs — Development Strategy

This document describes how the family of AES-256-GCM `preloop_tail`
correctness proofs (`one_block` … `eight_blocks`) is built. Each proof shows
that the hand-written AArch64 routine that encrypts `N` 16-byte blocks and
folds them into the running GHASH accumulator computes exactly the functional
spec `ghash_polyval_acc` (plus AES-CTR ciphertext). The proofs are HOL Light
files verified against the `.o` object code via the s2n-bignum symbolic
simulator.

The series was developed incrementally: each `N` reuses the structure of
`N-1`, so the per-block delta is small and largely mechanical. This document
captures both the **artifacts** produced for each `N` and the **recipe** for
producing the next one.

---

## 1. Artifacts per block count

For each `N` ∈ {1,…,8} there are (up to) four artifacts:

| Artifact | Path | Purpose |
|---|---|---|
| Assembly | `arm/aes-gcm/<N>_blocks_aes256_gcm_preloop_tail.S` | The routine, specialized from the full 8-wide unrolled kernel |
| Object | `arm/aes-gcm/<N>_blocks_aes256_gcm_preloop_tail.o` | Assembled machine code the proof is checked against |
| Proof | `arm/proofs/aes256_gcm_<N>_block.ml` | Spec + bridge lemmas + main correctness theorem |
| Companion | `arm/proofs/<N>_blocks_aes256_gcm_preloop_tail_proof.ml` | Bridge to the standard `ghash_polyval_acc` init-0 form |
| Test | `arm/aes-gcm/test_<N>_blocks_preloop_tail.c` | Runtime cross-check against aws-lc EVP AES-256-GCM |

(`one`/`two`/`three`/`four` are the older entries; `five`/`six`/`seven` are the
clean template instances; `eight` is the special full-width case — see §7.)

---

## 2. The assembly: specialize the 8-wide kernel

All `.S` files derive from one fully-unrolled 8-block kernel
(`arm/aes-gcm/aesv8_gcm_8x_enc_256.S`, itself from aws-lc's
`aesv8-gcm-armv8-unroll8.pl`). The N-block routine is that kernel with the
unused blocks **commented out**. Going from `N-1` to `N` blocks means
*uncommenting* the work for one more block:

1. **Block `N-1`'s AES rounds** — the 27 `aese`/`aesmc v(N-1)` lines (rounds
   0–13) in the pre-loop. The round-key cycle (`v26,v27,v28,v26,…`) is
   identical for every block, so this is a pure copy of the previous block's
   pattern on the next vector register.
2. **Block `N-1`'s `eor3` result** — the single `.inst 0xce..71..` line that
   XORs the AES output with the final round key.
3. **The `.L256_enc_blocks_more_than_(N-1)` GHASH stage** — the ~14-line block
   that stores the ciphertext, byte-reverses, feeds the partial tag, and does
   the Karatsuba `pmull`/`pmull2`/mid accumulation against `h^N`.
4. **The `h^N` H-table load** — uncomment the dead `ldp`/`ldr [x6,#…]` that
   brings the needed power and its Karatsuba "mid" into a vector register.

The dispatch is a fall-through cascade of `cmp x5,#16·k; b.gt more_than_k`
guards; for `N` blocks the runtime byte count selects the `more_than_(N-1)`
entry. **Build & sanity:**

```
sed -e 's|//.*||' file.S | aarch64-linux-gnu-gcc -E -I../../include \
  -xassembler-with-cpp - | tr ';' '\n' \
  | aarch64-linux-gnu-as -march=armv8.2-a+sha3 -o file.o
```

Confirm the instruction count grows by ~44 per block (14 `aese` + 13 `aesmc` +
1 `eor3` + 3 `pmull` + stores/loads) and that `aese` = `14·N`, `aesmc` = `13·N`.

**Validate immediately with the C test** (compile the `.S` + a test harness,
run on aarch64, compare ciphertext **and** GHASH tag against aws-lc EVP for
several key/nonce/plaintext vectors). The test is the fastest arbiter that the
assembly is correct *before* investing in the proof.

---

## 3. The proof file structure (the template)

The clean template (`five`/`six`/`seven`) lays out the file in this fixed
order. Each piece is the **only** per-N content; everything generic is
imported from `arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml`,
`arm/proofs/utils/gcm_aesgcm_helpers.ml`, and `common/ghash_spec.ml`.

```
header + needs
ghash_Nblock_karatsuba           (new_definition)  -- assembly-shape spec
GHASH_NBLOCK_AS_NBLOCK           (prove)           -- = generic ghash_Nblock_karatsuba
GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC (prove)      -- the bridge to polyval_reduce_prop3
GHASH_POLYVAL_ACC_N              (prove)           -- list-form GHASH = explicit pmul xor
POLYVAL_DOT_H4_EQ_LOCAL, H5_EQ, …(prove)           -- h-power associativity normalizers
INSERT_IDEM, INSERT_SUBWORD      (prove)           -- counter-insert word lemmas
<N>_blocks_prelooptail_mc        (define_assert_from_elf)  -- the machine code blob
<N>_BLOCKS_PRELOOP_TAIL_EXEC     (ARM_MK_EXEC_RULE)
GCM_CT1..CTN_STEP_TAC            (let tactics)     -- per-block ciphertext closures
bubble_sort_conv + helpers       (let)             -- XOR-AC canonicalizer
GCM_NBLOCK_GHASH_STEP_TAC        (let tactic)      -- the GHASH-conjunct closer
<N>_BLOCKS_PRELOOP_TAIL_CORRECT  (prove)           -- the main Hoare triple
```

### Key mathematical content

* **`ghash_Nblock_karatsuba`** mirrors the assembly: for each block `i`
  (1-indexed) it does a 64×64 Karatsuba product against `h^(N+1-i)`
  (`pl = b_lo·h_hi`, `ph = b_hi·h_lo`, `pm = (b_lo⊕b_hi)·hk_lo`), folds the `N`
  block results, then a 2-step Barrett reduction with the constant
  `word 13979173243358019584`, and returns `word_reversefields 8 (word_join g f)`.

* **The bridge** `GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC` proves the assembly
  reducer equals `word_reversefields 8 (polyval_reduce_prop3 (Σ word_pmul bᵢ hᵏ))`,
  given the Karatsuba-mid hypotheses on the H-table words. It is derived
  uniformly from the inductive `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` by building the
  `project_triples` quad list and discharging with `ASM_REWRITE` +
  `CONV_TAC WORD_RULE`.

* **Symmetric h-powers.** `GHASH_POLYVAL_ACC_N` emits *left-associated*
  powers `(((h·h)·h)·…)`, but the bridge needs the *symmetric* forms the
  assembly's H-table actually holds:
  - h² = `h·h`
  - h³ = `h·(h·h)`
  - h⁴ = `(h·h)·(h·h)`
  - h⁵ = `((h·h)·(h·h))·h`
  - h⁶ = `(((h·h)·(h·h))·h)·h`   (= h⁵·h), etc.
  `POLYVAL_DOT_H4_EQ_LOCAL` is the one non-trivial ring-algebra proof (via
  `MOD_POLYVAL_*` / `POLYVAL_DOT_CORRECT`); every higher `POLYVAL_DOT_Hk_EQ`
  follows trivially by congruence (`REWRITE_TAC[POLYVAL_DOT_H(k-1)_EQ]`).

---

## 4. Theorem dependency graph

Read `A` depends-on `B` top-to-bottom: each box is built using the boxes
indented below it. Tags: `[per-N]` = regenerated for each block count,
`[shared]` = proven once in `utils/` or `common/ghash_spec.ml`, `[tactic]` =
proof machinery (not a theorem).

The whole proof is two halves joined at one tactic. Read the tree top-down:

```
<N>_BLOCKS_PRELOOP_TAIL_CORRECT                                  [per-N]
|   the main theorem: a Hoare triple over the N-block .o
|   "running the code leaves ghash_polyval_acc(...) at xi_ptr"
|
+-- (A) EXECUTION SIDE -- symbolic simulation of the machine
|   |
|   +-- <N>_BLOCKS_PRELOOP_TAIL_EXEC                             [per-N]
|   |   +-- <N>_blocks_prelooptail_mc  (define_assert_from_elf : the .o)
|   |
|   +-- simulation tactics                                      [tactic, utils]
|   |   ARM_STEPS_TAC, GCM_ENC_SIMPLIFY_TAC,
|   |   POST_AES / TAIL_DISPATCH / POST_SIM_NORMALIZE_TAC,
|   |   ABBREV_FINAL_XI_TAC
|   |
|   +-- GCM_CT1_STEP_TAC .. GCM_CTN_STEP_TAC                     [tactic]
|       (close the N ciphertext conjuncts)
|       +-- INSERT_IDEM, INSERT_SUBWORD                          [per-N]
|
+-- (B) MATH SIDE -- the GHASH conjunct closer
    |
    +-- GCM_NBLOCK_GHASH_STEP_TAC                                [tactic]
        |   <<< THE JOIN: this is where (A) meets (B). >>>
        |   It folds the simulated state into ghash_Nblock_karatsuba,
        |   then rewrites it to the spec using the bridge.
        |
        +-- GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC   (★ THE BRIDGE) [per-N]
        |   |   "the code's Karatsuba bit-twiddling = the GHASH polynomial"
        |   |
        |   +-- GHASH_NBLOCK_AS_NBLOCK                            [per-N]
        |   |   +-- ghash_Nblock_karatsuba (per-N spec, new_definition) [per-N]
        |   |   +-- ghash_Nblock_karatsuba (generic, list-indexed)  [shared]
        |   |       kara_acc, karatsuba_block_pl/ph/pm, karatsuba_reduce_shared
        |   |
        |   +-- GHASH_NBLOCK_KARATSUBA_EQ_PROP3                   [shared]
        |   |   the generic INDUCTIVE bridge (proven once, over a list)
        |   |   +-- karatsuba_mid, byteswap128, word_reversefields [shared]
        |   |   +-- polyval_dot, polyval_reduce_prop3             [shared]
        |   |
        |   +-- project_triples, kara_quad_ok, kara_quad_pmul    [shared]
        |
        +-- GHASH_POLYVAL_ACC_N                                  [per-N]
        |   "list-form GHASH = explicit sum of word_pmul terms"
        |   +-- GHASH_POLYVAL_ACC_BATCHED                        [shared]
        |   |   +-- ghash_polyval_acc   (THE FUNCTIONAL SPEC)    [shared]
        |   +-- h_power, ghash_wide                              [shared]
        |
        +-- POLYVAL_DOT_H4_EQ_LOCAL -> H5_EQ -> H6_EQ -> ...     [per-N]
        |   symmetric h-power normalizers (each derives from the previous)
        |   +-- POLYVAL_DOT_CORRECT, MOD_POLYVAL_*               [shared]
        |       (bool_poly ring algebra; the one hard algebraic proof)
        |
        +-- bubble_sort_conv (+ word_xor_left_comm, etc.)       [tactic]
            XOR-AC canonicalizer for the final big equalities
```

The two ideas to take away:

1. **Only the `[per-N]` boxes are regenerated** for each block count; every
   `[shared]` box is proven once and reused. So the per-N work is the spec, its
   `AS_NBLOCK` equivalence, the bridge instance, `GHASH_POLYVAL_ACC_N`, the
   h-power lemmas, the `.o`/EXEC, and the main theorem.

2. **`GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC` (the bridge, ★)** is the contract
   between the two halves. Side (A) proves "the machine ends up holding the
   Karatsuba expression"; the bridge proves "that expression *is* GHASH"; and
   `GCM_NBLOCK_GHASH_STEP_TAC` is the single tactic that invokes the bridge to
   join them. Neither half can close the goal alone.

(Each per-N bridge is itself just a thin specialization of the one generic,
inductive `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` — that is where the genuinely hard
"bit-twiddling = polynomial" reasoning is done, once.)

---

## 5. Proven-once vs proven-per-N, and the equivalence hops

### Proven ONCE (shared, reused by every block count)

* `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` — the inductive bridge "generic Karatsuba
  reducer = polyval polynomial" (induction over the block list; covers all N).
* `GHASH_POLYVAL_ACC_BATCHED` — inductive "list-GHASH = Horner/pmul sum."
* The GF(2^128) algebra: `POLYVAL_DOT_CORRECT`, the `MOD_POLYVAL_*` family.
* The generic spec `ghash_Nblock_karatsuba` (+ `kara_acc`, `karatsuba_block_*`)
  and list plumbing (`project_triples`, `kara_quad_ok`, `kara_quad_pmul`).
* The AES model (`aes256_block_enc` lemmas), the simulator framework
  (`ARM_STEPS_TAC`, …), and all shared word lemmas / `bubble_sort_conv`.

These contain all the genuinely hard reasoning. They are never re-proven.

### Proven (or generated) EACH time a new N is added

* `ghash_<N>block_karatsuba` — positional spec (a `new_definition`).
* `GHASH_<N>BLOCK_AS_NBLOCK` — arity adapter (cheap `REWRITE`+`BETA`).
* `GHASH_<N>BLOCK_KARATSUBA_EQ_POLYVAL_ACC` — per-N correctness bridge; a thin
  `SPEC` of the shared `…_EQ_PROP3` at the concrete N-element list.
* `GHASH_POLYVAL_ACC_N` — fixed-length unrolling of `…_BATCHED` (imported N<=4,
  proved locally N>=5).
* The `.o` blob `<N>_blocks_prelooptail_mc` + its `EXEC` rule.
* The closure tactics `GCM_CT1..CTN_STEP_TAC`, `GCM_<N>BLOCK_GHASH_STEP_TAC`.
* `<N>_BLOCKS_PRELOOP_TAIL_CORRECT` — **the only expensive item**: a fresh
  symbolic-execution proof of the new `.o` (per-N step ranges, s13/ct abbrevs,
  N-way conjunction). Unavoidable because the code is branchless/unrolled —
  no loop to induct over, so each program is verified on its own.

Rule of thumb: everything per-N except the main theorem is a cheap
**specialization** of a shared theorem; the main theorem is where the work is.

### The equivalence sequence (the "spec hops") and the tactic for each `=`

Reading top-to-bottom, each line equals the next; the label is the lemma/tactic
that proves that single `=`:

```
read (memory :> bytes128 xi_ptr) s_final          (what the .o leaves in memory)
  =   [ main theorem: ENSURES_INIT_TAC, ARM_STEPS_TAC, GCM_ENC_SIMPLIFY_TAC,
        ABBREV_FINAL_XI_TAC, ENSURES_FINAL_STATE_TAC ]   (symbolic execution)
ghash_<N>block_karatsuba b1 .. bN ..               (positional per-N spec)
  =   [ GHASH_<N>BLOCK_AS_NBLOCK, applied GSYM inside GCM_<N>BLOCK_GHASH_STEP_TAC;
        proved by REWRITE_TAC[defs] + DEPTH_CONV BETA_CONV + WORD_XOR_ASSOC ]
ghash_Nblock_karatsuba [(b1,..);..;(bN,..)]        (generic spec @ N-list)
  =   [ GHASH_<N>BLOCK_KARATSUBA_EQ_POLYVAL_ACC, via MP_TAC(SPECL <list> ...) ;
        that lemma's own proof = SUBST project_triples + MP_TAC(SPEC <list>
        GHASH_NBLOCK_KARATSUBA_EQ_PROP3) + ASM_REWRITE + AP_TERM + WORD_RULE ]
word_reversefields 8 (polyval_reduce_prop3 (b1·h^N (+) .. (+) bN·h))
  =   [ GHASH_POLYVAL_ACC_N (REWRITE) ; + POLYVAL_DOT_Hk_EQ normalizers to put
        h-powers in symmetric form so both sides match ]
ghash_polyval_acc h xi [ct1; ..; ctN]              (functional spec)   QED
```

The middle two hops are the "spec hops": **positional spec -> list spec**
(`AS_NBLOCK`, pure repackaging) and **list spec -> polynomial**
(`KARATSUBA_EQ_POLYVAL_ACC`, the specialized inductive bridge). The first hop is
the symbolic-execution proof; the last is the Horner unrolling. The whole chain
is stitched together inside one tactic, `GCM_<N>BLOCK_GHASH_STEP_TAC`, after the
ciphertext conjuncts are closed by `GCM_CTk_STEP_TAC`.

---

## 6. The GHASH STEP tactic

`GCM_NBLOCK_GHASH_STEP_TAC` closes the single hardest conjunct — that the
stored `xi` equals the `ghash_polyval_acc` spec. It always has the same phases:

1. `REWRITE` with `GHASH_POLYVAL_ACC_N`, the `POLYVAL_DOT_Hk_EQ` normalizers,
   and `GSYM WORD_REVERSEFIELDS_XOR_8_128`.
2. **Fold the AES outputs to `ctk`:** N `SUBGOAL_THEN` blocks rewriting
   `word_xor ptk (aes256_block_enc (gcm_ctr_inc^{k-1} ivec) …) = ctk`. Block 1
   is trivial; blocks ≥3 unfold the iterated counter via `LANE*_BYTES_JOIN`,
   `CTR_WORD_INSERT`, `BYTEREVERSE_JOIN_FOLD`, `INSERT_SUBWORD`, `INSERT_IDEM`.
3. Normalize the remaining left-assoc h⁴/h³ to symmetric form.
4. Apply the bridge `MP_TAC(SPECL […] GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC)`;
   discharge the `word_join (word 0) (subword hk …)` Karatsuba-mid antecedents
   with `WORD_BLAST`.
5. Unfold `ghash_Nblock_karatsuba`, `BETA`, clean up `byteswap128`/`word_join`/
   `karatsuba_mid` subwords.
6. Strip the outer `word_reversefields 8 _` via a `MATCH_MP_TAC` congruence,
   then expand the abbreviated `final_xi`.
7. **Abbreviate and bubble-sort.** Introduce ABBREVs for the atoms
   (`c1lo..cNhi`, `xilo/xihi`, the h-power lo/hi pairs), the inner pmuls
   (`w1lo/w1hi/w1md..wNmd`), and their lo/hi halves (the z-vars). Then the two
   final XOR-AC equalities (each ~`(N·3)+` atoms) are closed with
   `CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC`.

`bubble_sort_conv` is a string-lexicographic bubble sort over `word_xor` chains.
It is necessary because `WORD_BITWISE_RULE` blows up exponentially past ~17–21
atoms (it is fine and simpler at small N, hence 2-block uses plain `WORD_RULE`
and 3-block historically used `WORD_BITWISE_RULE`).

**Type-annotation gotcha (cost a full debugging session at N=5):** every atom
in a `word_pmul (word_xor a (word_xor b …)) const` literal must carry an
explicit `:(64)word` on at least the first atom of each XOR chain. Because
`word_pmul`'s result type does not back-infer its argument type, an
un-annotated chain parses as a polymorphic `(?)word`, the `ABBREV_TAC`
silently fails to abstract, and a later `AP_TERM_TAC` fails far downstream.
Annotate the head atom; `word_xor` propagates the type through the chain.

---

## 7. The main theorem (interactive simulation)

The Hoare triple is proved by symbolic execution. The shape is identical for
every N; only step ranges and counts change:

```
REWRITE_TAC[C_ARGUMENTS; … fst <N>_BLOCKS_PRELOOP_TAIL_EXEC] THEN
REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
ARM_STEPS_TAC … (1--19) THEN          (* prologue *)
… RULE_ASSUM_TAC[STACK_PTR_CANCEL; …] THEN GCM_ENC_SIMPLIFY_TAC THEN
MAP_EVERY (step + GCM_ENC_SIMPLIFY) (20--AESEND) THEN   (* AES for all N blocks *)
abbrev s13_1..s13_N from Q0..Q(N-1) THEN               (* round-13 outputs *)
ABBREV ct1 THEN POST_AES_NORMALIZE THEN TAIL_DISPATCH_NORMALIZE THEN
RULE_ASSUM_TAC[2 EXP 64 restore] THEN
(cascade: step ranges + ABBREV ct2..ctN, each followed by 2 EXP 64 restore) THEN
GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN
(step the final Karatsuba reduce) THEN ABBREV_FINAL_XI_TAC THEN
ARM_STEPS_TAC … (epilogue, stop AT the ret) THEN
CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
ASM_REWRITE_TAC[] THEN
CONJ_TAC THENL [GCM_CT1_STEP_TAC; … ; GCM_CTN_STEP_TAC; GCM_NBLOCK_GHASH_STEP_TAC]
```

**Step-range discovery is the only genuinely per-N interactive work.** Develop
it live through the MCP server (never batch-load), reading the PC offset after
each chunk:

* **`AESEND` / s13 abbrev point** — step until PC reaches the block-result
  `eor3` for block 0, *just before* the dispatch register-shuffle. At that PC
  the registers `Q0..Q(N-1)` hold the N AES round-13 outputs in clean
  sequential order (verify by reading the counter-increment literal in each).
* **Cascade ct-abbrev boundaries** — step through `more_than_(N-1)` …
  `less_than_1`, abbreviating `ctk = word_xor (word_xor ptk s13_k) rk14` the
  moment each appears in a Q register, restoring `18446744073709551616 = 2 EXP 64`
  after each step so the ciphertext-store nonoverlapping checks pass.
* **`ABBREV_FINAL_XI`** — fire it right after the final `eor3` that forms the
  stored `v19`, *before* the `ext`/`rev64` consume it. The generic tactic
  matches `read Q19 s = x`.
* **Epilogue** — plain `ARM_STEPS_TAC` (no `GCM_ENC_SIMPLIFY`, which would
  re-expand `final_xi` into a ~100 KB term and hang the store). Stop at the
  `ret` instruction (its offset = the postcondition PC); executing past it
  makes the PC postcondition unprovable.

Postcondition constants scale predictably: `C_ARGUMENTS` length `word (128·N)`,
final `X0 = word (16·N)`, buffers `,(16·N)`, `nonoverlapping (word pc, BYTES)`
with BYTES a round figure above the `.o` size, and postcond PC = `word(pc + ret_offset)`.

---

## 8. Reproduction recipe for a new block count N

1. Build `<N>.S` by uncommenting block `N-1` from `<N-1>.S` (§2); assemble;
   **run the C test** — do not proceed until it passes all vectors.
2. Generate the proof file by scaling the `<N-1>` file with a small Python
   generator: bump the spec to `N` blocks/h-powers, the bridge to `N`
   hypotheses / a longer `project_triples` list / `N`-term pmul RHS, add
   `GHASH_POLYVAL_ACC_N` (tail list length `N-1`, `num_CONV` down to 1),
   `POLYVAL_DOT_H(N)_EQ`, copy `POLYVAL_DOT_H4_EQ_LOCAL`/`INSERT_*`/bubble_sort
   verbatim, embed the new `.o` byte list, add `GCM_CTN_STEP_TAC` (copy
   `CT(N-1)` with one more `gcm_ctr_inc`), and scale the GHASH STEP
   (`N` ct-folds, `(N+1)`-arg bridge SPECL with `hk=h1k, h2k=join(h1k.hi),
   h3k, h4k=join(h3k.hi), …`, `2(N+1)` atoms, `3N` pmuls, `6N` z-vars,
   N-term qS/qB). **Type-annotate every qB/qS atom `:(64)word`.**
3. Load the *static* portion first (everything before the GHASH STEP) to catch
   generation errors cheaply (~5 min).
4. Develop the main theorem interactively to discover the step ranges (§5);
   confirm the GHASH STEP closes; bake the ranges into the file.
5. Full clean reload (target < ~10 min); confirm 0 hypotheses, no `CHEAT_TAC`/
   `new_axiom`/`mk_thm`; load the companion file.

A new block typically lands in roughly one pass once N≥5, because the template
is stable and only the step ranges are unknown a priori.

---

## 9. Why 8 blocks is special

N=8 is the **native full width** of the unrolled kernel, so its tail is *not*
the "zero the accumulators, then XOR-accumulate, final `xi` ends up in `Q19`"
shape that N=1..7 share. The `more_than_7` stage *initializes* the GHASH
accumulators `v17/v18/v19` directly (it is the first block, not an
accumulate-into-zero), and the final reduced `xi` is not tracked in `Q19` at
the post-`eor3` point the generic `ABBREV_FINAL_XI_TAC` expects. Consequences:

* The `.S` tail-dispatch region must be replaced wholesale with the 8x
  reference's exact lines (with `cmp x5,#112; b.gt more_than_7` active), not
  just uncommented.
* The s13 registers are read straight from `Q0..Q7` (no pre-`cmp` shuffle).
* As of this writing the 8-block **assembly + C test + all proof scaffolding
  load and are proven**, but the main theorem is documented and commented out:
  it needs custom 8-wide final-reduce register bookkeeping to connect the
  stored `xi` to the spec.

N=1..7 are complete end-to-end (proven, no axioms; files load in ≈90 s–10 min).

---

## 10. Working practices that matter

* **Develop tactics live via the MCP server**, one step at a time, inspecting
  the goal state — never batch-load a half-finished proof. Backtracking and
  reading the PC after each chunk is how step ranges are found.
* **Generate the repetitive proof text with a script**, not by hand: the 22–34
  atom ABBREVs, 15–24 pmuls, 30–48 z-vars, and the byte list are far too
  error-prone to type. Check parenthesis/backtick balance programmatically.
* **The C test is the cheap oracle** — it catches assembly mistakes in seconds,
  long before the multi-minute proof load would.
* **Keep generic machinery in the `utils/` helpers**, per-N content in the
  per-N file. Resist re-proving shared lemmas locally unless the template
  genuinely needs a specialized instance (e.g. `GHASH_POLYVAL_ACC_N`).
