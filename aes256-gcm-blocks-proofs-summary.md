# AES-256-GCM Block Proofs — Summary

How the per-block AES-256-GCM "preloop-tail" proofs work, with a focus on the
**partial-final-block** generalization (handling any final block of 1..16 bytes
via the `bif` instruction).

There is one proof file per block count:
`arm/proofs/aes256_gcm_{one,two,three,four,five,six,seven}_block.ml`,
each verifying its own machine-code routine `arm/aes-gcm/aes256_gcm_<N>_block.S`.
Shared infrastructure lives in `arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml`.

---

## 1. What each proof proves

For an N-block call: blocks `1..N-1` are full 16-byte blocks; the **last** block
is `byte_len` bytes with `1 <= byte_len <= 16`. So input length = `16*(N-1) + byte_len`.
Across N = 1..7 this covers every length from 1 to 112 bytes.

Each file proves one `ensures`-style theorem `<N>_BLOCKS_PRELOOP_TAIL_CORRECT`:
"starting from a precondition state, executing the code reaches the postcondition
state, changing only what `MAYCHANGE` permits."

---

## 2. Specifications used (the layering)

The spec is **layered**; only the top layer knows about partial blocks.

| Layer | Model | Defined in | Changed for masking? |
|-------|-------|-----------|----------------------|
| AES keystream | `aes256_block_enc ivec rk0..rk14` | `utils/aesv8_gcm_1block_enc_256_spec.ml` | **No** — always a full 128-bit block |
| GHASH arithmetic | `ghash_Nblock_karatsuba` (assembly shape) ↔ `ghash_polyval_acc` (clean spec), bridged by `GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC` | per-N file + framework | **No** — takes opaque 128-bit block inputs |
| Ciphertext / mask / store | the **main theorem's** pre/postconditions | per-N file | **Yes** |

The masking lives entirely in the main theorem statement:

```
let ct_N  = word_xor pt_N (aes256_block_enc (gcm_ctr_inc^(N-1) ivec) rk0..rk14)
let mask  = word (2 EXP (8 * byte_len) - 1) : (128)word
let ctm_N = word_and ct_N mask
...
read (memory :> bytes128 (out_ptr + 16*(N-1))) s =
  word_or ctm_N (word_and out0 (word_not mask))            (* the bif store *)
read (memory :> bytes128 xi_ptr) s =
  word_reversefields 8 (ghash_polyval_acc h (reversefields xi)
                          [reversefields ct_1; ...; reversefields ctm_N])
```

Per-N partial-block spec changes versus the original full-block proof:
- new parameter `out0` + precond `read (memory :> bytes128 (out_ptr+16*(N-1))) = out0`
  (names the original output bytes the `bif` preserves);
- `byte_len` parameter and `1 <= byte_len /\ byte_len <= 16`;
- argument length `word (128*(N-1) + 8*byte_len)` (was `word (128*N)`);
- `PC` postcondition `+4` (the `bif` adds one instruction);
- `X0` return `word (16*(N-1) + byte_len)`;
- last store and last GHASH element use the masked block `ctm_N`.

Everything else (AES model, GHASH model and its correctness bridge) is reused
**unchanged** — this is why the work was mechanical across N.

---

## 3. Proof skeleton (what the tactics do to the goal)

The goal is an `ensures` triple. The proof symbolically executes the code one
instruction at a time, turning machine state into HOL assumptions, then matches
the final state against the postcondition.

1. **Setup**: `ENSURES_INIT_TAC "s0"` — introduce the initial state `s0`.
2. **Prologue + AES rounds**: `ARM_STEPS_TAC EXEC (1--k)` steps instructions;
   `GCM_ENC_SIMPLIFY_TAC` keeps the growing assumption set readable.
3. **Abbreviate AES outputs**: `s13_i` (round-13 result) and `ct_i` get named
   via `ABBREV_TAC`, so later terms stay small.
4. **Tail dispatch**: `GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC` normalizes the
   length comparison; then the cascade is resolved (see §5).
5. **Ciphertext stores**: each `ct_i` written to memory.
6. **Mask collapse** (partial-block): before the masking instructions, the
   data-dependent mask register is rewritten to `word (2^(8*byte_len)-1)`.
7. **GHASH Karatsuba + reduce**: the `pmull`/`eor3` sequence is simulated;
   `GCM_NBLOCK_POST_SIM_NORMALIZE_TAC` tidies up.
8. **Final reduction**: `ABBREV_FINAL_XI_TAC` names the reduced accumulator
   `final_xi` **before** the `rev64`/byte-explosion, keeping the term small.
9. **Epilogue**: step to just before `RET` (PC at the RET address).
10. **Close**: `ENSURES_FINAL_STATE_TAC`, then discharge each postcondition
    conjunct (PC, X0, each ciphertext store, GHASH).

---

## 4. Shared tactics (in `gcm_aesgcm_nblock_helpers.ml`) and what they change

| Tactic | Effect on the goal |
|--------|--------------------|
| `GCM_ENC_SIMPLIFY_TAC` | Simplifies/normalizes assumptions after each AES step (folds word ops, discards stale state) so terms don't blow up. |
| `GCM_NBLOCK_POST_AES_NORMALIZE_TAC` | After AES, rewrites the keystream/`reversefields` assumptions into the canonical shape the closers expect. |
| `GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC` | Normalizes the `word_sub`/flag terms produced by the `cmp` at the tail dispatch. |
| `GCM_NBLOCK_POST_SIM_NORMALIZE_TAC` | Post-simulation cleanup (stack-pointer arithmetic, `WORD_AND_MASK`, subword folds, pmul normalization). |
| `ABBREV_FINAL_XI_TAC` | Abbreviates the reduced GHASH accumulator (`read Q19 = ...`) as `final_xi` to avoid the byte-level explosion the trailing `rev64` would cause. |
| `GCM_NBLOCK_CT_STEP_TAC N k` | Closes the "block k ciphertext store" conjunct: proves `ct_k = pt_k ⊕ aes256(gcm_ctr_inc^(k-1) ivec, …)`. |

---

## 5. The partial-block additions (the masking work)

### Shared lemmas added to `gcm_aesgcm_nblock_helpers.ml`
- `NBLOCK_WORD_INSERT_BOTH_LANES` — collapses the two `ins` lane-writes that
  build the mask register into a single `word_join`.
- `NBLOCK_MASK_REG` (+ `nblock_cases16` / `NBLOCK_MASK_PEEL_TAC`) — proves the
  data-dependent mask register the hardware builds (`and #127; sub #128; neg;
  lsrv; csel; csel; ins`) equals `word (2^(8*byte_len) - 1)`. Proved by peeling
  the 16 values of `byte_len` one at a time (a single 16-way `ARITH_RULE` hangs).
- `NBLOCK_MASK_IDEM` — `word_and (word_and ct mask) mask = word_and ct mask`
  (the `bif` applies `mask` again to an already-masked store; idempotent).
- `NBLOCK_USHR_BYTELEN` — `total_bytes <= 127 ==> word_ushr (word (8*total)) 3 =
  word total` (recovers the block/byte count `X0` from a bit length).
- `NBLOCK_IVAL_WORD_SMALL` — `n < 2^63 ==> ival (word n) = &n` (bridges the
  signed branch condition to plain integer arithmetic).

### Per-N lemmas, derived in each file from the shared ones
- `<N>BLOCK_USHR` — instance of `NBLOCK_USHR_BYTELEN` for prefix `128*(N-1)`.
- `<N>BLOCK_MASK_REG` — instance of `NBLOCK_MASK_REG` with inner length
  `128*(N-1) + 8*byte_len`.
- `IVAL_WORD_SUB_SMALL`, `<N>BLOCK_GT_COND`, `<N>BLOCK_GT_COND_TRUE/FALSE`,
  `<N>BLOCK_CASCxx` — see §6.

### Where the masking changes the goal
- **In-simulation**: just before the `and`/`bif` store, the mask register
  (currently a big data-dependent term) is rewritten to
  `word (2^(8*byte_len)-1)` via `<N>BLOCK_MASK_REG`. This lets the rest of the
  simulation proceed symbolically.
- **At the masked GHASH closer** (`GCM_<N>BLOCK_GHASH_STEP_MASKED_TAC`): a copy
  of the original GHASH closer that additionally abbreviates `mask` and
  `ctm_N = word_and ct_N mask`, bridges `word_and mask ct_N = ctm_N`, and feeds
  `ctm_N` (not `ct_N`) into the GHASH bridge lemma. The underlying
  `ghash_Nblock_karatsuba` arithmetic and its correctness bridge are unchanged.
- **At the final store closer**: the postcondition store is
  `word_or (word_and (word_and mask ct_N) mask) (word_and out0 (word_not mask))`;
  `NBLOCK_MASK_IDEM` collapses the doubled mask, then it matches the spec's
  `word_or ctm_N (word_and out0 (word_not mask))`.

---

## 6. The newly defined cascade tactic — why it exists

In a multi-block routine the tail dispatch is a **cascade** of
`cmp x5, #16k; b.gt more_than_k`. With a symbolic `byte_len`, stepping a `b.gt`
leaves the PC as an unresolved `if <signed-gt condition> then word(pc+a) else
word(pc+b)`, and `ARM_STEPS_TAC` **cannot continue** until the PC is a concrete
address. (With the old full-block proofs `byte_len` was concrete, so the
simulator resolved each branch itself.)

To resolve each branch we prove and apply:
- `<N>BLOCK_GT_COND` : the hardware signed-greater-than condition for threshold
  `t` is equivalent to the plain numeric test `t < 16*(N-1) + byte_len`
  (proved via `IVAL_WORD_SUB_SMALL` + `VAL_EQ_0`/`IVAL_EQ_0` + integer arith).
- `<N>BLOCK_GT_COND_FALSE` (thresholds `> 16*(N-1)`: not taken) and
  `<N>BLOCK_GT_COND_TRUE` (threshold `= 16*(N-1)`: taken), plus literal-threshold
  instances `<N>BLOCK_CASC96/80/...`.
- `<N>BLOCK_CASCADE_TAC` : after each cascade step, rewrites every threshold's
  condition to its truth value and applies `COND_CLAUSES`, collapsing the
  if-then-else PC to a concrete `word(pc+offset)` so stepping can continue.

It is interleaved with the cascade simulation steps:
`ARM_STEPS_TAC EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC THEN <N>BLOCK_CASCADE_TAC`.
`CASCADE_TAC` is a no-op when the PC is already concrete, so over-covering a
range of steps is safe — needed because the taken branch can land a few
instructions inside the next code region.

---

## 7. Key gotchas (recorded for reuse)

- **Stop before `RET`.** Step to the last instruction *before* the `RET`; the
  postcondition PC is the RET's own address. Stepping the `RET` branches the PC
  away and destroys the `read PC = word(pc+offset)` fact.
- **MASK_REG lane width is 64, always.** When generating a per-N lemma block by
  substituting the cascade threshold (`word t`), never let that substitution
  touch the `(0,64)/(64,64)` lane widths or the `word 64` inside `MASK_REG`
  (the 64-bit lane split is independent of N).
- **`bif` is a memory-store fixup, not arithmetic.** It writes the *store*
  register; the GHASH path consumes the masked block from a different register
  produced earlier. That separation is why `aes256_block_enc` and
  `ghash_Nblock_karatsuba` needed no changes.

---

## 8. Combined single-binary branch lemmas (`arm/proofs/aes256_gcm.ml`)

The sections above cover the per-block files. The **combined** proof
`arm/proofs/aes256_gcm.ml` verifies one binary `aes256_gcm_mc` that dispatches
on input length into per-length-band branches. It adds its own family of small
arithmetic side-lemmas (all gated on `1 <= byte_len /\ byte_len <= 16`, or just
the upper bound) to resolve the entry/guard/cascade branches. Each is consumed
by a named `GCM_*_TAC` driver.

### 8.1 Simulation / discharge combinators

| Name | Type | What it does |
|------|------|--------------|
| `GCM_BOUNDS` | `thm` | The reassembled precondition `1 <= byte_len /\ byte_len <= 16` (built by `CONJ (ASSUME ..) (ASSUME ..)`), so it can be fed to `MATCH_MP`. |
| `GCM_RUN a b` | `tactic` | `ARM_STEPS_TAC` steps `a..b`, running `GCM_ENC_SIMPLIFY_TAC` after each step to keep terms small. |
| `GCM_RUN_THEN extra a b` | `tactic` | Like `GCM_RUN` but also runs `extra` after each step (e.g. a branch-cascade resolver). |
| `GCM_BND lemma` | `thm -> tactic` | Fires `lemma : ⊢ (1<=byte_len /\ byte_len<=16) ==> P` via `MATCH_MP ... GCM_BOUNDS`, then `RULE_ASSUM_TAC(REWRITE_RULE[P])` pushes `P` into every assumption. Used for the cbz / in-loop guards. |
| `GCM_BND16 lemma` | `thm -> tactic` | Upper-bound-only sibling: fires `lemma : ⊢ byte_len<=16 ==> P` against `ASSUME \`byte_len<=16\``, then rewrites all assumptions with `P`. Used to collapse tail-length registers. |

### 8.2 Branch-resolution side-lemmas

All proved with the same rhythm: a chain of
`SUBGOAL_THEN <piece = simpler> SUBST1_TAC THENL [prove; ALL_TAC]` peeling the
nested word term layer by layer, with bound side-conditions discharged by
`ASM_ARITH_TAC`, and a final `WORD_RULE` / `INT_ARITH_TAC` close.

| Lemma | Statement (gist) | Resolves |
|-------|------------------|----------|
| `GCM_CBZ_LEMMA` | `1<=byte_len<=16 ==> ~(val(word(8*byte_len):int64) = 0)` | Entry `cbz x1` (bit_len ≠ 0, so not taken — fall through). Proof: `VAL_WORD_EQ` says `val(word n)=n` when `n<2^64`, then `ASM_ARITH_TAC`. |
| `GCM_WSUB1` | `1<=n<=16 ==> word_sub (word n) (word 1) = word(n-1)` | A length-register decrement. Modular `word_sub` = truncated `num` `-` only without underflow; `WORD_SUB` + `COND_CASES_TAC` (the underflow branch is vacuous). |
| `GCM_ANDMASK0` | `m<128 ==> word_and (word m) (word 0xFF..F80) = word 0` | Small value AND high-mask (`~0x7F`) = 0 (no high bits set). `WORD_AND_NOT_MASK_WORD` reduces it to `word(128*(m DIV 128))`, then `m DIV 128 = 0`. |
| `GCM_X5_LEMMA` | `1<=byte_len<=16 ==> word_add (word_and (word_sub (word_ushr (word(8*byte_len)) 3) (word 1)) 0xFF..F80) in_ptr = in_ptr` | In-loop guard: X5 = main-loop **end pointer** = `in_ptr + (block-aligned byte offset)` collapses to `in_ptr` (no full 128-byte chunks), so `cmp x0,x5` is equal and `b.ge` into the tail is taken. Composes `NBLOCK_USHR_BYTELEN` + `GCM_WSUB1` + `GCM_ANDMASK0`, then `WORD_RULE`. **(Rename recommended: `GCM_LOOP_END_EQ_INPTR_1BLOCK` — see TODO.)** |
| `GCM_X5TAIL_LEMMA` | `byte_len<=16 ==> word_sub (word_add in_ptr (word_ushr (word(8*byte_len)) 3)) in_ptr = word byte_len` | Tail length: `(in_ptr + byte_len) - in_ptr = byte_len`; pointer arithmetic cancels (universal), only the `ushr` step needs a bound. `NBLOCK_USHR_BYTELEN` + `WORD_RULE`. *(Bound is non-fundamental — the cancellation holds for any length; see TODO to generalize + dedup the `2..6` band variants.)* |
| `GCM_CASC_FALSE` | `byte_len<=16 /\ 16<=t /\ t<=112 ==> (<signed-gt flag predicate for t> <=> F)` | Each tail-cascade `cmp x5,#t; b.gt` (t = 16..112) is **not** taken, so control falls through all multi-block tails to the `less_than_1` masked tail. Strategy: escape modular-word/flag land into ℤ (`NBLOCK_IVAL_WORD_SMALL`, `iword`/`ival` round-trips via `IVAL_IWORD`), then `INT_ARITH_TAC` (one fact, ∀`t`, kills all 7 thresholds). |

### 8.3 Branch-driver tactics

| Tactic | What it does |
|--------|--------------|
| `GCM_INIT_TAC cbz_lemma` | Entry boilerplate: unfold the triple, `REPEAT STRIP_TAC`, `ENSURES_INIT_TAC "s0"`, step the nop+cbz (1–2), discharge the cbz guard with the band's `cbz_lemma` via `GCM_BND`. |
| `GCM_PROLOGUE_TAC` | Shared stack/frame setup (steps 3–19) + offset-arithmetic folding. |
| `GCM_INLOOP_GUARD_TAC x5_lemma` | Step the in-loop guard and collapse X5 via `GCM_BND x5_lemma` so `b.ge` is taken. |
| `GCM_CASCADE_TAC` | Per-step cascade resolver. Finds the `byte_len<=16` assumption (`FIRST_X_ASSUM`), programmatically builds the 7 `GCM_CASC_FALSE` instances (`MATCH_MP` + `CONJ` + `ARITH_RULE`-generated `16<=t`/`t<=112` facts for `t∈{16,32,..,112}`), then `RULE_ASSUM_TAC(REWRITE_RULE(those @ [COND_CLAUSES]))` rewrites each pending `b.gt` test to `F` and collapses the `if` PC to its fall-through. No-op when no bound assumption is present. |

Each length band also carries numbered variants (`GCM_CBZ_LEMMA2..5`,
`GCM_X5_LEMMA2..5`, `GCM_X5TAIL_LEMMA2..6`, `GCM_X6TAIL_LEMMA6`, …) — same
shapes, bounds/registers retuned per band.

---

## 9. File inventory

- `arm/aes-gcm/aes256_gcm_<N>_block.S` — routine with the `bif` uncommented.
- `arm/proofs/aes256_gcm_<N>_block.ml` — partial-block spec + proof.
- `arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml` — shared step/normalize
  tactics, the N-block GHASH framework, and the shared partial-block lemmas
  (`NBLOCK_MASK_REG`, `NBLOCK_MASK_IDEM`, `NBLOCK_USHR_BYTELEN`,
  `NBLOCK_IVAL_WORD_SMALL`, `NBLOCK_WORD_INSERT_BOTH_LANES`).
