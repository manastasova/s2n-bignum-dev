# AES-256-GCM `preloop_tail` N-block Proofs — Methodology & Divergences from the 6-block Reference

**Scope.** The seven files
`aes256_gcm_{one,two,three,four,five,six,seven}_block.ml`
in `arm/proofs/`. Each proves `…_PRELOOP_TAIL_CORRECT` (functional correctness
of the N-block AES-256-GCM encrypt+GHASH tail) end-to-end, **no `CHEAT_TAC`, no
axioms**.

The **6-block file is the reference**. This document (1) states the shared
methodology, then (2) lists — per file — *every* point where the proof does not
strictly follow the 6-block pattern: tactics, lemmas, tactic order, theorems,
naming, and structure. All claims below were checked against the files directly.

Verified load times (fresh HOL Light process each, same machine):

| N | seconds | minutes |
|--:|--------:|--------:|
| 1 | 320.6 | 5.34 |
| 2 | 347.9 | 5.80 |
| 3 | 427.0 | 7.12 |
| 4 | 497.0 | 8.28 |
| 5 | 492.3 | 8.20 |
| 6 | 530.8 | 8.86 |
| 7 | 575.0 | 9.58 |

---

## 1. The shared methodology (what the 6-block reference does)

All files instantiate **one generic N-block framework** (`utils/gcm_aesgcm_nblock_helpers.ml`
+ `common/ghash_spec.ml`). The per-file content is only: the machine code, the
per-N Karatsuba spec, the per-N bridge lemma, the CT/GHASH tactics, and the main
theorem. Two layers:

### Layer A — symbolic ARM execution (the `ensures arm` triple)
In `…_PRELOOP_TAIL_CORRECT`, in this exact order (6-block line refs):

1. **Prologue** — `REWRITE_TAC[C_ARGUMENTS; MAYCHANGE…; SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst …_EXEC]`, `REPEAT STRIP_TAC`, `ENSURES_INIT_TAC "s0"`, `ARM_STEPS_TAC (1--19)`, then `RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS])`, `RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV)))`, `GCM_ENC_SIMPLIFY_TAC`. (L945–954)
2. **AES rounds** — `MAP_EVERY (fun n -> ARM_STEPS_TAC [n] THEN GCM_ENC_SIMPLIFY_TAC) (20--217)`. (L958–960)
3. **Abbreviate `s13_1..s13_N`** — six guarded `FIRST_ASSUM … ABBREV_TAC` reading `Q0..Q5` in order. (L963–980)
4. **`ct1` + dispatch normalize** — `ABBREV_TAC ct1`, then `GCM_NBLOCK_POST_AES_NORMALIZE_TAC`, `GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC`, then `RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE 18446744073709551616 = 2 EXP 64])`. (L982–985)
5. **Store/dispatch cascade** — one `MAP_EVERY` per block; **each `MAP_EVERY` re-applies the 2-EXP-64 restore inline** (`… THEN RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE …])`); `ABBREV_TAC ctK` between blocks. (L989–1011)
6. **Post-sim normalize + reduce** — `GCM_NBLOCK_POST_SIM_NORMALIZE_TAC`, then a final `MAP_EVERY` (with inline 2-EXP-64 restore) over the Barrett-reduce steps. (L1013–1019)
7. **`ABBREV_FINAL_XI_TAC`** — names Q19 as `final_xi` *before* the epilogue `ext`/`rev64` byte-explosion. (L1020)
8. **Epilogue** — single `ARM_STEPS_TAC (355--362)`, stop at the `ret`. (L1023)
9. **Finalize** — `CONV_TAC(TOP_DEPTH_CONV let_CONV)`, `ENSURES_FINAL_STATE_TAC`, `ASM_REWRITE_TAC[]`. (L1025–1026)
10. **(N+1)-way `CONJ_TAC THENL`** — `GCM_CT1..CTN_STEP_TAC` then `GCM_NBLOCK_GHASH_STEP_TAC`. (L1029–1047)

### Layer B — GHASH algebraic closure (`GCM_6BLOCK_GHASH_STEP_TAC`, L434)
1. `REWRITE_TAC[GHASH_POLYVAL_ACC_6; POLYVAL_DOT_H6_EQ; POLYVAL_DOT_H5_EQ; GSYM WORD_REVERSEFIELDS_XOR_8_128]`.
2. One `SUBGOAL_THEN` per block folding `ptK ⊕ aes256_block_enc(ctrK…) = ctK`.
3. `MP_TAC(SPECL […] GHASH_6BLOCK_KARATSUBA_EQ_POLYVAL_ACC)` (the per-N bridge), with `karatsuba_mid` subword side-goals.
4. Unfold `ghash_6block_karatsuba`; `BETA_CONV`; `BYTESWAP128_SUBWORD_LO/HI`.
5. **Abbreviate** in three tiers: atomic limbs `cKlo/cKhi, xilo/xihi, hd/he/hf/hg/hh` (named `cNlo`-style); inner pmuls `wKlo/wKhi/wKmd`; their subword halves (z-vars `wK*_l/_h`).
6. Barrett pmuls `qS`, `qB` (each re-derived in LHS XOR-order via a `SUBGOAL_THEN … bubble_sort_conv` / `WORD_RULE`).
7. **Terminal:** `BINOP_TAC THENL [CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; …]` — one half each.

### Per-N parameters (all intrinsically different — not "divergences")
| N | MC bytes | AES-round range | post-PC | X0 | atomic / pmul / z-var ABBREVs |
|--:|--:|:--:|:--:|--:|:--:|
| 1 | 448 | 20–84 | pc+444 | 16 | 4 / 3 / 7 |
| 2 | 652 | 20–92 | pc+648 | 32 | 10 / 6 / 12 |
| 3 | 1024 | 20–138 | pc+1020 | 48 | 14 / 9 / 18 |
| 4 | 1200 | 20–155 | pc+1196 | 64 | 18 / 12 / 24 |
| 5 | 1400 | 20–200 | pc+1368 | 80 | 22 / 15 / 30 |
| 6 | 1600 | 20–217 | pc+1544 | 96 | 26 / 18 / 36 |
| 7 | 1800 | 20–250 | pc+1716 | 112 | 30 / 21 / 42 |

These (MC blob, step ranges, PC offsets, IO sizes, ABBREV counts that scale with
N) are **expected per-N differences** and are not flagged as divergences below.

---

## 2. Divergences from the 6-block pattern, per file

Legend: 🟢 cosmetic/benign · 🟡 structural-but-correct · 🔴 fundamentally different technique.

### N = 1 — `one_block_…_nblock.ml`  🔴 (most divergent)
The 1-block predates the unified template and keeps an **older, distinct GHASH
closure**:
- 🔴 **Different bridge lemma & rewrite.** Uses `GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT` via `FIRST_ASSUM(… GSYM(MATCH_MP …))` and rewrites with `ghash_polyval_acc` (the raw recursive def) — **not** `GHASH_POLYVAL_ACC_1` + a `…_EQ_POLYVAL_ACC` bridge. (No `GHASH_POLYVAL_ACC_1` exists.)
- 🔴 **Different atom naming.** Atomic abbrevs are `uA0/uA1/uD0/uD1`; inner pmuls are `p1/p2/p3`; z-vars `z1..z6, zD` — vs the `cNlo/wKmd` scheme everywhere else.
- 🔴 **No `bubble_sort_conv`.** Terminal closure is `BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE]` (small enough for `WORD_RULE`). Every N≥2 file uses `bubble_sort_conv`.
- 🟡 **GHASH closure does its own byte-level expansion** (`WORD_SIMPLE_SUBWORD_CONV`, `REV64_*_LANE`, `REV8_JOIN_FOLD`, `KAR_SUBWORD_LEMMA`, `HALFSWAP_XOR`, `WORD_INSERT_AS_JOIN`) inline — the multi-block files push this into `GCM_NBLOCK_POST_AES/SIM_NORMALIZE_TAC`.
- 🟡 **No `POLYVAL_DOT_Hk_EQ`** in the leading rewrite (only one H-power; nothing to symmetrize).
- 🟡 **No tail-dispatch branch / no 2-EXP-64 restore** (single block ⇒ the `b.gt` length loop is not taken; X1=128 means one 16-byte block, immediate fall-through). So the proof has **no `GCM_NBLOCK_TAIL_DISPATCH_NORMALIZE_TAC`** and **no `2 EXP 64` rewrites**.
- 🟢 **`s13` is a single `ABBREV_TAC`** (Q0 only); CT closure is inline `GCM_NBLOCK_CT1_STEP_TAC 1` (no `GCM_CT1_STEP_TAC` name).
- 🟢 ~~`ONCE_DEPTH_CONV let_CONV`~~ → switched to `TOP_DEPTH_CONV let_CONV` (Tier-1, 2026-06-05) to match the family.
- 🟢 **2-way** final conjunction (`ct`, GHASH).
- 🟢 **No extra in-file lemmas.**

### N = 2 — `two_blocks_…_nblock.ml`  🟢 (template-conformant)
Follows the template. Minor benign points:
- 🟢 **GHASH_POLYVAL_ACC_2 is reused from `common/ghash_spec.ml`** (not defined in-file). Same for the bridge: `GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC` is proven in-file. Leading rewrite is `GHASH_POLYVAL_ACC_2; GSYM WORD_REVERSEFIELDS_XOR_8_128` (**no `POLYVAL_DOT_Hk_EQ`** — h and h² need no symmetrization beyond what the bridge handles).
- 🟢 **All CT tactics are the shared one-liner** `GCM_NBLOCK_CT_STEP_TAC 2 k` (no hand-written CT3+ since there's no ivec³ yet).
- 🟡 **Tail dispatch is split out as standalone steps:** after `…TAIL_DISPATCH_NORMALIZE_TAC` it does `ARM_STEPS_TAC [100]` then a **standalone** `RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE … 2 EXP 64])` (the 6-block folds the restore *inside* each cascade `MAP_EVERY`). This is the smallest-N shape of the same idea.
- 🟢 In-file extras: `ghash_2block_karatsuba`, `GHASH_2BLOCK_AS_NBLOCK`, `GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC` — the standard per-N trio.
- 🟢 **3-way** conjunction.

### N = 3 — `three_blocks_…_nblock.ml`  🔴 (unique fast-reduce)
Structurally template-conformant **except for the Barrett-reduce performance
workaround**, which is unique to this file (its assembly funnels the whole GHASH
accumulator into Q19 ≈ 38k nodes, so the `eor3` at step 244 explodes to ~480s if
stepped concretely). Divergences:
- 🔴 **Only-Q19 opaque reduce.** Build steps `(212--243)`; then a guarded `FIRST_ASSUM … ABBREV_TAC` makes **only Q19** opaque (`acc19`) — Q17/Q18 stay concrete so the Barrett pmulls still compute — then `(244--246)`. (Step 244: 480s → ~5s.)
- 🔴 **`ABBREV_FINAL_XI_TAC` is run while `acc19` is still opaque**, then `RULE_ASSUM_TAC(REWRITE_RULE[HALFSWAP_JOIN_SELF])` folds the half-swap, then `acc19` is expanded back.
- 🔴 **Head-shape bridge:** a guarded `FIRST_X_ASSUM(… REWRITE_RULE[GSYM REVERSEFIELDS8_SUBWORD_HI; GSYM REVERSEFIELDS8_SUBWORD_LO])` rewrites `final_xi`'s value-def to the `word_join (rev8 _) (rev8 _)` shape so the GHASH closer's `MATCH_MP_TAC` matches.
- 🟢 ~~Three extra in-file WORD_BLAST lemmas~~ `HALFSWAP_JOIN_SELF`, `HALFSWAP_REV8_LEMMA`, `JOIN_SUBWORD_IDENT` — MOVED to `gcm_aesgcm_helpers.ml` (Tier-1, 2026-06-05); no longer in-file. The 3-block still *uses* them but no longer *defines* them.
- 🔴 **GHASH terminal closure has the half-swap renormalization baked in:** `BINOP_TAC THENL [tail; tail]` where each `tail` is `REWRITE_TAC[REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO/HI; HALFSWAP_REV8_LEMMA; JOIN_SUBWORD_IDENT] THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN(…w1md…) … THEN ASM_REWRITE_TAC[] THEN CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC`. (Other files: bare `bubble_sort_conv THEN REFL_TAC` per half.)
- 🟡 **Epilogue stepped individually** `[247],[248],[249],[250]` rather than a single range (a side-effect of keeping the reduce controlled).
- 🟡 **GHASH leading rewrite has no `POLYVAL_DOT_Hk_EQ`** (`GHASH_POLYVAL_ACC_3; GSYM WORD_REVERSEFIELDS_XOR_8_128`); the h³ symmetrization is handled by an in-tactic `SUBGOAL_THEN … WORD_PMUL_SYM` instead.
- 🟡 `GCM_CT3_STEP_TAC` is **hand-written** (first file needing the ivec² counter unfolding) — same shape as 6-block's CT3.
- 🟢 `GHASH_POLYVAL_ACC_3` reused from `ghash_spec.ml`; standard per-N trio in-file. 4-way conjunction.

### N = 4 — `four_blocks_…_nblock.ml`  🟢 (CONVERGED 2026-06-05 — was the big outlier)
**REWRITTEN to the 5/6-block style.** The GHASH closer previously used the old
1-block lineage (`uA0..uK1` atoms, `p1..p4` pmuls, `qBigP/qSmallP`, 4×
`WORD_BITWISE_RULE`). It now uses the family-standard
`cNlo/cNhi/hd..hg` atoms + `w1..w4` pmuls + `qS`/`qB` + `bubble_sort_conv`
(zero `WORD_BITWISE_RULE`), mirroring the 5-block closer scaled to N=4. The
file dropped ~90 lines and loads ~46s faster (497s → 451s), still proven
end-to-end, no cheats.
- 🟡 **One residual 4-block-specific divergence (Tier-2 investigated, NOT
  removable):** two *byte-form folds* right after the atomic ABBREVs. The
  `karatsuba_mid` expansion of `(xi⊕ct1)` leaks the `(rev8 _)_lo/_hi` byte forms
  into the goal (and into the w1md mid-pmul argument); the folds re-fold them to
  `c1lo`/`c1hi`. **Tier-2 finding (2026-06-05):** the leak reproduces under
  *byte-identical* closer text — running the 4-block closer front-half gives 3
  byte-leaks at the atom-ABBREV point, whereas the same front-half on the 5-block
  goal gives 0. Both parked goals carry 0 live `ct1 =` hypotheses, so the cause
  is **not** an `ASM_REWRITE` expanding a stale `ct1` def; it is a structural
  property of how the 4-block block-1 term threads `s13_1`, which I could not
  eliminate by normalize-step alignment. Per plan, the folds stay (documented).
- 🟡 Uses `POLYVAL_DOT_H4_EQ_LOCAL` in the leading GHASH rewrite (reused from helpers).
- 🟡 `GCM_CT3_STEP_TAC`, `GCM_CT4_STEP_TAC` hand-written (ivec², ivec³).
- 🟢 `GHASH_POLYVAL_ACC_4` reused from `ghash_spec.ml`. Standard per-N trio in-file. 5-way conjunction.

> **Net:** 4-block now shares the `cNlo`/`wKmd`/`qS`/`qB`/`bubble_sort_conv`
> style of 2/3/5/6/7. The only remaining deviation is the pair of byte-form
> folds forced by the non-opaque `ct1` — a genuine structural feature, not a
> stylistic choice.

### N = 5 — `five_blocks_…_nblock.ml`  🟡 (one register-order quirk)
Closely matches the 6-block template (same `cNlo`/`wKmd`/`qS`/`qB`/`bubble_sort_conv`).
Divergences:
- 🟡 **`s13` register order skips Q2:** reads `Q0, Q1, Q3, Q4, Q5` (not the clean `Q0..Q5`). The 5-block object code shuffles the 3rd block result out of Q2 before it's abbreviated, so the proof reads it from a different register. (Every other file reads `Q0..Q(N-1)` contiguously.)
- 🟡 **First file to define `GHASH_POLYVAL_ACC_5` in-file** (ghash_spec only ships ACC_2/3/4). Same for 6, 7.
- 🟡 Leading GHASH rewrite uses `POLYVAL_DOT_H5_EQ` (cumulative symmetrization begins).
- 🟢 Uses 2 `WORD_BITWISE_RULE` (minor leftover; 6/7 trend to 1/0).
- 🟢 CT3/CT4/CT5 hand-written. 6-way conjunction.

### N = 6 — `six_blocks_…_nblock.ml`  ⭐ REFERENCE
The canonical structure. (Has a documentation-only placeholder banner
`POLYVAL_DOT_H4_EQ_LOCAL / H5_EQ / H6_EQ` at L221 with no body — those lemmas
live in `gcm_aesgcm_nblock_helpers.ml`.) `GHASH_POLYVAL_ACC_6` defined in-file.
Leading rewrite `POLYVAL_DOT_H6_EQ; POLYVAL_DOT_H5_EQ`. Uses 1 `WORD_BITWISE_RULE`.
7-way conjunction.

### N = 7 — `seven_blocks_…_nblock.ml`  🟢 (cleanest scale-up of the reference)
The closest match to 6-block; pure scale-up.
- 🟢 `s13` reads `Q0..Q6` contiguously (unlike 5-block).
- 🟢 Leading GHASH rewrite `POLYVAL_DOT_H7_EQ; POLYVAL_DOT_H6_EQ; POLYVAL_DOT_H5_EQ`. `GHASH_POLYVAL_ACC_7` in-file.
- 🟢 **Zero `WORD_BITWISE_RULE`** — fully on `bubble_sort_conv` (the most "modern" closure).
- 🟢 CT3–CT7 hand-written. 8-way conjunction.
- 🟢 Section-title style was aligned to the reference in the recent cosmetic pass (`GHASH_POLYVAL_ACC_7: …` descriptive header).

---

## 3. Cross-file divergence matrix

| Feature | 1 | 2 | 3 | 4 | 5 | **6** | 7 |
|---|:-:|:-:|:-:|:-:|:-:|:-:|:-:|
| Bridge lemma form | `…_POLYVAL_DOT` 🔴 | `…_POLYVAL_ACC` | `…_POLYVAL_ACC` | `…_POLYVAL_ACC` | `…_POLYVAL_ACC` | `…_POLYVAL_ACC` | `…_POLYVAL_ACC` |
| Leading `ghash_polyval_acc` rewrite | raw recursive def 🔴 | `ACC_2` | `ACC_3` | `ACC_4` | `ACC_5` | `ACC_6` | `ACC_7` |
| `GHASH_POLYVAL_ACC_N` source | n/a | ghash_spec | ghash_spec | ghash_spec | helpers ✅ | helpers ✅ | helpers ✅ |
| `POLYVAL_DOT_Hk_EQ` in lead rewrite | none | none | none | H4 | H5 | H6,H5 | H7,H6,H5 |
| Atom naming | `uX`/`pN` 🔴 | `cNlo`/`wK` | `cNlo`/`wK` | `cNlo`/`wK` ✅ | `cNlo`/`wK` | `cNlo`/`wK` | `cNlo`/`wK` |
| Outer-pmul vars | qBigP… 🔴 | qS/qB | qS/qB | qS/qB ✅ | qS/qB | qS/qB | qS/qB |
| `WORD_BITWISE_RULE` count | 0 | 0 | 0 | **0** ✅ | 2 | 1 | 0 |
| `bubble_sort_conv` | no 🔴 | yes | yes | yes | yes | yes | yes |
| Tail-dispatch branch / 2-EXP-64 | none 🟡 | standalone 🟡 | inline | inline | inline | inline | inline |
| `s13` register order | Q0 | Q0,1 | Q0,1,2 | Q0–3 | Q0,1,**3,4,5** 🟡 | Q0–5 | Q0–6 |
| Special fast reduce | no | no | **only-Q19** 🔴 | no | no | no | no |
| Extra in-file lemmas | 0 | 0 | 0 ✅ (halfswap centralized) | 0 | 0 | 0 | 0 |
| `let_CONV` flavor | `TOP_DEPTH` ✅ | `TOP_DEPTH` | `TOP_DEPTH` | `TOP_DEPTH` | `TOP_DEPTH` | `TOP_DEPTH` | `TOP_DEPTH` |
| Epilogue stepping | range | range | **singletons** 🟡 | singletons | range | range | range |
| Conjunction arity | 2 | 3 | 4 | 5 | 6 | 7 | 8 |

---

## 4. Summary: which files truly don't follow the pattern

1. **N=1 🔴 — different proof lineage.** Old-style GHASH closure: `POLYVAL_DOT`
   bridge, raw `ghash_polyval_acc`, `uX/pN` atoms, `WORD_RULE` terminal (no
   bubble-sort), inline byte-expansion, `ONCE_DEPTH_CONV`. No tail-dispatch.
   Would need a full GHASH-closure rewrite to match the 6-block style.

2. **N=4 🟢 — CONVERGED (2026-06-05).** Its GHASH closer was rewritten from the
   old `uX/pN/qBigP/WORD_BITWISE_RULE` (1-block) lineage to the family-standard
   `cNlo/wKmd/qS/qB/bubble_sort_conv` style. Only residual deviation: two
   byte-form folds forced by the non-opaque `ct1`. Loads 451s (was 497s), −90 lines.

3. **N=3 🔴 — unique performance workaround.** Conforms structurally but carries
   the only-Q19 opaque reduce + half-swap bridge + 3 extra lemmas, required
   because its object code funnels the accumulator into one register.

4. **N=5 🟡 — one register quirk.** `s13` reads skip Q2 (object-code shuffle).
   Otherwise template-conformant.

5. **N=2 🟡 / N=7 🟢 — conformant.** N=2 has only the smallest-N tail-dispatch
   shape (standalone 2-EXP-64 restore); N=7 is the cleanest scale-up (0
   `WORD_BITWISE_RULE`).

**Benign-but-systematic (all N):** the cumulative `POLYVAL_DOT_Hk_EQ` list grows
with N; ABBREV counts, step ranges, PC offsets, and conjunction arity all scale
with N. These are expected, not defects.

**Tier-1 centralization (2026-06-05):** `GHASH_POLYVAL_ACC_{2..7}` are now ALL
sourced from shared files — `ACC_2..4` from `common/ghash_spec.ml` (unchanged,
original) and `ACC_5/6/7` derived in `arm/proofs/utils/gcm_aesgcm_helpers.ml`
(moved out of the 5/6/7 block files; `ghash_spec.ml` is kept pristine). The
three half-swap lemmas (`HALFSWAP_JOIN_SELF`,
`HALFSWAP_REV8_LEMMA`, `JOIN_SUBWORD_IDENT`) used by the 3-block fast reduce were
moved from the 3-block file into `arm/proofs/utils/gcm_aesgcm_helpers.ml`
(alongside the related `REV8_JOIN_FOLD` family). N=1's finalize step was switched
from `ONCE_DEPTH_CONV let_CONV` to `TOP_DEPTH_CONV let_CONV` to match the family.
All seven proofs + both shared files re-verified loading end-to-end after these
relocations (no proof logic changed).

*Generated from direct inspection of the seven files; no proof logic was modified to produce this report.*
