# AES-256-GCM encrypt: every optimization experiment and its measurement

Consolidated record for `arm/aes-gcm/aesv8_gcm_8x_enc_256.S`. Graviton3 /
Neoverse-V1, `taskset -c 20`, idle core, min of 3 runs. Snapshot 2026-08-28.

Raw sources this consolidates: 32 per-session reports in
`orchestrator/logs/optimize-*-summary.md`, the cross-session memory
`orchestrator/state/OPTIMIZER_ADVICES.md` (~30 KB), and the commit subjects,
which carry the measured before/after for each landed change.

---

## 1. Landed optimizations, in commit order (oldest first)

Every row was re-proven 0-CHEAT / 3 axioms / both exported subroutine theorems at
0 hypotheses before commit. Sizes quoted are the ones the session measured, on the
official `benchmarks/benchmark.c` unless marked h2h.

| # | commit | optimization | measured |
|---|---|---|---|
| 1 | `fdf31b07` | parallelize SETUP counter chain | 256 B 80.4 -> 78.7 ns (**-2.1%**) |
| 2 | `8f322a42` | TAIL odd-block GHASH mid: `ins`+`pmull2` -> `ext`+`pmull` | 256 B 78.7 -> 75.3 ns (**-4.4%**) |
| 3 | `eb19f411` | TAIL data-side GHASH mid: `ins v27` -> `ext v27,v8,v8` | 512 B 118.7 -> 114.0 ns (**-4.0%**), 1024 B -2.2%, geomean -2.1% |
| 4 | `f95eb1fd` | dedicated exact-8 tail drain, drops 7 no-op tag `eor`s | 512 B 114.1 -> 111.8 ns (**-2.0%**), 1024 B -1.2%, geomean -1.3% |
| 5 | `c9a9ee70` | `eor3`-fuse exact-8 drain GHASH accumulate chains | 256 B 73.3 -> 67.8 ns (**-7.5%**), geomean -2.2% |
| 6 | `67cb82e3` | flatten SETUP counter chain, depth 4 -> 2 (parallel `base+offset`) | 256 B 68.3 -> 66.1 ns (**-3.2%**) |
| 7 | `b20e50f1` | `eor3`-fuse the rem=4 tail GHASH drain | 64 B 42.6 -> 41.5 ns (**-2.6%**), 192 B -1.1% |
| 8 | `a6279cf5` | rem=2 dispatch-block slide-skip | 32 B 39.8 -> 38.1 ns (**-4.3%**) |
| 9 | `a1fe6c03` | `eor3`-fuse the rem=2 drain GHASH | 32 B 38.1 -> 36.8 ns (**-3.4%**) |
| 10 | `ae75222c` | round-major SETUP AES schedule (blocks 0,1 first) -- pure permutation | 32 B 36.8 -> 35.9 ns (**-2.7%**) |
| 11 | `e88719b2` | **`fast2` early-dispatch (32 B)** | 32 B 36.0 -> 33.1 ns (**-8.1%**) |
| 12 | `82ef4d58` | `tbl` tail-format the 32 B (`fast2`) drain | 32 B 33.1 -> 32.2 ns (**-2.7%**) |
| 13 | `0a98fae9` | **`fast4` early-dispatch (64 B)** | 64 B 41.4 -> 36.9 ns (**-10.9%**) |
| 14 | `7bfbcc37` | `tbl` tail-format the 64 B (`fast4`) drain | 64 B 36.9 -> 36.1 ns (**-2.2%**) |
| 15 | `c9452246` | `fast4` drain clone-cleanup: drop 3 keystream `mov`s + 3 no-op tag `eor`s | 64 B 36.1 -> 34.0 ns (**-5.5%**) |
| -- | `1196c23b` | front-load SETUP + dispatch out of the braid | `.text` -212 B but **SLOWER**; see §3. **REVERTED** by `451de5b3` |
| 16 | `c313cb00` | **`fast1` (16 B) + `fast3` (48 B) early-dispatch** -- beat aws-lc 4x at all 8 small sizes | 16 B 26.6 -> 18.7 ns (**-30%**), 48 B 29.1 -> 22.1 ns (**-24%**) |
| 17 | `bbaea3d0` | **`fast5`/`fast6`/`fast7` (80/96/112 B) early-dispatch** | 80 B 32.4 -> 26.5 ns (**-18.3%**), 96 B 33.7 -> 28.4 (**-15.7%**), 112 B 34.7 -> 31.3 (**-9.7%**) |
| 18 | `3373f5ab` | `tbl` tail-format on `fast1`/`fast3` | 16 B 31.6 -> 30.5 ns (**-3.2%**), 48 B 34.2 -> 33.3 (**-2.7%**) |
| 19 | `abc66939` | `fast4` early-dispatch moved BEFORE the counter build | h2h 64 B 23.9 -> 23.1 ns (**-2.5%**), vs-4x ratio 1.112 -> 1.15 |
| 20 | `424a8e5b` | `fast2` early-dispatch moved BEFORE the counter build | h2h 32 B 20.6 -> 19.6 ns (**-4.9%**), vs-4x ratio 1.14 -> 1.20 |
| 21 | `00492897` | **AES re-roll** (14-round unroll -> loop) for `fast3/5/6/7` + drop dead `fast2`/`fast4` bodies. Branch `aes_gcm_256_x8_opt_sizecap` | `.text` 11848 -> **9100 B (-23%)**; speed-neutral EXCEPT **80 B +4.3%** (37.3 -> 38.9, A/B confirmed) |
| 22 | `3f893a36` | **fused `nb<=4` short path**: replace the seven `fastN` dispatch tests with ONE `cmp x9,#64 / b.le`; four braided bodies behind a shared prefix. Branch `aes_gcm_256_x8_opt_fused4` | `.text` 11848 -> **7780 B (-34%)**; 80/96/112 B **+11-14%** accepted (they lose `fast5/6/7`) |
| 23 | `de217086` | **(a) shared final GHASH reduction suffix** + unify the `tbl` index register to `v12` (nebeid item a) | `.text` 7780 -> **7660 B (-120)**; speed TIE at all 13 sizes |
| 24 | `5725221e` | **(c) direct final-counter construction** -- delete the 22 counter-rollback `sub`s (nebeid item c) | `.text` 7660 -> **7580 B (-80)**; speed TIE |
| 25 | `107b6236` | strip `rem4_drain`'s 3 no-op tag `eor`s + 3 dead `movi`s (the s097 lever, never applied there) + complete `small_3`'s `eor3` fusion (3-way fold, depth 2->1) | `.text` 7580 -> **7544 B**; 192 B **-1.1..-2.4%** |
| 26 | `8cb29b6d` | **redirect the generic cascade's rem 5/6/7 into the `eor3`-fused `rem4_drain`** -- `mt3`'s body is operation-identical to `rem4_drain`'s first block, so overwrite its redundant leading `st1` with `b rem4_drain`. ZERO PC shift: exactly one instruction word differs | 80/96/112 B **-3.3/-3.4/-3.4%**; `.text` unchanged |
| 27 | `8476aeda` | **(A) build the reversal index ONCE** in the shared prefix instead of in all four bodies (nebeid item b, via register synthesis -- her literal-table form is unprovable, see below) | `.text` 7544 -> **7424 B (-120)**; 16 B flat/faster |
| 28 | `b5ca504a` | **(C) re-roll `small_4`'s 14-round AES** into a 13-iteration loop | `.text` 7424 -> **7040 B (-384)**; 64 B median -0.20% = NEUTRAL |
| 29 | `d4d08b19` | **(C) complete the re-roll for `small_1/2/3`** -- narrow bodies benefit MORE, not less | `.text` 7040 -> **6464 B (-576)**; flat incl. 16 B |
| 30 | `279a0daf` | **(B) per-width counter build** -- stop building counters 1-3 unconditionally ahead of the dispatch (nebeid) | `.text` 6464 -> **6488 B (+24)** but 16 B **-2.8%**: removing 6 dead SIMD ops from before the 1-block dispatch cuts crypto-pipe contention |

Rows 22-30 are the **nebeid short-path alignment** (see
<https://github.com/nebeid/s2n-bignum/blob/10ec0962/_docs/aes-gcm-enc-fast1-4-experiment/aes256-gcm-4x-experiment/src/x8-enc-pareto-full.S>).
All four of her structural items are ported; her *literal* reversal index
(`.byte 15,14,...,1,0` + `ldr q12,<label>`) is **unprovable for us** -- `arm/proofs/decode.ml`
has no PC-relative `LDR (literal)` decode rule (0 of 172 rules match the `0b*011100` shape),
so symbolic execution cannot step it. Route B (hoisted synthesis) gets -120 B of her -140 B.

Cumulative: `.text` **4672 B (aws-lc original) -> 11848 B (speed-optimal) -> 6488 B (current)**,
faster than every AES-256 kernel measured at all 13 sizes 16 B..4096 B, and **1016 B smaller
than nebeid's 7504 B** while being faster on the 16-192 B geomean (-14.7% vs -13.2% against
aws-lc's 4x). Every row re-proven 0-CHEAT before commit.

---

## 2. Attribution: which mechanism produced which gain

Independent re-measurement of every milestone binary (16 builds x 6 sizes, min of
4 runs, ciphertext verified), differenced per step and grouped by mechanism. The
columns sum exactly to the totals, so this is an attribution, not an estimate.
Values in ns, negative = faster. (Measured at the `c9452246` stage, before
`fast1/3/5/6/7`.)

| mechanism | kind | 16 B | 32 B | 48 B | 64 B | 128 B | 256 B |
|---|---|---|---|---|---|---|---|
| Early dispatch | don't execute | -0.09 | **-5.15** | +0.11 | **-5.05** | +0.02 | -0.24 |
| Tail peepholes (`ins`->`ext`) | shorten chain | -0.02 | -0.11 | -1.70 | -0.62 | **-6.63** | **-7.22** |
| Cascade replacement (dedicated drains) | both | -0.16 | -1.47 | +0.03 | -1.21 | -2.67 | -2.89 |
| SETUP restructuring | shorten chain | **-1.71** | -2.10 | +0.55 | -0.48 | -0.81 | +0.03 |
| Drain format/cleanup (`tbl`, clone audit) | both | +0.03 | +0.06 | -0.21 | **-1.08** | +0.05 | +0.05 |
| **total** | | **-1.95** | **-8.77** | **-1.22** | **-8.44** | **-10.04** | **-10.27** |
| original -> then (ns) | | 28.45->26.50 | 29.31->20.54 | 30.67->29.45 | 32.35->23.91 | 42.25->32.21 | 64.65->54.38 |

Per-mechanism totals across those six sizes, with cost:

| mechanism | best single hit | share of total | commits | code added |
|---|---|---|---|---|
| Tail peepholes | -6.63 ns @128 B (-15.7%) | **40.1%** | 2 | **0 B** |
| Early dispatch | -5.15 ns @32 B (-17.6%) | 25.6% | 2 | 1,236 B |
| Cascade replacement | -2.67 ns @128 B | 20.6% | 5 | 760 B |
| SETUP restructuring | -2.10 ns @32 B | 11.1% | 3 | 252 B |
| Drain format/cleanup | -1.08 ns @64 B | 2.7% | 3 | ~0 B |

Best return on effort: the two `ins`->`ext` commits produced **40% of the total
gain for zero added code and zero added instructions**, at -8.15 ns per commit
against -1.67 for the cascade work.

Where the changes are (and are not): for inputs <=128 B the main loop and
prepretail **never execute** (`g = 0`), and they received **zero** optimizations
across the whole campaign -- a roofline measurement put the main loop at ~99% of
AES peak. That is also why the 4096 B gain is only -1.7%.

---

## 3. Measured dead ends -- do not re-explore

The expensive half of the record. Each was built and measured.

| experiment | measured result |
|---|---|
| **Front-load SETUP into phase groups** so small sizes branch out of the 8-way braid, deleting the duplicated AES | **+5.6% @128 B** (2 blocks), **+9.6%** (4 blocks), **+10.8%** (2+2). 16 B 26.5->29.1 and 48 B 29.5->32.2 also WORSE. 32 B flat. Saved only 212 B. Landed then **reverted**. |
| Manual `aese`/`aesmc` regrouping | **+31% WORSE** -- the hardware fusion is already optimal |
| AES-chain interleave restructuring | **+36% WORSE** (2 crypto pipes, resource-forced seriality) |
| GP-domain counter via `fmov` | worse everywhere (`fmov` shares the V-pipe, RMW) |
| Parallel accumulators in `fast4_drain` | **+0.9 ns** -- accumulate is not the bottleneck |
| Shift-based reduction instead of `pmull` | FLAT -- rules out shift-reduce as a lever |
| Schoolbook instead of Karatsuba | sub-bar (<2%) |
| Hoisting the `tbl` index build into shared SETUP | **REJECTED** -- `v25` is a LIVE H-power there; a dead-`v20` rebuild was MIXED and 80 B WORSE |
| **~40 further attempts, all FLAT** | instruction rescheduling, `.balign` alignment, `prfm` prefetch, register reallocation, breaking WAR/false deps on already-renamed regs, load hoisting, early constant materialization, H-table/h1 load hoist into the AES shadow, index-build 10 ops -> 1, counter-sub collapse, modulo-constant hoist, `movi`+`eor3` -> `eor` |

**Two rules these produced**, both learned expensively:

1. **A work-removal probe bounds only the instructions it deletes.** Gutting all
   112 SETUP `aese` measured -0.9 ns, so four sessions concluded early dispatch
   was not worth it and one recorded "32 B floor CONFIRMED 3rd time" -- then it
   was built and measured **-2.9 ns**. To bound a structural change, hack up
   something structurally faithful even if numerically wrong.
2. **On Neoverse-V1 only two things win:** remove an instruction from the true
   dependency chain, or do not execute the work at all. Everything else is
   absorbed by the out-of-order engine.

Plus a noise rule: always interleave A/B for sub-1% deltas. One candidate looked
-0.9% non-interleaved and was FLAT interleaved.

---

## 4. Floors that were confirmed, then broken

Worth recording because it shaped the "three consecutive stuck sessions" rule:

| claim | how it ended |
|---|---|
| "32 B floor CONFIRMED 3rd time" (three independent sessions) | broken by `fast2`, **-8.1%** |
| "64 B near floor" | broken twice more, by `fast4` then the clone-cleanup, **-12.8%** then -5.5% |
| "32/64/128 B all at a dependency-latency floor" (two fresh-eyes sessions, 25 attempts) | broken by early-dispatch-before-the-counter-build, -2.5% and -4.9% |
| "encrypting N blocks is 28N instructions of unrolled AES, irreducible" | broken by the AES re-roll: **-23% code, speed-neutral** |

---

## 5. Reading any number in this file

- **Two harnesses, never mixed.** `benchmarks/benchmark.c` (the arbiter, ours
  only) and `/tmp/h2h32` (both kernels in one binary, the only valid source for a
  ratio against aws-lc). They differ ~12 ns in absolute scale and have
  disagreed in sign: both `tbl` wins measured -2.7%/-2.2% official but FLAT on
  h2h.
- **The official harness understates advantages, unevenly.** It refills 30 round
  keys + 32 H-table words + Xi/ivec every call (8.7 ns standalone), and a long
  kernel hides that behind its own work while a short one cannot -- so it
  penalizes the faster kernel most. Raw-kernel scope shows our advantage over the
  x4 family at 16-128 B as ~90-135%, where the official tables show 8-25%.
- Run-to-run variance ~1.5%; anything under 2% needs min-of-N on a verified-idle
  core.
