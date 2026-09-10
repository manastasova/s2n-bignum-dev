# AES-256-GCM encrypt: current kernel vs every milestone, nebeid, and aws-lc

Graviton3 / Neoverse-V1, `taskset -c 20`, verified-idle core (load 0.03), interleaved
order-alternating, min-of-12. All seven kernels linked into ONE binary with the same
call-serializing shape as `benchmarks/benchmark.c` (30 round keys + 32 H-table words +
`Xi`/`ivec` refilled on every call). Measured 2026-09-10 at `b4cf58d6`.

## 1. ns per call

| kernel | `.text` | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 192 | 256 | 512 | 1024 | 4096 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **OURS (current)** | **6,488 B** | 29.9 | 32.3 | 32.9 | 34.3 | 40.8 | 42.0 | 43.3 | 43.0 | 62.4 | 65.5 | 108.8 | 196.6 | 722.5 |
| ours `fused4` | 7,780 B | 29.9 | 32.2 | 33.2 | 34.2 | 43.0 | 44.2 | 45.3 | 42.9 | 63.0 | 65.6 | 109.1 | 196.7 | 724.2 |
| ours `sizecap` | 9,100 B | 30.2 | 32.2 | 33.4 | 34.5 | 37.7 | 38.8 | 41.2 | 43.4 | 63.7 | 65.8 | 109.3 | 197.1 | 723.9 |
| ours `speed` | 11,848 B | 30.4 | 32.2 | 33.4 | 34.5 | 37.5 | 38.8 | 41.2 | 42.7 | 63.2 | 65.1 | 108.5 | 195.6 | 718.5 |
| nebeid (unproven) | 7,504 B | 29.6 | 32.1 | 33.3 | 34.1 | 42.9 | 44.3 | 45.4 | 42.8 | 63.2 | 65.4 | 108.5 | 196.2 | 721.5 |
| aws-lc x8 original | 4,672 B | 42.6 | 43.7 | 45.1 | 47.2 | 49.3 | 52.8 | 55.6 | 55.9 | 69.4 | 76.3 | 120.0 | 207.4 | 732.3 |
| aws-lc 4x (shipped) | 2,872 B | 32.2 | 35.8 | 37.8 | 38.2 | 50.2 | 52.6 | 53.4 | 54.7 | 70.2 | 85.9 | 149.1 | 275.1 | 1041.3 |

## 2. Geomean vs the kernel aws-lc would actually dispatch to

aws-lc routes `len < 256` to the 4x and `len >= 256` to the 8x (`crypto/fipsmodule/modes/gcm.c`),
so those are the correct references. Negative = faster.

| kernel | `.text` | < 256 B (vs 4x) | >= 256 B (vs x8) |
|---|---|---|---|
| **OURS (current)** | **6,488 B** | **-14.7%** | **-7.6%** |
| ours `fused4` | 7,780 B | -13.1% | -7.5% |
| ours `sizecap` | 9,100 B | -16.1% | -7.3% |
| ours `speed` | 11,848 B | **-16.3%** | **-8.1%** |
| nebeid | 7,504 B | -13.2% | -7.8% |
| aws-lc x8 original | 4,672 B | +10.6% | 0.0% |
| aws-lc 4x | 2,872 B | 0.0% | +27.5% |

## 3. Current kernel vs nebeid's, per size

negative = ours faster.

| 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 192 | 256 | 512 | 1024 | 4096 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| +1.1% | +0.7% | **-1.3%** | +0.6% | **-5.0%** | **-5.2%** | **-4.7%** | +0.6% | **-1.3%** | +0.2% | +0.3% | +0.2% | +0.1% |

**1,016 B smaller and faster on the geomean** (-14.7% vs -13.2%), with the profile explained by
exactly two known differences:

- **80/96/112 B, -5%**: ours redirects the generic cascade's rem 5/6/7 into the `eor3`-fused
  `rem4_drain` (`8cb29b6d`); her kernel leaves them on the unfused pairwise cascade.
- **16/32/64/128 B, +0.6..1.1%**: she loads the `tbl` reversal index from a `.balign 16` literal;
  we synthesise it in registers, because `ldr q12,<label>` has no decode rule in
  `arm/proofs/decode.ml` and so cannot be proven. This is the full cost of that substitution and
  it matches the ~1% predicted from the isolated A/B.

Everything else in the two kernels is instruction-for-instruction identical -- verified by diffing
the four short bodies and all five tail regions (`tail_dispatch`, `tail_slides`, `exact8_drain`,
`rem4_drain`, `rem2_drain` are **byte-identical**).

## 4. Reading these numbers

- **`speed` (11,848 B) is still the fastest below 256 B** (-16.3%), and the whole gap to the current
  kernel is 80/96/112 B: 37.5/38.8/41.2 vs 40.8/42.0/43.3. Those three sizes have dedicated
  `fast5/6/7` bodies there and fall back to the generic wave here. Restoring them costs ~1,045 B
  per width (measured, session 149) for -14.6/-13.3/-10.7% at those sizes.
- **The current kernel beats `fused4` while being 1,292 B smaller** -- the rem 5/6/7 redirect
  recovered roughly a third of the `fused4` regression for zero bytes.
- **>= 256 B barely moves across all variants** (-7.3 to -8.1%). The main loop was deliberately
  never optimized: a roofline measurement put it at ~99% of AES issue peak, which is also why the
  4096 B advantage is only -1.3%.
- **The < 256 B column is currently unreachable in production.** aws-lc's `len >= 256` dispatch gate
  means no 8x kernel runs below 256 B today; realising these wins needs that threshold lowered.
- Base-vs-base harness bias is ~+-0.14% at 16 B but **+0.9-1.2% at 96 B** and -0.9% at 112 B, and at
  32/48/64 B the median bias is itself noisy up to +1.0%. Treat anything under ~1.5% on the short
  path as flat within noise.

## 5. Provenance

- Our kernel: `arm/aes-gcm/aesv8_gcm_8x_enc_256.S` at `b4cf58d6`, proof
  `arm/proofs/aesv8_gcm_8x_enc_256.ml`, cold gate 0-CHEAT / 3 axioms / both exported subroutine
  theorems at 0 hypotheses.
- nebeid: `_docs/aes-gcm-enc-fast1-4-experiment/aes256-gcm-4x-experiment/src/x8-enc-pareto-full.S`
  @ `10ec0962` on `nebeid/s2n-bignum`, built at its defaults (`X8_PARETO_WIDTHS=4`,
  `X8_PARETO_SHARED_REDUCE=1`). Her report states the short code "has no HOL Light proof".
- aws-lc kernels: `benchmarks/reference/`, see `PROVENANCE.md`.
