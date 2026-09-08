# AES-256-GCM optimization status: encrypt (ours) vs decrypt (nebeid)

Snapshot 2026-08-28. Measured on Graviton3 / Neoverse-V1, `taskset -c 20`, idle
core, min of 3 runs.

---

## 1. What we integrated into the encrypt kernel

14 landed optimization commits on `aes_gcm_256_x8_verbose_opt_bench`
(`arm/aes-gcm/aesv8_gcm_8x_enc_256.S`), every one re-proven 0-CHEAT / 3 axioms /
both exported subroutine theorems at 0 hypotheses before commit.

| mechanism | what it does |
|---|---|
| **Early dispatch x7** (`fast1`..`fast7`) | entry tests on exact block count jump to appended paths that build ONLY the counters/keystreams needed. 16 B went from 112 to 14 `aese`. |
| **Dedicated drains** (`exact8`, `rem4`, `rem2`, `fastN_drain`) | peel remainders out of the fall-through cascade, removing keystream slides and the serially dependent `sub v30,v30,v31`. |
| **`eor3` fusion** | 3-input XOR collapses the GHASH accumulate tree: 21 dependent XORs at depth 7 -> 12 ops at depth 4. |
| **GF-identity removal** | 7 tag `eor`s against provably-zero values. Free when overlapped; pure latency on an exposed drain. |
| **`ins` -> `ext`** | deletes a read-modify-write false dependency that serialized all 7 Karatsuba mid terms, at identical instruction count. |
| **Counter-chain flattening** | serial `rev32`/`add`/`rev32` increment chain, depth 7 -> 2 via parallel `base + offset`. |
| **`tbl` tail-format** | `ext`+`rev64` -> a single `tbl` with a precomputed index, built in the AES shadow. |
| **Clone hygiene** | a cloned drain carried keystream `mov`s and no-op `eor`s that were dead on its specialized path (-5.5%). |
| **AES re-roll** (size-cap branch `aes_gcm_256_x8_opt_sizecap`) | re-rolling the 14-round unroll into a loop: `.text` 11848 -> 9100 B, speed-neutral except +4.3% at 80 B. |

Result: faster than every AES-256 kernel measured, at all 13 sizes 16 B..4096 B.
`.text` 11848 B (9100 B on the size-cap branch).

---

## 2. Where nebeid's optimizations live

Two active branches in <https://github.com/nebeid/s2n-bignum>:

- **`aes-gcm-dec-clean`** (2026-08-23) -- the DECRYPT kernel,
  `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S`. This is where the optimization
  commits are.
- **`aes-gcm-enc-fast1-4-experiment`** (2026-08-28) -- an encrypt experiment
  report plus a hybrid built on **Hanno's x4**, not on our x8.

Her decrypt optimization commits:

```
93988f22  Optimize: shorten the TAIL odd-block GHASH mid chains
d52802da  Optimize: flatten the SETUP counter chain (depth 7 -> 2)
f6133209  Optimize: eor3-fuse the exact-8 drain accumulate chains
37d08b36  Add a fused 1-4 block path, align the main loop, drop the size literal
29c53264  Test the kernel below aws-lc's dispatch threshold; add Wycheproof vectors
```

Other branches of interest: `aes-gcm-fused-wip` (2026-08-21),
`aes-gcm-wb-mainloop` (2026-08-13), `aes-gcm-nblock-tail` (2026-07-24),
`aesv8-gcm-1block-proof` (2026-06-15).

---

## 3. Ours vs hers

**The split is encrypt vs decrypt.** Four of our mechanisms are already ported
across; the structural difference is the short-message dispatch.

| mechanism | ours (encrypt) | hers (decrypt) |
|---|---|---|
| `ins` -> `ext` mid chains | yes | **ported** |
| counter flattening depth 7 -> 2 | yes | **ported** |
| `eor3`-fused exact-8 drain | yes | **ported** |
| GF-identity removal in `exact8_drain` | yes | **ported** |
| **short-message dispatch** | **7 separate paths, nb = 1..7** | **1 fused path, `cmp x9,#64 / b.le` -> nb <= 4** |
| `tbl` tail-format | yes | no |
| clone-hygiene audit | yes | no |
| 80/96/112 B paths (`fast5/6/7`) | yes | no |
| AES re-roll for size | yes (size-cap branch) | no |

**Cost of the structural difference.** Her fused design is much smaller -- her
encrypt-side "compact 8x" is 8624 B against our 11848 B -- but raw kernel timings
show where it gives up ground. Identical at 16/32/48/64/128 B; at the three sizes
`fast5/6/7` cover, ours is 12-20% faster:

| raw kernel ns, 16 B input | 80 B | 96 B | 112 B |
|---|---|---|---|
| ours | **25.6** | **27.2** | **29.6** |
| her compact 8x | 32.0 | 33.1 | 33.7 |
| delta | -20% | -18% | -12% |

---

## 4. How to equalize

Cross-port, in descending value:

1. **`fast5/6/7` -> decrypt.** Her dispatch stops at 4 blocks; 80/96/112 B is the
   largest measured gap and the mechanism is already proven three times.
2. **Her fused 1-4 design -> our encrypt, as the size lever.** Same goal as our
   size-cap work by a different technique (one fused path instead of four
   dedicated ones). Combined with the AES re-roll it could plausibly get us below
   8624 B while KEEPING `fast5/6/7`.
3. **`tbl` tail-format + clone-hygiene audit -> decrypt.** Cheap, mechanical,
   ~2-5% each on exposed drains.
4. **Share the drains.** GHASH-over-ciphertext is the same computation in both
   directions and the drains are `pmull`-dominated, needing no per-block-count
   braiding -- the cheapest thing to factor out rather than maintain twice.

Two process items that matter more than any single optimization:

5. **Agree one measurement protocol.** Published margins currently differ by ~9x
   between the two workstreams purely from (a) whether the per-call key refill is
   inside the timing loop and (b) whether the percentage denominator is the
   faster or the slower kernel. Proposal: always report **raw kernel ns AND
   with-setup ns**, and state the denominator explicitly. See §5.
6. **Settle the `len >= 256` dispatch threshold jointly.** She is already testing
   below it (`29c53264`); we independently found the same blocker. Neither side's
   short-message work reaches a caller until aws-lc's `gcm.c` gate changes, and
   that single change is what converts both efforts into real-world gain.

---

## 5. Measurement protocol -- why two correct reports disagreed

Reconciled to within +-0.6 pp at all eight short sizes. Three causes, in order of
magnitude:

**(a) Harness scope.** `benchmarks/benchmark.c` refills 30 round keys, 32 H-table
words and Xi/ivec from the output buffer on EVERY call (to reproduce a caller's
store->load serialization). Measured standalone at **8.7 ns**. nebeid's method
states "raw kernels only; ... caller overhead are excluded."

The effect is NOT a constant offset -- it depends on kernel length, because a
long kernel hides the setup behind its own work and a short one cannot:

| 16 B | raw | with setup | delta |
|---|---|---|---|
| ours | 15.4 | 29.8 | **+14.4** |
| `hanno_opt` (x4) | 29.3 | 33.0 | **+3.7** |

Same setup code, 4.7x different effect. Verified NOT to be inter-call overlap:
forcing a dependency between consecutive calls changes nothing (15.2 -> 15.4).
Consequence: **the with-setup harness systematically penalizes the faster
kernel**, so it understates advantages, and understates them most where our
kernel is strongest.

**(b) Percentage convention.** nebeid puts the *slower* kernel in the denominator
(a "% reduction"); we had been quoting "% speedup". At 16 B, ours 15.4 vs hanno
29.3: `(29.3-15.4)/15.4 = +90%` vs `(29.3-15.4)/29.3 = +48.1%`. Her table reports
+48.1%. That one choice halves every figure.

**(c) A real kernel difference**, only at 80/96/112 B -- see §3.

**Not causes:** the x4 baseline is byte-identical in both (md5
`e7c9e0e06b4b950b5da314ba7e2a2415`, Hanno's `scalar_iv_mem_late_tag_scalar_rk`
from `hanno-becker/aws-lc@83d5627a`), and the platform is the same core (G3/V1).

---

## 6. Benchmark inventory

Seven AES-256 kernels plus one AES-128 reference, all in
`benchmarks/reference/` (see `PROVENANCE.md` there for links and commits) and all
differential-tested in `tests/test.c` against the same independent C AES-256-GCM
reference on ciphertext, GHASH accumulator and counter.

| benchmark name | what it is |
|---|---|
| `aesv8_gcm_8x_enc_256` | ours -- optimized + HOL-Light-proven 8x |
| `aesv8_gcm_8x_enc_256_org` | aws-lc's original 8x (our campaign baseline) |
| `aes_gcm_enc_kernel_4x` | aws-lc's shipped 4x |
| `hanno_opt_256` | Hanno's SLOTHY-pipelined x4 -- identical to nebeid's baseline |
| `hanno_base_256` | Hanno's clean AES-256 base (SLOTHY's input) |
| `gcm_x4_swp_256` | our conversion of the AES-128 pipelined champion to AES-256 |
| `gcm_x4_scalar_rk_256` | our conversion of the AES-128 clean kernel to AES-256 |
| `aes_gcm_enc_kernel_x4_swp_128` | the AES-128 champion, unmodified -- NOT comparable |

ns/call, Graviton3/V1, `./benchmark 3000` (with-setup scope):

| input | OURS x8 | org x8 | awslc 4x | hanno_opt | hanno_base | my SWP | my clean |
|---|---|---|---|---|---|---|---|
| 16 B | **30.3** | 42.3 | 32.7 | 33.8 | 30.6 | 33.3 | 33.4 |
| 32 B | **32.0** | 43.3 | 35.9 | 40.2 | 38.7 | 39.6 | 39.6 |
| 48 B | **33.5** | 44.9 | 37.6 | 48.7 | 47.0 | 47.6 | 48.2 |
| 64 B | **34.4** | 46.8 | 38.7 | 47.1 | 46.5 | 37.5 | 46.5 |
| 80 B | **37.4** | 49.2 | 50.3 | 55.4 | 54.8 | 51.1 | 54.9 |
| 96 B | **38.8** | 52.7 | 52.3 | 64.5 | 64.4 | 58.0 | 64.6 |
| 112 B | **40.8** | 55.4 | 53.5 | 73.6 | 73.2 | 66.5 | 72.9 |
| 128 B | **42.7** | 60.1 | 55.0 | 53.3 | 53.6 | 53.5 | 72.8 |
| 192 B | **63.2** | 70.4 | 70.7 | 69.3 | 70.9 | 69.8 | 99.9 |
| 256 B | **65.3** | 77.9 | 86.5 | 85.4 | 88.2 | 85.8 | 126.8 |
| 512 B | **109.0** | 121.8 | 149.6 | 149.4 | 157.2 | 149.8 | 234.5 |
| 1024 B | **201.8** | 214.8 | 277.9 | 279.2 | 296.2 | 280.0 | 451.1 |
| 4096 B | **728.4** | 741.2 | 1053.0 | 1048.9 | 1125.6 | 1049.3 | 1740.5 |

Code size (`.text`): ours 11848 B (9100 B size-capped) | org x8 4672 | awslc 4x
2872 | hanno_opt 3864 | hanno_base 3416 | my SWP 4936 | my clean 1320.

Large messages, raw scope: ours and the ORIGINAL x8 converge -- 2829 vs 2827 ns
at 16 KB, ~5.8 GB/s both. All our work targeted small sizes; the main loop and
prepretail were deliberately never touched (measured at ~99% of AES peak).

---

## 7. Caveats that apply to every number here

- **Reachability:** aws-lc's `gcm.c` routes to an 8x kernel only when
  `CRYPTO_is_ARMv8_GCM_8x_capable()` (SHA3 AND Neoverse-V1/V2 or Apple-M) AND
  `len >= 256`. So Graviton2/N1 never runs an 8x kernel at all, Neoverse-V3/G5
  is not yet in the allowlist, and every 16-128 B win here currently reaches no
  caller on any platform.
- **I-cache:** ours is 4.1x the size of aws-lc's 4x. Every benchmark runs one
  kernel in a tight loop, keeping it hot; a workload interleaving other code
  could pay misses this harness cannot show.
- **Core:** all numbers are Neoverse-V1. Hanno's schedules were tuned for N1, and
  nebeid's G3/G4/G5 table shows N1-tuned code losing ~50% at short messages on
  V1/V2/V3.
- **Contract:** ours is whole-blocks-only AES-256 encrypt. It rejects
  non-block-aligned lengths and does not cover AES-128/192 or decrypt.
- **Proof:** ours is the only kernel here with a HOL Light proof. The reference
  kernels are unproven, and the software-pipelined ones are expensive to verify
  because pipelining does not preserve block boundaries or instruction counts.
