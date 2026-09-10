# Runtime optimizations — `aesv8_gcm_8x_enc_256`

Thirty machine-code optimizations applied to the AES-256-GCM 8x whole-blocks encrypt
kernel over 30 optimizer sessions. Each was verified three ways before being committed: it
passes `tests/test.c`, it is measurably faster (or size-reducing at parity) on
`benchmarks/benchmark.c`, and the HOL Light correctness proof
(`arm/proofs/aesv8_gcm_8x_enc_256.ml`) re-passes **0-CHEAT with a byte-identical goal**
against the new `.o` — 3 axioms, both exported subroutine theorems closing to 0 hypotheses.
The specification and the exported `*_SUBROUTINE_CORRECT` / `..._GEN` statements were never
changed; only the assembly and the proof tactics.

**Final kernel: `.text` 6488 B**, versus 4672 B for the aws-lc original it derives from
(`aesv8-gcm-armv8-unroll8-enc-256.pl`) — 1.39x the code for 18.7 % less time.

## Result

Graviton3 / Neoverse-V1, `taskset -c 20`, verified-idle core, interleaved order-alternating,
min-of-12, all kernels in one binary with the call-serializing shape of
`benchmarks/benchmark.c`. ns per call:

| kernel | `.text` | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 192 | 256 | 512 | 1024 | 4096 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **this kernel** | **6,488 B** | 29.9 | 32.3 | 32.9 | 34.3 | 40.8 | 42.0 | 43.3 | 43.0 | 62.4 | 65.5 | 108.8 | 196.6 | 722.5 |
| aws-lc x8 original | 4,672 B | 42.6 | 43.7 | 45.1 | 47.2 | 49.3 | 52.8 | 55.6 | 55.9 | 69.4 | 76.3 | 120.0 | 207.4 | 732.3 |
| aws-lc 4x (shipped) | 2,872 B | 32.2 | 35.8 | 37.8 | 38.2 | 50.2 | 52.6 | 53.4 | 54.7 | 70.2 | 85.9 | 149.1 | 275.1 | 1041.3 |

Improvement over the **original x8 kernel** (negative = faster):

| | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 192 | 256 | 512 | 1024 | 4096 | **geomean** |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| this kernel | -29.7 | -26.1 | -27.0 | -27.4 | -17.5 | -20.7 | -22.0 | -26.3 | -9.9 | -14.2 | -9.3 | -5.2 | -1.6 | **-18.7 %** |

Against the kernel aws-lc would actually dispatch to (`crypto/fipsmodule/modes/gcm.c` routes
`len < 256` to the 4x and `len >= 256` to the x8):

| regime | reference | this kernel |
|---|---|---|
| 16-192 B | aws-lc 4x | **-14.7 %** |
| 256-4096 B | aws-lc x8 | **-7.6 %** |
| 16-192 B | aws-lc x8 | **-23.2 %** |

**Why the gain is size-dependent.** Every win targets a *non-overlapped* phase — the SETUP
counter build (before any AES runs), the un-overlapped final GHASH drain (after all AES has
finished), or the short-message paths that skip the 8-block wave entirely. These are fixed
per-call costs, so they dominate small messages and vanish into the steady-state loop for
large ones. The main loop is at ~99 % of the AES crypto-pipe roofline with no realizable
slack, and is untouched — which is why 4096 B moves only -1.6 %.

On a wide out-of-order core the only levers that move the needle are **shortening an exposed
dependency chain**, **removing µops from a phase with no parallel work to hide behind**, or
**not executing the work at all**. Roughly 250 attempts across 30 sessions produced these 30
wins; the ~40 pure-reschedule attempts all measured flat (see "What we dropped", below).

## Kernel structure

```
line   77   cmp x9,#64 ; b.le L256_enc_small     <- ONE short-path test, before the counter build
            8-counter build + 112 aese            <- SETUP, runs only for nb >= 5
line  398   L256_enc_main_loop                    <- g >= 1 only; untouched, at the AES roofline
line  819   L256_enc_prepretail                   <- g >= 1 only; untouched
line 1199   L256_enc_tail                         <- 2-stage dispatch on the remainder
line 1499   L256_enc_epilogue
--------- appended past the epilogue (zero PC shift for everything above) ---------
            exact8_drain / rem4_drain / rem2_drain   <- 3 dedicated tail drains
            L256_enc_small       shared prefix (base counter, Xi, rk0/rk1, tbl index)
            L256_enc_small_1..4  four parallel FUSED bodies (AES and GHASH interleaved)
            L256_enc_small_reduce  ONE shared MODULO reduction + tag store
```

---

## 1. Parallelize the SETUP counter chain (`fdf31b07`)

The eight initial counter blocks were built as a single 7-deep serial `add` chain (each
block = previous + 1); split it into two independent depth-4 chains (a +1 stepper and a
precomputed +2 stepper) so the register renamer runs them in parallel. Correct because the
counter *values* are unchanged; faster because it halves the exposed startup critical path.
**256 B: −2.1 %.**

```asm
; before — each rev32 waits on the previous add        ; after — two chains advance in parallel
  add   v30, v30, v31   ;CTR 0                            add v28, v31, v31   ;+2 vector
  rev32 v1,  v30        ;CTR 1                            add v30, v29, v31   ;chain A -> v30_1
  add   v30, v30, v31   ;CTR 1                            add v29, v29, v28   ;chain B -> v30_2
  rev32 v2,  v30        ;CTR 2                            rev32 v1, v30 / rev32 v2, v29
  add   v30, v30, v31   ;CTR 2  ...                       ...  (A and B independent) ...
```

## 2. Shorten the TAIL odd-block GHASH mid, key side (`8f322a42`)

The Karatsuba "middle" term for odd tail blocks was formed with `ins v27.d[1],v27.d[0]`
(a lane-duplicate that sits *on* the `v27` dependency edge) followed by `pmull2`; replace
it with a `pmull` against the mid-key rotated by `ext`, which depends only on the
already-loaded key. Correct because only the low lane is consumed downstream (identical
value); faster because the mid-product moves off the critical path. **256 B: −4.4 %.**

```asm
; before                                    ; after
  ins    v27.d[1], v27.d[0]  ;on v27 chain     pmull v27, v27, v12   ;h-key in low reg,
  pmull2 v27, v27, v21       ;mid                                    ;off the critical path
```

## 3. Parallelize the TAIL data-side GHASH mid, all 7 blocks (`eb19f411`)

Every tail block built the data-side mid with `ins v27.d[0],v8.d[1]` — a read-modify-write
of `v27` that creates a *false* dependency on the previous block's `pmull v27`, serializing
all seven blocks; replace each with `ext v27,v8,v8,#8`, a full write depending only on `v8`.
Correct because the consumer reads only lane 0 (byte-identical) and `v27`'s clobbered high
lane is dead; faster because the renamer now runs the seven mids in parallel. **512 B: −4.0 %**
(the largest of the two `ins`→`ext` wins — this mid was on the cross-block critical path).

```asm
; before (×7)                          ; after (×7)
  ins v27.d[0], v8.d[1]                  ext v27.16b, v8.16b, v8.16b, #8
  ; RMW -> serial on prev block's v27    ; full write, depends only on v8 -> parallel
```

> Note: `dup vD.2d, vN.d[1]` is the obvious form for #2/#3 but is not decodable by
> `arm/proofs/decode.ml`; `ext` is the provable equivalent that yields the same low lane.

## 4. Dedicated exact-8 tail drain — drop no-op tag XORs (`f95eb1fd`)

The exact-8 fall-through re-executed 7 `eor v8,v8,v16` where `v16 = 0` (plus 6 dead
`movi v16,#0`) — XOR-with-zero identities sitting directly on the drain's critical path,
kept only because they are load-bearing at the shorter remainder entry points. Redirect the
exact-8 branch to a dedicated straight-line drain with those identity ops removed. Correct
because XOR with zero changes nothing; faster because it deletes work from the exposed drain.
**512 B: −2.0 %.**

```asm
; before                                   ; after
  b.gt L256_enc_blocks_more_than_7           b.gt L256_enc_exact8_drain      ; dedicated path
  ; fall-through path re-runs 7x            L256_enc_exact8_drain:
  ; `eor v8,v8,v16` (v16=0, no-op) +          ; one real tag feed, then a straight-line
  ; 6 dead `movi v16,#0`                       ; drain with the 7 no-op eors removed
```

## 5. `eor3`-fuse the tail-drain accumulate chains (`c9a9ee70`)

The drain accumulated each block's high/low/mid Karatsuba products with 21 pairwise `eor`
(three 7-deep serial chains); the main loop already batches these with the 3-input SHA3
`eor3` (one op = two XORs) but the drain did not. Pair the blocks, stash the A-block
products in free registers, and fuse via `eor3 acc,acc,prodB,prodA`. Correct because
`eor3(a,b,c) = a⊕b⊕c` is the same reduction; faster by −9 ops and accumulate-depth 7→4.
**256 B: −7.5 %** (the biggest tail win).

```asm
; before (2 ops per pair, depth +2)        ; after (1 fused op per pair, depth +1)
  eor  v17, v17, v28   ;block-6 high         eor3 v17, v17, v28, v13   ;fused high
  eor  v17, v17, v28   ;block-5 high         eor3 v19, v19, v26, v14   ;fused low
  eor  v19, v19, v26   ; ...                 eor3 v18, v18, v27, v15   ;fused mid
```

## 6. Flatten the SETUP counter chain, depth 4→2 (`67cb82e3`)

Builds on #1: precompute the +2..+7 increment vectors in the base-load / address-arithmetic
shadow (off the critical path), then compute all eight counter blocks in parallel as
`base + offset_k`. Correct because `base + k` yields the same big-endian counters as the
serial cascade (no 32-bit lane wrap in range); faster because the exposed startup path
collapses to `base → one parallel add → rev32 → first AES`. **256 B: −3.2 %.**

```asm
; before (#1's two chains, still stepwise)   ; after
  add   v28, v31, v31   ;+2                    add v28,v31,v31 ;+2 ┐ offsets built in the
  add   v30, v29, v31   ;block via chain A     add v10,v28,v31 ;+3 │ load shadow, off the
  rev32 v1, v30 / v2, v29  (alternating)       add v11,v28,v28 ;+4 │ critical path
  ...   blocks step off each other ...         add v12,v11,v31 ;+5 │
                                               add v13,v11,v28 ;+6 │
                                               add v14,v11,v10 ;+7 ┘
                                               add v8, v29,v31 ;CTR1=base+1 ┐ all 8 blocks
                                               ...  add v30,v29,v14 ;CTR7   ┘ 1 add deep, parallel
```

---

## 7. Dedicated `eor3`-fused remainder drains (`b20e50f1`, `a1fe6c03`, `107b6236`)

The same treatment as #4/#5 applied to the remainder paths the benchmark sizes actually hit.
`rem=4` (192 B) and `rem=2` got dedicated `eor3`-fused drains; `107b6236` later stripped
`rem4_drain`'s three surviving no-op tag `eor`s and completed `small_3`'s fusion into a
3-way fold (accumulate depth 2→1). **64 B −2.6 %, 32 B −3.4 %, 192 B −1.1..−2.4 %.**

## 8. Skip the tail slide cascade for hot remainders (`a6279cf5`)

Reaching a remainder's entry point in the shared cascade costs up to **21 register `mov`s +
7 `sub`s** of keystream shuffling, because the shared body always reads `v1..v7`. A two-stage
dispatch peels the hot cases (`rem=8`, `rem=2`) into appended code *before* any sliding.
The cost decomposition is the interesting part: the slides cost **−2.1 ns**, while gutting
**all 112 SETUP `aese`** was worth only **−0.9 ns** — register shuffling cost more than the
entire AES setup, because the AES was latency-hidden and the `mov`s were not. **32 B −4.3 %.**

## 9. Round-major SETUP AES schedule (`ae75222c`)

The generator emitted the eight blocks in a different scrambled order in each of the 14
rounds (block 0 sat at position 4, 8, 7, 8, 5, 1, 6, 2, 4, 8, 7, 6, 4, 4). Within a round all
eight `aese` use the same round key and touch distinct registers, so they are mutually
independent and any permutation has identical throughput — the only thing order controls is
*which block gets the earliest issue slots*. Fixing the order to `0..7` gives issue priority
to the blocks a short message actually consumes. A **pure permutation**: identical instruction
multiset, identical `.o` size, no PC shift — the cheapest possible re-prove. **32 B −2.7 %.**

## 10. Early dispatch — don't execute the wasted work (`e88719b2`, `0a98fae9`, `c313cb00`, `abc66939`, `424a8e5b`)

The original kernel is structurally *flat*: it always runs a full 8-block wave. At 16 B it
built 8 counters, executed **112 `aese`**, and discarded 7 of 8 keystreams. Dedicated
straight-line bodies for exact block counts skip that. **16 B −30 %, 48 B −24 %, 32 B −8.1 %,
64 B −10.9 %.** Moving the test *before* the counter build bought a further **−2.5 % / −4.9 %**
and broke two independently "confirmed" floors — the counter build was itself wasted work.

The other half of the win is structural: for `nb <= 8` the main loop and prepretail never
run, so the generic path degenerates to `SETUP (217 aese, 0 pmull) → tail (0 aese, 28 pmull)`
— all the AES, then all the GHASH, with nothing to overlap the drain against. A fused
short body restores the interleaving the loop would have provided.

## 11. `tbl` tail-formatting (`82ef4d58`, `7bfbcc37`, `3373f5ab`)

The final 16-byte tag byte-reversal was `ext` + `rev64`, two serially dependent ops on the
function's last dependency edge. One `tbl` with a precomputed index does it in one. The index
costs 10 instructions to build — but they sit in the AES shadow where the integer and permute
pipes are idle, so **+10 instructions in free slots buys −1 instruction from the serial tail.**
**16 B −3.2 %, 32 B −2.7 %, 48 B −2.7 %, 64 B −2.2 %.**

## 12. Fused `nb <= 4` short path (`3f893a36`, `de217086`, `5725221e`, `8476aeda`, `279a0daf`)

The seven dedicated `fastN` dispatch tests collapse to **one** `cmp x9,#64 / b.le`, with four
parallel width-specific bodies behind a shared prefix and a shared reduction suffix. Adopted
from nebeid's encrypt short-path experiment; the four structural items are the shared setup,
one shared final GHASH reduction suffix (**−120 B**), direct final-counter construction
(deleting 22 counter-rollback `sub`s, **−80 B**), building the `tbl` index once instead of
four times (**−120 B**), and a per-width counter build (**+24 B but 16 B −2.8 %**: removing 6
dead SIMD ops from ahead of the 1-block dispatch cuts crypto-pipe contention). `.text`
11848 → 7424 B.

## 13. Re-roll the fused bodies' AES (`b5ca504a`, `d4d08b19`)

Each body's fully-unrolled 14-round AES becomes a 13-iteration loop over `rk0..rk13` plus a
peeled final round. The loop overhead (`ldr`, `subs`, `b.ne`) executes in the scalar and load
pipes, which are idle while the two crypto pipes are the bottleneck, and the branch is
perfectly predicted. **−960 B across the four bodies, speed-neutral at every size** —
including 16 B, where the loop overhead hides behind the single block's AES latency.

Counter-intuitively the *narrow* bodies benefit most: `small_4` gave −384 B, `small_1/2/3`
together gave −576 B. **The code shrinks 5x but the proof does not** — HOL reasons about the
executed trace, which is unchanged, and because the trip count is the literal 13 the stepper
follows the concrete `b.ne` and needs no loop invariant.

## 14. Reuse a fused drain from inside the generic cascade (`8cb29b6d`)

`L256_enc_blocks_more_than_3` is reached only by fall-through from `rem 5/6/7`, and its body
is operation-identical to `rem4_drain`'s first block — same H-power, same keystream register,
same next-ciphertext — but it continues onto the *unfused* pairwise cascade. Overwriting its
redundant leading `st1` (which `rem4_drain` re-does) with `b L256_enc_rem4_drain` sends those
three sizes onto the `eor3`-fused drain. **Exactly one instruction word differs and `.text` is
unchanged**, so every appended drain keeps its PC — which is what let `TAIL_REM4` be reused
verbatim. **80/96/112 B −3.3 / −3.4 / −3.4 %.**

---

## What we dropped, and why

### Dropped from the final kernel

| dropped | why | what it cost |
|---|---|---|
| **`fast5`/`fast6`/`fast7`** — dedicated 80/96/112 B bodies (`bbaea3d0`, worth −18.3/−15.7/−9.7 %) | The fused design permits exactly **one** short-path entry test, and each extra width costs ~1045 B (measured). Keeping all seven put `.text` at 11848 B, 2.5x the original. | 80/96/112 B regressed **+11-14 %**, of which −3.3/−3.4/−3.4 % was recovered by #14. Restoring all three would cost ~3140 B. |
| **The seven `fastN` entry points** as separate tests | Collapsed into one `cmp x9,#64 / b.le`. | Nothing — their **bodies survive** as `small_1..small_4`, with the `tbl` formatting, `eor3` drains, clone-cleanup and dispatch-before-counter-build all intact. This is a restructure, not a loss. |
| **`fast2`/`fast4` dead AES prefixes** (784 B) | Unreachable after the `em` variants superseded them: 784 bytes containing no executed instruction. | Nothing. |
| **Front-load SETUP into phase groups** (`1196c23b`) | Landed, then **reverted** (`451de5b3`). The 8-way braid is load-bearing — it is what keeps both crypto pipes fed. Splitting SETUP into phases serialises the thing that was hiding the latency. | It was **+5.6 / +9.6 / +10.8 % at 128 B** and saved only 212 B. |

### Considered and rejected — measured, not assumed

| rejected | measured result | why |
|---|---|---|
| **Chaining the fused bodies into one-block stages** (nebeid's decrypt shape) | **64 B +43.1 %** (flat chain), +27.7 % (2-block stages), +44.6 % (no stub). Reached `.text` 6528 B. 6 designs. | In **encrypt** the AES must finish before GHASH can consume the ciphertext, so braiding 4 blocks is the only thing filling the two crypto pipes. In **decrypt** GHASH consumes the *input* ciphertext and never waits on AES — which is why the chain works there and not here. |
| **nebeid's literal reversal index** (`.byte 15,14,…,1,0` + `ldr q12,<label>`) — 20 B smaller and ~1 % faster than our hoisted synthesis | n/a | **Unprovable**: `arm/proofs/decode.ml` has no PC-relative `LDR (literal)` decode rule (0 of 172 rules match the `0b*011100` shape), so symbolic execution cannot step the instruction. Closing this needs an upstream `decode.ml` extension. |
| Manual `aese`/`aesmc` regrouping | **+31 %** | The hardware **fuses** adjacent `aese`+`aesmc` pairs; breaking the adjacency can only lose. |
| Interleaving independent AES chains | **+36 %** | Only 2 crypto pipes. The code is *resource*-bound, not latency-bound, so interleaving buys nothing and costs register pressure. |
| `tbl` tail-formatting on `fast5/6/7` | mixed, 80 B worse | Those widths have no idle permute slot to hide the index build in. `ext`+`rev64` is correct there. |
| Hoisting the `tbl` index into shared SETUP | rejected | `v25` is a **live H-power** there. |
| Counter arithmetic in GP registers via `fmov` | worse everywhere | `fmov` shares the vector pipe **and** is a read-modify-write. |
| Parallel accumulators in `fast4_drain` | +0.9 ns | The accumulate was not the bottleneck; the reduction was. |
| Shift-based reduction instead of `pmull`; schoolbook instead of Karatsuba | flat / sub-2 % | The 2-serial-`pmull` reduction is a hard latency floor, byte-identical to aws-lc's. |
| **Flattening the counter chain in the main loop** (the same transform as #1/#6) | **flat**; depth-2 **impossible** | The loop is issue-bound (224 crypto ops / 2 pipes ≈ 112 cycles) so the counter chain has ~100 cycles of slack, and **zero** registers are free across the loop back-edge to hold the offset constants. Same edit, opposite outcome, because the binding constraint differs. |
| **~40 further attempts, all flat** | — | Instruction rescheduling, `.balign` alignment, `prfm` prefetch, register reallocation, breaking WAR/false deps on already-renamed registers, load hoisting, early constant materialization, H-table load hoisting, index-build 10 ops → 1, counter-sub collapse, modulo-constant hoist. All absorbed by the out-of-order engine. |

### Four "floors" that were confirmed and then broken

Worth recording because each was declared unimprovable by an independent session before falling.

| claim | how it ended |
|---|---|
| "32 B floor CONFIRMED 3rd time" (three sessions) | broken by `fast2`, **−8.1 %** |
| "64 B near floor" | broken twice — `fast4` **−10.9 %**, then the drain clone-cleanup −5.5 % |
| "32/64/128 B at a dependency-latency floor" (two fresh-eyes sessions, 25 attempts) | broken by dispatch-before-the-counter-build, −2.5 % / −4.9 % |
| "28N instructions of unrolled AES is irreducible" | broken by the AES re-roll: **−960 B, speed-neutral** |

The lesson those produced, learned expensively: **a work-removal probe bounds only the
instructions it deletes.** Gutting all 112 SETUP `aese` measured −0.9 ns, so four sessions
concluded early dispatch was not worth building. When it was finally built it measured
−2.9 ns — about 3x the probe's ceiling — because the structural change also removed the
counter build and narrowed the drain.

---

## Cross-cutting notes

- **Three mechanisms cover all thirty wins:** shorten an exposed serial dependency chain
  (#1, #6, #9 in SETUP; #5, #7 in the drains); eliminate a false dependency or dead µop
  (#2, #3 `ins`→`ext`; #4, #8 no-op and slide removal; #11 `tbl`); or don't execute the work
  at all (#10, #12, #14). None of them helps inside the AES-saturated main loop — the same
  edits there measured as noise, and one (main-loop counter flattening) is provably impossible
  for want of free registers.
- **`ins` is the recurring trap.** It writes one lane and *preserves* the other, so the old
  value is an architectural input and the renamer cannot break the dependency. `ext`, `dup`,
  `rev64` and `tbl` write the whole register and don't. "Is there a read-modify-write on a
  live register?" became the first question asked of any exposed chain. (`dup`'s element form
  is not decodable by `decode.ml`, so `ext` is the provable equivalent.)
- **Append, never insert.** Every new path lives past `L256_enc_epilogue` and is reached by
  redirecting exactly one existing branch, so no pre-existing instruction moves and no PC
  anchor in the 15,000-line proof shifts. That pattern landed 9 times. Deleting or inserting
  mid-file forces a whole-file re-anchor of ~70 anchors.
- **Proof-adaptation cost varied by three orders of magnitude.** A pure permutation (#9) needs
  only the machine-code literal regenerated. Count-preserving opcode swaps (#2, #3) need no
  PC shift. Appended paths re-drive one leg. Deletions mid-file re-anchor everything. In every
  case the exported goal stayed byte-identical.
- **XOR's algebra is what makes the drain work cheap to re-prove.** `eor3` fusion is XOR
  reassociation and no-op removal is the GF identity, so the register state at the fold point
  is byte-identical and `TAIL_Q19_FOLD*` is reused verbatim. Only step indices move.
- **What is provably *not* improvable here** (measured, not assumed): the `rev32` counter
  byte-reversal (correctness-required for big-endian carry), the 2-serial-`pmull` modulo
  reduction, and any main-loop reschedule, alignment or load-coalescing (the loop is
  crypto-pipe saturated and register-full).
- **The `< 256 B` wins currently reach no caller.** aws-lc's `len >= 256` dispatch gate means
  no 8x kernel runs below 256 B today; realising the 16-192 B column needs that threshold
  lowered.
