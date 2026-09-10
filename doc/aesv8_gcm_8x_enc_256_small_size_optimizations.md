# `aesv8_gcm_8x_enc_256`: small-input optimizations and their proof cost

How the AES-256-GCM 8x encrypt kernel was made faster for inputs of 16–128 bytes,
and what each change required of the HOL Light proof.

Target: Neoverse V1 / Graviton3. All timings are `benchmarks/benchmark.c`,
`taskset -c 20`, idle core, min of 3 runs.

---

## 1. The problem

The kernel is *8x-unrolled*: its setup phase unconditionally builds 8 counter
blocks and runs all 14 AES rounds on all 8 of them — 112 `aese` — before it ever
looks at how many bytes it was given. It then enters a **fall-through tail
cascade** that handles remainders 1–8 by starting at the rem=8 label and sliding
keystreams down one register at a time.

At small sizes both phases are mostly waste. Executed-instruction counts
(gdb single-step, deterministic):

| input | blocks | instrs | `aese` | wasted `aese` |
|---|---|---|---|---|
| 16 B | 1 | 370 | 112 | 98 |
| 48 B | 3 | 395 | 112 | 70 |
| 128 B | 8 | 404 | 112 | 0 |

48 bytes took **395 instructions to encrypt 3 blocks** — more than 128 bytes
needs for eight.

## 2. What works on this microarchitecture, and what does not

Roughly 40 measured attempts established that the out-of-order engine already
handles the usual tricks. **Expect these to be flat:** instruction
rescheduling, `.balign` alignment, software prefetch (`prfm`), register
reallocation, breaking WAR/false dependencies on already-renamed registers,
hoisting loads, early constant materialisation. Regrouping `aese`/`aesmc` pairs
measured **+31 % worse** — the hardware fusion is already optimal.

Only two things ever won:

> **(a) remove an instruction from the true dependency chain, or
> (b) do not execute the work at all.**

Every mechanism below is one or the other.

## 3. The mechanisms

### 3.1 Early dispatch — *don't execute the work* (dominant)

Test the block count at function entry and jump to an appended path that builds
**only** the counters and keystreams actually needed, then falls into a dedicated
drain. Seven such paths exist (`fast1`…`fast7`), one per block count 1–7.

| input | `aese` before | after |
|---|---|---|
| 16 B | 112 | **14** |
| 64 B | 112 | **56** |
| 112 B | 112 | **98** |

This is the largest lever at 16–112 B and worth nothing at 128 B, where all
eight keystreams are genuinely used.

**Why it needs duplicated code rather than a jump.** The setup AES is
*round-major*: round 0 for blocks 0–7, then round 1 for blocks 0–7, and so on for
14 rounds. The work to keep and the work to skip are interleaved instruction by
instruction, and a branch can only skip a contiguous range — so there is no
program point where "blocks 0–1 are done and 2–7 have not started". Emitting the
un-braided sequence *is* the optimization.

Restructuring setup into phase groups so a branch could exit early was measured
and **rejected**: front-loading 2 blocks costs +5.6 % at 128 B, 4 blocks +9.6 %,
2+2 blocks +10.8 %. With two crypto pipes and ~4-cycle `aese` latency, at least
four independent blocks must be in flight to saturate; a 2-block group half-idles
the pipes. It also is not a pure permutation — only `q26`/`q27`/`q28` recycle to
hold all 15 round keys, so each group after the first must reload the whole key
schedule.

### 3.2 Dedicated drains — peel out of the cascade

The shared tail handled every remainder by entering at rem=8 and *sliding*
keystreams down with `mov` chains, a serially dependent `sub v30,v30,v31` counter
decrement, and a `cmp`/branch per step. A 32-byte call walked six slides it did
not need. Peeling the common remainders into straight-line drains removed that.
Worth −4.3 % for rem=2 alone.

### 3.3 `eor3` fusion — *shorten the chain*

`eor3` is a three-input XOR. It collapses the drains' pairwise GHASH accumulate
trees from 21 dependent `eor`s at depth 7 to 12 operations at depth 4.

### 3.4 Removing GF-identity no-ops — *don't execute the work*

Seven tag `eor`s XOR against values provably zero. Free when overlapped with
other work in the generic path; pure latency on an exposed drain.

### 3.5 False-dependency elimination: `ins` → `ext` — *shorten the chain*

The Karatsuba mid term needs each block's high 64-bit lane moved to the low lane.
`ins v27.d[0], v8.d[1]` is read-modify-write: because it must preserve v27's other
lane it depends on whoever last wrote v27, serialising all seven blocks' mid terms.
`ext v27,v8,v8,#8` computes the same value but writes the whole register, so it
depends only on v8. **Identical instruction count, one edge deleted from the
dependency graph.** The single largest delta in the campaign (−6.4 ns at 256 B),
though modest below 64 B.

### 3.6 Counter-chain flattening — *shorten the chain*

Counter *n+1* = counter *n* + 1 via `rev32`/`add`/`rev32` (the big-endian counter
must be byte-swapped to increment) was a **7-deep** chain gating when later
blocks' AES could start. Split to two chains of depth 4, then to **depth 2** by
materialising eight `+0..+7` offset vectors so every block computes as
`base + offset` independently.

### 3.7 Byte-reverse via `tbl`

The drain must byte-reverse the ciphertext before GHASH. `ext` + `rev64` (two
dependent vector ops) became a single `tbl` with a precomputed index, built in the
AES shadow. Valid only where the index register is dead on that path — `v25` is
live in the main loop as an H-table value, so this cannot be hoisted into shared
setup.

### 3.8 Clone hygiene

A drain cloned from a generic one carries plumbing that is dead on the specialised
path — keystream-copy `mov`s and no-op tag `eor`s. Deleting them was worth
**−5.5 %**. Cloning is how these paths get written quickly; auditing the clone is
a separate and profitable step.

## 4. Where the changes are, and are not

For inputs ≤128 B the main loop and prepretail **never execute** (`g = 0`), and
since early dispatch landed, the four smallest sizes do not even run setup.

| region | bytes | optimizations applied |
|---|---|---|
| setup / preloop | 1,268 | counter flattening, AES consumption-order permutation |
| **main loop** | 1,360 | **none** |
| **prepretail** | 1,232 | **none** |
| original tail cascade | 740 | `ins`→`ext` |
| appended paths + drains | 7,216 | everything else |

The two largest regions were never touched — deliberately. A roofline
measurement put the main loop at ~99 % of AES peak, and it does not run at these
sizes anyway.

## 5. Result

| input | before | after | vs aws-lc original 8x | vs aws-lc 4x |
|---|---|---|---|---|
| 16 B | 42.4 | **30.0** | −29.2 % | −7.7 % |
| 32 B | 43.4 | **32.0** | −26.3 % | −10.4 % |
| 48 B | 45.0 | **33.4** | −25.8 % | −10.9 % |
| 64 B | 47.0 | **34.4** | −26.8 % | −10.6 % |
| 80 B | 49.2 | **37.2** | −24.4 % | −25.9 % |
| 96 B | 52.7 | **39.0** | −26.0 % | −25.3 % |
| 112 B | 55.4 | **40.9** | −26.2 % | −23.6 % |
| 128 B | 60.3 | **42.7** | −29.2 % | −22.1 % |

**Cost:** `.text` grew 4,672 → 11,848 B (2.54×). Of the labelled regions, 68 % is
now specialised paths and drains. These benchmarks keep the kernel hot in
I-cache; a workload interleaving other code could see instruction-cache pressure
this harness cannot show.

**Note on reachability:** aws-lc's dispatch
(`crypto/fipsmodule/modes/gcm.c`) currently routes to an 8x kernel only at
`len >= 256`, and to the 4x kernel below that. These gains therefore reach no
caller until that threshold is lowered — which this work is what makes
defensible, since the 8x kernel now beats the 4x at every size rather than losing
below 128 B.

---

# Proof changes

The proof is `arm/proofs/aesv8_gcm_8x_enc_256.ml`, a layered case split with 41
named legs.

## 6. The invariant

**The exported statements were frozen.** `..._SUBROUTINE_CORRECT` and
`..._SUBROUTINE_CORRECT_GEN` are byte-identical across every optimization —
same quantifiers, same pre/postcondition, same `MAYCHANGE` frame, never widened.
No spec definition (`aes256_cipher`, `nist_ghash`, `ctr_block`, …) was touched.
No `cheat`, `mk_thm` or `SORRY_TAC`. So no optimization could be made to "pass"
by proving something weaker; only tactics and internal lemmas changed.

## 7. What each optimization required

**1. Regenerate the machine-code literal.** `define_assert_from_elf` re-reads the
`.o` at load time and asserts the literal equals it, so a stale literal fails
before any theorem is attempted. Currently 2,962 words = 11,848 bytes.

**2. Add a leg per new code path.** Each `fastN` needed two:

- `..._FASTN` — the specialised path itself
- `..._FASTN_TAIL` — its drain, **with the keystreams as preconditions**

**3. Add a case arm** in `..._CORRECT_ALL` routing that block count to the new leg:

```ocaml
ASM_CASES_TAC `nb = 1` THENL
 [(* nb = 1 (16B): the fast1 early-dispatch path *)
  ... AESV8_GCM_8X_ENC_256_FAST1) THEN
```

The generic legs (`MAIN_LOOP`, `PREPRETAIL`, `TAIL_REM1`…`TAIL_REM8`) were left
untouched; the top-level theorem still covers all `nb >= 0`.

## 8. Why it stayed affordable

**Append new code after the epilogue and redirect exactly one existing branch.**
That shifts no existing PC anchor, so only the touched leg re-drives symbolic
execution. Applied seven times, at roughly one session each.

The contrast is instructive: the one change that inserted instructions *mid-file*
(the rejected setup restructuring) shifted **71 PC anchors** and required a
single-pass re-anchor of the whole file plus re-driving the entire setup family.

## 9. Two traps worth documenting

**The `ENSURES_SEQUENCE` split point.** It must be at the **tail-setup start**,
not at the drain entry. After the long AES history, `ARM_STEPS` drops the inline
`eor3` ciphertext write because a raw `Q0` fact shadows the folded value. This is
why every `FASTN_TAIL` leg takes the keystreams as preconditions rather than
deriving them. Getting this wrong cost three sessions.

**Stale `DISCARD` lists.** The proof drops dead register facts to keep load time
down. When a code change makes a previously-dead register *live*, a blanket
discard silently deletes the fact that is now needed, and it surfaces far
downstream as an opaque `Exception: Failure "AP_TERM_TAC"` that never names the
register. Fix: replace the blanket discard with an explicit `DISCARD_REGS` list
that keeps the newly-live register. Audit these lists first whenever an added
instruction reads a new register.

Minor: a `MATCH_MP_TAC` "No match" can simply mean a conjunct sits at a different
position in the `ENSURES_SEQUENCE` target than in the leg's precondition —
conjunction order matters. And the final `NSTEP` range must include the appended
block's trailing branch to the epilogue.

## 10. Acceptance criterion

Nothing was committed until the full file passed a cold load with **0 cheats,
exactly 3 axioms, and both exported subroutine theorems at 0 hypotheses**. A
faster kernel whose proof could not be adapted was reverted rather than shipped.

## 11. Reproducing

```sh
export HOLDIR=<path to hol-light>
cd arm && make aes-gcm/aesv8_gcm_8x_enc_256.correct
grep -c "Running time" aes-gcm/aesv8_gcm_8x_enc_256.correct      # 1 = finished
grep -icE "error:|exception:" aes-gcm/aesv8_gcm_8x_enc_256.correct # 0 = passed
```

The `.correct` file is written incrementally, so its existence does not mean the
run finished — check for the `Running time` line.

---

## Addendum 2026-09-10 -- the fused short path (supersedes the seven `fastN` paths)

The seven dedicated `fastN` paths described above were **replaced by a single fused
`nb <= 4` short path** (`3f893a36`), then refined through `279a0daf`. Current kernel
`.text` **6488 B** (was 11848 B at the seven-path peak).

### Structure now

```
line   77   cmp x9,#64 ; b.le L256_enc_small        <- the ONE entry test, before the counter build
            ... 8-counter build + 112 aese ...      <- runs only for nb >= 5
line 1499   L256_enc_epilogue
--------- appended past the epilogue ---------
            L256_enc_small          shared prefix: reversed base counter, Xi, rk0/rk1, tbl index
            L256_enc_small_1..4     four parallel FUSED bodies (AES and GHASH interleaved)
            L256_enc_small_reduce   ONE shared MODULO reduction + tag store
```

### The five mechanisms added since the original document

| mechanism | what it does | effect |
|---|---|---|
| **fused `nb<=4` dispatch** | one `cmp x9,#64 / b.le` replaces seven `b.eq` tests; four braided bodies share a prefix | `.text` -34%; 80/96/112 B +11-14% (they lose their dedicated bodies) |
| **shared reduction suffix** | the maximal common tail (11 instrs: `ldr d16` -> MODULO fold -> `tbl v12` -> `st1` -> `b epilogue`) factored out of all four bodies | -120 B, speed TIE |
| **direct final-counter construction** | build the needed counter as `base + N` instead of subtracting back down from `base+8` -- deletes 22 rollback `sub`s | -80 B, speed TIE |
| **index built once** | the 10-instruction `movz`/`movk`/`fmov` reversal-index synthesis hoisted from all four bodies into the shared prefix | -120 B; 16 B flat/faster |
| **AES re-roll** | each body's 14-round unrolled AES becomes a 13-iteration loop over `rk0..rk13` + a peeled `rk13`/`rk14` | **-960 B**, speed-neutral at every size |
| **per-width counter build** | stop building counters 1-3 unconditionally ahead of the internal dispatch | +24 B but **16 B -2.8%** (removes 6 dead SIMD ops from before the 1-block dispatch, cutting crypto-pipe contention) |
| **rem 5/6/7 -> fused drain** | `mt3`'s body is operation-identical to `rem4_drain`'s first block, so overwrite its redundant leading `st1` with `b rem4_drain`; rem 5/6/7 finish on the `eor3`-fused drain instead of the pairwise cascade | 80/96/112 B **-3.3/-3.4/-3.4%**, `.text` unchanged, ONE instruction word differs |

### Proof cost of these seven

Every one re-proven 0-CHEAT / 3 axioms / both exported subroutine theorems at 0 hypotheses,
with the spec definitions and both `*_SUBROUTINE_CORRECT*` statement blocks byte-identical.
All the edits live **past `L256_enc_epilogue`**, so the main loop, prepretail, generic cascade,
the three tail drains and SETUP keep their PCs -- blast radius is the four `SMALL_*` legs, their
tails, and the `mc` literal.

Two techniques carried the cost:

- **The AES re-roll drives via a FLAT `MAP_EVERY NSTEP` range.** `ARM_STEP` auto-follows the
  concrete `b.ne` because the loop counter decrements deterministically, so no loop invariant is
  needed -- the trip count is a literal 13. Body steps = linear + 12x(3+2N) = 152/125/98/71 for
  N=4/3/2/1. **The re-roll makes the code 5x smaller but the proof no smaller**: HOL reasons about
  the executed trace, which is unchanged.
- **`TAIL_Q19_FOLD*` is reusable verbatim** for the shared suffix, the direct counter and the
  re-roll, because none of them changes the register state at the fold point.

Traps that cost real time: a re-rolled body's `NSTEP` range **10 steps too short** stops mid-13th
iteration and surfaces ~100 lines later as an opaque `AP_TERM_TAC` (s139); `fold_q19_at` carries a
hardcoded state index that must track any drain shift; and `DISCARD_REGS` silently drops facts for
registers a change makes newly live (`82ef4d58` had to explicitly KEEP `Q25` for this reason).

### What was NOT ported, and why

nebeid's kernel loads the reversal index from a `.balign 16` `.byte 15,14,...,1,0` table with one
`ldr q12,<label>`. That is 20 B smaller and ~1% faster than our hoisted synthesis, but
**`arm/proofs/decode.ml` has no PC-relative `LDR (literal)` decode rule** (0 of 172 rules match the
`0b*011100` shape), so symbolic execution cannot step the instruction. Same wall `prfm` hit.
