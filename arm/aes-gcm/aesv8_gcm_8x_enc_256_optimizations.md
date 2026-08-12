# Runtime optimizations — `aesv8_gcm_8x_enc_256`

Six machine-code optimizations applied to the AES-256-GCM 8x whole-blocks encrypt
kernel. Each was verified three ways before being committed: it passes `tests/test.c`,
it is **≥2 % faster** on `benchmarks/benchmark.c` (measured twice), and the HOL Light
correctness proof (`arm/proofs/aesv8_gcm_8x_enc_256.ml`) re-passes **0-CHEAT with a
byte-identical goal** against the new `.o`. The specification and the exported
`*_SUBROUTINE_CORRECT_GEN` statement were never changed — only the assembly and the
proof tactics.

## Result

| size    | baseline | optimized | speedup   |
|---------|---------:|----------:|----------:|
| 256 B   | 80.4 ns  | 66.1 ns   | **−17.8 %** |
| 512 B   | 124.0 ns | 109.7 ns  | **−11.5 %** |
| 1024 B  | 213.1 ns | 199.1 ns  | **−6.6 %**  |
| 4096 B  | 739.0 ns | 726.5 ns  | −1.7 %    |
| geomean | 199.1 ns | 180.5 ns  | **−9.3 %**  |

**Why the gain is size-dependent.** All six wins target the two *non-overlapped* phases
— the SETUP counter build (before any AES runs) and the un-overlapped final GHASH drain
(after all AES has finished). These are fixed per-call costs, so they dominate small
messages and vanish into the steady-state loop for large ones. The steady-state main loop
is already at ~99 % of the AES crypto-pipe roofline and was measured to have no realizable
slack, so it is untouched. On a wide out-of-order core (Neoverse-V1 / Graviton3) the only
levers that move the needle are **shortening an exposed dependency chain** or **removing
µops** on a phase that has no parallel work to hide behind.

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

## Cross-cutting notes

- **Two mechanisms cover all six wins:** shorten an exposed serial dependency chain
  (#1, #6 in SETUP; #5 in the drain) or eliminate a false dependency / dead µop
  (#2, #3 `ins`→`ext`; #4 no-op removal). Both only help in the non-overlapped phases;
  the same edits inside the AES-saturated main loop measured as noise.
- **Proof-adaptation cost varied.** The `ins`→`ext` swaps (#2, #3) are count-preserving
  in-place opcode changes — no PC shift, cheapest to re-prove. The chain reshapes that add
  instructions (#1, #4, #6) shift PC anchors and SETUP-family step indices and are the
  costlier re-proves. In every case the exported goal stayed byte-identical.
- **What is provably *not* improvable here** (measured, not assumed): removing the `rev32`
  counter byte-reversal (correctness-required for big-endian carry), and any main-loop
  reschedule/alignment/load-coalescing (the loop is crypto-pipe saturated and register-full).
```
