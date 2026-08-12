# `aesv8_gcm_8x_enc_256.ml` — Theorem Map

Schematic guide to the theorems in `arm/proofs/aesv8_gcm_8x_enc_256.ml`: what each layer
proves, why it is needed, and how they compose into the final result.

**Target kernel:** AES-256-GCM 8×-unrolled **encrypt**, whole-blocks-only variant
(`aesv8_gcm_8x_enc_256`). Input length must be a multiple of the 16-byte block (a runtime
guard `tst x1,#127; b.ne` rejects anything else).

---

## The final target (top of the pyramid)

```
AESV8_GCM_8X_ENC_256_SUBROUTINE_CORRECT_GEN   (line 10993)
    ← THE deliverable: correct for ANY input_len >= 0 (arbitrary whole-block count nblocks >= 0,
      including zero-input early return)
    └─ wraps WB_CORRECT_ALL through the C ABI (stack save/restore, ret, calling convention)
```

Everything below exists to build this theorem.
`AESV8_GCM_8X_ENC_256_SUBROUTINE_CORRECT` (line 10860) is the earlier NARROW twin
(only nblocks = 8*(k+2), k>=1, i.e. multiples of 8 and >= 24); kept for provenance.

---

## Layer 1 — Spec / algebra lemmas (≈ lines 1261–1730): "the math the hardware matches"

Prove the AES and GHASH byte-order / field / Karatsuba identities. Used everywhere below.

| Group | Theorems | Why needed |
|---|---|---|
| Byte-order toolkit | `WORD_SUBWORD_REVERSEFIELDS`, `BS_XOR` / `BS_INVOL` / `BS_INVOL2` / `BS_INJ` / `BS_EXT`, `WORD_SUBWORD_BYTESWAP128`, `EXT_TO_JOIN` | reconcile the byte-reversed / 64-bit-lane-swapped register values with the abstract spec |
| AES equivalences | `AES_SUB_BYTES_SHIFT_ROWS`, `AES_SUB_BYTES_REVERSEFIELDS`, `FIPS197_EQ_SHIFT_ROWS`, `FIPS197_EQ_MIX_COLUMNS`, `AES256_CIPHER_RECONSTRUCT`, `XOR_AES256_CIPHER_RECONSTRUCT`, `AES256_CIPHER_KEYLIST`, `CIPHER_BLOCK_NIST` | prove the hardware AES rounds = the FIPS-197 `aes256_cipher` spec |
| Counter blocks | `WORD_SUBWORD_CTR_BLOCK_32`, `CTR_BLOCK_RECONSTRUCT_REV8/REV32`, `AES_CTR_BLOCK_RECONSTRUCT` | prove the counter register value = `ctr_block nonce i` |
| GHASH multiply | `PMUL_KARATSUBA_JOIN(_ALT)`, `POLYVAL_REDUCE_G2`, `BYTESWAP128_G2_PROP3`, `GHASH_REDUCE_RAW_IS_POLYVAL_G2`, `GHASH_REDUCE_RAW_KARATSUBA_IS_DOT`, `PROP3_XOR`, `GHASH_REDUCE_RAW_XOR`, `KARATSUBA_IS_DOT_HW`, `DOTSUM_IS_PROP3SUM`, `REORD_CROSS`, `GHASH_REDUCE_RAW_DIST8(_HW/_B0/_PLAIN)`, `A0_LO/A0_HI/KDOT_B0` | prove the 3-pmull Karatsuba reduce (`ghash_reduce_raw`) = the spec `polyval_dot` / `nist_ghash` fold |

Representation note (verified from defs):
- `word_reversefields 8` = full 16-byte reverse — carried by memory-facing values (tag, ivec, keys, blocks).
- `byteswap128` = 64-bit **lane swap** (`word_join (low64) (high64)`) — carried by the H-power htable entries.
- `ghash_twist` = ×x in GF(2^128) — applied to the GHASH key H so the pmull-then-reduce comes out right.
- The multiply reads operands via `word_subword _ (0,64)` / `_ (64,64)` (lanes), so differing per-operand
  layouts are fine: the proof tracks each lane. No byte-order layer is needed AT the reduce; the reduce's
  `p2<->p3` argument order is a lane-naming convention (Q17=hi,Q18=mid,Q19=lo vs g2's hi,lo,mid).

---

## Layer 2 — Control-flow / branch + decomposition lemmas (≈ 2333–2790, 10076–10185)

Small lemmas proving *which branch the CPU takes* for a given block count, plus the block-count math.

| Theorems | Role |
|---|---|
| `X5_END_PTR(_GEN)`, `SETUP_X5_END_GEN`, `SETUP_GE_FALSE(_2)`, `SETUP_BRANCH_COND_FALSE(_2)(_GEN)`, `SETUP_BRANCH_COND_TRUE_2` | the loop-entry / tail-entry `b.ge`/`b.lt` decisions |
| `WB_ROUNDDOWN`, `WB_GROUPS0`, `WB_REM_BOUNDS`, `WB_X5_GROUPS0`, `WB_BRANCH_COND_TRUE` | block-count decomposition `nblocks = 8*g + rem` for the general proof |
| `WB_GUARD1_NONZERO(_GEN)`, `WB_GUARD2_MASK(_GEN)`, `WB_X9_NORM` | the entry guards (`cbz x1`, `tst x1,#0x7f`) |
| `BRIDGE_GE`, `IV_ADD`, `FLAG_LEM` | misc arithmetic/flag bridges |
| per-arm branch: `TAIL_X5_128`, `TAIL_X5_REM1..7`, `TAIL_X5_128_G` | the `cmp x5,#..; b.gt` cascade resolution for each remainder arm |

---

## Layer 3 — The four "phase" theorems (execution segments)

Heavy symbolic-execution proofs, each covering a PC range of the routine.

```
WB_SETUP        (4096)  prologue: key/counter/GHASH init          pc 0x38 ..0x4a0
WB_MAIN_LOOP    (3347)  the 8-block streaming loop body           pc 0x4a0..0x9f0
WB_PREPRETAIL   (4943)  loop -> tail drain transition             pc 0x9f0..0xec0
WB_TAIL         (5640)  final full 8-block group + GHASH reduce   pc 0xec0..end
                        + tag store
```
Supporting sub-proofs used inside these: `WB_AES_SETUP` (1762), `WB_GHASH_REDUCE` (1915),
`SETUP_Q30_LANES` (3845), `TAG_STORE_REV64` (5338), `IVEC_STORE_REV32` (5358),
`KS_SOLVE` (5392), `NCB_ETA` (5404).

---

## Layer 4 — Generalization legs (the `input_len >= 0` work)

The Layer-3 phases originally assumed nblocks >= 24. These cover the small / remainder cases so the
proof holds for ALL whole-block counts.

| Theorem(s) | Covers |
|---|---|
| `WB_RETURN0` (10035) | **nblocks = 0** (zero input → `cbz x1` early return) |
| `WB_SETUP0` (10244) + `WB_SETUP0_TAIL` (10404) | **1–8 block path** (loop runs zero times, straight to the tail) |
| `WB_TAIL_REM1..REM7` (6047–7382) | tail draining **1–7 leftover blocks** (each with its `TAIL_X5_REMn` branch lemma) |
| `WB_TAIL_REM8` (7629) | **g-general rem = 8** (fixes the nblocks = 8 and 16 gap the narrow `WB_TAIL` missed) |
| `WB_TAIL_REM` (7854) | **unified tail dispatcher** over rem ∈ 1..8, g >= 0 |
| `WB_SETUP_GEN` (4414), `WB_SETUP_G1` (4586), `WB_PREPRETAIL_GEN` (5128) | generalize the phases to loop_count >= 0, incl. the g=1 boundary |
| `SETUP_Q30_LANES_10` (10185) | the offset-counter lane lemma for the small-input setup |

---

## Layer 5 — Assembly (composition)

```
WB_CORRECT       (8450)   NARROW: SETUP -> MAIN_LOOP -> PREPRETAIL -> TAIL   (nblocks >= 24)
WB_CORRECT_GEN   (8991)   loop_count >= 2, rem 1..8
WB_CORRECT_G1    (9539)   the g = 1 boundary (nblocks 9..16)
WB_CORRECT_ALL   (10707)  GENERAL CORE: case-split nblocks = 0 | 1..8 | >=9,
                          dispatching each case to the proven leg (RETURN0 / SETUP0+REM / SETUP+
                          MAIN_LOOP+PREPRETAIL+TAIL_REM); reconciles nblocks = 8*loop_count + rem
      └─ WB_SUBROUTINE_CORRECT_GEN (10993)  FINAL: wraps WB_CORRECT_ALL through the C ABI
                                            = correct for any input_len >= 0
```
Helper: `ENSURES_EXISTS2_PRECONDITION` (8442) — existential-precondition composition lemma.
`WB_GUARD1_NONZERO_GEN` / `WB_GUARD2_MASK_GEN` (10833/10842) — general entry-guard discharges.

---

## Dependency flow (one picture)

```
Layer 1 (spec / byte-order / GHASH math)  ─┐
Layer 2 (branch + decomposition lemmas)   ─┼─► Layer 3 phases ─► Layer 4 gen legs ─► WB_CORRECT_ALL ─► WB_SUBROUTINE_CORRECT_GEN
                                           │    (SETUP/LOOP/       (REM1..8, SETUP0,   (case-split       (FINAL: any input_len>=0,
                                           └─    PREPRETAIL/TAIL)   RETURN0, *_GEN)     dispatch)          via C ABI)
```

**Why each layer is needed, one line each:**
- **Layer 1** — the machine's bytes/lanes/field-elements equal the spec math (used by every phase).
- **Layer 2** — the CPU takes the right branch for a given block count.
- **Layer 3** — each execution segment computes correctly.
- **Layer 4** — the small / leftover-block cases (0, 1–8, remainders) also compute correctly.
- **Layer 5** — chain the segments + case-split on block count → correct for ANY length, through the C ABI.

The `WB_TAIL_REM1..8` proliferation and the `_GEN`/`_G1` twins are the cost of generalizing to
nblocks >= 0: each is a distinct control-flow path the hardware actually takes, so each needs its own
proof before the final case-split can dispatch to it.

---

## The guarantee (what `WB_SUBROUTINE_CORRECT_GEN` proves)

For any whole-block input (`nblocks >= 0`), assuming the caller set up the preconditions
(round keys `rk` at `key_p`, precomputed H-power table at `htable_p`, non-overlapping buffers,
plaintext `inblock` at `in_p`), the routine:
- writes ciphertext `out[j] = word_xor (aes_ctr_block nonce rk j) (inblock j)` for j < nblocks,
- writes the authentication tag `word_reversefields 8 (nist_ghash H tag0 (ciphertext blocks))`
  to `tag_p` (H = `aes256_cipher (word 0) rk`),
- advances the counter block `ivec` to `ctr_block nonce (nblocks + 2)`,
- respects the C calling convention.
Proven 0-CHEAT against the three standard HOL Light axioms.
