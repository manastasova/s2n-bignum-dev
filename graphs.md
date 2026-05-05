# AES-256-GCM Data Flow: 16-Byte Input (AARCH64)

## Top-Level Entry

```
EVP_aead_aes_256_gcm() → aead_aes_gcm_seal_scatter_impl()
                          (crypto/fipsmodule/cipher/e_aes.c:1062)
```

## Full Call Graph

```
aead_aes_gcm_seal_scatter_impl()
│
├─── [1] KEY SETUP: aes_ctr_set_key()  (e_aes.c:242)
│    ├── hwaes_capable() → YES on ARMv8
│    ├── aes_hw_set_encrypt_key(key, 256, &aes_key)
│    └── CRYPTO_gcm128_init_key()  (gcm.c:289)
│        ├── H = AES_encrypt(0^128, aes_key)     ← GCM hash subkey
│        └── CRYPTO_ghash_init()  (gcm.c:205)
│            ├── gcm_pmull_capable() → YES
│            ├── gcm_init_v8(Htable, H)           ← precompute H powers
│            ├── gmult = gcm_gmult_v8             ← single-block GHASH
│            ├── ghash = gcm_ghash_v8             ← multi-block GHASH
│            └── use_hw_gcm_crypt = 1             ← enables fused kernel
│
├─── [2] SET IV: CRYPTO_gcm128_setiv()  (gcm.c:313)
│    ├── Yi = [nonce_96 || 0x00000001]            ← initial counter
│    ├── EK0 = AES_encrypt(Yi)                    ← saved for final tag XOR
│    └── Yi++ → [nonce_96 || 0x00000002]          ← first data counter
│
├─── [3] AAD: CRYPTO_gcm128_aad()  (gcm.c:355)
│    └── (if AAD present: GHASH over AAD blocks, then set ares flag)
│
├─── [4] ENCRYPT: CRYPTO_gcm128_encrypt_ctr32()  (gcm.c:596)
│    │
│    │   ┌─── len=16, use_hw_gcm_crypt=1 ───┐
│    │   │                                    │
│    │   ▼                                    │
│    ├── Finalize AAD: if ares≠0 → GCM_MUL    │
│    │                                         │
│    ├── hw_gcm_encrypt()  (gcm.c:106)  ◄──────┘
│    │   │
│    │   ├── len_blocks = 16 & ~15 = 16       ← 1 full block
│    │   ├── CRYPTO_is_ARMv8_GCM_8x_capable() && len≥256?
│    │   │   └── NO (16 < 256)
│    │   │
│    │   └── aes_gcm_enc_kernel(in, 128bits, out, Xi, Yi, key, Htable)
│    │       │   (aesv8-gcm-armv8.S — ARM assembly)
│    │       │
│    │       ├── [AES-256 CTR ENCRYPT]
│    │       │   counter = Yi = [nonce || 0x00000002]
│    │       │   AESE + AESMC × 13 rounds
│    │       │   AESE (round 14, no AESMC)
│    │       │   XOR with final round key
│    │       │   → keystream block
│    │       │
│    │       ├── [XOR] ciphertext = plaintext ⊕ keystream
│    │       │
│    │       └── [GHASH UPDATE — fused in kernel]
│    │           Xi = (Xi ⊕ ciphertext) • H  mod p(x)
│    │           Uses PMULL/PMULL2 (Karatsuba multiplication)
│    │           + polynomial reduction
│    │
│    ├── returns bulk=1 → len becomes 0
│    └── DONE (no remainder, no further processing)
│
└─── [5] TAG: CRYPTO_gcm128_tag()  (gcm.c:829)
     │
     └── CRYPTO_gcm128_finish()  (gcm.c:805)
         │
         ├── [LENGTH BLOCK]
         │   len_block = [aad_bits(64) || msg_bits(64)]
         │            = [0x0000000000000000 || 0x0000000000000080]
         │
         ├── [FINAL GHASH]
         │   Xi = (Xi ⊕ len_block) • H  mod p(x)
         │   └── GCM_MUL(ctx, Xi) → gcm_gmult_v8()
         │       (single-block multiply via PMULL)
         │
         └── [TAG = GHASH ⊕ EK0]
             tag = Xi ⊕ EK0
             (EK0 = AES(nonce||0x00000001) from step 2)
```

## Key Decisions for 16 Bytes

| Branch Point | Condition | Outcome |
|---|---|---|
| CPU dispatch (e_aes.c:242) | `hwaes_capable()` | → hardware AES path |
| GHASH init (gcm.c:205) | `gcm_pmull_capable()` | → `gcm_gmult_v8` / `gcm_ghash_v8` |
| Fused kernel? (gcm.c:646) | `use_hw_gcm_crypt && len>0` | → YES, `hw_gcm_encrypt()` |
| 8x unroll? (gcm.c:116) | `len >= 256` | → NO (16 < 256), use **4x kernel** |
| Remainder? (gcm.c:680) | `len > 0` after bulk? | → NO, len=0, nothing left |

## GHASH Multiplications (Total: 2)

1. **During encryption** — fused inside `aes_gcm_enc_kernel`: `Xi = (Xi ⊕ C1) * H`
2. **During finalization** — in `CRYPTO_gcm128_finish` via `gcm_gmult_v8`: `Xi = (Xi ⊕ lenblock) * H`

## Summary

For 16 bytes on AARCH64: the entire input is one complete AES block. It takes the
**fused hardware path** through `aes_gcm_enc_kernel` (ARMv8 assembly), which does
AES-CTR encryption and GHASH update in a single pass using AESE/AESMC and PMULL
instructions. The tag finalization happens separately in `CRYPTO_gcm128_finish` with
one additional `gcm_gmult_v8` call for the length block, then XORs with EK0 (the
encrypted initial counter J0).

---

# Hypothetical: Forcing `aesv8_gcm_8x_enc_256` for Small Inputs

## aesv8_gcm_8x_enc_256 — Structure Overview

Source: `aesv8-gcm-armv8-unroll8.pl`
Generated: `aesv8-gcm-armv8-unroll8.S` (lines 5351–6854)

### Function Signature

```
aesv8_gcm_8x_enc_256(
    x0 = input_ptr,        // plaintext
    x1 = bit_length,       // input length in BITS
    x2 = output_ptr,       // ciphertext
    x3 = current_tag,      // pointer to Xi (GHASH state)
    x4 = counter,          // pointer to 128-bit CTR block (nonce||ctr32)
    x5 = key,              // pointer to expanded AES-256 round keys
    x6 = Htable            // pointer to precomputed GHASH H-table
)
Returns: x0 = byte_length processed
```

### Complete Control Flow

```
aesv8_gcm_8x_enc_256  (line 5351)
│
├── cbz x1 → .L256_enc_ret  (empty input, return 0)
│
├── [INIT] (lines 5354–5401)
│   ├── Save d8-d15, set up modulo constant on stack
│   ├── byte_length = bit_length >> 3
│   ├── main_end = input_ptr + ((byte_length - 1) & ~0x7F)
│   │   (aligns to 128-byte boundary = 8 blocks; at least 1 byte for tail)
│   ├── Load CTR block 0 from [counter]
│   └── Generate CTR blocks 0–7 via rev32/add increment loop
│
├── [PRE-LOOP AES] (lines 5403–5674)
│   ├── AES rounds 0–13 on all 8 counter blocks (ctr0–ctr7)
│   │   14 rounds for AES-256: AESE+AESMC × 13, then AESE (no AESMC) for round 13
│   ├── Load GHASH accumulator from [current_tag]:
│   │   acc = ext(Xi, Xi, #8); rev64(acc)
│   └── After round 13 completes on all 8 blocks...
│
├── [FIRST BRANCH] (line 5679)
│   cmp input_ptr, main_end
│   b.ge .L256_enc_tail       ◄── FOR ≤ 8 BLOCKS (128 bytes), JUMP TO TAIL
│   │
│   ├── [FIRST 8-BLOCK ENCRYPT] (lines 5681–5718)
│   │   ├── Load 8 plaintext blocks (ldp pairs)
│   │   ├── eor3 res[i] = PT[i] ⊕ ctr[i] ⊕ rk14  (final AES round + XOR)
│   │   ├── Store 8 ciphertext blocks
│   │   └── Generate next CTR blocks 8–12
│   │
│   ├── [SECOND BRANCH] (line 5720)
│   │   cmp input_ptr, main_end
│   │   b.ge .L256_enc_prepretail  ◄── if no more full 8-block groups
│   │
│   ├── [MAIN LOOP] .L256_enc_main_loop  (line 5722)
│   │   │  Processes 8 blocks per iteration:
│   │   │  - GHASH previous 8 ciphertext blocks (Karatsuba via PMULL)
│   │   │  - AES rounds 0–13 on next 8 counter blocks (interleaved with GHASH)
│   │   │  - Load 8 plaintext, XOR, store 8 ciphertext
│   │   │  - Generate next CTR blocks
│   │   │  cmp input_ptr, main_end
│   │   └── b.lt .L256_enc_main_loop
│   │
│   └── [PREPRETAIL] .L256_enc_prepretail  (line 6143)
│       ├── GHASH final full 8-block group (same structure as main loop body)
│       ├── AES rounds + encrypt last full 8-block group
│       └── Falls through to .L256_enc_tail
│
└── [TAIL] .L256_enc_tail  (line 6523)
    │
    │  At this point:
    │  - 8 AES-encrypted counter blocks are ready in ctr0–ctr7 (from either
    │    the pre-loop AES or the prepretail's next-batch AES)
    │  - remaining = end_input_ptr - input_ptr (in bytes)
    │
    ├── Load first tail plaintext block
    ├── eor3 res = PT ⊕ ctr0 ⊕ rk14  (encrypt block 0 of tail)
    ├── Prepare partial tag: ext v16 = swap halves of accumulator
    │
    ├── [CASCADE DISPATCH] (lines 6536–6601)
    │   │
    │   │  cmp remaining, #112  → b.gt .L256_enc_blocks_more_than_7  (8 blocks)
    │   │  (reset accumulators, shift ctr registers down)
    │   │  cmp remaining, #96   → b.gt .L256_enc_blocks_more_than_6  (7 blocks)
    │   │  cmp remaining, #80   → b.gt .L256_enc_blocks_more_than_5  (6 blocks)
    │   │  cmp remaining, #64   → b.gt .L256_enc_blocks_more_than_4  (5 blocks)
    │   │  cmp remaining, #48   → b.gt .L256_enc_blocks_more_than_3  (4 blocks)
    │   │  cmp remaining, #32   → b.gt .L256_enc_blocks_more_than_2  (3 blocks)
    │   │  cmp remaining, #16   → b.gt .L256_enc_blocks_more_than_1  (2 blocks)
    │   │  b .L256_enc_blocks_less_than_1                             (1 block)
    │   │
    │   │  NOTE: between each compare, the code shifts ctr registers:
    │   │  mov v7=v6, v6=v5, v5=v4, ... so the "last" encrypted block
    │   │  always ends up in v7 for the final-block GHASH path.
    │   │  Also decrements v30 (counter) to undo unused increments.
    │
    ├── [TAIL BLOCKS — fall-through chain] (lines 6602–6779)
    │   │
    │   │  .L256_enc_blocks_more_than_7:  (line 6602)
    │   │  ├── Store CT[final-7], GHASH it with h8
    │   │  ├── Load next PT, encrypt with ctr1 → res
    │   │  └── fall through ↓
    │   │
    │   │  .L256_enc_blocks_more_than_6:  (line 6622)
    │   │  ├── Store CT[final-6], GHASH it with h7
    │   │  ├── Load next PT, encrypt with ctr2 → res
    │   │  └── fall through ↓
    │   │
    │   │  .L256_enc_blocks_more_than_5:  (line 6647)
    │   │  ├── Store CT[final-5], GHASH it with h6
    │   │  ├── Load next PT, encrypt with ctr3 → res
    │   │  └── fall through ↓
    │   │
    │   │  .L256_enc_blocks_more_than_4:  (line 6673)
    │   │  ├── Store CT[final-4], GHASH it with h5
    │   │  ├── Load next PT, encrypt with ctr4 → res
    │   │  └── fall through ↓
    │   │
    │   │  .L256_enc_blocks_more_than_3:  (line 6698)
    │   │  ├── Store CT[final-3], GHASH it with h4
    │   │  ├── Load next PT, encrypt with ctr5 → res
    │   │  └── fall through ↓
    │   │
    │   │  .L256_enc_blocks_more_than_2:  (line 6725)
    │   │  ├── Store CT[final-2], GHASH it with h3
    │   │  ├── Load next PT, encrypt with ctr6 → res
    │   │  └── fall through ↓
    │   │
    │   │  .L256_enc_blocks_more_than_1:  (line 6752)
    │   │  ├── Store CT[final-1], GHASH it with h2
    │   │  ├── Load next PT, encrypt with ctr7 → res
    │   │  └── fall through ↓
    │   │
    │   └── .L256_enc_blocks_less_than_1:  (line 6780)
    │       ├── Mask partial block (if last block < 16 bytes)
    │       ├── Store CT[final], GHASH it with h1
    │       ├── Store updated counter to [counter]
    │       │
    │       ├── [MODULO REDUCTION] (lines 6827–6839)
    │       │   ├── Karatsuba tidy: eor3 acc_m, acc_m, acc_h, acc_l
    │       │   ├── pmull acc_h.1d × mod_constant → fold top into mid
    │       │   ├── eor3 mid = mid ⊕ folded ⊕ ext(top)
    │       │   ├── pmull mid.1d × mod_constant → fold mid into low
    │       │   └── eor3 acc_l = acc_l ⊕ folded ⊕ ext(mid)
    │       │
    │       └── [OUTPUT TAG] (lines 6840–6842)
    │           ├── ext acc_l (swap halves)
    │           ├── rev64 acc_l (byte-reverse)
    │           └── st1 acc_l → [current_tag]  (partial tag output)
    │
    └── Return x0 = byte_length
```

## Path for 16 Bytes Through the 8x Kernel

If we force `aesv8_gcm_8x_enc_256` to be called with `bit_length = 128` (16 bytes):

```
INIT:
  byte_length = 128 >> 3 = 16
  main_end = input_ptr + ((16 - 1) & ~0x7F)
           = input_ptr + (15 & 0xFFFFFF80)
           = input_ptr + 0                    ← main_end == input_ptr!

PRE-LOOP AES:
  Generate CTR blocks 0–7 (all 8 encrypted, even though only 1 needed)
  AES rounds 0–13 on all 8 blocks

FIRST BRANCH:
  cmp input_ptr, main_end   → input_ptr == main_end → EQUAL → b.ge taken
  → Jump to .L256_enc_tail

TAIL:
  remaining = end_input_ptr - input_ptr = 16 bytes
  Load 1 plaintext block
  eor3: CT = PT ⊕ ctr0 ⊕ rk14

  CASCADE:
    cmp 16, #112 → not taken
    (shift ctr regs, zero accumulators)
    cmp 16, #96  → not taken
    cmp 16, #80  → not taken
    cmp 16, #64  → not taken
    cmp 16, #48  → not taken
    cmp 16, #32  → not taken
    cmp 16, #16  → NOT greater, not taken  (16 is not > 16)
    b .L256_enc_blocks_less_than_1

  .L256_enc_blocks_less_than_1:
    bit_length % 128 = 0 → mask = all 1s (full block)
    Store CT to [output]
    GHASH: Xi = (acc ⊕ CT) • h1  (single Karatsuba multiply)
    MODULO REDUCTION
    Store partial tag to [current_tag]
    Return 16
```

### GHASH H-key Usage for N Tail Blocks

The tail always GHASHes with h_N, h_{N-1}, ..., h_1 (highest power first):

| Tail blocks | H-keys used (in order)                  |
|-------------|-----------------------------------------|
| 1           | h1                                      |
| 2           | h2, h1                                  |
| 3           | h3, h2, h1                              |
| 4           | h4, h3, h2, h1                          |
| 5           | h5, h4, h3, h2, h1                      |
| 6           | h6, h5, h4, h3, h2, h1                 |
| 7           | h7, h6, h5, h4, h3, h2, h1             |
| 8           | h8, h7, h6, h5, h4, h3, h2, h1         |

This implements Horner's rule: `((((CT1•h_N) ⊕ CT2)•h_{N-1}) ⊕ ... ⊕ CT_N)•h1`

Actually the tail uses a **schoolbook approach** (not Horner): each block is
independently multiplied by its H power and the results are summed, then a single
modular reduction is done at the end:

```
acc_h = CT1•h_N[high] + CT2•h_{N-1}[high] + ... + CT_N•h1[high]
acc_l = CT1•h_N[low]  + CT2•h_{N-1}[low]  + ... + CT_N•h1[low]
acc_m = CT1•h_N[mid]  + CT2•h_{N-1}[mid]  + ... + CT_N•h1[mid]
Then: single Karatsuba reduction on (acc_h, acc_m, acc_l)
```

This is equivalent to: `CT1•H^N ⊕ CT2•H^{N-1} ⊕ ... ⊕ CT_N•H`

---

## Incremental Build Plan for `aesv8_gcm_8x_enc_256`

The goal: incrementally verify the function by building up from 1-block to full 8x-unrolled.

### Phase 1: Single Block (16 bytes) — TAIL ONLY

```
Executed path:
  INIT → PRE-LOOP AES (all 8 ctr blocks) → .L256_enc_tail → cascade to
  .L256_enc_blocks_less_than_1

What to verify:
  ┌─────────────────────────────────────────────────┐
  │ AES-256-CTR encryption of 1 block:              │
  │   CT = PT ⊕ AESE...(ctr0) ⊕ rk14              │
  │                                                  │
  │ GHASH of 1 block:                               │
  │   acc = (old_tag ⊕ CT) • h1   (Karatsuba)      │
  │   modular reduction                              │
  │   store partial tag                              │
  └─────────────────────────────────────────────────┘

Assembly range:
  Lines 5351–5401  (init)
  Lines 5403–5674  (AES rounds on ctr0 — ignore ctr1-7)
  Line  5679       (branch to tail)
  Lines 6523–6601  (tail entry + cascade → blocks_less_than_1)
  Lines 6780–6842  (final block GHASH + reduction + tag store)
```

### Phase 2: Two Blocks (32 bytes) — TAIL with 2 blocks

```
Executed path:
  INIT → PRE-LOOP AES → .L256_enc_tail → cascade to
  .L256_enc_blocks_more_than_1 → .L256_enc_blocks_less_than_1

What's new vs Phase 1:
  ┌─────────────────────────────────────────────────┐
  │ Second AES block uses ctr7 (after ctr shifting) │
  │ GHASH with h2 for first CT, h1 for second CT   │
  │ Accumulated (schoolbook): single reduction      │
  └─────────────────────────────────────────────────┘

Assembly range (added):
  Lines 6752–6779  (.L256_enc_blocks_more_than_1)
```

### Phase 3: Three Blocks (48 bytes) — TAIL with 3 blocks

```
Executed path:
  → .L256_enc_blocks_more_than_2 → more_than_1 → less_than_1

What's new:
  ┌─────────────────────────────────────────────────┐
  │ Third block uses ctr6                            │
  │ GHASH with h3, h2, h1                           │
  └─────────────────────────────────────────────────┘

Assembly range (added):
  Lines 6725–6751  (.L256_enc_blocks_more_than_2)
```

### Phase 4: Four Blocks (64 bytes)

```
→ .L256_enc_blocks_more_than_3 → more_than_2 → more_than_1 → less_than_1

New: h4, h3, h2, h1
Assembly: Lines 6698–6724
```

### Phase 5: Five Blocks (80 bytes)

```
→ .L256_enc_blocks_more_than_4 → ... → less_than_1

New: h5, h4, h3, h2, h1
Assembly: Lines 6673–6697
```

### Phase 6: Six Blocks (96 bytes)

```
→ .L256_enc_blocks_more_than_5 → ... → less_than_1

New: h6, h5, ..., h1
Assembly: Lines 6647–6672
```

### Phase 7: Seven Blocks (112 bytes)

```
→ .L256_enc_blocks_more_than_6 → ... → less_than_1

New: h7, h6, ..., h1
Assembly: Lines 6622–6646
```

### Phase 8: Eight Blocks (128 bytes) — Full Tail

```
→ .L256_enc_blocks_more_than_7 → ... → less_than_1

New: h8, h7, ..., h1
Assembly: Lines 6602–6621
This completes the TAIL section.
```

### Phase 9: 9 Blocks (144 bytes) — First 8 + 1 Tail

```
Executed path:
  INIT → PRE-LOOP AES → [FIRST 8-BLOCK ENCRYPT] (lines 5681–5718)
  → .L256_enc_prepretail (line 6143: GHASH those 8 blocks + AES next 8)
  → .L256_enc_tail → cascade: remaining=16 → less_than_1

What's new:
  ┌──────────────────────────────────────────────────────┐
  │ First 8-block encrypt section:                       │
  │   Load 8 PT blocks, eor3 with ctr0-7 and rk14       │
  │   Store 8 CT blocks                                  │
  │   Generate next CTR blocks 8–12                      │
  │                                                       │
  │ PREPRETAIL section:                                  │
  │   GHASH the 8 CTs from first batch (h8..h1)          │
  │   interleaved with AES rounds on next 8 ctr blocks   │
  │                                                       │
  │ Then tail handles remaining 1 block                  │
  └──────────────────────────────────────────────────────┘

Assembly range (added):
  Lines 5681–5720  (first 8-block encrypt + store)
  Lines 6143–6522  (prepretail: GHASH 8 blocks + AES next 8)
```

### Phase 10: 10 Blocks (160 bytes) — First 8 + 2 Tail

```
Same as Phase 9 but tail handles 2 remaining blocks.
GHASH: prepretail does 8 blocks (h8..h1), tail does 2 (h2,h1).
```

### Phases 11–16: First 8 + 3..8 Tail

Continue adding tail blocks. Phase 16 = 16 blocks (256 bytes).

### Phase 17: 17 Blocks (272 bytes) — First 8 + Loop×1 + 1 Tail

```
Executed path:
  INIT → PRE-LOOP AES → [FIRST 8-BLOCK ENCRYPT]
  → .L256_enc_main_loop (1 iteration: GHASH prev 8, AES+encrypt next 8)
  → .L256_enc_prepretail (GHASH those 8)
  → .L256_enc_tail (1 remaining block)

What's new:
  ┌──────────────────────────────────────────────────────┐
  │ MAIN LOOP (lines 5722–6141):                        │
  │   Interleaved:                                       │
  │   - GHASH previous 8 CTs with h8..h1 (Karatsuba)   │
  │   - AES rounds 0-13 on next 8 ctr blocks            │
  │   - Load 8 PT, XOR, store 8 CT                      │
  │   - Generate next CTR batch                          │
  │   Loop condition: b.lt .L256_enc_main_loop           │
  └──────────────────────────────────────────────────────┘
```

### Phase 18+: Multiple Loop Iterations

Each additional 8 blocks adds one more main loop iteration.
The loop is the same code repeated — once verified for 1 iteration,
the induction step covers all iterations.

---

## Summary Table

| Phase | Bytes | Blocks | Path | New Code Section |
|-------|-------|--------|------|------------------|
| 1     | 16    | 1      | init → AES8 → tail(1)           | tail: less_than_1 |
| 2     | 32    | 2      | init → AES8 → tail(2)           | tail: more_than_1 |
| 3     | 48    | 3      | init → AES8 → tail(3)           | tail: more_than_2 |
| 4     | 64    | 4      | init → AES8 → tail(4)           | tail: more_than_3 |
| 5     | 80    | 5      | init → AES8 → tail(5)           | tail: more_than_4 |
| 6     | 96    | 6      | init → AES8 → tail(6)           | tail: more_than_5 |
| 7     | 112   | 7      | init → AES8 → tail(7)           | tail: more_than_6 |
| 8     | 128   | 8      | init → AES8 → tail(8)           | tail: more_than_7 |
| 9     | 144   | 8+1    | init → AES8 → enc8 → prepretail → tail(1) | first-8-enc, prepretail |
| 10    | 160   | 8+2    | init → AES8 → enc8 → prepretail → tail(2) | — |
| ...   | ...   | 8+N    | ...                              | — |
| 16    | 256   | 8+8    | init → AES8 → enc8 → prepretail → tail(8) | — |
| 17    | 272   | 8+8+1  | init → AES8 → enc8 → loop×1 → prepretail → tail(1) | main_loop |
| 25    | 400   | 8+8+8+1| init → AES8 → enc8 → loop×2 → prepretail → tail(1) | (loop induction) |
