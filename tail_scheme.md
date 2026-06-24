# AES-256-GCM Tail — Custom Tactic/Theorem Call Trees (per length band)

Call trees of **our** custom tactics/theorems (excluding generic s2n-bignum / HOL Light
tactics such as `REPEAT STRIP_TAC`, `ARM_STEPS_TAC`, `ENSURES_*`, `MATCH_MP_TAC`, etc.)
used to discharge each length band of `AES256_GCM_ENCRYPT_CORRECT`. The top-level theorem
dispatches by `val len` (`ASM_CASES_TAC` cascade at 16, 32, …, 112) to one
`AES256_GCM_ENCRYPT_LT_NBLOCK_ABS` lemma per band; each band is `N-1` full blocks plus one
partial (masked) tail block, with `byte_len = val len - 16*(N-1)` and `1 <= byte_len <= 16`.

## One Block (1 <= val len <= 16)

```
AES256_GCM_ENCRYPT_CORRECT (aes256_gcm.ml:8293)
│   (dispatch: ASM_CASES_TAC `val len <= 16` routes the 1-block band to LT_1BLOCK_ABS)
│
└─ AES256_GCM_ENCRYPT_LT_1BLOCK_ABS (aes256_gcm.ml:6741)
   │   (restates band in spec vocabulary; lifts raw-word result to byte_list_at / gcm_final_xi)
   │
   ├─ AES256_GCM_ENCRYPT_LT_1BLOCK_CONCRETE (aes256_gcm.ml:1356)   ← only place instructions run
   │  │
   │  ├─ GCM_INIT_TAC (aes256_gcm.ml:1220)              (entry + nop/cbz, steps 1-2)
   │  │  ├─ GCM_CBZ_LEMMA (aes256_gcm.ml:1266)
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)  → uses GCM_BOUNDS (aes256_gcm.ml:1198)
   │  │
   │  ├─ GCM_PROLOGUE_TAC (aes256_gcm.ml:1228)          (stack/frame setup, steps 3-19)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  │
   │  ├─ GCM_RUN 20 263 (aes256_gcm.ml:1201)            (counter setup + AES rounds)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  │
   │  ├─ GCM_INLOOP_GUARD_TAC (aes256_gcm.ml:1236)      (steps 264-266; b.ge into tail)
   │  │  ├─ GCM_X5_LEMMA (aes256_gcm.ml:1297)
   │  │  │  ├─ NBLOCK_USHR_BYTELEN (utils/gcm_aesgcm_nblock_helpers.ml)
   │  │  │  ├─ GCM_WSUB1 (aes256_gcm.ml:1273)
   │  │  │  └─ GCM_ANDMASK0 (aes256_gcm.ml:1280)
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)
   │  │
   │  ├─ GCM_RUN 267 272 (aes256_gcm.ml:1201)           (tail entry loads)
   │  ├─ GCM_BND16 (aes256_gcm.ml:1215)                 (collapse tail length X5 = byte_len)
   │  │  └─ GCM_X5TAIL_LEMMA (aes256_gcm.ml:1310)
   │  │     └─ NBLOCK_USHR_BYTELEN (utils/gcm_aesgcm_nblock_helpers.ml)
   │  │
   │  ├─ GCM_RUN_THEN GCM_CASCADE_TAC 273 321 (aes256_gcm.ml:1206)  (tail length cascade)
   │  │  ├─ GCM_CASCADE_TAC (aes256_gcm.ml:1344)
   │  │  │  └─ GCM_CASC_FALSE (aes256_gcm.ml:1320)
   │  │  │     ├─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml)
   │  │  │     └─ (general: IWORD_INT_SUB, IVAL_IWORD, INT_ARITH_TAC)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  │
   │  ├─ (step 322 b .L256_enc_blocks_less_than_1) THEN GCM_ENC_SIMPLIFY_TAC
   │  ├─ ABBREV_TAC s13 / ABBREV_TAC ct                 (freeze AES output + ciphertext)
   │  │
   │  ├─ GCM_RUN 323 336 (aes256_gcm.ml:1201)           (tail mask build)
   │  ├─ NBLOCK_MASK_REG (utils/gcm_aesgcm_nblock_helpers.ml:951)   (collapse Q0 mask → word(2^(8·byte_len)-1))
   │  │
   │  ├─ GCM_RUN 337 359 (aes256_gcm.ml:1201)           (AND_VEC, bif, masked store, GHASH Karatsuba)
   │  ├─ GCM_NBLOCK_POST_SIM_NORMALIZE_TAC (utils/gcm_aesgcm_nblock_helpers.ml:525)
   │  ├─ ABBREV_FINAL_XI_TAC (utils/gcm_aesgcm_nblock_helpers.ml:504)   (freeze Q19 = final_xi)
   │  │
   │  ├─ (ARM_STEPS 360-367 then TOP_DEPTH let_CONV, ENSURES_FINAL_STATE_TAC)
   │  ├─ ONE_BLOCK_USHR_BYTELEN (utils/gcm_one_block_closers.ml:64)
   │  ├─ ONE_BLOCK_MASK_IDEM (utils/gcm_one_block_closers.ml:75)
   │  │
   │  ├─ GCM_CT_STEP_TAC (utils/gcm_one_block_closers.ml:87)   ← closes ciphertext conjunct
   │  │  └─ GCM_NBLOCK_CT1_STEP_TAC 1 (utils/gcm_aesgcm_nblock_helpers.ml:560)
   │  │     ├─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │  │     ├─ LET_DEF / LET_END_DEF        (general)
   │  │     └─ WORD_XOR_ASSOC               (general)
   │  │
   │  └─ GCM_GHASH_STEP_MASKED_TAC (utils/gcm_one_block_closers.ml:99)   ← closes GHASH conjunct
   │     ├─ GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT (utils/gcm_aesgcm_helpers.ml:210)
   │     ├─ ghash_1block_karatsuba (utils/gcm_aesgcm_helpers.ml:128)
   │     ├─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │     ├─ karatsuba_mid (common/polyval_ghash.ml:386)
   │     └─ custom bitvector/byteswap rewrite lemmas (gcm_aesgcm_helpers.ml / nblock_helpers.ml):
   │        WORD_REVERSEFIELDS_XOR_8_128, REV64_LOWER_LANE, REV64_UPPER_LANE,
   │        REV8_JOIN_FOLD, WORD_INSERT_AS_JOIN_1, WORD_INSERT_AS_JOIN_2,
   │        KAR_SUBWORD_LEMMA, WORD_SWAP_HALVES_INVOLUTION, BYTESWAP128_SUBWORD_LO/HI,
   │        HALFSWAP_XOR, REVERSEFIELDS8_SUBWORD_LO/HI, KAR_MID_BRIDGE,
   │        DOUBLE_SUBWORD_JOIN, DOUBLE_SUBWORD_JOIN_HI
   │        (+ general: WORD_XOR_ASSOC, WORD_XOR_0, WORD_SUBWORD_XOR, WORD_RULE, WORD_BLAST)
   │
   │   ── lift-to-spec lemmas used by LT_1BLOCK_ABS proof: ──
   ├─ OUT_BRIDGE_GEN (aes256_gcm.ml:6357)       (per-block 128-bit stores ⟹ byte_list_at aes256_gcm_encrypt)
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   ├─ GCM_FINAL_XI_UNFOLD (aes256_gcm.ml:6456)  (fold accumulator into gcm_final_xi)
   ├─ GHASH_BLOCKS_1 (aes256_gcm.ml:6469)       (the 1-block GHASH block list)
   └─ INPUT_READS_128 (aes256_gcm.ml:6436)      (precondition reshape: input reads 128 bytes)
```

## Notes

- `GCM_ENC_SIMPLIFY_TAC` (utils/gcm_aesgcm_helpers.ml:335) is invoked after *every*
  simulated step via `GCM_RUN` / `GCM_RUN_THEN` / `GCM_INIT_TAC` / `GCM_PROLOGUE_TAC` —
  it is the per-step AES-state simplifier and appears throughout.
- The two leaf closers actually finishing the final state are `GCM_CT_STEP_TAC`
  (ciphertext-store conjunct) and `GCM_GHASH_STEP_MASKED_TAC` (the masked GHASH / tag
  conjunct), split by the final `CONJ_TAC THENL [...]` at aes256_gcm.ml:1493.
- The `LT_1BLOCK_ABS` layer's other machinery (`ENSURES_FRAME_SUBSUMED`,
  `ENSURES_POSTCONDITION_THM`, `ENSURES_PRECONDITION_THM`, `SUBSUMED_MAYCHANGE_TAC`)
  are generic s2n-bignum sandwich/frame tactics, so they are omitted per the
  "ours only" constraint.

---

## Two Blocks (16 < val len <= 32)

```
AES256_GCM_ENCRYPT_CORRECT (aes256_gcm.ml:8293)
│   (dispatch: ASM_CASES_TAC `val len <= 32` -> MATCH_MP AES256_GCM_ENCRYPT_LT_2BLOCK_ABS, aes256_gcm.ml:8407)
└─ AES256_GCM_ENCRYPT_LT_2BLOCK_ABS (aes256_gcm.ml:6927)
   ├─ AES256_GCM_ENCRYPT_LT_2BLOCK_CONCRETE (aes256_gcm.ml:1589)
   │  ├─ GCM_INIT_TAC GCM_CBZ_LEMMA2 (aes256_gcm.ml:1220)
   │  │  ├─ GCM_BND (aes256_gcm.ml:1212)
   │  │  └─ GCM_CBZ_LEMMA2 (aes256_gcm.ml:1509)   ← cbz x1 guard: bit_len 128+8*byte_len != 0
   │  ├─ GCM_PROLOGUE_TAC (aes256_gcm.ml:1228)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  │     └─ SIMD_SIMPLIFY_ASSUM_TAC (utils/gcm_aesgcm_helpers.ml:283)
   │  ├─ GCM_RUN 20 263 (aes256_gcm.ml:1201)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  ├─ GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA2 (aes256_gcm.ml:1236)
   │  │  ├─ GCM_BND (aes256_gcm.ml:1212)
   │  │  └─ GCM_X5_LEMMA2 (aes256_gcm.ml:1518)    ← X5 collapses to in_ptr -> b.ge taken
   │  │     ├─ TWOBLOCK_USHR (utils/gcm_two_block_closers.ml:442)
   │  │     ├─ GCM_WSUB2 (aes256_gcm.ml:1515)
   │  │     └─ GCM_ANDMASK0 (aes256_gcm.ml:1280)
   │  ├─ GCM_RUN 267 272 (aes256_gcm.ml:1201)
   │  ├─ GCM_BND16 GCM_X5TAIL_LEMMA2 (aes256_gcm.ml:1215)
   │  │  └─ GCM_X5TAIL_LEMMA2 (aes256_gcm.ml:1530)  ← X5 = word(16+byte_len)
   │  │     └─ TWOBLOCK_USHR (utils/gcm_two_block_closers.ml:442)
   │  ├─ GCM_RUN_THEN GCM_CASCADE2_TAC 273 321 (aes256_gcm.ml:1206)
   │  │  ├─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  │  └─ GCM_CASCADE2_TAC (aes256_gcm.ml:1576)   ← thresholds 32..112 fall through, 0x10 taken (b.gt) into .more_than_1
   │  │     ├─ GCM_CASC2_FALSE (aes256_gcm.ml:1535)
   │  │     │  └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml:991)
   │  │     └─ GCM_CASC2_TRUE (aes256_gcm.ml:1555)
   │  │        └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml:991)
   │  ├─ GCM_RUN 322 331 (aes256_gcm.ml:1201)       ← more_than_1 body: st1 block 1 + first GHASH
   │  ├─ GCM_RUN 332 350 (aes256_gcm.ml:1201)       ← tail mask build
   │  ├─ TWOBLOCK_MASK_REG (utils/gcm_two_block_closers.ml:457)  ← mask reg -> word(2^(8*byte_len)-1)
   │  ├─ GCM_RUN 351 374 (aes256_gcm.ml:1201)       ← masked store, GHASH Karatsuba, Barrett up to EOR3+EXT
   │  ├─ GCM_NBLOCK_POST_SIM_NORMALIZE_TAC (utils/gcm_aesgcm_nblock_helpers.ml:525)
   │  ├─ ABBREV_FINAL_XI_TAC (utils/gcm_aesgcm_nblock_helpers.ml:504)
   │  ├─ TWOBLOCK_MASK_REG (utils/gcm_two_block_closers.ml:457)  ← re-applied to the post-state goal
   │  ├─ TWOBLOCK_USHR (utils/gcm_two_block_closers.ml:442)      ← ASM_SIMP in tail length normalization
   │  ├─ GCM_CT1_STEP_TAC (aes256_gcm.ml:1505)      ← closes ciphertext block 1 (full)
   │  │  └─ GCM_NBLOCK_CT_STEP_TAC 2 1 (utils/gcm_aesgcm_nblock_helpers.ml:659)
   │  │     └─ GCM_NBLOCK_CT1_STEP_TAC 2 (utils/gcm_aesgcm_nblock_helpers.ml:560)  ← ivec_1 = ivec, no CTR chain
   │  ├─ GCM_CTR1_FOLD_TAC "s13_2" (utils/gcm_two_block_closers.ml:309)   ← closes ciphertext block 2 (partial/masked)
   │  ├─ NBLOCK_MASK_IDEM (utils/gcm_aesgcm_nblock_helpers.ml:973)
   │  └─ GCM_2BLOCK_GHASH_VIA_BRANCH_TAC (utils/gcm_two_block_closers.ml:412)   ← closes GHASH conjunct
   │     ├─ GCM_2BLOCK_GHASH_PREFIX_TAC (utils/gcm_two_block_closers.ml:142)
   │     │  ├─ GHASH_POLYVAL_ACC_2 (utils/gcm_aesgcm_helpers.ml:467)
   │     │  └─ GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC (utils/gcm_two_block_closers.ml:88)
   │     │     └─ ghash_2block_karatsuba (utils/gcm_two_block_closers.ml:12)
   │     ├─ JOIN_XI_SELF (utils/gcm_two_block_closers.ml:360)   ← refold xi reassembled from halves
   │     ├─ GCM_2BLOCK_FOLD_QB_TAC (utils/gcm_two_block_closers.ml:389)
   │     │  └─ bubble_fix (utils/gcm_two_block_closers.ml:378)
   │     └─ bubble_fix (utils/gcm_two_block_closers.ml:378)   ← per-half AC sort to fixpoint
   ├─ OUT_BRIDGE_GEN (aes256_gcm.ml:6357)            ← lift CONCRETE ct1/ctm2 stores to byte_list_at spec
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   ├─ GCM_FINAL_XI_UNFOLD (aes256_gcm.ml:6456)       ← unfold gcm_final_xi for val len = 16+byte_len
   ├─ GHASH_BLOCKS_2 (aes256_gcm.ml:6481)            ← spec GHASH over the 2 blocks = polyval_acc [ct1; ctm2]
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   └─ INPUT_READS_128 (aes256_gcm.ml:6436)           ← byte_list_at pt_in -> bytes128 reads of pt1/pt2
```

**Notes (vs 1-block)**

- Branch taken differs: 1-block falls through the whole cascade (`b .less_than_1`); 2-block's
  `GCM_CASCADE2_TAC` takes `cmp x5,#0x10; b.gt` into `.more_than_1`, so the cascade resolver needs
  a TRUE case (`GCM_CASC2_TRUE`) in addition to the FALSE cases.
- Address arithmetic is `128 + 8*byte_len` (one full leading block): `GCM_CBZ_LEMMA2`,
  `GCM_X5_LEMMA2`, `GCM_X5TAIL_LEMMA2`, `GCM_WSUB2`, `TWOBLOCK_USHR`, `TWOBLOCK_MASK_REG`.
- Block 1 uses `ivec` (counter 0); block 2 uses `gcm_ctr_inc ivec`. Block 2's keystream is folded
  back via `GCM_CTR1_FOLD_TAC "s13_2"` — no counter-fold exists in the 1-block path.
- Three closing conjuncts: ct block 1 (`GCM_CT1_STEP_TAC`), masked block 2
  (`GCM_CTR1_FOLD_TAC` + `NBLOCK_MASK_IDEM`), GHASH (`GCM_2BLOCK_GHASH_VIA_BRANCH_TAC`).
- The `.more_than_1` path reassembles `xi` from its halves, so the GHASH closer is the "via branch"
  variant (`JOIN_XI_SELF` refold, `GCM_2BLOCK_FOLD_QB_TAC`, `bubble_fix` fixpoint sort), keyed by the
  2-block Karatsuba bridge `GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC` / `ghash_2block_karatsuba`.

---

## Three Blocks (32 < val len <= 48)

```
AES256_GCM_ENCRYPT_CORRECT (aes256_gcm.ml:8293)
│   (length-band dispatch -> 3-block band)
└─ AES256_GCM_ENCRYPT_LT_3BLOCK_ABS (aes256_gcm.ml:7117)
   ├─ AES256_GCM_ENCRYPT_LT_3BLOCK_CONCRETE (aes256_gcm.ml:1887)
   │  ├─ GCM_INIT_TAC GCM_CBZ_LEMMA3 (aes256_gcm.ml:1220)
   │  │  ├─ GCM_CBZ_LEMMA3 (aes256_gcm.ml:1769)        ← cbz x1 guard: 256+8*byte_len ≠ 0
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)
   │  │     └─ GCM_BOUNDS (aes256_gcm.ml:1198)
   │  ├─ GCM_PROLOGUE_TAC (aes256_gcm.ml:1228)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  ├─ GCM_RUN 20 263 (aes256_gcm.ml:1201)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  ├─ GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA3 (aes256_gcm.ml:1236)
   │  │  ├─ GCM_X5_LEMMA3 (aes256_gcm.ml:1779)          ← X5 = in_ptr, b.ge taken into tail
   │  │  │  └─ THREEBLOCK_USHR (utils/gcm_three_block_closers.ml:429)
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)
   │  ├─ GCM_RUN 267 272 (aes256_gcm.ml:1201)
   │  ├─ GCM_BND16 GCM_X5TAIL_LEMMA3 (aes256_gcm.ml:1215)
   │  │  └─ GCM_X5TAIL_LEMMA3 (aes256_gcm.ml:1791)      ← tail length reg X5 = word(32+byte_len)
   │  │     └─ THREEBLOCK_USHR (utils/gcm_three_block_closers.ml:429)
   │  ├─ GCM_RUN_THEN GCM_CASCADE3_TAC 273 321 (aes256_gcm.ml:1206)
   │  │  ├─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  │  └─ GCM_CASCADE3_TAC (aes256_gcm.ml:1839)       ← 48..112 fall through, 32 taken into .more_than_2
   │  │     ├─ GCM_CASC3_FALSE (aes256_gcm.ml:1796)
   │  │     │  └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml)
   │  │     └─ GCM_CASC3_TRUE (aes256_gcm.ml:1816)
   │  │        └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml)
   │  ├─ GCM_RUN 322 346 (aes256_gcm.ml:1201)
   │  ├─ GCM_3B_CT1_ABBREV_TAC (aes256_gcm.ml:1855)     ← abbreviates ct1/ct2 (full blocks 1,2) + s13_1/s13_2
   │  ├─ GCM_RUN 347 366 (aes256_gcm.ml:1201)
   │  ├─ THREEBLOCK_MASK_REG (utils/gcm_three_block_closers.ml:437)   ← partial-block mask register
   │  ├─ GCM_RUN 367 374 (aes256_gcm.ml:1201)
   │  ├─ GCM_3B_CT3_ABBREV_TAC (aes256_gcm.ml:1870)     ← abbreviates partial ct3 + s13_3 from masked out_ptr+32 store
   │  ├─ GCM_RUN 375 385 (aes256_gcm.ml:1201)
   │  ├─ GCM_NBLOCK_POST_SIM_NORMALIZE_TAC (utils/gcm_aesgcm_nblock_helpers.ml:525)
   │  ├─ ABBREV_FINAL_XI_TAC (utils/gcm_aesgcm_nblock_helpers.ml:504)   ← names Q19 result `final_xi`
   │  ├─ THREEBLOCK_USHR (utils/gcm_three_block_closers.ml:429)   ← closes X0 = word(32+byte_len) conjunct
   │  ├─ GCM_NBLOCK_CT1_STEP_TAC (inline: EXPAND ct1/s13_1 + aes256_block_enc)   ← closes ct1 (block 1)
   │  ├─ GCM_CT2_STEP_TAC (aes256_gcm.ml:1765 = GCM_NBLOCK_CT_STEP_TAC 3 2)   ← closes ct2 (block 2)
   │  │  └─ GCM_NBLOCK_CT_LATER_STEP_TAC 3 2 (utils/gcm_aesgcm_nblock_helpers.ml:591)
   │  │     └─ aes256_block_enc, LANE0..3_BYTES_JOIN, CTR_WORD_INSERT, gcm_ctr_inc, BYTEREVERSE_JOIN_FOLD
   │  ├─ NBLOCK_MASK_IDEM (utils/gcm_aesgcm_nblock_helpers.ml:973)   ← masked block-3 store (ct3)
   │  ├─ GCM_CTR2_FOLD_TAC "s13_3" (utils/gcm_two_block_closers.ml:330)   ← folds ct3 keystream = aes(gcm_ctr_inc^2 ivec)
   │  └─ GCM_3BLOCK_GHASH_STEP_MASKED_TAC (utils/gcm_three_block_closers.ml:206)   ← closes GHASH conjunct
   │     ├─ GHASH_POLYVAL_ACC_3 (utils/gcm_aesgcm_helpers.ml:511)
   │     ├─ GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC (utils/gcm_three_block_closers.ml:88)
   │     │  ├─ GHASH_3BLOCK_AS_NBLOCK (utils/gcm_three_block_closers.ml:66)
   │     │  │  └─ ghash_3block_karatsuba (utils/gcm_three_block_closers.ml:12), ghash_Nblock_karatsuba
   │     │  └─ GHASH_NBLOCK_KARATSUBA_EQ_PROP3 (utils/gcm_aesgcm_nblock_helpers.ml)
   │     ├─ ghash_3block_karatsuba (utils/gcm_three_block_closers.ml:12)
   │     ├─ karatsuba_mid, PMUL_NORM_CONV / WORD_SIMPLE_SUBWORD_CONV (utils helpers)
   │     └─ GCM_3BLOCK_HALF_CLOSE (utils/gcm_three_block_closers.ml:191)
   │        ├─ GCM_3BLOCK_FOLD_MIDS_TAC (utils/gcm_three_block_closers.ml:149)   ← folds w1md/w2md/w3md
   │        ├─ GCM_3BLOCK_FOLD_TO `qS` 3 / `qB` 13 (utils/gcm_three_block_closers.ml:171)
   │        └─ bubble_fix (utils/gcm_three_block_closers.ml:144)   ← XOR-AC fixpoint sort
   ├─ OUT_BRIDGE_GEN (aes256_gcm.ml:6357)   ← lifts masked-store post into spec ciphertext (2 full + partial)
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   ├─ GCM_FINAL_XI_UNFOLD (aes256_gcm.ml:6456)   ← unfolds gcm_final_xi (val len = 16*2+byte_len ≠ 0)
   ├─ GHASH_BLOCKS_3 (aes256_gcm.ml:6496)   ← spec GHASH over 3 blocks = ghash_polyval_acc on [ct1;ct2;ctm3]
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   └─ INPUT_READS_128 (aes256_gcm.ml:6436)   ← byte_list_at pt_in -> bytes128 reads of pt1/pt2/pt3
```

**Notes (vs 1-block)**

- Three blocks: 1 and 2 full (`ct1`,`ct2`), block 3 partial/masked (`ctm3`). CONCRETE carries
  `pt1/pt2/pt3` and `out0` (the pre-existing word at `out_ptr+32` merged under the mask).
- Length/cascade lemmas are the `*3` variants over `256 + 8*byte_len` (= `32 + byte_len` after
  `ushr 3`), built on `THREEBLOCK_USHR`; cascade threshold 32 is TRUE (into `.more_than_2`).
- Extra abbreviation tactics: `GCM_3B_CT1_ABBREV_TAC`, `THREEBLOCK_MASK_REG`, `GCM_3B_CT3_ABBREV_TAC`.
- Ciphertext conjuncts: block 1 inline (`GCM_NBLOCK_CT1_STEP_TAC`), block 2 `GCM_CT2_STEP_TAC`
  (needs `gcm_ctr_inc` chain), block 3 `NBLOCK_MASK_IDEM` + `GCM_CTR2_FOLD_TAC "s13_3"`.
- GHASH via `GCM_3BLOCK_GHASH_STEP_MASKED_TAC` → `GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC` /
  `GHASH_3BLOCK_AS_NBLOCK` and the `GCM_3BLOCK_HALF_CLOSE` AC-closure (3 mids + qS/qB).

---

## Four Blocks (48 < val len <= 64)

```
AES256_GCM_ENCRYPT_CORRECT (aes256_gcm.ml:8293)
└─ AES256_GCM_ENCRYPT_LT_4BLOCK_ABS (aes256_gcm.ml:7309)
   ├─ AES256_GCM_ENCRYPT_LT_4BLOCK_CONCRETE (aes256_gcm.ml:2732)
   │  ├─ GCM_INIT_TAC GCM_CBZ_LEMMA4 (aes256_gcm.ml:1220)
   │  │  ├─ GCM_CBZ_LEMMA4 (aes256_gcm.ml:2048)
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)  → GCM_BOUNDS (aes256_gcm.ml:1198)
   │  ├─ GCM_PROLOGUE_TAC (aes256_gcm.ml:1228)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  ├─ GCM_RUN 20 263 (aes256_gcm.ml:1201)   (ABBREV s13_1..s13_4 keystreams; generic)
   │  ├─ GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA4 (aes256_gcm.ml:1236)
   │  │  └─ GCM_X5_LEMMA4 (aes256_gcm.ml:2058)
   │  ├─ GCM_RUN 267 272 (aes256_gcm.ml:1201)
   │  ├─ GCM_BND16 GCM_X5TAIL_LEMMA4 (aes256_gcm.ml:1215)
   │  │  └─ GCM_X5TAIL_LEMMA4 (aes256_gcm.ml:2070)
   │  ├─ GCM_RUN_THEN GCM_CASCADE4_TAC 273 321 (aes256_gcm.ml:1206)
   │  │  └─ GCM_CASCADE4_TAC (aes256_gcm.ml:2116)        ← thresholds 64/80/96/112
   │  │     ├─ GCM_CASC4_FALSE (aes256_gcm.ml:2075)
   │  │     └─ GCM_CASC4_TRUE  (aes256_gcm.ml:2095)
   │  ├─ (ABBREV ct1 ; GCM_RUN 322 335 ; ct2 ; GCM_RUN 336 348 ; ct3 ; GCM_RUN 349 366)  (aes256_gcm.ml:1201)
   │  ├─ FOURBLOCK_MASK_REG (utils/gcm_four_block_closers.ml:171)   ← partial-block mask folded into asm reg
   │  ├─ GCM_RUN 367 379 / GCM_RUN 380 394 (aes256_gcm.ml:1201)
   │  ├─ GCM_NBLOCK_POST_SIM_NORMALIZE_TAC (utils/gcm_aesgcm_nblock_helpers.ml:525)
   │  ├─ ABBREV_FINAL_XI_TAC (utils/gcm_aesgcm_nblock_helpers.ml:504)
   │  ├─ FOURBLOCK_MASK_REG (utils/gcm_four_block_closers.ml:171)  (reapplied to goal)
   │  ├─ FOURBLOCK_USHR (utils/gcm_four_block_closers.ml:163)
   │  ├─ GCM_4BLOCK_CT1_FILE_TAC = GCM_NBLOCK_CT_STEP_TAC 4 1 (aes256_gcm.ml:2730)   ← closes CT block 1
   │  │  └─ GCM_NBLOCK_CT_STEP_TAC (utils/gcm_aesgcm_nblock_helpers.ml:659)
   │  │     └─ GCM_NBLOCK_CT1_STEP_TAC 4 (utils/gcm_aesgcm_nblock_helpers.ml:560)
   │  │        ├─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │  │        ├─ LANE0/1/2_BYTES_JOIN, LANE3_BYTES_JOIN_BE (utils/gcm_aesgcm_nblock_helpers.ml:46/56/66/76)
   │  │        ├─ CTR_WORD_INSERT (utils/gcm_aesgcm_nblock_helpers.ml:86)
   │  │        ├─ gcm_ctr_inc (utils/gcm_aesgcm_nblock_helpers.ml:38)
   │  │        └─ WORD_REVERSEFIELDS_8_BYTEREVERSE_32 / BYTEREVERSE_JOIN_FOLD (…:108 / …:95)
   │  ├─ GCM_4BLOCK_CT2_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 4 2 (utils/gcm_four_block_closers.ml:158)   ← closes CT block 2
   │  │  └─ GCM_NBLOCK_CT_LATER_STEP_TAC 4 2 (utils/gcm_aesgcm_nblock_helpers.ml:591)  [k=2 path]
   │  ├─ GCM_4BLOCK_CT3_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 4 3 (utils/gcm_four_block_closers.ml:159)   ← closes CT block 3
   │  │  └─ GCM_NBLOCK_CT_LATER_STEP_TAC 4 3 (utils/gcm_aesgcm_nblock_helpers.ml:591)  [k=3 nest collapse]
   │  │     (+ INSERT_SUBWORD (…:574), INSERT_IDEM (…:568), ABBREV ctr3/br3/step1_3 counter peel)
   │  ├─ CT block 4 conjunct (inline, aes256_gcm.ml:2761-2788)                          ← closes CT block 4 (partial)
   │  │  ├─ FOURBLOCK_MASK_REG (utils/gcm_four_block_closers.ml:171)
   │  │  ├─ NBLOCK_MASK_IDEM (utils/gcm_aesgcm_nblock_helpers.ml:973)
   │  │  ├─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │  │  ├─ LANE0/1/2_BYTES_JOIN, LANE3_BYTES_JOIN_BE, CTR_WORD_INSERT (utils/gcm_aesgcm_nblock_helpers.ml:46-86)
   │  │  ├─ gcm_ctr_inc (utils/gcm_aesgcm_nblock_helpers.ml:38)
   │  │  └─ WORD_REVERSEFIELDS_8_BYTEREVERSE_32 / BYTEREVERSE_JOIN_FOLD / INSERT_SUBWORD / INSERT_IDEM
   │  └─ GHASH conjunct (final xi):                                                      ← closes GHASH conjunct
   │     ├─ GCM_4B_MASK_COLLAPSE_TAC (aes256_gcm.ml:2145)  → FOURBLOCK_MASK_REG (…:171)
   │     ├─ GCM_4B_FOLD_AND_BRIDGE (aes256_gcm.ml:2230)
   │     │  ├─ GHASH_POLYVAL_ACC_4 (utils/gcm_aesgcm_helpers.ml:577)
   │     │  ├─ POLYVAL_DOT_H4_EQ_LOCAL (utils/gcm_aesgcm_nblock_helpers.ml:674)
   │     │  ├─ WORD_REVERSEFIELDS_XOR_8_128 (utils/gcm_aesgcm_helpers.ml:399)
   │     │  ├─ aes256_block_enc / LANE*_BYTES_JOIN / CTR_WORD_INSERT / gcm_ctr_inc  (fold ct1..ct4)
   │     │  └─ GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC (utils/gcm_four_block_closers.ml:89)   ← karatsuba bridge
   │     │     └─ karatsuba_mid (common/polyval_ghash.ml:386)
   │     ├─ GCM_4B_TAIL3A (aes256_gcm.ml:2428)
   │     │  ├─ ghash_4block_karatsuba (utils/gcm_four_block_closers.ml:2)
   │     │  ├─ BYTESWAP128_SUBWORD_LO/HI (utils/gcm_aesgcm_helpers.ml:196)
   │     │  ├─ WORD_SIMPLE_SUBWORD_CONV (utils/gcm_aesgcm_helpers.ml:78)
   │     │  ├─ REV64_LOWER_LANE / REV64_UPPER_LANE / REV8_JOIN_FOLD (…:230/240 ; …:421)
   │     │  ├─ WORD_SWAP_HALVES_INVOLUTION / WORD_INSERT_AS_JOIN_1/2 / KAR_SUBWORD_LEMMA
   │     │  ├─ HALFSWAP_XOR / REVERSEFIELDS8_SUBWORD_LO/HI
   │     │  └─ PMUL_NORM_CONV (utils/gcm_aesgcm_helpers.ml:119)
   │     ├─ GCM_4B_MASK_COLLAPSE_TAC (aes256_gcm.ml:2145)  → FOURBLOCK_MASK_REG
   │     ├─ GCM_4B_DROP_CT_STORES (aes256_gcm.ml:2150)
   │     ├─ GCM_4B_TAIL_P1 (aes256_gcm.ml:2483)  (karatsuba_mid, WORD_REVERSEFIELDS_XOR_8_128, ct1 half re-fold)
   │     ├─ GCM_4B_TAIL_P2C (aes256_gcm.ml:2529)
   │     │  ├─ DOUBLE_SUBWORD_JOIN / DOUBLE_SUBWORD_JOIN_HI (utils/gcm_aesgcm_helpers.ml:665)
   │     │  └─ qB via bubble_sort_conv (utils/gcm_aesgcm_nblock_helpers.ml:888)
   │     └─ GCM_4B_LEAF_CLOSE (aes256_gcm.ml:2225)
   │        ├─ XI_HS_LO / XI_HS_HI (aes256_gcm.ml:2133/2138)
   │        ├─ GCM_4B_CTM4_FOLD (aes256_gcm.ml:2157)
   │        ├─ GCM_4B_W1MD_FOLD (aes256_gcm.ml:2164)
   │        └─ GCM_4B_HALF_CLOSE (aes256_gcm.ml:2215)
   │           ├─ REV8_JOIN_FOLD / REVERSEFIELDS8_SUBWORD_LO/HI
   │           ├─ HALFSWAP_REV8_LEMMA (utils/gcm_aesgcm_helpers.ml:438)
   │           ├─ JOIN_SUBWORD_IDENT (utils/gcm_aesgcm_helpers.ml:449)
   │           ├─ GCM_4B_FOLD_MIDS_TAC (aes256_gcm.ml:2177)   (fold w1md..w4md)
   │           ├─ GCM_4B_FOLD_TO `qS` 4 / `qB` 17 (aes256_gcm.ml:2198)
   │           │  └─ bubble_fix (utils/gcm_three_block_closers.ml:144)
   │           └─ bubble_fix (utils/gcm_three_block_closers.ml:144)
   ├─ OUT_BRIDGE_GEN (aes256_gcm.ml:6357)                ← lifts 4 store-eqs to byte_list_at ciphertext spec
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   ├─ GCM_FINAL_XI_UNFOLD (aes256_gcm.ml:6456)
   ├─ GHASH_BLOCKS_4 (aes256_gcm.ml:6512)                ← per-band GHASH-list spec (4 ct blocks)
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   └─ INPUT_READS_128 (aes256_gcm.ml:6436)               ← byte_list_at ⇒ 4 bytes128 reads
```

**Notes (vs 1-block)**

- 3 full blocks + 1 partial (block 4 masked); CT1 via `GCM_4BLOCK_CT1_FILE_TAC`, CT2/CT3 via
  `GCM_4BLOCK_CT{2,3}_STEP_TAC` (`GCM_NBLOCK_CT_STEP_TAC 4 k`), partial block 4 closed inline.
- Partial-block masking: `FOURBLOCK_MASK_REG` / `FOURBLOCK_USHR`, `GCM_4B_MASK_COLLAPSE_TAC`,
  `NBLOCK_MASK_IDEM`, `ctm4 = word_and ct4 mask`.
- GHASH uses the 4-block bridge `GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC` + `ghash_4block_karatsuba`,
  `GHASH_POLYVAL_ACC_4`, `POLYVAL_DOT_H4_EQ_LOCAL`; the leaf folds 4 mids and qS(4)/qB(17).
- ABS lift instantiates `OUT_BRIDGE_GEN` with 3 full + `byte_len` partial (`co3`), `GHASH_BLOCKS_4`.
- Cascade `GCM_CASCADE4_TAC` thresholds 64/80/96/112; length lemmas over `384 + 8*byte_len`.

---

## Five Blocks (64 < val len <= 80)

```
AES256_GCM_ENCRYPT_CORRECT (aes256_gcm.ml:8293)
│   (dispatch: routes the 5-block band, 64 < val len <= 80, to LT_5BLOCK_ABS)
└─ AES256_GCM_ENCRYPT_LT_5BLOCK_ABS (aes256_gcm.ml:7502)
   │   (byte_len = val len - 64; len = 16*4 + byte_len; lifts raw-word result to spec)
   ├─ AES256_GCM_ENCRYPT_LT_5BLOCK_CONCRETE (aes256_gcm.ml:3500)   (goal = gcm_5b_goal, aes256_gcm.ml:2893)
   │  ├─ GCM_INIT_TAC (aes256_gcm.ml:1220)
   │  │  ├─ GCM_CBZ_LEMMA5 (aes256_gcm.ml:2810)         (bit_len = 512+8*byte_len ≠ 0)
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)  → GCM_BOUNDS (aes256_gcm.ml:1198)
   │  ├─ GCM_PROLOGUE_TAC (aes256_gcm.ml:1228)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  ├─ GCM_RUN 20 263 (aes256_gcm.ml:1201)   (4 full AES blocks)
   │  ├─ GCM_INLOOP_GUARD_TAC (aes256_gcm.ml:1236)
   │  │  ├─ GCM_X5_LEMMA5 (aes256_gcm.ml:2820)
   │  │  │  ├─ FIVEBLOCK_USHR (utils/gcm_five_block_closers.ml:184)
   │  │  │  │  └─ NBLOCK_USHR_BYTELEN (utils/gcm_aesgcm_nblock_helpers.ml:980)
   │  │  │  ├─ GCM_WSUB5 (aes256_gcm.ml:2816)
   │  │  │  └─ GCM_ANDMASK0 (aes256_gcm.ml:1280)
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)
   │  ├─ GCM_RUN 267 272 (aes256_gcm.ml:1201)
   │  ├─ GCM_BND16 GCM_X5TAIL_LEMMA5 (aes256_gcm.ml:1215)   (tail length X5 = 64+byte_len)
   │  │  └─ GCM_X5TAIL_LEMMA5 (aes256_gcm.ml:2832)
   │  │     └─ FIVEBLOCK_USHR (utils/gcm_five_block_closers.ml:184)
   │  ├─ GCM_RUN_THEN GCM_CASCADE5_TAC 273 321 (aes256_gcm.ml:1206)
   │  │  ├─ GCM_CASCADE5_TAC (aes256_gcm.ml:2878)
   │  │  │  ├─ GCM_CASC5_FALSE (aes256_gcm.ml:2837)     (thresholds 80,96,112 fall through)
   │  │  │  │  └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml:991)
   │  │  │  └─ GCM_CASC5_TRUE (aes256_gcm.ml:2857)      (threshold 64 taken → more_than_4)
   │  │  │     └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml:991)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  ├─ abbrev_ct_from_store 0 1 / 16 2 / 32 3 / 48 4 (aes256_gcm.ml:3049)  (store-based s13_k/ct_k)
   │  │  (interleaved with GCM_RUN 322 348 / 349 362)
   │  ├─ FIVEBLOCK_MASK_REG (utils/gcm_five_block_closers.ml:192)   (collapse Q mask → word(2^(8·byte_len)-1))
   │  ├─ GCM_RUN 363 403 (aes256_gcm.ml:1201)   (mask build, masked store, GHASH Karatsuba)
   │  ├─ GCM_NBLOCK_POST_SIM_NORMALIZE_TAC (utils/gcm_aesgcm_nblock_helpers.ml:525)
   │  ├─ ABBREV_FINAL_XI_TAC (utils/gcm_aesgcm_nblock_helpers.ml:504)
   │  ├─ FIVEBLOCK_MASK_REG (utils/gcm_five_block_closers.ml:192)   (re-applied to goal masks)
   │  ├─ FIVEBLOCK_USHR (utils/gcm_five_block_closers.ml:184)
   │  ├─ CT_CLOSE_5 1 (aes256_gcm.ml:3465)              ← closes ciphertext conjunct 1
   │  │  └─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │  ├─ GCM_5BLOCK_CT2_STEP_TAC (utils/gcm_five_block_closers.ml:177)  ← closes ciphertext conjunct 2
   │  │  └─ GCM_NBLOCK_CT_STEP_TAC 5 2 (utils/gcm_aesgcm_nblock_helpers.ml:659)
   │  │     └─ GCM_NBLOCK_CT_LATER_STEP_TAC 5 2 (utils/gcm_aesgcm_nblock_helpers.ml:591)
   │  │        ├─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │  │        ├─ gcm_ctr_inc (utils/gcm_aesgcm_nblock_helpers.ml:38)
   │  │        └─ CTR_WORD_INSERT / WORD_REVERSEFIELDS_REVERSEFIELDS (utils/gcm_aesgcm_helpers.ml)
   │  ├─ GCM_5BLOCK_CT3_STEP_TAC (utils/gcm_five_block_closers.ml:178)  ← closes ciphertext conjunct 3
   │  │  └─ GCM_NBLOCK_CT_STEP_TAC 5 3 → GCM_NBLOCK_CT_LATER_STEP_TAC 5 3 (utils/gcm_aesgcm_nblock_helpers.ml:591)
   │  ├─ GCM_5BLOCK_CT4_STEP_TAC (utils/gcm_five_block_closers.ml:179)  ← closes ciphertext conjunct 4
   │  │  └─ GCM_NBLOCK_CT_STEP_TAC 5 4 → GCM_NBLOCK_CT_LATER_STEP_TAC 5 4 (utils/gcm_aesgcm_nblock_helpers.ml:591)
   │  ├─ GCM_5B_MASKED_CT5_CLOSE (aes256_gcm.ml:3482)   ← closes masked ciphertext conjunct 5 (partial block)
   │  │  ├─ FIVEBLOCK_MASK_REG (utils/gcm_five_block_closers.ml:192)
   │  │  ├─ NBLOCK_MASK_IDEM (utils/gcm_aesgcm_nblock_helpers.ml:973)
   │  │  ├─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │  │  ├─ gcm_ctr_inc (utils/gcm_aesgcm_nblock_helpers.ml:38)
   │  │  └─ CTR_WORD_INSERT / WORD_REVERSEFIELDS_REVERSEFIELDS / WORD_REVERSEFIELDS_8_BYTEREVERSE_32 /
   │  │     INSERT_SUBWORD / INSERT_IDEM (utils/gcm_aesgcm_helpers.ml ; nblock_helpers)
   │  └─ GCM_5B_GHASH_CLOSE (aes256_gcm.ml:3444)        ← closes GHASH / tag conjunct
   │     ├─ GCM_5B_FOLD_SPEC_CTS (aes256_gcm.ml:3289)   (fold ct1..ct4 spec forms into RHS ghash list)
   │     │  └─ GCM_5BLOCK_CT{2,3,4}_STEP_TAC (utils/gcm_five_block_closers.ml:177-179)
   │     ├─ GHASH_POLYVAL_ACC_5 (utils/gcm_aesgcm_helpers.ml:596)
   │     ├─ POLYVAL_DOT_H5_EQ (utils/gcm_aesgcm_nblock_helpers.ml:828)
   │     ├─ WORD_REVERSEFIELDS_XOR_8_128 (utils/gcm_aesgcm_helpers.ml)
   │     ├─ GCM_5B_MASK_COLLAPSE_ASMS (aes256_gcm.ml:3330)  → FIVEBLOCK_MASK_REG (…:192)
   │     ├─ GCM_5B_KS5_FOLD (aes256_gcm.ml:3340)        (bridge machine ks5 = spec ct5, fold into final_xi)
   │     ├─ GCM_5B_TAIL_NOFINAL (aes256_gcm.ml:3100)    (ctm5 abbrev + 5-block Karatsuba bridge + atomic/qS/qB ABBREVs)
   │     │  ├─ POLYVAL_DOT_H4_EQ_LOCAL (utils/gcm_aesgcm_nblock_helpers.ml:674)  (h⁴ left → symmetric)
   │     │  ├─ GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC (utils/gcm_five_block_closers.ml:98)   ← per-band bridge
   │     │  ├─ ghash_5block_karatsuba (utils/gcm_five_block_closers.ml:2)
   │     │  ├─ karatsuba_mid (common/polyval_ghash.ml:386)
   │     │  └─ BYTESWAP128_SUBWORD_LO/HI (utils/gcm_aesgcm_helpers.ml)
   │     ├─ XI_HS_LO_5 (aes256_gcm.ml:3086) / XI_HS_HI_5 (aes256_gcm.ml:3092)
   │     └─ GCM_5B_HALF_CLOSE (aes256_gcm.ml:3437)  [×2, one per Barrett half via BINOP_TAC]
   │        ├─ GCM_5B_FOLD_MIDS_TAC (aes256_gcm.ml:3397)   (fold w1md..w5md)
   │        ├─ GCM_5B_FOLD_TO `qS` 5 / `qB` 21 (aes256_gcm.ml:3420)
   │        │  └─ bubble_fix (utils/gcm_three_block_closers.ml)
   │        └─ bubble_fix (utils/gcm_three_block_closers.ml)
   ├─ OUT_BRIDGE_GEN (aes256_gcm.ml:6357)       (instanced offset=4, byte_len, co4)
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   ├─ GCM_FINAL_XI_UNFOLD (aes256_gcm.ml:6456)  (~(16*4+byte_len=0))
   ├─ GHASH_BLOCKS_5 (aes256_gcm.ml:6529)       (the 5-block GHASH block list)
   └─ INPUT_READS_128 (aes256_gcm.ml:6436)
```

**Notes (vs 1-block)**

- Length base `512 + 8*byte_len` (4 full + partial 5th): `GCM_*5` / `FIVEBLOCK_*` lemmas; cascade
  resolves 80/96/112 FALSE and 64 TRUE (into `.more_than_4`).
- Six-way `CONJ_TAC` (ct1..ct4, masked-ct5, GHASH); ct1 via `CT_CLOSE_5 1`, ct2–ct4 full-block
  `GCM_NBLOCK_CT_STEP_TAC 5 k`, block 5 masked via `GCM_5B_MASKED_CT5_CLOSE`.
- ct abbreviation is store-based (`abbrev_ct_from_store`) interleaved with `GCM_RUN`.
- GHASH closer uses `GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC` + `ghash_5block_karatsuba`,
  `GHASH_POLYVAL_ACC_5`, `POLYVAL_DOT_H5_EQ`, plus `GCM_5B_HALF_CLOSE` (w1md..w5md, qS-5, qB-21).
- `GCM_5B_KS5_FOLD` is an extra step bridging the collapsed +4 counter keystream of block 5 to spec.

---

## Six Blocks (80 < val len <= 96)

```
AES256_GCM_ENCRYPT_CORRECT (aes256_gcm.ml:8293)
└─ AES256_GCM_ENCRYPT_LT_6BLOCK_ABS (aes256_gcm.ml:7697)
   ├─ AES256_GCM_ENCRYPT_LT_6BLOCK_CONCRETE (aes256_gcm.ml:4238)   (goal = gcm_6b_goal, aes256_gcm.ml:3631)
   │  ├─ GCM_INIT_TAC GCM_CBZ_LEMMA6 (aes256_gcm.ml:1220)
   │  │  ├─ GCM_CBZ_LEMMA6 (aes256_gcm.ml:3544)                    (640+8*byte_len ≠ 0)
   │  │  └─ GCM_BND (aes256_gcm.ml:1212) → GCM_BOUNDS (aes256_gcm.ml:1198)
   │  ├─ GCM_PROLOGUE_TAC (aes256_gcm.ml:1228)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  ├─ GCM_RUN 20 263 (aes256_gcm.ml:1201)
   │  ├─ GCM_INLOOP_GUARD_TAC GCM_X6_LEMMA6 (aes256_gcm.ml:1236)
   │  │  ├─ GCM_X6_LEMMA6 (aes256_gcm.ml:3554)
   │  │  │  ├─ SIXBLOCK_USHR (utils/gcm_six_block_closers.ml:190)  (ushr(640+8*byte_len,3) = 80+byte_len)
   │  │  │  ├─ GCM_WSUB6 (aes256_gcm.ml:3550)
   │  │  │  └─ GCM_ANDMASK0 (aes256_gcm.ml:1280)
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)
   │  ├─ GCM_RUN 267 272 (aes256_gcm.ml:1201)
   │  ├─ GCM_BND16 GCM_X6TAIL_LEMMA6 (aes256_gcm.ml:1215)
   │  │  └─ GCM_X6TAIL_LEMMA6 (aes256_gcm.ml:3566)                 (X5 = 80+byte_len)
   │  │     └─ SIXBLOCK_USHR (utils/gcm_six_block_closers.ml:190)
   │  ├─ GCM_RUN_THEN GCM_CASCADE6_TAC 273 321 (aes256_gcm.ml:1206)
   │  │  └─ GCM_CASCADE6_TAC (aes256_gcm.ml:3616)                  (96,112 FALSE; 80 TRUE → more_than_5)
   │  │     ├─ GCM_CASC6_FALSE (aes256_gcm.ml:3575)
   │  │     │  └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml:991)
   │  │     └─ GCM_CASC6_TRUE (aes256_gcm.ml:3595)
   │  │        └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml:991)
   │  ├─ abbrev_ct_from_store 0 1 / 16 2 / 32 3 / 48 4 / 64 5 (aes256_gcm.ml:3049)
   │  │  (interleaved with GCM_RUN 322 335 / 336 362 / 363 376 / 377 411)
   │  ├─ SIXBLOCK_MASK_REG (utils/gcm_six_block_closers.ml:198)   (collapse nested word_insert mask reg)
   │  │  ├─ NBLOCK_WORD_INSERT_BOTH_LANES (utils/gcm_aesgcm_nblock_helpers.ml:942)
   │  │  └─ NBLOCK_MASK_PEEL_TAC 1 (utils/gcm_aesgcm_nblock_helpers.ml)
   │  ├─ GCM_NBLOCK_POST_SIM_NORMALIZE_TAC (utils/gcm_aesgcm_nblock_helpers.ml:525)
   │  ├─ ABBREV_FINAL_XI_TAC (utils/gcm_aesgcm_nblock_helpers.ml:504)
   │  ├─ SIXBLOCK_MASK_REG (utils/gcm_six_block_closers.ml:198)   (second use, into goal)
   │  ├─ SIXBLOCK_USHR (utils/gcm_six_block_closers.ml:190)       (ASM_SIMP X0 = word(80+byte_len))
   │  ├─ CT_CLOSE_6 1 (aes256_gcm.ml:4213)                        ← closes ct1 (counter = ivec)
   │  ├─ GCM_6BLOCK_CT2_STEP_TAC (utils/gcm_six_block_closers.ml:176)   ← closes ct2
   │  │  └─ GCM_NBLOCK_CT_STEP_TAC 6 2 (utils/gcm_aesgcm_nblock_helpers.ml:659)
   │  │     └─ GCM_NBLOCK_CT_LATER_STEP_TAC 6 2 (utils/gcm_aesgcm_nblock_helpers.ml:591)
   │  ├─ GCM_6BLOCK_CT3_STEP_TAC (utils/gcm_six_block_closers.ml:180)   ← closes ct3
   │  ├─ GCM_6BLOCK_CT4_STEP_TAC (utils/gcm_six_block_closers.ml:182)   ← closes ct4
   │  ├─ GCM_6BLOCK_CT5_STEP_TAC (utils/gcm_six_block_closers.ml:184)   ← closes ct5
   │  │  (each → GCM_NBLOCK_CT_STEP_TAC 6 k → GCM_NBLOCK_CT_LATER_STEP_TAC 6 k)
   │  ├─ GCM_6B_MASKED_CT6_CLOSE (aes256_gcm.ml:4221)             ← closes masked ct6 (partial, +5 counter)
   │  │  ├─ SIXBLOCK_MASK_REG (utils/gcm_six_block_closers.ml:198)
   │  │  ├─ NBLOCK_MASK_IDEM (utils/gcm_aesgcm_nblock_helpers.ml:973)
   │  │  ├─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │  │  └─ gcm_ctr_inc (utils/gcm_aesgcm_nblock_helpers.ml:38)
   │  └─ GCM_6B_GHASH_CLOSE (aes256_gcm.ml:4192)                  ← closes GHASH conjunct
   │     ├─ GCM_6B_FOLD_SPEC_CTS (aes256_gcm.ml:4035)            (fold ct1..ct5 spec forms into RHS ghash list)
   │     │  └─ GCM_6BLOCK_CT{2,3,4,5}_STEP_TAC (utils/gcm_six_block_closers.ml:176-184)
   │     ├─ GHASH_POLYVAL_ACC_6 (utils/gcm_aesgcm_helpers.ml:617)
   │     ├─ POLYVAL_DOT_H6_EQ (utils/gcm_aesgcm_nblock_helpers.ml:835)
   │     ├─ POLYVAL_DOT_H5_EQ (utils/gcm_aesgcm_nblock_helpers.ml:828)
   │     ├─ GCM_6B_MASK_COLLAPSE_ASMS (aes256_gcm.ml:4083)  → SIXBLOCK_MASK_REG (…:198)
   │     ├─ GCM_6B_KS6_FOLD (aes256_gcm.ml:4093)            (bridge machine block-6 keystream (+5 ctr) → spec ct6)
   │     ├─ GCM_6B_TAIL_NOFINAL (aes256_gcm.ml:3816)
   │     │  ├─ POLYVAL_DOT_H4_EQ_LOCAL (utils/gcm_aesgcm_nblock_helpers.ml:674)
   │     │  ├─ GHASH_6BLOCK_KARATSUBA_EQ_POLYVAL_ACC (utils/gcm_six_block_closers.ml:109)   ← per-N bridge
   │     │  │  ├─ GHASH_6BLOCK_AS_NBLOCK (utils/gcm_six_block_closers.ml:85)
   │     │  │  │  └─ ghash_Nblock_karatsuba (utils/gcm_aesgcm_nblock_helpers.ml:192)
   │     │  │  ├─ project_triples (utils/gcm_aesgcm_nblock_helpers.ml:401)
   │     │  │  └─ GHASH_NBLOCK_KARATSUBA_EQ_PROP3 (utils/gcm_aesgcm_nblock_helpers.ml:450)
   │     │  ├─ ghash_6block_karatsuba (utils/gcm_six_block_closers.ml:4)
   │     │  ├─ karatsuba_mid (common/polyval_ghash.ml:386)
   │     │  └─ bubble_sort_conv (utils/gcm_aesgcm_nblock_helpers.ml)
   │     ├─ XI_HS_LO_6 (aes256_gcm.ml:3804) / XI_HS_HI_6 (aes256_gcm.ml:3810)
   │     └─ GCM_6B_HALF_CLOSE (aes256_gcm.ml:4185)  [×2 via BINOP_TAC]
   │        ├─ GCM_6B_FOLD_MIDS_TAC (aes256_gcm.ml:4143)   (fold w1md..w6md)
   │        └─ GCM_6B_FOLD_TO `qS` 6 / `qB` 25 (aes256_gcm.ml:4168)
   │           └─ bubble_fix (utils/gcm_aesgcm_nblock_helpers.ml)
   ├─ OUT_BRIDGE_GEN (aes256_gcm.ml:6357)                        (KS_ITER=5, tail block co5)
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   ├─ GCM_FINAL_XI_UNFOLD (aes256_gcm.ml:6456)                  (~(16*5+byte_len=0))
   ├─ GHASH_BLOCKS_6 (aes256_gcm.ml:6547)
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   └─ INPUT_READS_128 (aes256_gcm.ml:6436)                      (pt1..pt6 = SUB_LIST chunks)
```

**Notes (vs 1-block)**

- Length base `640 + 8*byte_len` (5 full + partial 6th); cascade 96/112 FALSE, 80 TRUE
  (into `.more_than_5`). Mask register is a nested `word_insert` (collapsed via
  `SIXBLOCK_MASK_REG` → `NBLOCK_WORD_INSERT_BOTH_LANES` + `NBLOCK_MASK_PEEL_TAC`).
- Seven conjuncts: ct1..ct5 full (`CT_CLOSE_6 1` + `GCM_6BLOCK_CT{2,3,4,5}_STEP_TAC`), masked ct6
  (`GCM_6B_MASKED_CT6_CLOSE`, counter `gcm_ctr_inc^5`), GHASH (`GCM_6B_GHASH_CLOSE`).
- GHASH folds 6 blocks: `ghash_6block_karatsuba` + `GHASH_6BLOCK_KARATSUBA_EQ_POLYVAL_ACC`,
  `GHASH_POLYVAL_ACC_6`, `POLYVAL_DOT_H6_EQ`/`H5_EQ`; `GCM_6B_HALF_CLOSE` folds 6 mids, qS-6, qB-25.
- Consumes H-powers up to `h^6` and the `h5k` karatsuba-mid column; `h7k` first appears at 7-block.

---

## Seven Blocks (96 < val len <= 112)

```
AES256_GCM_ENCRYPT_CORRECT (aes256_gcm.ml:8293)
└─ AES256_GCM_ENCRYPT_LT_7BLOCK_ABS (aes256_gcm.ml:7893)        ← invoked at aes256_gcm.ml:8422
   ├─ AES256_GCM_ENCRYPT_LT_7BLOCK_CONCRETE (aes256_gcm.ml:5094)  (goal = gcm_7b_goal, aes256_gcm.ml:4370)
   │  ├─ GCM_INIT_TAC GCM_CBZ_LEMMA7 (aes256_gcm.ml:1220)
   │  │  ├─ GCM_CBZ_LEMMA7 (aes256_gcm.ml:4283)                  ← cbz-x1 guard nonzero
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)
   │  ├─ GCM_PROLOGUE_TAC (aes256_gcm.ml:1228)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  ├─ GCM_RUN 20 263 (aes256_gcm.ml:1201)
   │  ├─ GCM_INLOOP_GUARD_TAC GCM_X7_LEMMA7 (aes256_gcm.ml:1236)
   │  │  ├─ GCM_X7_LEMMA7 (aes256_gcm.ml:4293)                   ← X5 collapses to in_ptr
   │  │  │  ├─ SEVENBLOCK_USHR (utils/gcm_seven_block_closers.ml:191)
   │  │  │  ├─ GCM_WSUB7 (aes256_gcm.ml:4289)
   │  │  │  └─ GCM_ANDMASK0 (aes256_gcm.ml:1280)
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)
   │  ├─ GCM_RUN 267 272 (aes256_gcm.ml:1201)
   │  ├─ GCM_BND16 GCM_X7TAIL_LEMMA7 (aes256_gcm.ml:1215)
   │  │  └─ GCM_X7TAIL_LEMMA7 (aes256_gcm.ml:4305)               ← tail-length = word(96+byte_len)
   │  │     └─ SEVENBLOCK_USHR (utils/gcm_seven_block_closers.ml:191)
   │  ├─ GCM_RUN_THEN GCM_CASCADE7_TAC 273 321 (aes256_gcm.ml:1206)
   │  │  ├─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  │  └─ GCM_CASCADE7_TAC (aes256_gcm.ml:4355)                ← cmp x5,#0x70/#0x60 cascade
   │  │     ├─ GCM_CASC7_FALSE (aes256_gcm.ml:4314)              [threshold 112 falls through]
   │  │     │  └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml)
   │  │     └─ GCM_CASC7_TRUE (aes256_gcm.ml:4334)               [threshold 96 taken → more_than_6]
   │  │        └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml)
   │  ├─ abbrev_ct7 0 1 / 16 2 / 32 3 (aes256_gcm.ml:4556)       ← store-based ct1..ct3 abbreviation
   │  │  (interleaved: GCM_RUN 322 348 ; abbrev_ct7 48 4 ; GCM_RUN 349 362 ; abbrev_ct7 64 5 ;
   │  │   GCM_RUN 363 376 ; abbrev_ct7 80 6 ; GCM_RUN 377 417)
   │  ├─ SEVENBLOCK_MASK_REG (utils/gcm_seven_block_closers.ml:199)  ← collapse mask reg (pre-sim, RULE_ASSUM)
   │  ├─ GCM_NBLOCK_POST_SIM_NORMALIZE_TAC (utils/gcm_aesgcm_nblock_helpers.ml:525)
   │  ├─ ABBREV_FINAL_XI_TAC (utils/gcm_aesgcm_nblock_helpers.ml:504)  ← names read Q19 = final_xi
   │  ├─ SEVENBLOCK_MASK_REG (utils/gcm_seven_block_closers.ml:199)  ← collapse mask reg in goal
   │  ├─ SEVENBLOCK_USHR (utils/gcm_seven_block_closers.ml:191)
   │  ├─ CT_CLOSE_7 1 (aes256_gcm.ml:4581)                       ← closes ct1
   │  ├─ GCM_7BLOCK_CT2_STEP_TAC (utils/gcm_seven_block_closers.ml:177) ← closes ct2
   │  │  └─ GCM_NBLOCK_CT_STEP_TAC 7 2 (utils/gcm_aesgcm_nblock_helpers.ml:659)
   │  ├─ GCM_7BLOCK_CT3_STEP_TAC (utils/gcm_seven_block_closers.ml:179) ← closes ct3
   │  ├─ GCM_7BLOCK_CT4_STEP_TAC (utils/gcm_seven_block_closers.ml:181) ← closes ct4
   │  ├─ GCM_7BLOCK_CT5_STEP_TAC (utils/gcm_seven_block_closers.ml:183) ← closes ct5
   │  ├─ GCM_7BLOCK_CT6_STEP_TAC (utils/gcm_seven_block_closers.ml:185) ← closes ct6
   │  │  (each → GCM_NBLOCK_CT_STEP_TAC 7 k)
   │  ├─ GCM_7B_MASKED_CT7_CLOSE (aes256_gcm.ml:4587)            ← closes masked ct7 (partial, +6 counter)
   │  │  ├─ NBLOCK_MASK_IDEM (utils/gcm_aesgcm_nblock_helpers.ml)
   │  │  ├─ gcm_ctr_inc (utils/gcm_aesgcm_nblock_helpers.ml:38)
   │  │  ├─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │  │  └─ WORD_REVERSEFIELDS_8_BYTEREVERSE_32 / WORD_REVERSEFIELDS_REVERSEFIELDS /
   │  │     INSERT_SUBWORD / INSERT_IDEM / CTR_WORD_INSERT
   │  └─ GCM_7B_GHASH_CLOSE (aes256_gcm.ml:5072)                 ← closes GHASH conjunct
   │     ├─ GCM_7B_FOLD_SPEC_CTS (aes256_gcm.ml:4908; shadows 4603)  (folds ct1..ct6 into spec ghash list)
   │     │  └─ GCM_7BLOCK_CT{2,3,4,5,6}_STEP_TAC (utils/gcm_seven_block_closers.ml:177-185)
   │     ├─ GHASH_POLYVAL_ACC_7 (utils/gcm_aesgcm_helpers.ml:640)
   │     ├─ POLYVAL_DOT_H7_EQ (utils/gcm_aesgcm_nblock_helpers.ml:842)
   │     ├─ POLYVAL_DOT_H6_EQ (utils/gcm_aesgcm_nblock_helpers.ml:835)
   │     ├─ POLYVAL_DOT_H5_EQ (utils/gcm_aesgcm_nblock_helpers.ml:828)
   │     ├─ GCM_7B_MASK_COLLAPSE_ASMS (aes256_gcm.ml:4963)  → SEVENBLOCK_MASK_REG (…:199)
   │     ├─ GCM_7B_KS7_FOLD (aes256_gcm.ml:4973)            (bridge machine ks7 (+6 ctr) → spec ct7)
   │     ├─ GCM_7B_TAIL_NOFINAL (aes256_gcm.ml:4671)
   │     │  ├─ POLYVAL_DOT_H4_EQ_LOCAL (utils/gcm_aesgcm_nblock_helpers.ml:674)
   │     │  ├─ GHASH_7BLOCK_KARATSUBA_EQ_POLYVAL_ACC (utils/gcm_seven_block_closers.ml:117)
   │     │  ├─ ghash_7block_karatsuba (utils/gcm_seven_block_closers.ml:4)
   │     │  ├─ karatsuba_mid / KAR_SUBWORD_LEMMA
   │     │  ├─ WORD_REVERSEFIELDS_XOR_8_128 / REV8_JOIN_FOLD / REVERSEFIELDS8_SUBWORD_{LO,HI}
   │     │  └─ PMUL_NORM_CONV / bubble_sort_conv  (30 ct ABBREVs, 21 pmul ABBREVs, 42 z-vars, qS, qB)
   │     ├─ XI_HS_LO_7 (aes256_gcm.ml:4659) / XI_HS_HI_7 (aes256_gcm.ml:4665)
   │     └─ GCM_7B_HALF_CLOSE (aes256_gcm.ml:5066)  [×2 via BINOP_TAC]
   │        ├─ GCM_7B_FOLD_MIDS_TAC (aes256_gcm.ml:5022)         (7 mids: w1md..w7md)
   │        ├─ GCM_7B_FOLD_TO `qS` 7 / `qB` 29 (aes256_gcm.ml:5049)
   │        └─ bubble_fix  (XOR-AC normalization)
   ├─ OUT_BRIDGE_GEN (aes256_gcm.ml:6357)                     ← 6 full lanes + co6 via KS_ITER/CTR_ITER
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   ├─ GCM_FINAL_XI_UNFOLD (aes256_gcm.ml:6456)
   ├─ GHASH_BLOCKS_7 (aes256_gcm.ml:6566)
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   └─ INPUT_READS_128 (aes256_gcm.ml:6436)
```

**Notes (vs 1-block)**

- Six full lanes (ct1..ct6) + masked partial ct7 → eight conjuncts. ct1 `CT_CLOSE_7 1`;
  ct2..ct6 `GCM_7BLOCK_CT{k}_STEP_TAC` (`GCM_NBLOCK_CT_STEP_TAC 7 k`); ct7 `GCM_7B_MASKED_CT7_CLOSE`.
- Partial/last-block counter offset is +6 (`gcm_ctr_inc^6`); length lemmas over `768 + 8*byte_len`.
  Cascade resolves `cmp x5,#0x70` (112 FALSE) and `cmp x5,#0x60` (96 TRUE → `.more_than_6`).
- Mask collapse uses `SEVENBLOCK_MASK_REG`/`SEVENBLOCK_USHR` (3 appearances).
- GHASH: `GHASH_7BLOCK_KARATSUBA_EQ_POLYVAL_ACC` / `ghash_7block_karatsuba`, `GHASH_POLYVAL_ACC_7`,
  `POLYVAL_DOT_H5/H6/H7_EQ`; half-close folds 7 mids, qS-7, qB-29.
- Two `GCM_7B_FOLD_SPEC_CTS` definitions (4603, 4908); the later (4908) is the live binding.

---

## Eight Blocks (112 < val len <= 128)

```
AES256_GCM_ENCRYPT_CORRECT (aes256_gcm.ml:8293)
└─ AES256_GCM_ENCRYPT_LT_8BLOCK_ABS (aes256_gcm.ml:8091)        ← lifts concrete 8-block band to byte-list spec
   ├─ AES256_GCM_ENCRYPT_LT_8BLOCK_CONCRETE (aes256_gcm.ml:5892)   ← symbolic simulation
   │  ├─ GCM_INIT_TAC GCM_CBZ_LEMMA8 (aes256_gcm.ml:1220)
   │  │  ├─ GCM_CBZ_LEMMA8 (aes256_gcm.ml:5143)                  ← cbz x1 guard: 896+8*byte_len ≠ 0
   │  │  └─ GCM_BND (aes256_gcm.ml:1212) → GCM_BOUNDS (aes256_gcm.ml:1198)
   │  ├─ GCM_PROLOGUE_TAC (aes256_gcm.ml:1228)
   │  │  └─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  ├─ GCM_RUN 20 263 (aes256_gcm.ml:1201)
   │  ├─ GCM_INLOOP_GUARD_TAC GCM_X8_LEMMA8 (aes256_gcm.ml:1236)
   │  │  ├─ GCM_X8_LEMMA8 (aes256_gcm.ml:5153)                   ← X5 = in_ptr (no full chunks)
   │  │  │  ├─ EIGHTBLOCK_USHR (utils/gcm_eight_block_closers.ml:215)
   │  │  │  ├─ GCM_WSUB8 (aes256_gcm.ml:5149)
   │  │  │  └─ GCM_ANDMASK0 (aes256_gcm.ml:1280)
   │  │  └─ GCM_BND (aes256_gcm.ml:1212)
   │  ├─ GCM_RUN 267 272 (aes256_gcm.ml:1201)
   │  ├─ GCM_BND16 GCM_X8TAIL_LEMMA8 (aes256_gcm.ml:1215)        ← tail length = word(112+byte_len)
   │  │  └─ GCM_X8TAIL_LEMMA8 (aes256_gcm.ml:5165)
   │  │     └─ EIGHTBLOCK_USHR (utils/gcm_eight_block_closers.ml:215)
   │  ├─ GCM_RUN_THEN GCM_CASCADE8_TAC 273 276 (aes256_gcm.ml:1206)
   │  │  ├─ GCM_ENC_SIMPLIFY_TAC (utils/gcm_aesgcm_helpers.ml:335)
   │  │  └─ GCM_CASCADE8_TAC (aes256_gcm.ml:5195)                ← b.gt #112 (more_than_7) TRUE
   │  │     └─ GCM_CASC8_TRUE (aes256_gcm.ml:5174)               ← 113 ≤ total ≤ 128 ⇒ highest dispatch taken
   │  │        └─ NBLOCK_IVAL_WORD_SMALL (utils/gcm_aesgcm_nblock_helpers.ml)
   │  ├─ GCM_RUN 277 300 / 301 340 / 341 370 / 371 417 (aes256_gcm.ml:1201)  ← masked store + GHASH + Barrett tail
   │  ├─ abbrev_ct8 0 1 .. abbrev_ct8 96 7 (aes256_gcm.ml:5386)  ← store-based ct1..ct7 abbreviations
   │  ├─ EIGHTBLOCK_MASK_REG (utils/gcm_eight_block_closers.ml:226)  ← collapses the general mask register
   │  ├─ GCM_NBLOCK_POST_SIM_NORMALIZE_TAC (utils/gcm_aesgcm_nblock_helpers.ml:525)
   │  ├─ ABBREV_FINAL_XI_TAC (utils/gcm_aesgcm_nblock_helpers.ml:504)
   │  ├─ EIGHTBLOCK_MASK_REG (utils/gcm_eight_block_closers.ml:226)  [again, post ENSURES_FINAL_STATE]
   │  ├─ EIGHTBLOCK_USHR (utils/gcm_eight_block_closers.ml:215)
   │  ├─ CT_CLOSE_8 1 (aes256_gcm.ml:5411)                       ← closes ciphertext block ct1 (counter = ivec)
   │  │  └─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │  ├─ GCM_8BLOCK_CT2_STEP_TAC (utils/gcm_eight_block_closers.ml:206)  ← closes ct2
   │  │  └─ GCM_NBLOCK_CT_STEP_TAC 8 2 (utils/gcm_aesgcm_nblock_helpers.ml:659)
   │  │     └─ GCM_NBLOCK_CT_LATER_STEP_TAC 8 2 (utils/gcm_aesgcm_nblock_helpers.ml:591)
   │  ├─ GCM_8BLOCK_CT3_STEP_TAC (utils/gcm_eight_block_closers.ml:207)  ← closes ct3
   │  ├─ GCM_8BLOCK_CT4_STEP_TAC (utils/gcm_eight_block_closers.ml:208)  ← closes ct4
   │  ├─ GCM_8BLOCK_CT5_STEP_TAC (utils/gcm_eight_block_closers.ml:209)  ← closes ct5
   │  ├─ GCM_8BLOCK_CT6_STEP_TAC (utils/gcm_eight_block_closers.ml:210)  ← closes ct6
   │  ├─ GCM_8BLOCK_CT7_STEP_TAC (utils/gcm_eight_block_closers.ml:211)  ← closes ct7
   │  │  (each → GCM_NBLOCK_CT_STEP_TAC 8 k → GCM_NBLOCK_CT_LATER_STEP_TAC 8 k)
   │  ├─ GCM_8B_MASKED_CT8_CLOSE (aes256_gcm.ml:5417)            ← closes MASKED ct8 (partial tail, +7 counter)
   │  │  ├─ NBLOCK_MASK_IDEM (utils/gcm_aesgcm_nblock_helpers.ml:973)
   │  │  └─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │  └─ GCM_8B_GHASH_CLOSE (aes256_gcm.ml:5869)                 ← closes the GHASH (xi) conjunct
   │     ├─ GCM_8B_FOLD_SPEC_CTS (aes256_gcm.ml:5433)            (fold machine cts back to spec ct1..ct7)
   │     │  └─ GCM_8BLOCK_CT2..CT7_STEP_TAC (utils/gcm_eight_block_closers.ml:206-211)
   │     ├─ GHASH_POLYVAL_ACC_8 (utils/gcm_eight_block_closers.ml:181)   ← 8-block GHASH expansion
   │     ├─ POLYVAL_DOT_H8_EQ (utils/gcm_aesgcm_nblock_helpers.ml:849)
   │     ├─ POLYVAL_DOT_H7_EQ (utils/gcm_aesgcm_nblock_helpers.ml:842)
   │     ├─ POLYVAL_DOT_H6_EQ (utils/gcm_aesgcm_nblock_helpers.ml:835)
   │     ├─ POLYVAL_DOT_H5_EQ (utils/gcm_aesgcm_nblock_helpers.ml:828)
   │     ├─ WORD_REVERSEFIELDS_XOR_8_128 (utils/gcm_aesgcm_helpers.ml:399)
   │     ├─ GCM_8B_MASK_COLLAPSE_ASMS (aes256_gcm.ml:5761)  → EIGHTBLOCK_MASK_REG (…:226)
   │     ├─ GCM_8B_KS8_FOLD (aes256_gcm.ml:5769)                ← bridges machine ks8 (+7 counter) → spec ct8
   │     │  └─ aes256_block_enc (utils/aes256_gcm_block_enc_spec.ml:18)
   │     ├─ GCM_8B_TAIL_NOFINAL (aes256_gcm.ml:5497)
   │     │  └─ POLYVAL_DOT_H4_EQ_LOCAL (utils/gcm_aesgcm_nblock_helpers.ml:674)
   │     ├─ XI_HS_LO_8 (aes256_gcm.ml:5485) / XI_HS_HI_8 (aes256_gcm.ml:5491)
   │     └─ GCM_8B_HALF_CLOSE (aes256_gcm.ml:5862)              [×2, one per Barrett half]
   │        ├─ GCM_8B_FOLD_MIDS_TAC (aes256_gcm.ml:5816)        (folds 8 Karatsuba mids w1md..w8md)
   │        └─ GCM_8B_FOLD_TO `qS` 8 / `qB` 33 (aes256_gcm.ml:5845)
   ├─ OUT_BRIDGE_GEN (aes256_gcm.ml:6357)                        ← ciphertext word-form ⇒ byte_list_at output spec
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   ├─ GCM_FINAL_XI_UNFOLD (aes256_gcm.ml:6456)
   ├─ GHASH_BLOCKS_8 (aes256_gcm.ml:6586)                        ← gcm_ghash_blocks = [ct1..ct7] ++ [masked ct8]
   │  ├─ KS_ITER (aes256_gcm.ml:6295)
   │  └─ CTR_ITER_CLAUSES (aes256_gcm.ml:6302)
   └─ INPUT_READS_128 (aes256_gcm.ml:6436)                       ← byte_list_at input ⇒ 8 bytes128 reads (pt1..pt8)
```

**Notes (vs 1-block)**

- Still a partial-tail band: `112 < val len <= 128`, `byte_len = val len - 112`, `1 <= byte_len <= 16`.
  The 8th block is generally partial, so the postcondition masks it (`ctm8 = word_and ct8 mask`);
  `GHASH_BLOCKS_8` is `[ct1;…;ct7] ++ [masked ct8]` (7 full + masked tail). Full block only when `byte_len = 16`.
- Highest dispatch branch: `GCM_CASC8_TRUE`/`GCM_CASCADE8_TAC` resolve `b.gt #112` (`more_than_7`)
  TRUE directly — no FALSE thresholds below it.
- Mask collapse uses `EIGHTBLOCK_MASK_REG`/`EIGHTBLOCK_USHR` and `GCM_8B_MASK_COLLAPSE_ASMS`.
  Block 8 keystream uses `gcm_ctr_inc^7 ivec` (an `add7` WORD_RULE collapses seven increments).
- Nine conjuncts: ct1..ct7 (`CT_CLOSE_8 1` + `GCM_8BLOCK_CT{2..7}_STEP_TAC`), masked ct8
  (`GCM_8B_MASKED_CT8_CLOSE`), GHASH (`GCM_8B_GHASH_CLOSE`). GHASH needs `GHASH_POLYVAL_ACC_8` and
  `POLYVAL_DOT_H5..H8_EQ`; `GCM_8B_HALF_CLOSE` folds 8 mids, qS-8, qB-33.

---

## Cross-band summary

All bands share the same three-layer structure (`CORRECT` dispatch → `LT_NBLOCK_ABS` spec lift →
`LT_NBLOCK_CONCRETE` symbolic simulation) and the same shared per-step / lift machinery:

- **Per-step simulation:** `GCM_INIT_TAC`, `GCM_PROLOGUE_TAC`, `GCM_RUN` / `GCM_RUN_THEN`,
  `GCM_INLOOP_GUARD_TAC`, `GCM_ENC_SIMPLIFY_TAC` (after every step),
  `GCM_NBLOCK_POST_SIM_NORMALIZE_TAC`, `ABBREV_FINAL_XI_TAC`.
- **ABS lift (every band):** `OUT_BRIDGE_GEN` (+ `KS_ITER`, `CTR_ITER_CLAUSES`),
  `GCM_FINAL_XI_UNFOLD`, `GHASH_BLOCKS_N`, `INPUT_READS_128`.

Per-band the work scales with N:

| N | total `val len` | address base | cascade TRUE threshold | full + partial | GHASH bridge | half-close folds (mids / qS / qB) |
|---|-----------------|--------------|------------------------|----------------|--------------|-----------------------------------|
| 1 | 1..16   | `8*byte_len`     | (all fall through)         | 0 + 1 | `GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT` | 1 / — / —  |
| 2 | 17..32  | `128+8*byte_len` | `#0x10` (16)               | 1 + 1 | `GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC` | (via-branch) |
| 3 | 33..48  | `256+8*byte_len` | `#0x20` (32)               | 2 + 1 | `GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC` | 3 / 3 / 13 |
| 4 | 49..64  | `384+8*byte_len` | `#0x30` (48)               | 3 + 1 | `GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC` | 4 / 4 / 17 |
| 5 | 65..80  | `512+8*byte_len` | `#0x40` (64)               | 4 + 1 | `GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC` | 5 / 5 / 21 |
| 6 | 81..96  | `640+8*byte_len` | `#0x50` (80)               | 5 + 1 | `GHASH_6BLOCK_KARATSUBA_EQ_POLYVAL_ACC` | 6 / 6 / 25 |
| 7 | 97..112 | `768+8*byte_len` | `#0x60` (96)               | 6 + 1 | `GHASH_7BLOCK_KARATSUBA_EQ_POLYVAL_ACC` | 7 / 7 / 29 |
| 8 | 113..128| `896+8*byte_len` | `#0x70` (112)              | 7 + 1 | (8-block via `GHASH_POLYVAL_ACC_8`)     | 8 / 8 / 33 |

Notes on the table:
- "full + partial" = number of full leading blocks plus the single masked (partial) tail block.
- The partial tail block's keystream uses `gcm_ctr_inc^(N-1) ivec`, folded back via the per-band
  `GCM_NB_KSN_FOLD` step (no analogue in the 1-block band, whose single block uses `ivec` directly).
- 1- and 2-block use legacy GHASH closers (`GCM_GHASH_STEP_MASKED_TAC` /
  `GCM_2BLOCK_GHASH_VIA_BRANCH_TAC`); bands 3–8 use the uniform
  `GCM_NB_GHASH_CLOSE` → `GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC` → `GCM_NB_HALF_CLOSE` style.

---

## Are the eight proofs identical? — comparison & conclusion

**Short answer: no, and they cannot be — but they get progressively closer, and bands 5–8 *are*
the same proof script modulo `N`.** The expectation that "they should be identical" is right in
spirit (one shared binary, one shared tail), but three things genuinely force per-band variation,
and a fourth (historical) difference is incidental and *could* be unified.

### What is identical across all 8 bands

Every CONCRETE proof has the same skeleton, in the same order:

```
GCM_INIT_TAC GCM_CBZ_LEMMA_N  THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
GCM_INLOOP_GUARD_TAC GCM_X*_LEMMA_N  THEN GCM_RUN 267 272 THEN GCM_BND16 GCM_X*TAIL_LEMMA_N THEN
GCM_RUN_THEN GCM_CASCADE_N_TAC 273 ... THEN
   < interleaved  GCM_RUN <range> / abbreviate-ciphertext >
DISCH_THEN(... MATCH_MP  *BLOCK_MASK_REG ...) THEN
GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
ARM_STEPS_TAC ... THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
DISCH_THEN(... MATCH_MP *BLOCK_MASK_REG ...) THEN ASM_SIMP_TAC[*BLOCK_USHR] THEN
   < one CONJ_TAC per full ciphertext block > THEN
   < CONJ_TAC for the masked partial block > THEN
   < GHASH closer >
```

And every ABS proof is the *same* lift: `MP_TAC …CONCRETE`, then
`ENSURES_FRAME_SUBSUMED` / `ENSURES_POSTCONDITION_THM` / `ENSURES_PRECONDITION_THM` plumbing,
discharging the spec via `OUT_BRIDGE_GEN` (+ `KS_ITER`, `CTR_ITER_CLAUSES`),
`GCM_FINAL_XI_UNFOLD`, `GHASH_BLOCKS_N`, `INPUT_READS_128`. The top-level
`AES256_GCM_ENCRYPT_CORRECT` is just a uniform `ASM_CASES_TAC` cascade with one identical
one-liner per band.

So the *shape* is identical. The differences are all in the parameters and in two closers.

### Difference 1 — the band index `N` is threaded through everything (unavoidable, by design)

Each band is `N-1` full blocks + 1 partial. So `N` appears in:

- the per-band arithmetic lemmas (`GCM_CBZ_LEMMA_N`, `GCM_X*_LEMMA_N`, `GCM_X*TAIL_LEMMA_N`,
  `GCM_CASC*_N`, `*BLOCK_USHR`, `*BLOCK_MASK_REG`) — all the *same theorem* over a different
  address base `128*(N-1) + 8*byte_len` and a different cascade TRUE threshold `16*(N-1)`;
- the number of `CONJ_TAC … CT*_STEP_TAC` lines (one per full block, `N-1` of them);
- the counter depth of the masked block (`gcm_ctr_inc^(N-1) ivec`);
- the GHASH bridge (`GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC`) and the fold widths in the
  half-closer (`N` mids, qS over `N`, qB over `4N+1`).

This is intrinsic: the proofs operate on different numbers of blocks, so this kind of variation
is *not* removable — it is exactly what makes them eight different theorems rather than one.

### Difference 2 — the instruction step ranges differ (unavoidable — different code path)

The shared 8-lane body (steps 20–263), in-loop guard (264–266) and tail-length cascade are common,
but each band's `b.gt` cascade exits to a *different* `.L256_enc_blocks_more_than_k` label, so the
masked-store + per-block-GHASH windows differ. The `GCM_RUN <a> <b>` ranges and the
`ARM_STEPS_TAC` final ranges are therefore band-specific (e.g. 1-block finishes at 360–367,
2-block at 375–381, 8-block at 418–425, and 8-block even splits the cascade at `273 276`). This is
a property of the binary, not of the proof style.

### Difference 3 — two GHASH/CT closers are *historically* different (incidental — could be unified)

This is the only place where the proofs differ in *method* rather than in *parameter*:

| band | ciphertext-block closer(s) | masked-block closer | GHASH closer |
|------|----------------------------|---------------------|--------------|
| 1 | `GCM_CT_STEP_TAC` (= `GCM_NBLOCK_CT1_STEP_TAC 1`) | — (its single block *is* the partial) | `GCM_GHASH_STEP_MASKED_TAC` *(legacy, bespoke)* |
| 2 | `GCM_CT1_STEP_TAC` | `GCM_CTR1_FOLD_TAC` + `NBLOCK_MASK_IDEM` | `GCM_2BLOCK_GHASH_VIA_BRANCH_TAC` *(legacy, "via-branch")* |
| 3 | inline `GCM_NBLOCK_CT1_STEP_TAC` + `GCM_CT2_STEP_TAC` | `NBLOCK_MASK_IDEM` + `GCM_CTR2_FOLD_TAC` | `GCM_3BLOCK_GHASH_STEP_MASKED_TAC` |
| 4 | `GCM_4BLOCK_CT{1,2,3}…` | inline | `GCM_4B_FOLD_AND_BRIDGE … GCM_4B_LEAF_CLOSE` *(bespoke multi-step)* |
| 5 | `CT_CLOSE_5 1` + `GCM_5BLOCK_CT{2,3,4}_STEP_TAC` | `GCM_5B_MASKED_CT5_CLOSE` | `GCM_5B_GHASH_CLOSE` |
| 6 | `CT_CLOSE_6 1` + `GCM_6BLOCK_CT{2..5}_STEP_TAC` | `GCM_6B_MASKED_CT6_CLOSE` | `GCM_6B_GHASH_CLOSE` |
| 7 | `CT_CLOSE_7 1` + `GCM_7BLOCK_CT{2..6}_STEP_TAC` | `GCM_7B_MASKED_CT7_CLOSE` | `GCM_7B_GHASH_CLOSE` |
| 8 | `CT_CLOSE_8 1` + `GCM_8BLOCK_CT{2..7}_STEP_TAC` | `GCM_8B_MASKED_CT8_CLOSE` | `GCM_8B_GHASH_CLOSE` |

- **Bands 1–4 each use a *different, hand-written* GHASH closer.** 1-block reaches the Karatsuba
  result via `GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT` and closes with raw `WORD_RULE`; 2-block uses
  the "via-branch" reassembly (`JOIN_XI_SELF`, `GCM_2BLOCK_FOLD_QB_TAC`, `bubble_fix`); 3-block
  uses `GCM_3BLOCK_GHASH_STEP_MASKED_TAC`; 4-block is a long bespoke chain
  (`GCM_4B_FOLD_AND_BRIDGE THEN GCM_4B_TAIL3A THEN … THEN GCM_4B_LEAF_CLOSE`). These were written
  one at a time, before the uniform pattern was factored out.
- **Bands 5, 6, 7, 8 are the *same proof* — `GCM_NB_GHASH_CLOSE` → (`GCM_NB_FOLD_SPEC_CTS`,
  `GHASH_POLYVAL_ACC_N`, `POLYVAL_DOT_H*_EQ`, `GCM_NB_KSN_FOLD`, `GCM_NB_TAIL_NOFINAL` with
  `GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC`, `XI_HS_LO/HI_N`, `GCM_NB_HALF_CLOSE`) — instantiated at
  `N = 5,6,7,8`.** A normalized diff of the 5-/6-/7-block CONCRETE bodies (erasing digits and the
  `N`-BLOCK prefixes) is empty except for: the count of `CONJ_TAC … CT_STEP` lines, the count of
  `GCM_RUN`/abbreviate interleavings, and the counter nesting depth — i.e. exactly the Difference-1
  parameters. They are mechanically the same script.

### Difference 4 — ciphertext-abbreviation helper differs (incidental — naming drift)

A small wart: bands 5 and 6 abbreviate captured ciphertext with `abbrev_ct_from_store`, band 7 uses
`abbrev_ct7`, band 8 uses `abbrev_ct8`. These do the same job (pull `s13_k`/`ct_k` out of the store
facts); the suffix-named variants are leftovers. This is pure naming drift, not a methodological
difference.

### Conclusion

- The eight proofs are **structurally identical** at the level of: three-layer architecture, ABS
  lift, simulation skeleton, mask-collapse / final-xi / ENSURES_FINAL_STATE handshake.
- They **necessarily differ** in (a) the band index `N` threaded through every per-band lemma and
  the conjunct/counter counts, and (b) the instruction step ranges (different `more_than_k` exit in
  the one binary). Neither is removable.
- They **incidentally differ** in (c) the GHASH/CT closers for bands 1–4, each hand-written before
  the uniform closer existed, and (d) the `abbrev_ct*` helper name in bands 7–8. **Bands 5–8 are
  already the single uniform script instantiated at different `N`.**
- **If the goal is to make them "identical": bands 5–8 are the template.** Re-deriving the per-band
  arithmetic lemmas, the CT/masked closers, and the GHASH closer for `N = 1,2,3,4` from the same
  generators used by `N = 5..8` (and switching bands 5–8 to one `abbrev_ct` helper) would collapse
  all eight CONCRETE proofs to one parameterized tactic `GCM_NBLOCK_TAIL_TAC N` plus the
  unavoidable per-band step-range arguments. Bands 1–4 are the only real obstacle, and the obstacle
  is legacy bespoke closers, not anything intrinsic.

---

## Specification "jumps" and the theorems that prove them equivalent (5-block exemplar)

The proof is a chain of *representations*, each connected to the next by a theorem (or tactic) that
proves the two equivalent. There are two distinct kinds of jump: **architecture jumps** (vertical,
between the three layers — these change vocabulary/framing, not math) and **GHASH equivalence jumps**
(the real mathematical content, forming a wedge that meets at one point). The 5-block band is used
as the exemplar; bands 6/7/8 instantiate the identical wedge at different `N`.

```
═══════════════════════════════════════════════════════════════════════════════
 ARCHITECTURE JUMPS  (the three layers)
═══════════════════════════════════════════════════════════════════════════════

  ┌─────────────────────────────────────────────────────────────────────┐
  │  SPEC TRIPLE  (what the world wants)                                  │
  │    byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec keys) ...    │
  │    read xi_ptr = gcm_final_xi (val len) pt_in ivec keys xi h          │
  │    phrased over `val len`, input as a byte list                       │
  └─────────────────────────────────────────────────────────────────────┘
        ▲
        │  AES256_GCM_ENCRYPT_LT_5BLOCK_ABS         ← SPEC-LIFT layer
        │    • byte_len = val len − 64 arithmetic
        │    • ENSURES_FRAME_SUBSUMED   (frames)
        │    • ENSURES_POSTCONDITION_THM:  OUT_BRIDGE_GEN (stores→ciphertext)
        │                                  GCM_FINAL_XI_UNFOLD + GHASH_BLOCKS_5
        │    • ENSURES_PRECONDITION_THM:   INPUT_READS_128 (byte_list→bytes128)
        ▼
  ┌─────────────────────────────────────────────────────────────────────┐
  │  RAW-WORD TRIPLE  (gcm_5b_goal)                                       │
  │    per-block 128-bit stores:  ctk = word_xor ptk (aes256_block_enc …) │
  │    read xi_ptr = word_reversefields 8                                 │
  │                     (ghash_polyval_acc h (rev xi) [rev ct1;…;rev ctm5])│
  │    phrased over `byte_len`, input as bytes128 reads                   │
  └─────────────────────────────────────────────────────────────────────┘
        ▲
        │  AES256_GCM_ENCRYPT_LT_5BLOCK_CONCRETE    ← SIMULATION layer
        │    symbolic execution (GCM_RUN …), abbreviate ct_k / final_xi,
        │    then discharge 6 conjuncts:
        │       ct1..ct4  : CT_CLOSE_5 1 / GCM_5BLOCK_CT{2,3,4}_STEP_TAC
        │       masked ct5: GCM_5B_MASKED_CT5_CLOSE
        │       GHASH (xi): GCM_5B_GHASH_CLOSE  ────────┐
        ▼                                               │ (zoom below)
  ┌─────────────────────────────────────────────────┐  │
  │  MACHINE STATE  (Q-registers, memory bytes)      │  │
  │    actual aese/aesmc/pmull/eor3/str instructions │  │
  └─────────────────────────────────────────────────┘  │
                                                         │
═══════════════════════════════════════════════════════╪═══════════════════════
 GHASH JUMPS   (inside GCM_5B_GHASH_CLOSE)              ▼
═══════════════════════════════════════════════════════════════════════════════

  ┌──────────────────────────────────────────────────────────────────────┐
  │  [A] ASSEMBLY GHASH, fixed 5-arity                                     │
  │      ghash_5block_karatsuba b1..b5 (byteswap128 h) hk … h5k            │
  │      = word_reversefields 8 (word_join g f)    -- int128, byte-reversed│
  └──────────────────────────────────────────────────────────────────────┘
        │  GHASH_5BLOCK_AS_NBLOCK            (unfold fixed def → generic list;
        │                                    pure syntactic re-expression)
        ▼
  ┌──────────────────────────────────────────────────────────────────────┐
  │  [B] GENERIC N-BLOCK GHASH                                             │
  │      ghash_Nblock_karatsuba (project_triples quads)                    │
  │      = karatsuba_reduce_shared (kara_acc …)     -- SAME int128 value   │
  └──────────────────────────────────────────────────────────────────────┘
        │  GHASH_NBLOCK_KARATSUBA_EQ_PROP3   ◄══ THE KEYSTONE (induction)
        │     built from 3 structural lemmas:
        │       1. KARATSUBA_REDUCE_AS_PROP3_CLEAN  (Barrett = prop3∘pack)
        │       2. KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN (3 half-prods = full pmul)
        │       3. PACK_CORRECTED_XOR               (pack is XOR-linear)
        │     + KARA_ACC_PACK_HELPER (the list induction)
        │     side-cond discharged by hk_lo = karatsuba_mid h  (kara_quad_ok)
        ▼
  ┌──────────────────────────────────────────────────────────────────────┐
  │  [C] BATCHED CLEAN FIELD FORM   ◄══ THE MEETING POINT                  │
  │      word_reversefields 8                                              │
  │        (polyval_reduce_prop3 (⊕ₖ word_pmul bₖ hₖ))                     │
  └──────────────────────────────────────────────────────────────────────┘
        ▲
        │  GHASH_POLYVAL_ACC_5      (Horner spec → batched pmul-sum + prop3)
        │     └ ACC_2/3 proved in bool_poly ring; ACC_4..7 via ACC_BATCHED
        │  POLYVAL_DOT_H5_EQ        (reassociate h⁵: Horner → square-and-multiply,
        │     └ from POLYVAL_DOT_H4_EQ_LOCAL    to match the H-table powers)
        │
  ┌──────────────────────────────────────────────────────────────────────┐
  │  [D] SPEC GHASH  (iterative POLYVAL accumulator)                       │
  │      ghash_polyval_acc h (rev xi) [rev ct1; …; rev ctm5]               │
  └──────────────────────────────────────────────────────────────────────┘

   The closer drives [A]→[B]→[C] (assembly up) and [D]→[C] (spec down);
   the two meet at [C], then BINOP_TAC + GCM_5B_HALF_CLOSE (bubble_fix XOR-AC)
   finishes the two 64-bit Barrett halves by syntactic identity.

═══════════════════════════════════════════════════════════════════════════════
 CIPHERTEXT JUMP   (the ct conjuncts, for contrast)
═══════════════════════════════════════════════════════════════════════════════

   machine store  ──CT_CLOSE_5 / GCM_5BLOCK_CTk_STEP_TAC──►  raw-word ctk
        (aese/aesmc/str)   aes256_block_enc + gcm_ctr_inc       word_xor ptk (aes(ctrᵏ))
                                                                         │
                                      OUT_BRIDGE_GEN (in ABS) ───────────┘
                                      KS_ITER + CTR_ITER_CLAUSES
                                                                         ▼
                                   byte_list_at (aes256_gcm_encrypt …)   (spec)
```

### Reading the scheme

- **Architecture jumps** change *vocabulary/framing*, not math: `…_CONCRETE` (machine → raw-word
  per-store facts via symbolic simulation), `…_ABS` (raw-word → abstract spec via `OUT_BRIDGE_GEN`,
  `GHASH_BLOCKS_5`, `GCM_FINAL_XI_UNFOLD`, `INPUT_READS_128`), `…_CORRECT` (dispatch by `val len`).
- **GHASH equivalence jumps** are the real mathematical content and form a **wedge meeting at [C]**:
  - **[A]→[B]** `GHASH_5BLOCK_AS_NBLOCK` — syntactic only (same `int128` value).
  - **[B]→[C]** `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` — the keystone; proves Karatsuba+Barrett =
    polynomial multiply-accumulate, **once, by induction, for all N**.
  - **[D]→[C]** `GHASH_POLYVAL_ACC_5` + `POLYVAL_DOT_H5_EQ` — Horner-unroll the spec and fix the
    h-power associativity so it lands on the *same* `polyval_reduce_prop3 (⊕ pmul bₖ hₖ)`.
- **Output representation at [A] and [B]:** both are an `int128` *already in byte-reversed (memory)
  order* — specifically `word_reversefields 8 (word_join g f)`, the two 64-bit Barrett-reduced limbs
  joined high:low then byte-swapped. The `word_reversefields 8` wrapping `polyval_reduce_prop3` at
  [C] is the same reversal carried through, not introduced by the bridge.
- **Recurring engineering pattern:** every hard jump is proven **once, generically**
  (`GHASH_NBLOCK_KARATSUBA_EQ_PROP3`, `GHASH_POLYVAL_ACC_BATCHED`, `POLYVAL_DOT_H4_EQ_LOCAL`,
  `OUT_BRIDGE_GEN`); the per-N / per-band lemmas are cheap instantiations. This is exactly why bands
  5/6/7/8 share one framework — they instantiate this identical wedge at `N = 5,6,7,8`.
