# Plan — bring the 4-block proof to the 5/6/7-block framework

Goal: make `AES256_GCM_ENCRYPT_LT_4BLOCK_CONCRETE` and its closer machinery
structurally identical (modulo `N=4`) to the 5/6/7/8-block bands, so all of
3..8 read as one parameterized recipe. The underlying math is already shared
(`GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC` routes through the generic
`GHASH_NBLOCK_KARATSUBA_EQ_PROP3`); this is a structural / naming refactor,
verified interactively at every step. No new mathematics, no axioms.

## The canonical 5/6/7 framework (target shape)

CONCRETE body (uniform across 5/6/7/8):
```
GCM_INIT_TAC GCM_CBZ_LEMMA{N}  THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
GCM_INLOOP_GUARD_TAC GCM_X{..}_LEMMA{N} THEN GCM_RUN 267 272 THEN
GCM_BND16 GCM_X{..}TAIL_LEMMA{N} THEN
GCM_RUN_THEN GCM_CASCADE{N}_TAC 273 321 THEN
abbrev_ct_from_store 0 1 THEN ... abbrev_ct_from_store .. (N-1) THEN   (* store-based *)
SUBGOAL_THEN `1<=byte_len /\ byte_len<=16` MP_TAC THENL [ASM_REWRITE_TAC[];ALL_TAC] THEN
DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP {N}BLOCK_MASK_REG th])) THEN
GCM_RUN .. .. THEN
GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
ARM_STEPS_TAC AES256_GCM_EXEC (..--..) THEN
CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
SUBGOAL_THEN `1<=byte_len /\ byte_len<=16` MP_TAC THENL [ASM_REWRITE_TAC[];ALL_TAC] THEN
DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP {N}BLOCK_MASK_REG th]) THEN
ASM_SIMP_TAC[{N}BLOCK_USHR] THEN
(* N conjuncts: ct1..ct(N-1) full, masked-ct(N), GHASH *)
CONJ_TAC THENL [CT_CLOSE_{N} 1; ALL_TAC] THEN
CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_{N}BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
... (CT3..CT(N-1)) ...
CONJ_TAC THENL [GCM_{N}B_MASKED_CT{N}_CLOSE; ALL_TAC] THEN
ABBREV_TAC `ct{N} = word_xor pt{N} (aes256_block_enc (gcm_ctr_inc^{N-1} ivec) ...)` THEN
GCM_{N}B_GHASH_CLOSE
```

GHASH closer (uniform 5/6/7):
```
let GCM_{N}B_GHASH_CLOSE : tactic =
  GCM_{N}B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_{N}; POLYVAL_DOT_H{N}_EQ; ...down to H5_EQ...;
              GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_{N}B_MASK_COLLAPSE_ASMS THEN
  GCM_{N}B_KS{N}_FOLD THEN
  GCM_{N}B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_{N}; XI_HS_HI_{N}] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_pmul (...xihi...c1hi...xilo...c1lo...) (word_xor h?0 h?1) = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_{N}B_HALF_CLOSE; GCM_{N}B_HALF_CLOSE];;
```

## Current 4-block status (what matches / what differs)

ALREADY ALIGNED:
- CONCRETE simulation skeleton (INIT/PROLOGUE/RUN/INLOOP/CASCADE/MASK_REG/
  POST_SIM_NORMALIZE/ABBREV_FINAL_XI/ENSURES_FINAL_STATE) — same shape.
- Outer closer is now a single named `GCM_4B_GHASH_CLOSE` ending in
  `BINOP_TAC THENL [..;..]` (done in prior session, machine-verified).
- The math bridge `GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC` already exists and
  routes through the generic PROP3 bridge.
- Building blocks present: GCM_4B_FOLD_AND_BRIDGE, GCM_4B_TAIL3A,
  GCM_4B_TAIL_P1, GCM_4B_TAIL_P2C, GCM_4B_LEAF_CLOSE, GCM_4B_HALF_CLOSE,
  GCM_4B_MASK_COLLAPSE_TAC, GCM_4B_FOLD_MIDS_TAC, GCM_4B_FOLD_TO,
  GCM_4B_DROP_CT_STORES, XI_HS_LO/HI (unsuffixed).

DIFFERS (the work):
1. CONCRETE body uses inline `ABBREV_TAC ct1..ct3` + `FIRST_ASSUM Q0..Q3 s13`
   captures, not `abbrev_ct_from_store`. (5/6/7 use store-based.)
2. CONCRETE body closes the 4 CT conjuncts inline (CT1_FILE_TAC, CT2/CT3,
   and a long inline block-4 masked closer), not via `CT_CLOSE_4` +
   `GCM_4BLOCK_CT{2,3}_STEP_TAC` + a named `GCM_4B_MASKED_CT4_CLOSE`.
3. No `GCM_4B_FOLD_SPEC_CTS` — the ct-folds live inside `GCM_4B_FOLD_AND_BRIDGE`.
4. ACC/H-power REWRITE is inside FOLD_AND_BRIDGE, not a standalone step.
5. `GCM_4B_MASK_COLLAPSE_TAC` rewrites the GOAL; template
   `GCM_{N}B_MASK_COLLAPSE_ASMS` rewrites ASSUMPTIONS (RULE_ASSUM_TAC) and is a
   *step of the closer*, not mid-tail.
6. No `GCM_4B_KS4_FOLD` (block-4 keystream fold is done inline in the CONCRETE
   body before the closer).
7. No single `GCM_4B_TAIL_NOFINAL`; it is split as
   TAIL3A + MASK_COLLAPSE_TAC + DROP_CT_STORES + TAIL_P1 + TAIL_P2C.
8. No `XI_HS_LO_4`/`XI_HS_HI_4` and no explicit w1md SUBGOAL in the closer
   (folded inside GCM_4B_LEAF_CLOSE).
9. Closer uses `GCM_4B_LEAF_CLOSE` (= XI_HS rewrite + CTM4_FOLD + W1MD_FOLD +
   HALF_CLOSE); template uses `GCM_{N}B_HALF_CLOSE` directly with the XI_HS
   rewrite and w1md SUBGOAL lifted up into GCM_{N}B_GHASH_CLOSE.

## Decision: two conformance levels

LEVEL A — "closer reads like the template" (DONE): single named
`GCM_4B_GHASH_CLOSE`, BINOP_TAC THENL shape. Already machine-verified.

LEVEL B — "internally identical modulo N" (THIS PLAN): carve the 4-block
internals into the same six named slices and lift the CONCRETE body to the
store-based / named-CT-closer shape, so a future `GCM_NB_*` generator could
emit 4..8 uniformly.

Recommended scope = LEVEL B for the GHASH closer slices (steps 1-6 below);
the CONCRETE-body CT-conjunct restructure (steps 7-8) is optional polish and
can be deferred — flag for user.

## Step-by-step (each step: define in session, re-enter the live GHASH goal,
##                apply, confirm `proved`/single-subgoal, then splice + reload)

Reuse the proven workflow: load prefix live into polyval session
(`loadt prefix_4b.ml` after `Sys.chdir`), `set_goal gcm_4b_goal`, replay the
sim prefix to the GHASH conjunct (already scripted last session), then iterate.

S1. Add `XI_HS_LO_4` / `XI_HS_HI_4` as the N=4 copies of `XI_HS_LO`/`XI_HS_HI`
    (they are currently unsuffixed; 5/6/7 use the suffixed names). Trivial
    aliases — `let XI_HS_LO_4 = XI_HS_LO;;` or re-`prove` with the same body.

S2. Define `GCM_4B_FOLD_SPEC_CTS` = the ct-fold prefix of `GCM_4B_FOLD_AND_BRIDGE`
    WITHOUT the leading ACC/H-power REWRITE. Concretely: take FOLD_AND_BRIDGE's
    body minus its first `REWRITE_TAC[GHASH_POLYVAL_ACC_4; POLYVAL_DOT_H4_EQ_LOCAL;
    GSYM WORD_REVERSEFIELDS_XOR_8_128]`, so the REWRITE can be hoisted to the
    closer as its own step (matching the template's step 2).

S3. Define `GCM_4B_MASK_COLLAPSE_ASMS` as the RULE_ASSUM_TAC variant (copy
    GCM_5B_MASK_COLLAPSE_ASMS, swap FIVEBLOCK->FOURBLOCK). Keep
    GCM_4B_MASK_COLLAPSE_TAC too if the CONCRETE body still needs the goal-rewrite
    flavor; the closer uses the ASMS flavor.

S4. Define `GCM_4B_KS4_FOLD` mirroring `GCM_5B_KS5_FOLD` but for block 4 / +3
    counter. NOTE: in 4-block the block-4 keystream fold currently happens in the
    CONCRETE body (the `ABBREV ct4` + SUBGOAL before the closer). Two options:
      (a) leave that in the body and make GCM_4B_KS4_FOLD a no-op/ALL_TAC-ish
          placeholder (keeps closer shape but not honest), OR
      (b) move the block-4 keystream bridge into GCM_4B_KS4_FOLD so the closer
          owns it like 5/6/7. Prefer (b). Use add3 = WORD_RULE for the +3 counter
          (5-block uses add4; 4-block needs +3).

S5. Define `GCM_4B_TAIL_NOFINAL` = `GCM_4B_TAIL3A THEN GCM_4B_MASK_COLLAPSE_TAC
    THEN GCM_4B_DROP_CT_STORES THEN GCM_4B_TAIL_P1 THEN GCM_4B_TAIL_P2C`
    (the existing fused middle), as one named tactic matching GCM_5B_TAIL_NOFINAL.
    Verify the mask-collapse inside is reconciled with S3 (avoid double-collapse).

S6. Re-define `GCM_4B_GHASH_CLOSE` in the exact template body:
```
  GCM_4B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_4; POLYVAL_DOT_H4_EQ_LOCAL; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_4B_MASK_COLLAPSE_ASMS THEN
  GCM_4B_KS4_FOLD THEN
  GCM_4B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_4; XI_HS_HI_4] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xihi) (word_xor c1hi (word_xor xilo c1lo)))
                          (word_xor (hg0) hg1):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_4B_HALF_CLOSE; GCM_4B_HALF_CLOSE];;
```
    (h-power atom for block 1 in 4-block is `hg0/hg1`, cf. 5-block `hh0/hh1` —
    confirm against GCM_4B_TAIL_P1's ABBREVs: hg = polyval_dot(h^2)(h^2) = h^4.)
    Note: GCM_4B_HALF_CLOSE currently re-does the ctm4 fold + XI_HS internally;
    may need to trim it to match GCM_5B_HALF_CLOSE (mids-fold + qS + qB +
    bubble_fix only) once XI_HS/w1md are lifted out. Reconcile overlap.

S7. (OPTIONAL) Lift the CONCRETE body's CT-conjunct closes to named closers:
    add `CT_CLOSE_4`, `GCM_4BLOCK_CT2/3_STEP_TAC` already exist; add
    `GCM_4B_MASKED_CT4_CLOSE` (mirror GCM_5B_MASKED_CT5_CLOSE, +3 counter), then
    rewrite the 4 CONJ_TAC lines to match the 5-block body.

S8. (OPTIONAL) Switch CONCRETE body ct-abbrev to `abbrev_ct_from_store 0 1 ..
    48 4` instead of the inline Q0..Q3 captures + `ABBREV ct1..ct3`.

## Verification protocol (per step)
- After each S{i}: re-enter the live GHASH goal (cached sim prefix), apply the
  updated `GCM_4B_GHASH_CLOSE`, confirm it returns `proved` on that subgoal.
- After S6 (and after S7/S8 if done): splice into aes256_gcm.ml, regenerate
  `head -n <end-of-4block-proof>` prefix, `loadt` in a FRESH session, and confirm
  `AES256_GCM_ENCRYPT_LT_4BLOCK_CONCRETE` binds with `hyp = []` (hyps=0).
- Final: full-file `needs "arm/proofs/aes256_gcm.ml"` clean load (no regression
  in 5/6/7/8 or the top-level AES256_GCM_ENCRYPT_CORRECT).

## Risks / watch-items
- S4(b): the +3 counter bridge for block 4 may need different INSERT/peel depth
  than 5-block's +4; reuse the existing inline block-4 peel from the CONCRETE
  body (lines ~2768-2788) verbatim inside GCM_4B_KS4_FOLD.
- S5/S3 double mask-collapse: GCM_4B_TAIL_NOFINAL contains MASK_COLLAPSE_TAC; if
  GCM_4B_MASK_COLLAPSE_ASMS already collapsed in-asms, the second one may no-op
  or fail — test and drop whichever is redundant.
- S6: GCM_4B_LEAF_CLOSE vs GCM_4B_HALF_CLOSE overlap (LEAF = XI_HS + CTM4_FOLD +
  W1MD_FOLD + HALF). Lifting XI_HS + w1md into the closer means the per-half
  branch should call GCM_4B_HALF_CLOSE (not LEAF). Confirm HALF_CLOSE alone
  closes each half once the prep is hoisted.
- Keep `hyps=0` as the always-checked correctness signal.
```
