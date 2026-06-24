# AES-256-GCM proof — TODO

## Cosmetic: collapse `co0..co7` to a single tail-slot variable

**What:** The uniform precondition of `AES256_GCM_ENCRYPT_CORRECT` (and every
`AES256_GCM_ENCRYPT_LT_{N}BLOCK_ABS`) currently names 8 prior-output values:

```
read (memory :> bytes128 out_ptr) s = co0 /\
read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
... (through word 112) ... = co7
```

Only **one** of these is ever semantically used: the masked partial-tail store
reads back the prior contents of the tail slot at `out_ptr + 16*nf`, where
`nf = (val len - 1) DIV 16` is the band's full-block count. The other 7 `co`
variables are unconstrained dead weight (the full blocks are fully overwritten).

**Proposed form:** replace the 8 reads with a single

```
read (memory :> bytes128 (word_add out_ptr (word (16 * nf)))) s = coN
```

(per-band: `nf` is the concrete 0/1/.../7; in the combined theorem:
`nf = (val len - 1) DIV 16`). NOTE: the offset is `16*nf` (the tail block's
address), NOT `byte_len` — `byte_len` (1..16) is the tail *size*, not its offset.

**Status:** NOT STARTED. Purely cosmetic — the theorem proves the identical
statement either way; the extra `co` vars are harmless.

**Cost / risk:** touches the uniform precondition in all 9 ABS band lemmas +
the combined theorem, and each band's pre-impl bridge must derive the tail-slot
read from the new form. Needs full ~56 min reload validation, likely 2-3
iterations. Real breakage risk in the dispatch plumbing. Recommend prototyping
on the 1-block band on a scratch copy first.

**Related machinery:** `OUT_BRIDGE_GEN` already uses an indexed/quantified
`out0` form internally, so the bridge side is closer to this shape than the
surface precondition is.
