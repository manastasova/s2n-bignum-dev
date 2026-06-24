# Verifying AES-256-GCM Encryption in HOL Light — One-Page Overview

## What is being verified

A single ARM64 binary, `aes256_gcm.o`, that encrypts a buffer of any length 0–128 bytes and updates the GCM authentication tag. We prove **one theorem**, `AES256_GCM_ENCRYPT_CORRECT`: *for every input, running the actual machine instructions produces exactly the ciphertext and authentication value that the GCM standard prescribes.* The proof is **end-to-end** — from the literal bytes of the executable down to polynomial arithmetic over the finite field GF(2¹²⁸).

## The specifications (the mathematical reference)

Three layers of "what correct means," each defined independently of the code:

- **`aes256_gcm_encrypt`** — the ciphertext: each block is `plaintext ⊕ AES(counter)`, with the final partial block masked. (the *confidentiality* spec)
- **`gcm_final_xi`** — the authentication tag: the ciphertext blocks folded through **`ghash_polyval_acc`**, the GHASH Horner iteration `acc := (acc ⊕ block)·H`.
- **`polyval_dot`** — the field multiply underneath GHASH, defined as multiplication modulo the **RFC 8452 polynomial** `Q(x) = x¹²⁸+x¹²⁷+x¹²⁶+x¹²¹+1`. This is the bottom of the spec stack and is tied to the published standard, not to the code.

## The equivalence theorems (how the layers connect)

The proof is a chain of equalities, each a separately-proved theorem:

| Theorem | Proves |
|---|---|
| **`LT_NBLOCK_CONCRETE`** | *Running the instructions* = a raw bit-arithmetic formula (by symbolic simulation of the actual opcodes). **The trust boundary**: its right-hand side is a faithful transcript of the hardware, with no spec-shaping. |
| **`GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC`** (and the 1-block `…_EQ_POLYVAL_DOT`) | The hardware's Karatsuba-multiply + Barrett-reduction GHASH = the field operation `polyval_dot`. *This is the cryptographic heart* — it certifies the assembly's bit-twiddling really is multiplication in GF(2¹²⁸). |
| **`POLYVAL_DOT_CORRECT`** | `polyval_dot a b · x¹²⁸ ≡ a·b (mod Q(x))` — i.e. `polyval_dot` genuinely is the field multiply, proved in HOL's polynomial-ring algebra. |
| **`LT_NBLOCK_ABS`** | Rephrases each CONCRETE result in spec vocabulary (`aes256_gcm_encrypt` / `gcm_final_xi`), bridging raw words to the spec via `OUT_BRIDGE_GEN`, `GHASH_BLOCKS_N`, `GCM_FINAL_XI_UNFOLD`. |

## The whole structure, top to bottom

```
AES256_GCM_ENCRYPT_CORRECT            "the binary meets the GCM spec, all lengths"
        │  dispatch on input length (9 bands, 0–8 blocks)
        ▼
LT_NBLOCK_ABS                         spec-form: aes256_gcm_encrypt / gcm_final_xi
        │  bridge (pure algebra, no code)
        ▼
LT_NBLOCK_CONCRETE                    raw-word formula  ◀── instructions executed here
        │  GHASH closers
        ▼
ghash_Nblock_karatsuba  =  polyval_dot   (assembly GHASH = field multiply)
        │
        ▼
polyval_dot  =  multiply mod Q(x)        (= GF(2¹²⁸), Q from RFC 8452)
```

**One sentence:** the binary is simulated instruction-by-instruction into a raw bit formula (`CONCRETE`), that formula is proved equal to finite-field arithmetic over the published GCM polynomial (`…KARATSUBA_EQ_POLYVAL…` + `POLYVAL_DOT_CORRECT`), and that arithmetic is repackaged as the standard GCM spec (`ABS`), with a uniform length-dispatch assembling all cases into the single theorem `AES256_GCM_ENCRYPT_CORRECT`.

## What this guarantees, and the one caveat

There are **no axioms or cheats** — the theorem reduces to HOL Light's logical core. The trust rests on two human-checkable endpoints: the `CONCRETE` postcondition faithfully transcribes the hardware (verifiable by inspection), and `Q(x)` is the real GCM polynomial (RFC 8452). **Caveat:** the chain certifies against **POLYVAL** (RFC 8452); the formal proof that POLYVAL equals **NIST GHASH** (SP 800-38D) exists (`GUERON_PROP1`) but is not yet wired into this theorem.
