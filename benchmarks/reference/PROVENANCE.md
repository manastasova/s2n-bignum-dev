# Provenance of the AES-GCM reference kernels

Everything in this directory is **benchmark/test reference code only**: not part of
`libs2nbignum.a`, not covered by any HOL Light proof, linked into the `benchmark`
and `test` binaries alone. Upstream licences are Apache-2.0 / ISC / MIT-0.

Measured on Graviton3 (Neoverse-V1), `taskset -c 20`, idle core, min of 3 runs,
via `benchmarks/benchmark.c`. All kernels below are **AES-256** except where noted.

---

## 1. `awslc_aes_gcm_enc_kernel_4x.S` — aws-lc's shipped 4x kernel

- **Symbol:** `aes_gcm_enc_kernel_4x` (upstream `aes_gcm_enc_kernel`)
- **Repo:** <https://github.com/aws/aws-lc>
- **Generator:** `crypto/fipsmodule/modes/asm/aesv8-gcm-armv8.pl`
  <https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/modes/asm/aesv8-gcm-armv8.pl>
- **Extracted from the generated assembly:** `crypto/fipsmodule/aesv8-gcm-armv8.S`
- **Local checkout:** `/home/ubuntu/aws-lc-all/aws-lc` @ `47b0bb8cb6910304c1a53c0ba941282a51ecdda3`
- **Notes:** 722 instructions copied verbatim, **including** BoringSSL's FIPS
  dispatch-test instrumentation (`BORINGSSL_function_hit`, defined locally so the
  object links standalone). This is what aws-lc actually ships and what its
  dispatch uses for `len < 256`.

## 2. `awslc_aesv8_gcm_8x_enc_256_org.S` — aws-lc's original 8x kernel

- **Symbol:** `aesv8_gcm_8x_enc_256_org` (upstream `aesv8_gcm_8x_enc_256` — renamed
  because it collides exactly with ours)
- **Repo:** <https://github.com/aws/aws-lc>
- **Generator:** `crypto/fipsmodule/modes/asm/aesv8-gcm-armv8-unroll8-enc-256.pl`
  <https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/modes/asm/aesv8-gcm-armv8-unroll8-enc-256.pl>
- **Extracted from:** `crypto/fipsmodule/aesv8-gcm-armv8-unroll8-enc-256.S`
- **Local checkout:** same as above
- **Notes:** this is the code our optimized kernel derives from, i.e. the campaign
  baseline. NB `aesv8-gcm-armv8-unroll8.pl` generates only the 128/192 variants;
  the AES-256 encrypt kernel lives in the `-enc-256.pl` file above.

## 3. `awslc_hanno_enc_base_256.S` — Hanno Becker's clean AES-256 base

- **Symbol:** `aes_gcm_enc_kernel_slothy_base_256_base256`
- **Repo/branch:** <https://github.com/hanno-becker/aws-lc/tree/aarch64_aes_gcm_slothy>
- **File:** `crypto/fipsmodule/modes/asm/aesv8-gcm-armv8-enc-slothy-256.S`
  <https://github.com/hanno-becker/aws-lc/blob/aarch64_aes_gcm_slothy/crypto/fipsmodule/modes/asm/aesv8-gcm-armv8-enc-slothy-256.S>
- **Commit:** `83d5627a1d4315a71057fe6bc75900e080f255be` (2026-01-08)
- **Notes:** the *clean* / readability-oriented implementation, the input to
  SLOTHY, not its output — despite the file name, the symbol says `base`.
  `#include`s openssl headers, so `AWSLC_INC` must point at an aws-lc checkout.

## 4. `awslc_hanno_enc_opt_256_scalar_rk.S` — SLOTHY-optimized AES-256

- **Symbol:** `aes_gcm_enc_kernel_slothy_base_256_opt256`
- **Repo/branch:** as above
- **File:** `crypto/fipsmodule/modes/asm/slothy/opt/enc/aesv8-gcm-armv8-enc-opt-256_x4_scalar_iv_mem_late_tag_scalar_rk.S`
- **Notes:** SLOTHY-**rescheduled** (not software-pipelined — the pipelined ones
  carry `_swp`). Same symbol as #3 upstream, since base and opt are drop-in
  swaps; renamed here so they coexist. That branch also carries a `slothy/`
  benchmark tree (`benchmarks_g2.md`, `bench.md`) — those published numbers are
  **AES-128 on Graviton2**.

## 5. `gcm_x4_swp_aes256_derived.S` — DERIVED: AES-256 from the pipelined champion

- **Symbol:** `aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp_256`
- **Base repo/branch:** <https://github.com/jargh/s2n-bignum-dev/tree/gcm>
- **Base file:** `arm/aes_gcm/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp.S`
  <https://github.com/jargh/s2n-bignum-dev/blob/gcm/arm/aes_gcm/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp.S>
- **Commit:** `00fcedaf16b0a5fa6eebc007faeef727756a796f` (2026-08-22)
- **Modification:** AES round count 10 -> 14 ONLY; the SLOTHY schedule was not
  re-run. All 32 vector registers are live in that kernel, so the 4 extra round
  keys are handled by walking `v27` (rk9, used only as the final `aese` key)
  through rk9->rk13 at each of the 20 block sites and restoring it — the same
  key-recycling our own `aesv8_gcm_8x_enc_256` uses. `scalar_rk` now carries rk14.
- **Upstream status:** that base is the branch's measured **Graviton2 champion**
  (2874 MB/s @16KB, ~+19% over non-pipelined; commits `a61aabb8`, `7d0353cc`),
  and it has **no HOL Light proof** upstream.

## 6. `gcm_x4_scalar_rk_aes256_derived.S` — DERIVED: AES-256 from the clean kernel

- **Symbol:** `aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_256`
- **Base repo/branch:** as #5
- **Base file:** `arm/aes_gcm/unopt/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_unopt.S`
  <https://github.com/jargh/s2n-bignum-dev/blob/gcm/arm/aes_gcm/unopt/aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_unopt.S>
- **Modification:** AES round count 10 -> 14 ONLY, at the macro level (9 scripted
  edits). rk11/rk12/rk13 use v2/v3/v4, which are unused in that file; the extra
  rounds reuse the upstream-but-unused `aesr_9_10` / `aesr_11_12` macros.

## 7. `jargh_aes_gcm_enc_x4_swp_aes128.S` — the AES-128 champion, unmodified

- **Symbol:** `aes_gcm_enc_kernel_x4_scalar_iv_mem_late_tag_scalar_rk_swp`
- **Repo/branch/file/commit:** identical to #5's base, imported verbatim.
- **NOT COMPARABLE:** this is **AES-128** (10 rounds). It does ~10/14 of the AES
  work per block. Present only as the baseline for the #5 conversion.

---

## Our own kernel (for reference; not in this directory)

- `arm/aes-gcm/aesv8_gcm_8x_enc_256.S`, branch `aes_gcm_256_x8_verbose_opt_bench`
  @ `d1915515`. The only kernel here with a HOL Light proof
  (`arm/proofs/aesv8_gcm_8x_enc_256.ml`).

## Correctness

Every kernel above is differential-tested in `tests/test.c` against the same
independent C AES-256-GCM reference (`CRYPTO_gcm128_encrypt` + `gcm_init_nohw`,
32-byte key, `rounds = 14`) on ciphertext, GHASH accumulator and counter, across
the 13 benchmarked lengths plus every block count 1..64. All pass with 0
disparities. A control confirms the harness discriminates AES-128 from AES-256:
kernel #7 run against the AES-256 reference fails at the first case.
