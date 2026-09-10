// Reference model for gcm_init_v8 (GHASH/POLYVAL key-table expansion), for
// differential and regression testing of the imported AArch64 assembly.
//
// The three arithmetic functions below are copied BYTE-FOR-BYTE from AWS-LC
// (crypto/fipsmodule/modes/gcm_nohw.c): gcm_mul64_nohw (the BORINGSSL_HAS_UINT128
// branch), gcm_init_nohw, and gcm_polyval_nohw. Their bodies are a verbatim
// substring of that file and MUST NOT be edited.
//
// AWS-LC's constant-time nohw path only ever computes Htable[0] (the "twisted"
// key H_twisted = x*H mod Q(x)); it recomputes products on the fly rather than
// building the v8 power table. So there is no standalone C counterpart for
// Htable[1..11]. We therefore compose them from the verbatim arithmetic:
// iterate verbatim gcm_polyval_nohw from Htable[0] to obtain H^1..H^8 in the
// POLYVAL domain, then lay them out exactly as gcm_init_v8 stores them. That
// layout (byteswap of even powers, packed Karatsuba middles of power pairs) is
// the htable_mem predicate in common/polyval_ghash.ml, and it was verified
// empirically to match the assembly byte-for-byte over the all-zero, kH,
// all-ones and thousands of random inputs. The byteswap / xor "glue" around the
// two verbatim function bodies is permitted surrounding glue under the verbatim
// rule; every field multiplication is routed through verbatim gcm_polyval_nohw.

// glue: the u128 type is verbatim from crypto/fipsmodule/modes/internal.h:89
typedef struct { uint64_t hi,lo; } u128;
// glue: BoringSSL's uint128_t is __uint128_t; enables the BORINGSSL_HAS_UINT128
// branch of gcm_mul64_nohw copied below.
typedef unsigned __int128 uint128_t;

// ==== BEGIN VERBATIM (AWS-LC gcm_nohw.c, BORINGSSL_HAS_UINT128 branch) ====
static void gcm_mul64_nohw(uint64_t *out_lo, uint64_t *out_hi, uint64_t a,
                           uint64_t b) {
  // One term every four bits means the largest term is 64/4 = 16, which barely
  // overflows into the next term. Using one term every five bits would cost 25
  // multiplications instead of 16. It is faster to mask off the bottom four
  // bits of |a|, giving a largest term of 60/4 = 15, and apply the bottom bits
  // separately.
  uint64_t a0 = a & UINT64_C(0x1111111111111110);
  uint64_t a1 = a & UINT64_C(0x2222222222222220);
  uint64_t a2 = a & UINT64_C(0x4444444444444440);
  uint64_t a3 = a & UINT64_C(0x8888888888888880);

  uint64_t b0 = b & UINT64_C(0x1111111111111111);
  uint64_t b1 = b & UINT64_C(0x2222222222222222);
  uint64_t b2 = b & UINT64_C(0x4444444444444444);
  uint64_t b3 = b & UINT64_C(0x8888888888888888);

  uint128_t c0 = (a0 * (uint128_t)b0) ^ (a1 * (uint128_t)b3) ^
                 (a2 * (uint128_t)b2) ^ (a3 * (uint128_t)b1);
  uint128_t c1 = (a0 * (uint128_t)b1) ^ (a1 * (uint128_t)b0) ^
                 (a2 * (uint128_t)b3) ^ (a3 * (uint128_t)b2);
  uint128_t c2 = (a0 * (uint128_t)b2) ^ (a1 * (uint128_t)b1) ^
                 (a2 * (uint128_t)b0) ^ (a3 * (uint128_t)b3);
  uint128_t c3 = (a0 * (uint128_t)b3) ^ (a1 * (uint128_t)b2) ^
                 (a2 * (uint128_t)b1) ^ (a3 * (uint128_t)b0);

  // Multiply the bottom four bits of |a| with |b|.
  uint64_t a0_mask = UINT64_C(0) - (a & 1);
  uint64_t a1_mask = UINT64_C(0) - ((a >> 1) & 1);
  uint64_t a2_mask = UINT64_C(0) - ((a >> 2) & 1);
  uint64_t a3_mask = UINT64_C(0) - ((a >> 3) & 1);
  uint128_t extra = (a0_mask & b) ^ ((uint128_t)(a1_mask & b) << 1) ^
                    ((uint128_t)(a2_mask & b) << 2) ^
                    ((uint128_t)(a3_mask & b) << 3);

  *out_lo = (((uint64_t)c0) & UINT64_C(0x1111111111111111)) ^
            (((uint64_t)c1) & UINT64_C(0x2222222222222222)) ^
            (((uint64_t)c2) & UINT64_C(0x4444444444444444)) ^
            (((uint64_t)c3) & UINT64_C(0x8888888888888888)) ^ ((uint64_t)extra);
  *out_hi = (((uint64_t)(c0 >> 64)) & UINT64_C(0x1111111111111111)) ^
            (((uint64_t)(c1 >> 64)) & UINT64_C(0x2222222222222222)) ^
            (((uint64_t)(c2 >> 64)) & UINT64_C(0x4444444444444444)) ^
            (((uint64_t)(c3 >> 64)) & UINT64_C(0x8888888888888888)) ^
            ((uint64_t)(extra >> 64));
}

void gcm_init_nohw(u128 Htable[16], const uint64_t Xi[2]) {
  // We implement GHASH in terms of POLYVAL, as described in RFC 8452. This
  // avoids a shift by 1 in the multiplication, needed to account for bit
  // reversal losing a bit after multiplication, that is,
  // rev128(X) * rev128(Y) = rev255(X*Y).
  //
  // Per Appendix A, we run mulX_POLYVAL. Note this is the same transformation
  // applied by |gcm_init_clmul|, etc. Note |Xi| has already been byteswapped.
  //
  // See also slide 16 of
  // https://crypto.stanford.edu/RealWorldCrypto/slides/gueron.pdf
  Htable[0].lo = Xi[1];
  Htable[0].hi = Xi[0];

  uint64_t carry = Htable[0].hi >> 63;
  carry = 0u - carry;

  Htable[0].hi <<= 1;
  Htable[0].hi |= Htable[0].lo >> 63;
  Htable[0].lo <<= 1;

  // The irreducible polynomial is 1 + x^121 + x^126 + x^127 + x^128, so we
  // conditionally add 0xc200...0001.
  Htable[0].lo ^= carry & 1;
  Htable[0].hi ^= carry & UINT64_C(0xc200000000000000);

  // This implementation does not use the rest of |Htable|.
}

static void gcm_polyval_nohw(uint64_t Xi[2], const u128 *H) {
  // Karatsuba multiplication. The product of |Xi| and |H| is stored in |r0|
  // through |r3|. Note there is no byte or bit reversal because we are
  // evaluating POLYVAL.
  uint64_t r0, r1;
  gcm_mul64_nohw(&r0, &r1, Xi[0], H->lo);
  uint64_t r2, r3;
  gcm_mul64_nohw(&r2, &r3, Xi[1], H->hi);
  uint64_t mid0, mid1;
  gcm_mul64_nohw(&mid0, &mid1, Xi[0] ^ Xi[1], H->hi ^ H->lo);
  mid0 ^= r0 ^ r2;
  mid1 ^= r1 ^ r3;
  r2 ^= mid1;
  r1 ^= mid0;

  // Now we multiply our 256-bit result by x^-128 and reduce. |r2| and
  // |r3| shifts into position and we must multiply |r0| and |r1| by x^-128. We
  // have:
  //
  //       1 = x^121 + x^126 + x^127 + x^128
  //  x^-128 = x^-7 + x^-2 + x^-1 + 1
  //
  // This is the GHASH reduction step, but with bits flowing in reverse.

  // The x^-7, x^-2, and x^-1 terms shift bits past x^0, which would require
  // another reduction steps. Instead, we gather the excess bits, incorporate
  // them into |r0| and |r1| and reduce once. See slides 17-19
  // of https://crypto.stanford.edu/RealWorldCrypto/slides/gueron.pdf.
  r1 ^= (r0 << 63) ^ (r0 << 62) ^ (r0 << 57);

  // 1
  r2 ^= r0;
  r3 ^= r1;

  // x^-1
  r2 ^= r0 >> 1;
  r2 ^= r1 << 63;
  r3 ^= r1 >> 1;

  // x^-2
  r2 ^= r0 >> 2;
  r2 ^= r1 << 62;
  r3 ^= r1 >> 2;

  // x^-7
  r2 ^= r0 >> 7;
  r2 ^= r1 << 57;
  r3 ^= r1 >> 7;

  Xi[0] = r2;
  Xi[1] = r3;
}
// ==== END VERBATIM ====

// Compose the full 12-entry (192-byte) v8 table from the verbatim arithmetic.
// out is 24 uint64 words = Htable[0..11] in the exact byte layout that
// gcm_init_v8 stores (each word i occupies bytes [8i, 8i+8) of Htable).
static void ref_gcm_init_v8(uint64_t out[24], const uint64_t H[2]) {
  u128 tab[16];
  gcm_init_nohw(tab, H);        // verbatim: fills tab[0] = twisted H
  u128 hp[8];
  hp[0] = tab[0];               // h_power h 0 = h (POLYVAL domain: low=lo, high=hi)
  for (int n = 1; n < 8; ++n) { // h_power h (n) = polyval_dot(h_power h (n-1), h)
    uint64_t Xi[2] = { hp[n - 1].lo, hp[n - 1].hi };
    gcm_polyval_nohw(Xi, &tab[0]);   // verbatim field multiply by base H
    hp[n].lo = Xi[0];
    hp[n].hi = Xi[1];
  }
  // Layout (htable_mem, common/polyval_ghash.ml): four groups of three,
  //   [ byteswap128(H^{2k+1}), pack(kmid H^{2k+1}, kmid H^{2k+2}), byteswap128(H^{2k+2}) ].
  // byteswap128(v) stores word0 = v.hi, word1 = v.lo (swap of 64-bit halves);
  // karatsuba_mid(v) = v.lo ^ v.hi, packed word0 = kmid(first), word1 = kmid(second).
  #define REF_BSW(i,k)   do { out[2*(i)] = hp[k].hi; out[2*(i)+1] = hp[k].lo; } while (0)
  #define REF_MID(i,a,b) do { out[2*(i)] = hp[a].lo ^ hp[a].hi; \
                              out[2*(i)+1] = hp[b].lo ^ hp[b].hi; } while (0)
  REF_BSW(0,0);  REF_MID(1,0,1);  REF_BSW(2,1);
  REF_BSW(3,2);  REF_MID(4,2,3);  REF_BSW(5,3);
  REF_BSW(6,4);  REF_MID(7,4,5);  REF_BSW(8,5);
  REF_BSW(9,6);  REF_MID(10,6,7); REF_BSW(11,7);
  #undef REF_BSW
  #undef REF_MID
}

// Regression / known-answer vectors for gcm_init_v8.
//
// IMPORTANT: these are NOT independent published known-answer vectors. AWS-LC
// publishes no expected Htable bytes anywhere (gcm_test.cc only ABI-checks
// gcm_init_v8 via CHECK_ABI with no value comparison; gcm_tests.txt holds only
// end-to-end AES-GCM AEAD vectors). These are regression vectors: the INPUTS
// are real AWS-LC byte patterns (cited per entry), and the EXPECTED outputs are
// produced by the verbatim layered reference above (ref_gcm_init_v8). They pin
// the assembly's output to the AWS-LC C reference; independent assurance for
// Htable[1..11] comes from the formal proof that follows this import.
typedef struct { uint64_t H[2]; uint64_t Htable[24]; } gcm_init_kat;

static const gcm_init_kat gcm_init_v8_kats[] = {
  { // all-zero key (gcm_test.cc kKey[16]={0}; gcm_tests.txt Key=000..0)
    { UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000) },
    { UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000),
      UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000),
      UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000),
      UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000),
      UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000),
      UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000),
      UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000),
      UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000),
      }
  },
  { // kH GHASH hash key (gcm_test.cc:81)
    { UINT64_C(0x66e94bd4ef8a2c3b), UINT64_C(0x884cfa59ca342b2e) },
    { UINT64_C(0xcdd297a9df145877), UINT64_C(0x1099f4b39468565c), UINT64_C(0xdd4b631a4b7c0e2b),
      UINT64_C(0x62d81a7fe5da3296), UINT64_C(0x88d320376963120d), UINT64_C(0xea0b3a488cb9209b),
      UINT64_C(0x8695e702c322faf9), UINT64_C(0x35c1a04f8bfb2395), UINT64_C(0xb354474d48d9d96c),
      UINT64_C(0xb2261b4d0cb1e020), UINT64_C(0x568bd97348bd9145), UINT64_C(0xe4adc23e440c7165),
      UINT64_C(0xf9151b1f632d10b4), UINT64_C(0x7d845b630bb0a55d), UINT64_C(0x8491407c689db5e9),
      UINT64_C(0xa674eba8f9d7f250), UINT64_C(0xec87cfb0e19d1c4e), UINT64_C(0x4af32418184aee1e),
      UINT64_C(0x7d1998bcfc545474), UINT64_C(0xf109e6e0b31d1eee), UINT64_C(0x8c107e5c4f494a9a),
      UINT64_C(0x7498729da40cd280), UINT64_C(0xd0e417a05fe61ba4), UINT64_C(0xa47c653dfbeac924),
      }
  },
  { // X GHASH input block (gcm_test.cc:89)
    { UINT64_C(0x0388dace60b3a392), UINT64_C(0xf328c2b971b2fe78) },
    { UINT64_C(0x0711b59cc1674725), UINT64_C(0xe6518572e365fcf0), UINT64_C(0xe14030ee2202bbd5),
      UINT64_C(0x5809f1c26f9f77c6), UINT64_C(0x6ba634e2f78cb9bd), UINT64_C(0x33afc5209813ce7b),
      UINT64_C(0x2480a9a5ef935ea6), UINT64_C(0x996cff76b5a00d91), UINT64_C(0xbdec56d35a335337),
      UINT64_C(0x4bba3862e02746c1), UINT64_C(0x6f9df9f603adb10c), UINT64_C(0x2427c194e38af7cd),
      UINT64_C(0x6647806647024eaf), UINT64_C(0x2f850ebdc5090839), UINT64_C(0x49c28edb820b4696),
      UINT64_C(0xed25cdc99f7863b7), UINT64_C(0xe72719448e4134e0), UINT64_C(0x0a02d48d11395757),
      UINT64_C(0x67f882252c9e3487), UINT64_C(0xad61670c6f1b3e58), UINT64_C(0xca99e52943850adf),
      UINT64_C(0x13ae98e5749160d7), UINT64_C(0x58056643d3e0e64a), UINT64_C(0x4babfea6a771869d),
      }
  },
  { // buf fill 0x2a (gcm_test.cc:87 memset(buf,42))
    { UINT64_C(0x2a2a2a2a2a2a2a2a), UINT64_C(0x2a2a2a2a2a2a2a2a) },
    { UINT64_C(0x5454545454545454), UINT64_C(0x5454545454545454), UINT64_C(0x0000000000000000),
      UINT64_C(0x1840000000000000), UINT64_C(0x34ae2cee2cee2cee), UINT64_C(0x2cee2cee2cee2cee),
      UINT64_C(0x775e451544144515), UINT64_C(0x4414451544144515), UINT64_C(0x334a000000000000),
      UINT64_C(0x7e10100000000000), UINT64_C(0xd5248f97ab349f97), UINT64_C(0xab349f97ab349f97),
      UINT64_C(0x7083ae8514540051), UINT64_C(0x4000540514540051), UINT64_C(0x3083fa8000000000),
      UINT64_C(0x4d41104400000000), UINT64_C(0xa36d308a2c2ce2ce), UINT64_C(0xee2c20ce2c2ce2ce),
      UINT64_C(0x6bc27d24f4141550), UINT64_C(0x5455141054141550), UINT64_C(0x3f976934a0000000),
      UINT64_C(0x5b00010001000000), UINT64_C(0x82bb48c6117d5a4d), UINT64_C(0xd9bb49c6107d5a4d),
      }
  },
  { // NIST GCM key feffe992... (gcm_tests.txt)
    { UINT64_C(0x1c73658692e9fffe), UINT64_C(0x08833067948f6a6d) },
    { UINT64_C(0x38e6cb0d25d3fffc), UINT64_C(0x110660cf291ed4da), UINT64_C(0x29e0abc20ccd2b26),
      UINT64_C(0x82fb84a3f34674de), UINT64_C(0xeb93960f636d6c9b), UINT64_C(0x696812ac902b1845),
      UINT64_C(0xa988a28e756ac4d7), UINT64_C(0xd354acc3b14deb82), UINT64_C(0x7adc0e4dc4272f55),
      UINT64_C(0x201f0b729f33a2c9), UINT64_C(0xe558185dc0d17fb1), UINT64_C(0xc547132f5fe2dd78),
      UINT64_C(0x8a65b26231e48476), UINT64_C(0xb4dd049516c04cb8), UINT64_C(0x3eb8b6f72724c8ce),
      UINT64_C(0x8e6f5db74a2ee760), UINT64_C(0x273597be13e08cf2), UINT64_C(0xa95aca0959ce6b92),
      UINT64_C(0x776a1a1a4b06c139), UINT64_C(0x92651eab346f7a7c), UINT64_C(0xe50f04b17f69bb45),
      UINT64_C(0xfe24bfd49adee1a8), UINT64_C(0xd9acef7aea84dc33), UINT64_C(0x278850ae705a3d9b),
      }
  },
  { // ByteSwap pattern 0x0102030405060708 (gcm_test.cc:74)
    { UINT64_C(0x0102030405060708), UINT64_C(0x0807060504030201) },
    { UINT64_C(0x020406080a0c0e10), UINT64_C(0x100e0c0a08060402), UINT64_C(0x120a0a02020a0a12),
      UINT64_C(0x87e2803080308130), UINT64_C(0x0fd6007ba878a037), UINT64_C(0x8834804b28482107),
      UINT64_C(0xda832e983a70c72b), UINT64_C(0x9136ea9c061a5954), UINT64_C(0x4bb5c4043c6a9e7f),
      UINT64_C(0xddc95ed29389ce1c), UINT64_C(0xd4f1d7c250800913), UINT64_C(0x09388910c309c70f),
      UINT64_C(0x586d89fa95970578), UINT64_C(0x985d42989d9ec86d), UINT64_C(0xc030cb620809cd15),
      UINT64_C(0xbd18b861820de3d5), UINT64_C(0x184784d4478bb86e), UINT64_C(0xa55f3cb5c5865bbb),
      UINT64_C(0x17695928a3581176), UINT64_C(0x62b41b2bc6d21821), UINT64_C(0x75dd4203658a0957),
      UINT64_C(0x69939bca8f1ff8a9), UINT64_C(0x143511bba1e413c6), UINT64_C(0x7da68a712efbeb6f),
      }
  },
};

static const int gcm_init_v8_num_kats =
  (int)(sizeof(gcm_init_v8_kats) / sizeof(gcm_init_v8_kats[0]));
