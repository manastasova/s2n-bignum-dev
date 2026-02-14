/*
 * Modified version with loop-based rounds: 12 iterations, 2 rounds per iteration.
 * Instead of fully unrolled rounds24, this uses a for loop with 2x unrolling.
 *
 * Compilation:
 *   gcc -mavx2 -c 5_KeccakP_1600_times4_SIMD256_x2_unrolled.c -o keccak_x2_unrolled.o
 */

#include <immintrin.h>
#include <stdint.h>

#define MLK_ALIGN __attribute__((aligned(32)))

#define ANDnu256(a, b) _mm256_andnot_si256(a, b)
#define CONST256(a) _mm256_load_si256((const __m256i *)&(a))
#define CONST256_64(a) (__m256i) _mm256_broadcast_sd((const double *)(&a))
#define ROL64in256(d, a, o) \
  d = _mm256_or_si256(_mm256_slli_epi64(a, o), _mm256_srli_epi64(a, 64 - (o)))
#define ROL64in256_8(d, a) d = _mm256_shuffle_epi8(a, CONST256(rho8))
#define ROL64in256_56(d, a) d = _mm256_shuffle_epi8(a, CONST256(rho56))

static const uint64_t rho8[4] = {0x0605040302010007, 0x0E0D0C0B0A09080F,
                                 0x1615141312111017, 0x1E1D1C1B1A19181F};
static const uint64_t rho56[4] = {0x0007060504030201, 0x080F0E0D0C0B0A09,
                                  0x1017161514131211, 0x181F1E1D1C1B1A19};
#define XOR256(a, b) _mm256_xor_si256(a, b)
#define XOReq256(a, b) a = _mm256_xor_si256(a, b)

/* Round constants table is passed as parameter, accessed via local pointer */
static const uint64_t *keccakf1600RoundConstants;

#define declareABCDE               \
  __m256i Aba, Abe, Abi, Abo, Abu; \
  __m256i Aga, Age, Agi, Ago, Agu; \
  __m256i Aka, Ake, Aki, Ako, Aku; \
  __m256i Ama, Ame, Ami, Amo, Amu; \
  __m256i Asa, Ase, Asi, Aso, Asu; \
  __m256i Bba, Bbe, Bbi, Bbo, Bbu; \
  __m256i Bga, Bge, Bgi, Bgo, Bgu; \
  __m256i Bka, Bke, Bki, Bko, Bku; \
  __m256i Bma, Bme, Bmi, Bmo, Bmu; \
  __m256i Bsa, Bse, Bsi, Bso, Bsu; \
  __m256i Ca, Ce, Ci, Co, Cu;      \
  __m256i Ca1, Ce1, Ci1, Co1, Cu1; \
  __m256i Da, De, Di, Do, Du;      \
  __m256i Tba, Tbe, Tbi, Tbo, Tbu; \
  __m256i Tga, Tge, Tgi, Tgo, Tgu; \
  __m256i Tka, Tke, Tki, Tko, Tku; \
  __m256i Tma, Tme, Tmi, Tmo, Tmu; \
  __m256i Tsa, Tse, Tsi, Tso, Tsu; \

/* thetaRhoPiChiIota with round index parameter (rc accessed via global pointer) */
#define thetaRhoPiChiIota(i, A)                               \
  Ca = XOR256(A##ba, XOR256(A##ga, XOR256(A##ka, XOR256(A##ma, A##sa)))); \
  Ce = XOR256(A##be, XOR256(A##ge, XOR256(A##ke, XOR256(A##me, A##se)))); \
  Ci = XOR256(A##bi, XOR256(A##gi, XOR256(A##ki, XOR256(A##mi, A##si)))); \
  Co = XOR256(A##bo, XOR256(A##go, XOR256(A##ko, XOR256(A##mo, A##so)))); \
  Cu = XOR256(A##bu, XOR256(A##gu, XOR256(A##ku, XOR256(A##mu, A##su)))); \
                                                              \
  ROL64in256(Ce1, Ce, 1);                                     \
  Da = XOR256(Cu, Ce1);                                       \
  ROL64in256(Ci1, Ci, 1);                                     \
  De = XOR256(Ca, Ci1);                                       \
  ROL64in256(Co1, Co, 1);                                     \
  Di = XOR256(Ce, Co1);                                       \
  ROL64in256(Cu1, Cu, 1);                                     \
  Do = XOR256(Ci, Cu1);                                       \
  ROL64in256(Ca1, Ca, 1);                                     \
  Du = XOR256(Co, Ca1);                                       \
                                                              \
  XOReq256(A##ba, Da);                                        \
  Bba = A##ba;                                                \
  XOReq256(A##ge, De);                                        \
  ROL64in256(Bbe, A##ge, 44);                                 \
  XOReq256(A##ki, Di);                                        \
  ROL64in256(Bbi, A##ki, 43);                                 \
  Tba = XOR256(Bba, ANDnu256(Bbe, Bbi));                      \
  XOReq256(Tba, CONST256_64(keccakf1600RoundConstants[i]));   \
  Ca = Tba;                                                   \
  XOReq256(A##mo, Do);                                        \
  ROL64in256(Bbo, A##mo, 21);                                 \
  Tbe = XOR256(Bbe, ANDnu256(Bbi, Bbo));                      \
  Ce = Tbe;                                                   \
  XOReq256(A##su, Du);                                        \
  ROL64in256(Bbu, A##su, 14);                                 \
  Tbi = XOR256(Bbi, ANDnu256(Bbo, Bbu));                      \
  Ci = Tbi;                                                   \
  Tbo = XOR256(Bbo, ANDnu256(Bbu, Bba));                      \
  Co = Tbo;                                                   \
  Tbu = XOR256(Bbu, ANDnu256(Bba, Bbe));                      \
  Cu = Tbu;                                                   \
                                                              \
  XOReq256(A##bo, Do);                                        \
  ROL64in256(Bga, A##bo, 28);                                 \
  XOReq256(A##gu, Du);                                        \
  ROL64in256(Bge, A##gu, 20);                                 \
  XOReq256(A##ka, Da);                                        \
  ROL64in256(Bgi, A##ka, 3);                                  \
  Tga = XOR256(Bga, ANDnu256(Bge, Bgi));                      \
  XOReq256(Ca, Tga);                                          \
  XOReq256(A##me, De);                                        \
  ROL64in256(Bgo, A##me, 45);                                 \
  Tge = XOR256(Bge, ANDnu256(Bgi, Bgo));                      \
  XOReq256(Ce, Tge);                                          \
  XOReq256(A##si, Di);                                        \
  ROL64in256(Bgu, A##si, 61);                                 \
  Tgi = XOR256(Bgi, ANDnu256(Bgo, Bgu));                      \
  XOReq256(Ci, Tgi);                                          \
  Tgo = XOR256(Bgo, ANDnu256(Bgu, Bga));                      \
  XOReq256(Co, Tgo);                                          \
  Tgu = XOR256(Bgu, ANDnu256(Bga, Bge));                      \
  XOReq256(Cu, Tgu);                                          \
                                                              \
  XOReq256(A##be, De);                                        \
  ROL64in256(Bka, A##be, 1);                                  \
  XOReq256(A##gi, Di);                                        \
  ROL64in256(Bke, A##gi, 6);                                  \
  XOReq256(A##ko, Do);                                        \
  ROL64in256(Bki, A##ko, 25);                                 \
  Tka = XOR256(Bka, ANDnu256(Bke, Bki));                      \
  XOReq256(Ca, Tka);                                          \
  XOReq256(A##mu, Du);                                        \
  ROL64in256_8(Bko, A##mu);                                   \
  Tke = XOR256(Bke, ANDnu256(Bki, Bko));                      \
  XOReq256(Ce, Tke);                                          \
  XOReq256(A##sa, Da);                                        \
  ROL64in256(Bku, A##sa, 18);                                 \
  Tki = XOR256(Bki, ANDnu256(Bko, Bku));                      \
  XOReq256(Ci, Tki);                                          \
  Tko = XOR256(Bko, ANDnu256(Bku, Bka));                      \
  XOReq256(Co, Tko);                                          \
  Tku = XOR256(Bku, ANDnu256(Bka, Bke));                      \
  XOReq256(Cu, Tku);                                          \
                                                              \
  XOReq256(A##bu, Du);                                        \
  ROL64in256(Bma, A##bu, 27);                                 \
  XOReq256(A##ga, Da);                                        \
  ROL64in256(Bme, A##ga, 36);                                 \
  XOReq256(A##ke, De);                                        \
  ROL64in256(Bmi, A##ke, 10);                                 \
  Tma = XOR256(Bma, ANDnu256(Bme, Bmi));                      \
  XOReq256(Ca, Tma);                                          \
  XOReq256(A##mi, Di);                                        \
  ROL64in256(Bmo, A##mi, 15);                                 \
  Tme = XOR256(Bme, ANDnu256(Bmi, Bmo));                      \
  XOReq256(Ce, Tme);                                          \
  XOReq256(A##so, Do);                                        \
  ROL64in256_56(Bmu, A##so);                                  \
  Tmi = XOR256(Bmi, ANDnu256(Bmo, Bmu));                      \
  XOReq256(Ci, Tmi);                                          \
  Tmo = XOR256(Bmo, ANDnu256(Bmu, Bma));                      \
  XOReq256(Co, Tmo);                                          \
  Tmu = XOR256(Bmu, ANDnu256(Bma, Bme));                      \
  XOReq256(Cu, Tmu);                                          \
                                                              \
  XOReq256(A##bi, Di);                                        \
  ROL64in256(Bsa, A##bi, 62);                                 \
  XOReq256(A##go, Do);                                        \
  ROL64in256(Bse, A##go, 55);                                 \
  XOReq256(A##ku, Du);                                        \
  ROL64in256(Bsi, A##ku, 39);                                 \
  Tsa = XOR256(Bsa, ANDnu256(Bse, Bsi));                      \
  XOReq256(Ca, Tsa);                                          \
  XOReq256(A##ma, Da);                                        \
  ROL64in256(Bso, A##ma, 41);                                 \
  Tse = XOR256(Bse, ANDnu256(Bsi, Bso));                      \
  XOReq256(Ce, Tse);                                          \
  XOReq256(A##se, De);                                        \
  ROL64in256(Bsu, A##se, 2);                                  \
  Tsi = XOR256(Bsi, ANDnu256(Bso, Bsu));                      \
  XOReq256(Ci, Tsi);                                          \
  Tso = XOR256(Bso, ANDnu256(Bsu, Bsa));                      \
  XOReq256(Co, Tso);                                          \
  Tsu = XOR256(Bsu, ANDnu256(Bsa, Bse));                      \
  XOReq256(Cu, Tsu);                                          \
                                                              \
  A##ba = Tba; A##be = Tbe; A##bi = Tbi; A##bo = Tbo; A##bu = Tbu; \
  A##ga = Tga; A##ge = Tge; A##gi = Tgi; A##go = Tgo; A##gu = Tgu; \
  A##ka = Tka; A##ke = Tke; A##ki = Tki; A##ko = Tko; A##ku = Tku; \
  A##ma = Tma; A##me = Tme; A##mi = Tmi; A##mo = Tmo; A##mu = Tmu; \
  A##sa = Tsa; A##se = Tse; A##si = Tsi; A##so = Tso; A##su = Tsu;

#define LOAD_LANE_4X(X0, X1, X2, X3, state, lane) \
  do { \
    const uint64_t *state64 = (const uint64_t *)(state); \
    __m256i t0, t1, t2, t3; \
    t0 = _mm256_loadu_si256((const __m256i *)&state64[lane]); \
    t1 = _mm256_loadu_si256((const __m256i *)&state64[lane + 25]); \
    t2 = _mm256_loadu_si256((const __m256i *)&state64[lane + 50]); \
    t3 = _mm256_loadu_si256((const __m256i *)&state64[lane + 75]); \
    \
    __m256i tmp0 = _mm256_unpacklo_epi64(t0, t1); \
    __m256i tmp1 = _mm256_unpackhi_epi64(t0, t1); \
    __m256i tmp2 = _mm256_unpacklo_epi64(t2, t3); \
    __m256i tmp3 = _mm256_unpackhi_epi64(t2, t3); \
    \
    X0 = _mm256_permute2x128_si256(tmp0, tmp2, 0x20); \
    X1 = _mm256_permute2x128_si256(tmp1, tmp3, 0x20); \
    X2 = _mm256_permute2x128_si256(tmp0, tmp2, 0x31); \
    X3 = _mm256_permute2x128_si256(tmp1, tmp3, 0x31); \
  } while(0)

#define LOAD_LANE_1X(X, state, lane) \
  do { \
    const uint64_t *state64 = (const uint64_t *)(state); \
    X = _mm256_set_epi64x( \
      state64[lane + 75], \
      state64[lane + 50], \
      state64[lane + 25], \
      state64[lane]); \
  } while(0)

#define copyFromState(X, state) \
  do { \
    LOAD_LANE_4X(X##ba, X##be, X##bi, X##bo, state, 0); \
    LOAD_LANE_4X(X##bu, X##ga, X##ge, X##gi, state, 4); \
    LOAD_LANE_4X(X##go, X##gu, X##ka, X##ke, state, 8); \
    LOAD_LANE_4X(X##ki, X##ko, X##ku, X##ma, state, 12); \
    LOAD_LANE_4X(X##me, X##mi, X##mo, X##mu, state, 16); \
    LOAD_LANE_4X(X##sa, X##se, X##si, X##so, state, 20); \
    LOAD_LANE_1X(X##su, state, 24); \
  } while(0)

#define SCATTER_STORE256_4X(state, idx, lane0, lane1, lane2, lane3) \
  do { \
    uint64_t *state64 = (uint64_t *)(state); \
    \
    /* Inverse transpose: from interleaved lanes to consecutive per-instance storage */ \
    __m256i tmp0 = _mm256_unpacklo_epi64(lane0, lane1); \
    __m256i tmp1 = _mm256_unpackhi_epi64(lane0, lane1); \
    __m256i tmp2 = _mm256_unpacklo_epi64(lane2, lane3); \
    __m256i tmp3 = _mm256_unpackhi_epi64(lane2, lane3); \
    \
    __m256i t0 = _mm256_permute2x128_si256(tmp0, tmp2, 0x20); \
    __m256i t1 = _mm256_permute2x128_si256(tmp1, tmp3, 0x20); \
    __m256i t2 = _mm256_permute2x128_si256(tmp0, tmp2, 0x31); \
    __m256i t3 = _mm256_permute2x128_si256(tmp1, tmp3, 0x31); \
    \
    /* Store 4 consecutive lanes for each instance */ \
    _mm256_storeu_si256((__m256i *)&state64[(idx)], t0);      /* A0[idx+0..3] */ \
    _mm256_storeu_si256((__m256i *)&state64[(idx) + 25], t1); /* A1[idx+0..3] */ \
    _mm256_storeu_si256((__m256i *)&state64[(idx) + 50], t2); /* A2[idx+0..3] */ \
    _mm256_storeu_si256((__m256i *)&state64[(idx) + 75], t3); /* A3[idx+0..3] */ \
  } while (0)

/* Keep single-lane scatter for lane 24 */
#define SCATTER_STORE256_1X(state, idx, v) \
  do { \
    uint64_t *state64 = (uint64_t *)(state); \
    __m128d t = _mm_castsi128_pd(_mm256_castsi256_si128((v))); \
    _mm_storel_pd((double *)&state64[0 + (idx)], t); \
    _mm_storeh_pd((double *)&state64[25 + (idx)], t); \
    t = _mm_castsi128_pd(_mm256_extracti128_si256((v), 1)); \
    _mm_storel_pd((double *)&state64[50 + (idx)], t); \
    _mm_storeh_pd((double *)&state64[75 + (idx)], t); \
  } while (0)

#define copyToState(state, X) \
  do { \
    /* Store lanes 0-3 */ \
    SCATTER_STORE256_4X(state, 0, X##ba, X##be, X##bi, X##bo); \
    \
    /* Store lanes 4-7 */ \
    SCATTER_STORE256_4X(state, 4, X##bu, X##ga, X##ge, X##gi); \
    \
    /* Store lanes 8-11 */ \
    SCATTER_STORE256_4X(state, 8, X##go, X##gu, X##ka, X##ke); \
    \
    /* Store lanes 12-15 */ \
    SCATTER_STORE256_4X(state, 12, X##ki, X##ko, X##ku, X##ma); \
    \
    /* Store lanes 16-19 */ \
    SCATTER_STORE256_4X(state, 16, X##me, X##mi, X##mo, X##mu); \
    \
    /* Store lanes 20-23 */ \
    SCATTER_STORE256_4X(state, 20, X##sa, X##se, X##si, X##so); \
    \
    /* Store lane 24 */ \
    SCATTER_STORE256_1X(state, 24, X##su); \
  } while(0)

/* 
 * rounds24 using a loop: 12 iterations, 2 rounds per iteration
 * Using switch-case to expand the twoRounds macro with compile-time constants
 */
#define rounds24_loop \
      do { \
        for (int i = 0; i < 12; i++) { \
            thetaRhoPiChiIota( 2*i, A) \
            thetaRhoPiChiIota( 2*i+1, A) \
        } \
    } while(0)

void mlk_keccakf1600x4_permute24_x2_unrolled_one_arg_special_rho(void *states, const uint64_t rc[24])
{
  __m256i *statesAsLanes = (__m256i *)states;
  /* Set the global pointer to use the passed-in round constants */
  keccakf1600RoundConstants = rc;
  declareABCDE
  copyFromState(A, statesAsLanes);
  /* Use loop-based rounds: 12 iterations x 2 rounds each */
  rounds24_loop;
  copyToState(statesAsLanes, A);
}
