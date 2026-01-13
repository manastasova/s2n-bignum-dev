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
#define XOR256(a, b) _mm256_xor_si256(a, b)
#define XOReq256(a, b) a = _mm256_xor_si256(a, b)

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
  __m256i Eba, Ebe, Ebi, Ebo, Ebu; \
  __m256i Ega, Ege, Egi, Ego, Egu; \
  __m256i Eka, Eke, Eki, Eko, Eku; \
  __m256i Ema, Eme, Emi, Emo, Emu; \
  __m256i Esa, Ese, Esi, Eso, Esu;

/* thetaRhoPiChiIota with round index parameter (rc accessed via global pointer) */
#define thetaRhoPiChiIota(i, A, E)                                         \
  Ca = XOR256(A##ba, XOR256(A##ga, XOR256(A##ka, XOR256(A##ma, A##sa))));   \
  Ce = XOR256(A##be, XOR256(A##ge, XOR256(A##ke, XOR256(A##me, A##se))));   \
  Ci = XOR256(A##bi, XOR256(A##gi, XOR256(A##ki, XOR256(A##mi, A##si))));   \
  Co = XOR256(A##bo, XOR256(A##go, XOR256(A##ko, XOR256(A##mo, A##so))));   \
  Cu = XOR256(A##bu, XOR256(A##gu, XOR256(A##ku, XOR256(A##mu, A##su))));   \
  ROL64in256(Ce1, Ce, 1); Da = XOR256(Cu, Ce1);                            \
  ROL64in256(Ci1, Ci, 1); De = XOR256(Ca, Ci1);                            \
  ROL64in256(Co1, Co, 1); Di = XOR256(Ce, Co1);                            \
  ROL64in256(Cu1, Cu, 1); Do = XOR256(Ci, Cu1);                            \
  ROL64in256(Ca1, Ca, 1); Du = XOR256(Co, Ca1);                            \
  XOReq256(A##ba, Da); Bba = A##ba;                                        \
  XOReq256(A##ge, De); ROL64in256(Bbe, A##ge, 44);                         \
  XOReq256(A##ki, Di); ROL64in256(Bbi, A##ki, 43);                         \
  E##ba = XOR256(Bba, ANDnu256(Bbe, Bbi));                                 \
  XOReq256(E##ba, CONST256_64(rc[i]));                                     \
  XOReq256(A##mo, Do); ROL64in256(Bbo, A##mo, 21);                         \
  E##be = XOR256(Bbe, ANDnu256(Bbi, Bbo));                                 \
  XOReq256(A##su, Du); ROL64in256(Bbu, A##su, 14);                         \
  E##bi = XOR256(Bbi, ANDnu256(Bbo, Bbu));                                 \
  E##bo = XOR256(Bbo, ANDnu256(Bbu, Bba));                                 \
  E##bu = XOR256(Bbu, ANDnu256(Bba, Bbe));                                 \
  XOReq256(A##bo, Do); ROL64in256(Bga, A##bo, 28);                         \
  XOReq256(A##gu, Du); ROL64in256(Bge, A##gu, 20);                         \
  XOReq256(A##ka, Da); ROL64in256(Bgi, A##ka, 3);                          \
  E##ga = XOR256(Bga, ANDnu256(Bge, Bgi));                                 \
  XOReq256(A##me, De); ROL64in256(Bgo, A##me, 45);                         \
  E##ge = XOR256(Bge, ANDnu256(Bgi, Bgo));                                 \
  XOReq256(A##si, Di); ROL64in256(Bgu, A##si, 61);                         \
  E##gi = XOR256(Bgi, ANDnu256(Bgo, Bgu));                                 \
  E##go = XOR256(Bgo, ANDnu256(Bgu, Bga));                                 \
  E##gu = XOR256(Bgu, ANDnu256(Bga, Bge));                                 \
  XOReq256(A##be, De); ROL64in256(Bka, A##be, 1);                          \
  XOReq256(A##gi, Di); ROL64in256(Bke, A##gi, 6);                          \
  XOReq256(A##ko, Do); ROL64in256(Bki, A##ko, 25);                         \
  E##ka = XOR256(Bka, ANDnu256(Bke, Bki));                                 \
  XOReq256(A##mu, Du); ROL64in256(Bko, A##mu, 8);                          \
  E##ke = XOR256(Bke, ANDnu256(Bki, Bko));                                 \
  XOReq256(A##sa, Da); ROL64in256(Bku, A##sa, 18);                         \
  E##ki = XOR256(Bki, ANDnu256(Bko, Bku));                                 \
  E##ko = XOR256(Bko, ANDnu256(Bku, Bka));                                 \
  E##ku = XOR256(Bku, ANDnu256(Bka, Bke));                                 \
  XOReq256(A##bu, Du); ROL64in256(Bma, A##bu, 27);                         \
  XOReq256(A##ga, Da); ROL64in256(Bme, A##ga, 36);                         \
  XOReq256(A##ke, De); ROL64in256(Bmi, A##ke, 10);                         \
  E##ma = XOR256(Bma, ANDnu256(Bme, Bmi));                                 \
  XOReq256(A##mi, Di); ROL64in256(Bmo, A##mi, 15);                         \
  E##me = XOR256(Bme, ANDnu256(Bmi, Bmo));                                 \
  XOReq256(A##so, Do); ROL64in256(Bmu, A##so, 56);                         \
  E##mi = XOR256(Bmi, ANDnu256(Bmo, Bmu));                                 \
  E##mo = XOR256(Bmo, ANDnu256(Bmu, Bma));                                 \
  E##mu = XOR256(Bmu, ANDnu256(Bma, Bme));                                 \
  XOReq256(A##bi, Di); ROL64in256(Bsa, A##bi, 62);                         \
  XOReq256(A##go, Do); ROL64in256(Bse, A##go, 55);                         \
  XOReq256(A##ku, Du); ROL64in256(Bsi, A##ku, 39);                         \
  E##sa = XOR256(Bsa, ANDnu256(Bse, Bsi));                                 \
  XOReq256(A##ma, Da); ROL64in256(Bso, A##ma, 41);                         \
  E##se = XOR256(Bse, ANDnu256(Bsi, Bso));                                 \
  XOReq256(A##se, De); ROL64in256(Bsu, A##se, 2);                          \
  E##si = XOR256(Bsi, ANDnu256(Bso, Bsu));                                 \
  E##so = XOR256(Bso, ANDnu256(Bsu, Bsa));                                 \
  E##su = XOR256(Bsu, ANDnu256(Bsa, Bse));

/* Two round macro: A->E (even) then E->A (odd) */
#define twoRounds(r) \
  thetaRhoPiChiIota(r, A, E) \
  thetaRhoPiChiIota(r + 1, E, A)

#define LOAD_LANE(X, state, lane) \
  do { \
    const uint64_t *state64 = (const uint64_t *)(state); \
    __m256i t0, t1, t2, t3, t4, t6; \
    t0 = _mm256_loadu_si256((const __m256i *)&state64[lane]); \
    t1 = _mm256_loadu_si256((const __m256i *)&state64[lane + 25]); \
    t2 = _mm256_loadu_si256((const __m256i *)&state64[lane + 50]); \
    t3 = _mm256_loadu_si256((const __m256i *)&state64[lane + 75]); \
    t4 = _mm256_unpacklo_epi64(t0, t1); \
    t6 = _mm256_unpacklo_epi64(t2, t3); \
    X = _mm256_permute2x128_si256(t4, t6, 0x20); \
  } while(0)

#define copyFromState(X, state) \
  do { \
    LOAD_LANE(X##ba, state, 0); \
    LOAD_LANE(X##be, state, 1); \
    LOAD_LANE(X##bi, state, 2); \
    LOAD_LANE(X##bo, state, 3); \
    LOAD_LANE(X##bu, state, 4); \
    LOAD_LANE(X##ga, state, 5); \
    LOAD_LANE(X##ge, state, 6); \
    LOAD_LANE(X##gi, state, 7); \
    LOAD_LANE(X##go, state, 8); \
    LOAD_LANE(X##gu, state, 9); \
    LOAD_LANE(X##ka, state, 10); \
    LOAD_LANE(X##ke, state, 11); \
    LOAD_LANE(X##ki, state, 12); \
    LOAD_LANE(X##ko, state, 13); \
    LOAD_LANE(X##ku, state, 14); \
    LOAD_LANE(X##ma, state, 15); \
    LOAD_LANE(X##me, state, 16); \
    LOAD_LANE(X##mi, state, 17); \
    LOAD_LANE(X##mo, state, 18); \
    LOAD_LANE(X##mu, state, 19); \
    LOAD_LANE(X##sa, state, 20); \
    LOAD_LANE(X##se, state, 21); \
    LOAD_LANE(X##si, state, 22); \
    LOAD_LANE(X##so, state, 23); \
    LOAD_LANE(X##su, state, 24); \
  } while(0)

#define SCATTER_STORE256(state, idx, v)                        \
  do {                                                         \
    uint64_t *state64 = (uint64_t *)(state);                   \
    __m128d t = _mm_castsi128_pd(_mm256_castsi256_si128((v))); \
    _mm_storel_pd((double *)&state64[0 + (idx)], t);           \
    _mm_storeh_pd((double *)&state64[25 + (idx)], t);          \
    t = _mm_castsi128_pd(_mm256_extracti128_si256((v), 1));    \
    _mm_storel_pd((double *)&state64[50 + (idx)], t);          \
    _mm_storeh_pd((double *)&state64[75 + (idx)], t);          \
  } while (0)

#define copyToState(state, X)         \
  SCATTER_STORE256(state, 0, X##ba);  \
  SCATTER_STORE256(state, 1, X##be);  \
  SCATTER_STORE256(state, 2, X##bi);  \
  SCATTER_STORE256(state, 3, X##bo);  \
  SCATTER_STORE256(state, 4, X##bu);  \
  SCATTER_STORE256(state, 5, X##ga);  \
  SCATTER_STORE256(state, 6, X##ge);  \
  SCATTER_STORE256(state, 7, X##gi);  \
  SCATTER_STORE256(state, 8, X##go);  \
  SCATTER_STORE256(state, 9, X##gu);  \
  SCATTER_STORE256(state, 10, X##ka); \
  SCATTER_STORE256(state, 11, X##ke); \
  SCATTER_STORE256(state, 12, X##ki); \
  SCATTER_STORE256(state, 13, X##ko); \
  SCATTER_STORE256(state, 14, X##ku); \
  SCATTER_STORE256(state, 15, X##ma); \
  SCATTER_STORE256(state, 16, X##me); \
  SCATTER_STORE256(state, 17, X##mi); \
  SCATTER_STORE256(state, 18, X##mo); \
  SCATTER_STORE256(state, 19, X##mu); \
  SCATTER_STORE256(state, 20, X##sa); \
  SCATTER_STORE256(state, 21, X##se); \
  SCATTER_STORE256(state, 22, X##si); \
  SCATTER_STORE256(state, 23, X##so); \
  SCATTER_STORE256(state, 24, X##su);

/* 
 * rounds24 using a loop: 12 iterations, 2 rounds per iteration
 * Using switch-case to expand the twoRounds macro with compile-time constants
 */
#define rounds24_loop \
      do { \
        for (int i = 0; i < 12; i++) { \
            thetaRhoPiChiIota( 2*i, A, E) \
            thetaRhoPiChiIota( 2*i+1, E, A) \
        } \
    } while(0)

void mlk_keccakf1600x4_permute24_x2_unrolled(void *states, const uint64_t rc[24])
{
  __m256i *statesAsLanes = (__m256i *)states;
  declareABCDE
  copyFromState(A, statesAsLanes);
  /* Use loop-based rounds: 12 iterations x 2 rounds each */
  rounds24_loop;
  copyToState(statesAsLanes, A);
}