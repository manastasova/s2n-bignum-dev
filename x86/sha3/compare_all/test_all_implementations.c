/*
 * Test and Benchmark file for Keccak-f1600x4 implementations
 * 
 * This file tests and benchmarks various Keccak-f1600x4 implementations for correctness
 * and performance.
 *
 * Compilation instructions:
 *   cd ~/mlkem_keccak_bench/compare_all && make clean && make
 *
 * Run instructions:
 *   ./test_all_implementations              # Run all tests and benchmarks
 *   ./test_all_implementations -10000       # Custom repetition count
 *   ./test_all_implementations org          # Test only "org" implementation
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>
#include <time.h>
#include <math.h>

/* =============================================================================
 * Configuration
 * ============================================================================= */

#define INNER_REPS UINT64_C(10000)
#define OUTER_REPS 5
#define CORE_REPS (65 * OUTER_REPS)
#define CORE_REPF ((double) CORE_REPS)
#define BUFFERSIZE 1000
#define KECCAK_STATE_SIZE 100

/* =============================================================================
 * External declarations for implementations to test
 * ============================================================================= */

// Original mlkem-native implementation (no rc parameter)
extern void mlk_keccakf1600x4_permute24_org(void *states);

// All other implementations take rc parameter
extern void mlk_keccakf1600x4_permute24_rc_table(void *states, const uint64_t rc[24]);
extern void mlk_keccakf1600x4_permute24_no_special_rho(void *states, const uint64_t rc[24]);
extern void mlk_keccakf1600x4_permute24_no_thepta_preps(void *states, const uint64_t rc[24]);
extern void mlk_keccakf1600x4_permute24_updae_load(void *states, const uint64_t rc[24]);
extern void mlk_keccakf1600x4_permute24_x2_unrolled(void *states, const uint64_t rc[24]);
extern void mlk_keccakf1600x4_permute24_loop(void *states, const uint64_t rc[24]);
extern void mlk_keccakf1600x4_permute24_x2_unrolled_one_arg(void *states, const uint64_t rc[24]);
extern void mlk_keccakf1600x4_permute24_x2_unrolled_one_arg_special_rho(void *states, const uint64_t rc[24]);
extern void mlk_keccakf1600x4_permute24_loop_special_rho(void *states, const uint64_t rc[24]);
extern void mlk_keccakf1600x4_permute24_x2_unrolled_one_arg_special_rho_adds(void *states, const uint64_t rc[24]);

// Assembly implementation from s2n-bignum
extern void sha3_keccak4_f1600(void *states, const uint64_t rc[24]);

/* =============================================================================
 * Keccak round constants
 * ============================================================================= */

static const uint64_t keccak_rc[24] = {
    UINT64_C(0x0000000000000001), UINT64_C(0x0000000000008082),
    UINT64_C(0x800000000000808a), UINT64_C(0x8000000080008000),
    UINT64_C(0x000000000000808b), UINT64_C(0x0000000080000001),
    UINT64_C(0x8000000080008081), UINT64_C(0x8000000000008009),
    UINT64_C(0x000000000000008a), UINT64_C(0x0000000000000088),
    UINT64_C(0x0000000080008009), UINT64_C(0x000000008000000a),
    UINT64_C(0x000000008000808b), UINT64_C(0x800000000000008b),
    UINT64_C(0x8000000000008089), UINT64_C(0x8000000000008003),
    UINT64_C(0x8000000000008002), UINT64_C(0x8000000000000080),
    UINT64_C(0x000000000000800a), UINT64_C(0x800000008000000a),
    UINT64_C(0x8000000080008081), UINT64_C(0x8000000000008080),
    UINT64_C(0x0000000080000001), UINT64_C(0x8000000080008008)
};

static const uint64_t keccak_r[5][5] = {
    { 0, 36, 3, 41, 18 }, { 1, 44, 10, 45, 2 }, { 62, 6, 43, 15, 61 },
    { 28, 55, 25, 21, 56 }, { 27, 20, 39, 8, 14 }
};

/* =============================================================================
 * Global variables
 * ============================================================================= */

static uint64_t b0[BUFFERSIZE];
static uint64_t default_reps = INNER_REPS;
static uint64_t inner_reps = INNER_REPS;
static char *function_to_test = "";
static double arithmean = 0.0, geomean = 0.0;
static int benchmark_tests = 0;
static uint64_t keccak_states_bench[KECCAK_STATE_SIZE] __attribute__((aligned(32)));

/* =============================================================================
 * Helper functions
 * ============================================================================= */

static inline uint64_t rol(uint64_t x, uint64_t k) {
    k &= 0x3F;
    return k ? (x << k) | (x >> (64 - k)) : x;
}

#define add5(x,y) (((x) + (y)) % 5)
#define sub5(x,y) (((x) + (5 - (y))) % 5)

/* =============================================================================
 * Reference Keccak-f1600 implementation
 * ============================================================================= */

static void reference_keccak_f1600(uint64_t r[25], uint64_t a[25]) {
    uint64_t A[5][5], B[5][5], C[5], D[5];

    for (int x = 0; x < 5; ++x)
        for (int y = 0; y < 5; ++y)
            A[x][y] = a[5*y+x];

    for (int i = 0; i < 24; ++i) {
        for (int x = 0; x < 5; ++x)
            C[x] = A[x][0] ^ A[x][1] ^ A[x][2] ^ A[x][3] ^ A[x][4];
        for (int x = 0; x < 5; ++x)
            D[x] = C[sub5(x,1)] ^ rol(C[add5(x,1)],1);
        for (int x = 0; x < 5; ++x)
            for (int y = 0; y < 5; ++y)
                A[x][y] ^= D[x];
        for (int x = 0; x < 5; ++x)
            for (int y = 0; y < 5; ++y)
                B[y][(2*x+3*y)%5] = rol(A[x][y], keccak_r[x][y]);
        for (int x = 0; x < 5; ++x)
            for (int y = 0; y < 5; ++y)
                A[x][y] = B[x][y] ^ (~B[add5(x,1)][y] & B[add5(x,2)][y]);
        A[0][0] ^= keccak_rc[i];
    }

    for (int x = 0; x < 5; ++x)
        for (int y = 0; y < 5; ++y)
            r[5*y+x] = A[x][y];
}

/* =============================================================================
 * Random number generation
 * ============================================================================= */

static uint64_t random64(void) {
    uint64_t r = 0;
    for (int i = 0; i < 64; i++)
        r = (r << 1) | (rand() & 1);
    return r;
}

static void random_bignum(uint64_t k, uint64_t *a) {
    for (uint64_t i = 0; i < k; ++i)
        a[i] = random64();
}

static uint64_t random64d(int density) {
    uint64_t r = 0;
    for (int i = 0; i < 64; i++)
        r = (r << 1) | ((rand() & 0x3F) < density);
    return r;
}

static void random_bignumd(uint64_t k, uint64_t *a, int density) {
    for (uint64_t i = 0; i < k; ++i)
        a[i] = random64d(density);
}

/* =============================================================================
 * Implementation structure - uses two-arg function pointer
 * ============================================================================= */

typedef struct {
    const char *name;
    const char *short_name;
    void (*permute_func)(void *states, const uint64_t *rc);
    int uses_rc;  // 1 if function uses rc parameter, 0 for org
    int enabled;
} implementation_t;

// Adapter for original implementation (ignores rc)
static void mlk_keccakf1600x4_permute24_org_adapter(void *states, const uint64_t *rc) {
    (void)rc;
    mlk_keccakf1600x4_permute24_org(states);
}

static implementation_t implementations[] = {
    { "mlk_keccakf1600x4_permute24_org (original)", "org",
      mlk_keccakf1600x4_permute24_org_adapter, 0, 1 },
    { "mlk_keccakf1600x4_permute24_rc_table (rc as param)", "rc_table",
      mlk_keccakf1600x4_permute24_rc_table, 1, 1 },
    { "mlk_keccakf1600x4_permute24_no_special_rho", "no_special_rho",
      mlk_keccakf1600x4_permute24_no_special_rho, 1, 1 },
    { "mlk_keccakf1600x4_permute24_no_theta_preps", "no_theta_preps",
      mlk_keccakf1600x4_permute24_no_thepta_preps, 1, 1 },
    { "mlk_keccakf1600x4_permute24_update_load", "update_load",
      mlk_keccakf1600x4_permute24_updae_load, 1, 1 },
    { "mlk_keccakf1600x4_permute24_x2_unrolled (12x2)", "x2_unrolled",
      mlk_keccakf1600x4_permute24_x2_unrolled, 1, 1 },
    { "mlk_keccakf1600x4_permute24_loop (24x1)", "loop",
      mlk_keccakf1600x4_permute24_loop, 1, 1 },
    { "mlk_keccakf1600x4_permute24_x2_unrolled_one_arg", "x2_one_arg",
      mlk_keccakf1600x4_permute24_x2_unrolled_one_arg, 1, 1 },
    { "mlk_keccakf1600x4_permute24_x2_unrolled_one_arg_special_rho", "x2_one_arg_special_rho",
      mlk_keccakf1600x4_permute24_x2_unrolled_one_arg_special_rho, 1, 1 },
    { "mlk_keccakf1600x4_permute24_loop_special_rho (24x1, special rho)", "loop_special_rho",
      mlk_keccakf1600x4_permute24_loop_special_rho, 1, 1 },
    { "mlk_keccakf1600x4_permute24_x2_unrolled_one_arg_special_rho_adds", "x2_adds",
      mlk_keccakf1600x4_permute24_x2_unrolled_one_arg_special_rho_adds, 1, 1 },
    { "sha3_keccak4_f1600 (s2n-bignum assembly)", "s2n_asm",
      sha3_keccak4_f1600, 1, 1 },
    { NULL, NULL, NULL, 0, 0 }
};

/* =============================================================================
 * Correctness testing
 * ============================================================================= */

static int test_implementation(implementation_t *impl) {
    uint64_t a[KECCAK_STATE_SIZE] __attribute__((aligned(32)));
    uint64_t expected[KECCAK_STATE_SIZE] __attribute__((aligned(32)));
    int passed = 0, failed = 0;

    printf("--------------------------------------------------------------------------------\n");
    printf("Testing: %s\n", impl->name);
    printf("--------------------------------------------------------------------------------\n");

    if (!impl->enabled) {
        printf("  SKIPPED\n");
        return 0;
    }

    // Test 1: All zeros
    printf("  Test 1: All-zero input... ");
    memset(a, 0, sizeof(a));
    for (int state = 0; state < 4; ++state) {
        uint64_t temp_in[25] = {0}, temp_out[25];
        reference_keccak_f1600(temp_out, temp_in);
        memcpy(&expected[state * 25], temp_out, 25 * sizeof(uint64_t));
    }
    impl->permute_func(a, keccak_rc);
    if (memcmp(a, expected, sizeof(a)) == 0) {
        printf("PASSED\n"); passed++;
    } else {
        printf("FAILED\n"); failed++;
    }

    // Test 2: All ones
    printf("  Test 2: All-ones input... ");
    memset(a, 0xFF, sizeof(a));
    for (int state = 0; state < 4; ++state) {
        uint64_t temp_in[25], temp_out[25];
        memset(temp_in, 0xFF, sizeof(temp_in));
        reference_keccak_f1600(temp_out, temp_in);
        memcpy(&expected[state * 25], temp_out, 25 * sizeof(uint64_t));
    }
    impl->permute_func(a, keccak_rc);
    if (memcmp(a, expected, sizeof(a)) == 0) {
        printf("PASSED\n"); passed++;
    } else {
        printf("FAILED\n"); failed++;
    }

    // Test 3: Single bit patterns
    printf("  Test 3: Single bit patterns... ");
    int test3_pass = 1;
    for (int bit = 0; bit < 64 && test3_pass; ++bit) {
        memset(a, 0, sizeof(a));
        a[0] = a[25] = a[50] = a[75] = (uint64_t)1 << bit;
        for (int state = 0; state < 4; ++state) {
            uint64_t temp_in[25] = {0}, temp_out[25];
            temp_in[0] = (uint64_t)1 << bit;
            reference_keccak_f1600(temp_out, temp_in);
            memcpy(&expected[state * 25], temp_out, 25 * sizeof(uint64_t));
        }
        impl->permute_func(a, keccak_rc);
        if (memcmp(a, expected, sizeof(a)) != 0) test3_pass = 0;
    }
    if (test3_pass) { printf("PASSED\n"); passed++; }
    else { printf("FAILED\n"); failed++; }

    // Test 4: Different values per state
    printf("  Test 4: Different values per state... ");
    int test4_pass = 1;
    for (int t = 0; t < 10 && test4_pass; ++t) {
        for (int state = 0; state < 4; ++state)
            random_bignum(25, &a[state * 25]);
        memcpy(expected, a, sizeof(a));
        for (int state = 0; state < 4; ++state) {
            uint64_t temp_in[25], temp_out[25];
            memcpy(temp_in, &expected[state * 25], 25 * sizeof(uint64_t));
            reference_keccak_f1600(temp_out, temp_in);
            memcpy(&expected[state * 25], temp_out, 25 * sizeof(uint64_t));
        }
        impl->permute_func(a, keccak_rc);
        if (memcmp(a, expected, sizeof(a)) != 0) test4_pass = 0;
    }
    if (test4_pass) { printf("PASSED\n"); passed++; }
    else { printf("FAILED\n"); failed++; }

    // Test 5: Random tests
    printf("  Test 5: Random tests... ");
    int test5_pass = 1;
    for (int t = 0; t < 100 && test5_pass; ++t) {
        random_bignum(25, a);
        memcpy(a + 25, a, 25 * sizeof(uint64_t));
        memcpy(a + 50, a, 25 * sizeof(uint64_t));
        memcpy(a + 75, a, 25 * sizeof(uint64_t));
        memcpy(expected, a, sizeof(a));
        for (int state = 0; state < 4; ++state) {
            uint64_t temp_in[25], temp_out[25];
            memcpy(temp_in, &expected[state * 25], 25 * sizeof(uint64_t));
            reference_keccak_f1600(temp_out, temp_in);
            memcpy(&expected[state * 25], temp_out, 25 * sizeof(uint64_t));
        }
        impl->permute_func(a, keccak_rc);
        if (memcmp(a, expected, sizeof(a)) != 0) test5_pass = 0;
    }
    if (test5_pass) { printf("PASSED\n"); passed++; }
    else { printf("FAILED\n"); failed++; }

    printf("  Results: %d passed, %d failed\n", passed, failed);
    return failed;
}

static int run_all_correctness_tests(void) {
    int total_failures = 0;
    printf("================================================================================\n");
    printf("CORRECTNESS TESTS\n");
    printf("================================================================================\n");
    srand(12345);
    
    for (implementation_t *impl = implementations; impl->name; ++impl) {
        if (strlen(function_to_test) > 0 &&
            !strstr(impl->name, function_to_test) &&
            strcmp(impl->short_name, function_to_test) != 0)
            continue;
        total_failures += test_implementation(impl);
    }
    
    printf("================================================================================\n");
    printf(total_failures ? "CORRECTNESS TESTS FAILED: %d failure(s)\n" : "ALL CORRECTNESS TESTS PASSED\n", total_failures);
    printf("================================================================================\n");
    return total_failures;
}

/* =============================================================================
 * Benchmarking
 * ============================================================================= */

#define repeat(bod) { inner_reps = default_reps; for (uint64_t _i = 0; _i < inner_reps; ++_i) { bod; } }

// Current implementation being benchmarked
static implementation_t *current_impl;

static void bench_wrapper(void) {
    for (int j = 0; j < KECCAK_STATE_SIZE; ++j)
        keccak_states_bench[j] = b0[j % BUFFERSIZE];
    repeat(current_impl->permute_func(keccak_states_bench, keccak_rc));
}

static void timingtest(int enabled, const char *name, void (*f)(void)) {
    if (!enabled) {
        printf("%-55s:             *** NOT APPLICABLE  ***\n", name);
        return;
    }

    const char *spaceptr = strchr(name, ' ');
    int compline = spaceptr ? (int)(spaceptr - name) : (int)strlen(name);
    int wantline = strlen(function_to_test);
    int testline = wantline == 0 ? 0 : (function_to_test[wantline-1] == '_' ? wantline-1 : (wantline < compline ? compline : wantline));
    if (strncmp(name, function_to_test, testline)) return;

    double timing[CORE_REPS];
    clock_t start_time, finish_time;

    (*f)();  // Warmup

    for (uint64_t i = 0; i < CORE_REPS; ++i) {
        random_bignumd(BUFFERSIZE, b0, i % 65);
        start_time = clock();
        (*f)();
        finish_time = clock();
        timing[i] = (1e9 * (double)(finish_time - start_time)) / ((double)inner_reps * (double)CLOCKS_PER_SEC);
    }

    double mean = 0.0, variance = 0.0, covariance = 0.0, dvariance = 0.0;
    for (uint64_t i = 0; i < CORE_REPS; ++i) mean += timing[i];
    mean /= CORE_REPF;
    for (uint64_t i = 0; i < CORE_REPS; ++i) {
        double tt = timing[i] - mean, dd = (double)(i % 65) - 32.5;
        variance += tt * tt; dvariance += dd * dd; covariance += tt * dd;
    }
    variance /= CORE_REPF; covariance /= CORE_REPF; dvariance /= CORE_REPF;

    double stddev = sqrt(variance), dstddev = sqrt(dvariance);
    printf("%-55s: %7.1f ns each (var %4.1f%%, corr %5.2f) = %10.0f ops/sec\n",
           name, mean, 100.0 * stddev / mean, covariance / (stddev * dstddev), 1e9 / mean);

    arithmean += mean;
    geomean += log(mean);
    ++benchmark_tests;
}

static void run_all_benchmarks(void) {
    printf("\n================================================================================\n");
    printf("PERFORMANCE BENCHMARKING\n");
    printf("================================================================================\n");
    printf("Repetitions per function = %d * 65 * %"PRIu64" = %"PRIu64"\n",
           OUTER_REPS, default_reps, OUTER_REPS * 65 * default_reps);
    printf("================================================================================\n\n");

    arithmean = geomean = 0.0;
    benchmark_tests = 0;

    printf("Warming up...\n");
    for (implementation_t *impl = implementations; impl->name; ++impl)
        if (impl->enabled)
            for (int i = 0; i < 100; ++i)
                impl->permute_func(keccak_states_bench, keccak_rc);
    printf("\n");

    for (implementation_t *impl = implementations; impl->name; ++impl) {
        if (!impl->enabled) continue;
        if (strlen(function_to_test) > 0 &&
            !strstr(impl->name, function_to_test) &&
            strcmp(impl->short_name, function_to_test) != 0)
            continue;
        current_impl = impl;
        timingtest(impl->enabled, impl->name, bench_wrapper);
    }

    if (benchmark_tests > 0) {
        arithmean /= (double)benchmark_tests;
        geomean = exp(geomean / (double)benchmark_tests);
        printf("\n================================================================================\n");
        printf("ARITHMEAN (%3d tests): %6.1f ns | GEOMEAN: %6.1f ns\n", benchmark_tests, arithmean, geomean);
        printf("================================================================================\n");
    }
}

/* =============================================================================
 * Main
 * ============================================================================= */

static void print_usage(const char *prog) {
    printf("Usage: %s [-reps] [impl_name]\n\nImplementations:\n", prog);
    for (implementation_t *impl = implementations; impl->name; ++impl)
        printf("  %-25s %s\n", impl->short_name, impl->name);
}

int main(int argc, char *argv[]) {
    function_to_test = "";
    default_reps = INNER_REPS;

    if (argc >= 2) {
        if (strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "--help") == 0) {
            print_usage(argv[0]);
            return 0;
        }
        char *end;
        long n = strtol(argv[1], &end, 10);
        if (end == argv[1]) {
            if (argc >= 3 || argv[1][0] == '-') { print_usage(argv[0]); return -1; }
            function_to_test = argv[1];
        } else {
            default_reps = n < 0 ? -n : n;
            if (argc >= 3) function_to_test = argv[2];
        }
    }

    printf("================================================================================\n");
    printf("Keccak-f1600x4 Implementation Test & Benchmark Suite\n");
    printf("================================================================================\n\n");

    int failures = run_all_correctness_tests();
    if (failures) {
        printf("\n*** CORRECTNESS TESTS FAILED ***\n");
        return 1;
    }

    printf("\nAll correctness tests PASSED! Running benchmarks...\n");
    run_all_benchmarks();
    printf("\nDone.\n");
    return 0;
}
