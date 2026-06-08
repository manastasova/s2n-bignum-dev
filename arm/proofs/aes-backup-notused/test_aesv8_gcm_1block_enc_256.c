// Test: compare aesv8_gcm_1block_enc_256 against aws-lc EVP AES-256-GCM
//
// Build:
//   gcc -O2 -o test_one_block_preloop_tail \
//     test_one_block_preloop_tail.c \
//     aesv8_gcm_1block_enc_256.S \
//     -I/home/ubuntu/auto_proofs/aws-lc/include \
//     -L/home/ubuntu/aws-lc-all/aws-lc/build/crypto \
//     -lcrypto -lpthread -ldl
//
// Run:
//   LD_LIBRARY_PATH=/home/ubuntu/aws-lc-all/aws-lc/build/crypto ./test_one_block_preloop_tail

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include <openssl/evp.h>
#include <openssl/aes.h>

// Our assembly function
extern size_t aesv8_gcm_1block_enc_256(
    const uint8_t *in, size_t bit_len, uint8_t *out,
    uint8_t *Xi, uint8_t ivec[16], const void *key,
    const void *Htable);

// aws-lc internal functions we need to set up the same state
extern void aes_hw_set_encrypt_key(const uint8_t *key, int bits, AES_KEY *aeskey);
extern void aes_hw_encrypt(const uint8_t *in, uint8_t *out, const AES_KEY *key);

// u128 type matching aws-lc's internal.h
typedef struct { uint64_t hi, lo; } u128;

// GHASH init to populate Htable (same as aws-lc uses on aarch64 with PMULL)
extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);

static void print_hex(const char *label, const uint8_t *data, size_t len) {
    printf("%s: ", label);
    for (size_t i = 0; i < len; i++)
        printf("%02x", data[i]);
    printf("\n");
}

// Encrypt a 32-bit big-endian counter at offset 12 of ivec
static void increment_ctr32(uint8_t ivec[16]) {
    uint32_t ctr = ((uint32_t)ivec[12] << 24) | ((uint32_t)ivec[13] << 16) |
                   ((uint32_t)ivec[14] << 8) | (uint32_t)ivec[15];
    ctr++;
    ivec[12] = (ctr >> 24) & 0xff;
    ivec[13] = (ctr >> 16) & 0xff;
    ivec[14] = (ctr >> 8) & 0xff;
    ivec[15] = ctr & 0xff;
}

static int run_test(const char *name,
                    const uint8_t key_bytes[32],
                    const uint8_t nonce[12],
                    const uint8_t plaintext[16]) {
    int ok = 1;

    printf("=== %s ===\n", name);
    print_hex("Key      ", key_bytes, 32);
    print_hex("Nonce    ", nonce, 12);
    print_hex("Plaintext", plaintext, 16);

    // -----------------------------------------------------------------
    // 1) Reference: aws-lc EVP AES-256-GCM
    // -----------------------------------------------------------------
    uint8_t ref_ct[16] = {0};
    uint8_t ref_tag[16] = {0};
    {
        EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
        int outlen = 0;

        EVP_EncryptInit_ex(ctx, EVP_aes_256_gcm(), NULL, NULL, NULL);
        EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, 12, NULL);
        EVP_EncryptInit_ex(ctx, NULL, NULL, key_bytes, nonce);
        // No AAD
        EVP_EncryptUpdate(ctx, ref_ct, &outlen, plaintext, 16);
        EVP_EncryptFinal_ex(ctx, ref_ct + outlen, &outlen);
        EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, 16, ref_tag);

        EVP_CIPHER_CTX_free(ctx);
    }

    print_hex("Ref CT   ", ref_ct, 16);
    print_hex("Ref TAG  ", ref_tag, 16);

    // -----------------------------------------------------------------
    // 2) Our assembly: aesv8_gcm_1block_enc_256
    //    We need to set up the same state as aws-lc's GCM context:
    //    - Expanded AES key
    //    - Htable (precomputed GHASH powers)
    //    - Counter (nonce || 0x00000002) — ctr 1 was used for EK0
    //    - Xi = 0 (no AAD, no prior blocks)
    // -----------------------------------------------------------------
    uint8_t asm_ct[16] = {0};
    uint8_t asm_Xi[16] = {0};    // GHASH accumulator, starts at 0
    uint8_t asm_ivec[16] = {0};  // counter block

    // Set up expanded AES key
    AES_KEY aes_key;
    aes_hw_set_encrypt_key(key_bytes, 256, &aes_key);

    // Compute H = AES(K, 0^128)
    uint8_t H[16] = {0};
    aes_hw_encrypt(H, H, &aes_key);

    // gcm_init_v8 expects H as byte-swapped uint64_t pair (big-endian load),
    // matching CRYPTO_ghash_init's CRYPTO_load_u64_be calls
    uint64_t H_be[2];
    for (int i = 0; i < 8; i++) {
        ((uint8_t *)&H_be[0])[7-i] = H[i];
        ((uint8_t *)&H_be[1])[7-i] = H[8+i];
    }

    // Initialize Htable using gcm_init_v8
    u128 Htable[16] __attribute__((aligned(16))) = {{0}};
    gcm_init_v8(Htable, H_be);

    // Set up counter: nonce || 0x00000002
    // (ctr=1 → EK0 for tag, ctr=2 → first data block)
    memcpy(asm_ivec, nonce, 12);
    asm_ivec[12] = 0x00;
    asm_ivec[13] = 0x00;
    asm_ivec[14] = 0x00;
    asm_ivec[15] = 0x02;

    // Call our assembly function
    size_t ret = aesv8_gcm_1block_enc_256(
        plaintext, 128, asm_ct, asm_Xi, asm_ivec, &aes_key, Htable);

    print_hex("Asm CT   ", asm_ct, 16);
    print_hex("Asm Xi   ", asm_Xi, 16);
    printf("Asm ret  : %zu\n", ret);

    // -----------------------------------------------------------------
    // 3) Compare ciphertext
    // -----------------------------------------------------------------
    if (memcmp(ref_ct, asm_ct, 16) != 0) {
        printf("FAIL: ciphertext mismatch!\n");
        ok = 0;
    } else {
        printf("PASS: ciphertext matches\n");
    }

    // -----------------------------------------------------------------
    // 4) Compute the full GCM tag from Xi
    //    The assembly outputs a "partial tag" = GHASH(CT).
    //    Full GCM tag requires:
    //      Xi' = GHASH(Xi || len_block) = (Xi XOR len_block) * H
    //      Tag = Xi' XOR EK0
    //    where len_block = [aad_bits(64) || msg_bits(64)]
    //                    = [0 || 128]
    //    and EK0 = AES(K, nonce||0x00000001)
    // -----------------------------------------------------------------

    // Compute EK0 = AES(K, nonce||0x00000001)
    uint8_t ek0_block[16] = {0};
    memcpy(ek0_block, nonce, 12);
    ek0_block[12] = 0x00;
    ek0_block[13] = 0x00;
    ek0_block[14] = 0x00;
    ek0_block[15] = 0x01;
    uint8_t EK0[16];
    aes_hw_encrypt(ek0_block, EK0, &aes_key);

    // The partial tag from assembly is GHASH over just the CT block.
    // We still need to GHASH the length block and XOR with EK0.
    // Use gcm_gmult_v8 to do: Xi = (Xi XOR lenblock) * H
    extern void gcm_gmult_v8(uint8_t Xi[16], const u128 Htable[16]);

    // Build length block: [0 (aad_bits, 64-bit BE) || 128 (msg_bits, 64-bit BE)]
    uint8_t len_block[16] = {0};
    // msg_bits = 128 = 0x80, in big-endian 64-bit at offset 8
    len_block[15] = 0x80;

    // XOR len_block into Xi
    uint8_t final_Xi[16];
    memcpy(final_Xi, asm_Xi, 16);
    for (int i = 0; i < 16; i++)
        final_Xi[i] ^= len_block[i];

    // GHASH multiply: final_Xi = final_Xi * H
    gcm_gmult_v8(final_Xi, Htable);

    // Tag = final_Xi XOR EK0
    uint8_t asm_tag[16];
    for (int i = 0; i < 16; i++)
        asm_tag[i] = final_Xi[i] ^ EK0[i];

    print_hex("Asm TAG  ", asm_tag, 16);

    if (memcmp(ref_tag, asm_tag, 16) != 0) {
        printf("FAIL: tag mismatch!\n");
        ok = 0;
    } else {
        printf("PASS: tag matches\n");
    }

    printf("\n");
    return ok;
}

int main(void) {
    int all_ok = 1;

    // Test 1: NIST-like test vector (all-zero key)
    {
        uint8_t key[32] = {0};
        uint8_t nonce[12] = {0};
        uint8_t pt[16] = {0};
        all_ok &= run_test("Test 1: all zeros", key, nonce, pt);
    }

    // Test 2: NIST GCM test case-like
    {
        uint8_t key[32] = {
            0xfe,0xff,0xe9,0x92,0x86,0x65,0x73,0x1c,
            0x6d,0x6a,0x8f,0x94,0x67,0x30,0x83,0x08,
            0xfe,0xff,0xe9,0x92,0x86,0x65,0x73,0x1c,
            0x6d,0x6a,0x8f,0x94,0x67,0x30,0x83,0x08
        };
        uint8_t nonce[12] = {
            0xca,0xfe,0xba,0xbe,0xfa,0xce,0xdb,0xad,
            0xde,0xca,0xf8,0x88
        };
        uint8_t pt[16] = {
            0xd9,0x31,0x32,0x25,0xf8,0x84,0x06,0xe5,
            0xa5,0x59,0x09,0xc5,0xaf,0xf5,0x26,0x9a
        };
        all_ok &= run_test("Test 2: NIST-like", key, nonce, pt);
    }

    // Test 3: random-looking values
    {
        uint8_t key[32] = {
            0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef,
            0xfe,0xdc,0xba,0x98,0x76,0x54,0x32,0x10,
            0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,
            0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff,0x00
        };
        uint8_t nonce[12] = {
            0xaa,0xbb,0xcc,0xdd,0xee,0xff,0x00,0x11,
            0x22,0x33,0x44,0x55
        };
        uint8_t pt[16] = {
            0x48,0x65,0x6c,0x6c,0x6f,0x2c,0x20,0x57,
            0x6f,0x72,0x6c,0x64,0x21,0x00,0x00,0x00
        };
        all_ok &= run_test("Test 3: Hello, World!", key, nonce, pt);
    }

    // Test 4: all 0xFF
    {
        uint8_t key[32];
        memset(key, 0xff, 32);
        uint8_t nonce[12];
        memset(nonce, 0xff, 12);
        uint8_t pt[16];
        memset(pt, 0xff, 16);
        all_ok &= run_test("Test 4: all 0xFF", key, nonce, pt);
    }

    if (all_ok) {
        printf("ALL TESTS PASSED\n");
        return 0;
    } else {
        printf("SOME TESTS FAILED\n");
        return 1;
    }
}
