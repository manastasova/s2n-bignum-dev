// Test: compare aes256_gcm_seven_block against aws-lc EVP AES-256-GCM
//
// Build:
//   gcc -O2 -o test_seven_blocks_preloop_tail \
//     test_seven_blocks_preloop_tail.c \
//     aes256_gcm_seven_block.S \
//     -I/home/ubuntu/auto_proofs/aws-lc/include \
//     -L/home/ubuntu/aws-lc-all/aws-lc/build/crypto \
//     -lcrypto -lpthread -ldl
//
// Run:
//   LD_LIBRARY_PATH=/home/ubuntu/aws-lc-all/aws-lc/build/crypto ./test_seven_blocks_preloop_tail

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include <openssl/evp.h>
#include <openssl/aes.h>

#define NBLK 7
#define NBYTES (NBLK*16)

// Our assembly function
extern size_t aes256_gcm_seven_block(
    const uint8_t *in, size_t bit_len, uint8_t *out,
    uint8_t *Xi, uint8_t ivec[16], const void *key,
    const void *Htable);

extern void aes_hw_set_encrypt_key(const uint8_t *key, int bits, AES_KEY *aeskey);
extern void aes_hw_encrypt(const uint8_t *in, uint8_t *out, const AES_KEY *key);

typedef struct { uint64_t hi, lo; } u128;

extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);
extern void gcm_gmult_v8(uint8_t Xi[16], const u128 Htable[16]);

static void print_hex(const char *label, const uint8_t *data, size_t len) {
    printf("%s: ", label);
    for (size_t i = 0; i < len; i++)
        printf("%02x", data[i]);
    printf("\n");
}

static int run_test(const char *name,
                    const uint8_t key_bytes[32],
                    const uint8_t nonce[12],
                    const uint8_t plaintext[NBYTES]) {
    int ok = 1;

    printf("=== %s ===\n", name);
    print_hex("Key      ", key_bytes, 32);
    print_hex("Nonce    ", nonce, 12);
    print_hex("Plaintext", plaintext, NBYTES);

    // ----------------------------------------------------------------
    // 1) Reference: aws-lc EVP AES-256-GCM
    // ----------------------------------------------------------------
    uint8_t ref_ct[NBYTES] = {0};
    uint8_t ref_tag[16] = {0};
    {
        EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
        int outlen = 0;
        EVP_EncryptInit_ex(ctx, EVP_aes_256_gcm(), NULL, NULL, NULL);
        EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, 12, NULL);
        EVP_EncryptInit_ex(ctx, NULL, NULL, key_bytes, nonce);
        EVP_EncryptUpdate(ctx, ref_ct, &outlen, plaintext, NBYTES);
        EVP_EncryptFinal_ex(ctx, ref_ct + outlen, &outlen);
        EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, 16, ref_tag);
        EVP_CIPHER_CTX_free(ctx);
    }

    print_hex("Ref CT   ", ref_ct, NBYTES);
    print_hex("Ref TAG  ", ref_tag, 16);

    // ----------------------------------------------------------------
    // 2) Our assembly: aes256_gcm_seven_block
    // ----------------------------------------------------------------
    uint8_t asm_ct[NBYTES] = {0};
    uint8_t asm_Xi[16] = {0};
    uint8_t asm_ivec[16] = {0};

    AES_KEY aes_key;
    aes_hw_set_encrypt_key(key_bytes, 256, &aes_key);

    uint8_t H[16] = {0};
    aes_hw_encrypt(H, H, &aes_key);

    uint64_t H_be[2];
    for (int i = 0; i < 8; i++) {
        ((uint8_t *)&H_be[0])[7-i] = H[i];
        ((uint8_t *)&H_be[1])[7-i] = H[8+i];
    }

    u128 Htable[16] __attribute__((aligned(16))) = {{0}};
    gcm_init_v8(Htable, H_be);

    // Counter: nonce || 0x00000002 (ctr=1 reserved for EK0)
    memcpy(asm_ivec, nonce, 12);
    asm_ivec[12] = 0x00;
    asm_ivec[13] = 0x00;
    asm_ivec[14] = 0x00;
    asm_ivec[15] = 0x02;

    size_t ret = aes256_gcm_seven_block(
        plaintext, NBYTES*8, asm_ct, asm_Xi, asm_ivec, &aes_key, Htable);

    print_hex("Asm CT   ", asm_ct, NBYTES);
    print_hex("Asm Xi   ", asm_Xi, 16);
    printf("Asm ret  : %zu\n", ret);

    if (memcmp(ref_ct, asm_ct, NBYTES) != 0) {
        printf("FAIL: ciphertext mismatch!\n");
        ok = 0;
    } else {
        printf("PASS: ciphertext matches\n");
    }

    // ----------------------------------------------------------------
    // 3) Full GCM tag from Xi (partial tag = GHASH(CT blocks))
    //    Tag = ((Xi XOR lenblock) * H) XOR EK0
    //    lenblock = [aad_bits(64 BE) || msg_bits(64 BE)] = [0 || NBYTES*8]
    // ----------------------------------------------------------------
    uint8_t ek0_block[16] = {0};
    memcpy(ek0_block, nonce, 12);
    ek0_block[15] = 0x01;
    uint8_t EK0[16];
    aes_hw_encrypt(ek0_block, EK0, &aes_key);

    uint8_t len_block[16] = {0};
    uint64_t msg_bits = (uint64_t)NBYTES * 8;  // 768
    for (int i = 0; i < 8; i++)
        len_block[15-i] = (msg_bits >> (8*i)) & 0xff;

    uint8_t final_Xi[16];
    memcpy(final_Xi, asm_Xi, 16);
    for (int i = 0; i < 16; i++)
        final_Xi[i] ^= len_block[i];

    gcm_gmult_v8(final_Xi, Htable);

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

    {
        uint8_t key[32] = {0};
        uint8_t nonce[12] = {0};
        uint8_t pt[NBYTES] = {0};
        all_ok &= run_test("Test 1: all zeros", key, nonce, pt);
    }

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
        uint8_t pt[NBYTES];
        for (int i = 0; i < NBYTES; i++) pt[i] = (uint8_t)(0xd9 + i*7);
        all_ok &= run_test("Test 2: NIST-like (7 blocks)", key, nonce, pt);
    }

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
        uint8_t pt[NBYTES];
        const char *msg = "Hello, World! This is a seven-block AES-GCM test vector.....!!!";
        memset(pt, 0, NBYTES);
        memcpy(pt, msg, strlen(msg) < NBYTES ? strlen(msg) : NBYTES);
        all_ok &= run_test("Test 3: text (7 blocks)", key, nonce, pt);
    }

    {
        uint8_t key[32];
        memset(key, 0xff, 32);
        uint8_t nonce[12];
        memset(nonce, 0xff, 12);
        uint8_t pt[NBYTES];
        memset(pt, 0xff, NBYTES);
        all_ok &= run_test("Test 4: all 0xFF (7 blocks)", key, nonce, pt);
    }

    if (all_ok) {
        printf("ALL TESTS PASSED\n");
        return 0;
    } else {
        printf("SOME TESTS FAILED\n");
        return 1;
    }
}
