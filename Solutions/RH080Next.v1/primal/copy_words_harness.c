/* Exercise the actual, unchanged recursive numerical source helper. This is
   runtime evidence; the universal correctness proof is in Lean. */
#include <stdint.h>
#include <stdio.h>
#define main rh080_original_main
#include "w4_fft_recursive.c"
#undef main

static uint64_t seed = UINT64_C(0x4f1bbcdc7135a9e7);
static uint64_t draw(void) {
    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
    return seed;
}
static uint64_t before[1024], actual[1024], other[1024];
static uint64_t cases = 0;
static int one(uint64_t out, uint64_t in, uint64_t n, int separate) {
    uint64_t j;
    for (j = 0; j < 1024; ++j) before[j] = actual[j] = draw();
    before[0] = actual[0] = UINT64_MAX;
    before[1] = actual[1] = UINT64_C(1) << 63;
    for (j = 0; j < 1024; ++j) other[j] = before[j];
    if (copy_words(actual + out, (separate ? other : actual) + in, n) != 0) return 1;
    for (j = 0; j < 1024; ++j) {
        uint64_t expected = (out <= j && j < out + n) ? before[in + j - out] : before[j];
        if (actual[j] != expected || other[j] != before[j]) return 2;
    }
    ++cases;
    return 0;
}
int main(void) {
    uint64_t n;
    for (n = 0; n <= 257; ++n) {
        if (one(3, 0, n, 1) || one(512, 0, n, 0) ||
            one(3, 512, n, 0) || one(17, 17, n, 0)) return 1;
    }
    printf("PASS actual copy_words: %llu cases; seed=4f1bbcdc7135a9e7; final_seed=%016llx\n",
        (unsigned long long) cases, (unsigned long long) seed);
    return 0;
}
