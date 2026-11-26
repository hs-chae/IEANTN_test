/* Runtime exercise of the actual unchanged source; universal Lean proofs are
   separate and do not depend on these finite test cases. */
#include <stdint.h>
#include <stdio.h>
#define main rh080_original_main
#include "w4_fft_recursive.c"
#undef main
static uint64_t seed = UINT64_C(0x58234dd618c34a19);
static uint64_t before[1024], actual[1024], cases = 0;
static uint64_t draw(void) {
    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; return seed;
}
static int one(uint64_t start, uint64_t n) {
    uint64_t j;
    for (j=0; j<1024; ++j) before[j]=actual[j]=draw();
    if (start<1024) before[start]=actual[start]=UINT64_MAX;
    if (start+1<1024) before[start+1]=actual[start+1]=UINT64_C(1)<<63;
    if (zero_words(actual+start,n)!=0) return 1;
    for (j=0; j<1024; ++j) {
        uint64_t expected=(start<=j && j<start+n) ? 0 : before[j];
        if (actual[j]!=expected) return 2;
    }
    ++cases; return 0;
}
int main(void) {
    uint64_t n;
    for (n=0; n<=80; ++n) {
        if (one(0,n)||one(7,n)||one(36,n)||one(128,n)) return 1;
    }
    if (one(512,512)||one(1024,0)) return 1;
    printf("PASS actual zero_words slices: %llu cases; seed=58234dd618c34a19; final_seed=%016llx\n",
      (unsigned long long)cases,(unsigned long long)seed);
    return 0;
}
