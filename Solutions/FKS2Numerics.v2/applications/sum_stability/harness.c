#include <float.h>
#include <fenv.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

_Static_assert(sizeof(double) == 8 && FLT_RADIX == 2 && DBL_MANT_DIG == 53 &&
               DBL_MIN_EXP == -1021 && DBL_MAX_EXP == 1024, "binary64 required");
_Static_assert(sizeof(unsigned) == 4, "32-bit unsigned required");
extern double sum(const double *, unsigned);

int main(void) {
    unsigned n;
    if (fegetround() != FE_TONEAREST) return 2;
    while (scanf("%u", &n) == 1) {
        if (n < 1 || n > 64) return 3;
        double a[64];
        for (unsigned i = 0; i < n; ++i) {
            uint64_t bits;
            if (scanf("%" SCNx64, &bits) != 1) return 4;
            memcpy(&a[i], &bits, sizeof bits);
            if (!(a[i] >= 0x1p-40 && a[i] <= 1.0)) return 5;
        }
        double out = sum(a, n);
        uint64_t bits;
        memcpy(&bits, &out, sizeof bits);
        printf("%016" PRIx64 "\n", bits);
    }
    return ferror(stdin) ? 6 : 0;
}
