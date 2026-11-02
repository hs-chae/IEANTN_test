#include <float.h>
#include <fenv.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <xmmintrin.h>

_Static_assert(sizeof(double) == 8 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024,
               "selected profile requires IEEE binary64 double");
_Static_assert(FLT_EVAL_METHOD == 0, "excess precision excluded");
extern double fks2_value(void);
int main(void) {
    unsigned csr = _mm_getcsr();
    if (fegetround() != FE_TONEAREST || (csr & 0xe040u) != 0) return 2;
    double value = fks2_value();
    uint64_t bits;
    memcpy(&bits, &value, sizeof bits);
    printf("bits=0x%016" PRIx64 "\nvalue=%.17g\nhex=%a\nmxcsr=0x%x\n",
           bits, value, value, csr);
    return 0;
}
