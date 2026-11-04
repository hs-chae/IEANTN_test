#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <float.h>
#include <fenv.h>
#include <inttypes.h>
double ramanujan_epsilon_bound(void);
int main(void) {
 if (FLT_RADIX!=2 || DBL_MANT_DIG!=53 || sizeof(double)!=8 || sizeof(unsigned)!=4 || fegetround()!=FE_TONEAREST) return 9;
 double value=ramanujan_epsilon_bound(); uint64_t bits=0;memcpy(&bits,&value,8);
 printf("%.17g %016" PRIx64 "\n",value,bits);return 0;
}
