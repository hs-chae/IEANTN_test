#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <fenv.h>
#include <float.h>
extern double fks2_table4_transport(void);
int main(void) {
 if(sizeof(double)!=8||FLT_RADIX!=2||DBL_MANT_DIG!=53||DBL_MAX_EXP!=1024)return 2;
 if(fesetround(FE_TONEAREST)||fegetround()!=FE_TONEAREST)return 3;
 double q=fks2_table4_transport(); uint64_t bits;memcpy(&bits,&q,8);
 printf("%.17g %a %016llx\n",q,q,(unsigned long long)bits);return 0;
}
