#include <stdio.h>
#include <inttypes.h>
#include "source/rh_coeff.c"
int main(void){for(uint64_t j=0;j<=20;j++)printf("%" PRIu64 " %" PRIu64 "\n",j,rh_coeff(j));return 0;}
