#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
uint64_t rpc_quotient_count(uint64_t,uint64_t,uint64_t*,uint64_t*);
static uint64_t small[1500000],large[1500000];
int main(void){uint64_t n=rpc_quotient_count(UINT64_C(1490000000000),1500000,small,large);if(printf("%" PRIu64 "\n",n)<0)return 1;return fflush(stdout)!=0;}
