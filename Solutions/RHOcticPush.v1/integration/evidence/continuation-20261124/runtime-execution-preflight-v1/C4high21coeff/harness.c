#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
uint64_t rpc_log_upper(uint64_t);
uint64_t rh_coeff(uint64_t);
int main(void){
uint64_t ns[]={610000000000ULL,619000000000ULL,620000000000ULL,640000000000ULL};
for(unsigned i=0;i<4;i++)printf("L %"PRIu64" %"PRIu64"\n",ns[i],rpc_log_upper(ns[i]));
for(uint64_t j=0;j<=20;j++)printf("C %"PRIu64" %"PRIu64"\n",j,rh_coeff(j));
return 0;}
