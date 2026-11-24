/*
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
*/
#include <stdint.h>

uint64_t rpc_log_ceildiv(__uint128_t a,__uint128_t b){if((b==0))return ((uint64_t)0);else ;
return ((uint64_t)((a/b)+((a%b)!=0)));}

uint64_t rpc_log_series_upper(uint64_t num,uint64_t den){uint64_t F=1152921504606846976;
uint64_t z=rpc_log_ceildiv((((__uint128_t)F)*num),den);
uint64_t z2=rpc_log_ceildiv((((__uint128_t)z)*z),F);
uint64_t power=z;
__uint128_t sum=0;
for(uint64_t k=0;(k<20);(++k)){(sum=(sum+rpc_log_ceildiv(power,((2*k)+1))));
(power=rpc_log_ceildiv((((__uint128_t)power)*z2),F));}
return ((uint64_t)((2*sum)+rpc_log_ceildiv(((((__uint128_t)2)*power)*F),(((__uint128_t)41)*(F-z2)))));}

uint64_t rpc_log_upper(uint64_t n){if((n<2))return ((uint64_t)0);else ;
uint64_t two=1;
uint64_t k=0;
while((two<=(n/2))){(two=(two*2));
(++k);}
uint64_t log2=rpc_log_series_upper(1,3);
return rpc_log_ceildiv(((((__uint128_t)k)*log2)+rpc_log_series_upper((n-two),(n+two))),1048576);}
