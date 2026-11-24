/*
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
*/
#include <stdint.h>
#include <stdio.h>

extern uint64_t rpc_quotient_count(uint64_t n,uint64_t capacity,uint64_t* small,uint64_t* large);
static uint64_t rpc_small[1500000];
static uint64_t rpc_large[1500000];

int main(){uint64_t result=rpc_quotient_count(1490000000000,1500000,rpc_small,rpc_large);
if((fwrite((&result),8,1,stdout)!=1))return 1;else ;
if((fflush(stdout)!=0))return 1;else ;
return 0;}
