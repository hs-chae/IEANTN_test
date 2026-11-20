/*
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
*/
#include <stdint.h>
#include "verified_finite_exp.c"
#include "verified_finite_log.c"

int rpc_finite_cell(uint64_t n,uint64_t next,uint64_t j,uint64_t P,uint64_t Q,uint64_t Lu,uint64_t A){if((n<38358837683))return 0;else ;
if((next<=n))return 0;else ;
if((next>2000000000001))return 0;else ;
if((j>n))return 0;else ;
if((Q>j))return 0;else ;
if((P>(next-1)))return 0;else ;
if((Lu==0))return 0;else ;
if((Lu!=rpc_log_upper(n)))return 0;else ;
uint64_t lo=rpc_e_low();
uint64_t hi=rpc_e_high();
if(((((__uint128_t)j)*hi)>(((__uint128_t)n)*1152921504606846976)))return 0;else ;
if((((__uint128_t)A)!=((((__uint128_t)n)*lo)/Lu)))return 0;else ;
return (((((__uint128_t)1048576)*P)*P)<(((__uint128_t)A)*Q));}
