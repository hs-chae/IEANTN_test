/*
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
*/
#include <stdint.h>

uint64_t rpc_e_low(){uint64_t term=1152921504606846976;
uint64_t total=1152921504606846976;
for(uint64_t k=1;(k<=20);(++k)){(term=(term/k));
(total=(total+term));}
return total;}

uint64_t rpc_e_high(){return (rpc_e_low()+22);}
