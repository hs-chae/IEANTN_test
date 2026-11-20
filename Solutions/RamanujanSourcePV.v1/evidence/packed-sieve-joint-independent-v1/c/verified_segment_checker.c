/*
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
*/
#include <stdint.h>

uint64_t rpc_check_segment(uint64_t lo,uint64_t hi,uint64_t capacity,uint64_t* claims,uint64_t* flags){if((lo<2))return 0;else ;
if((hi<lo))return 0;else ;
if((hi>2000000000000))return 0;else ;
uint64_t length=((hi-lo)+1);
if((capacity<length))return 0;else ;
for(uint64_t i=0;(i<length);(++i))((flags[i])=1);
for(uint64_t d=2;(d<=(hi/d));(++d)){uint64_t first=((lo/d)*d);
if((first<lo))(first=(first+d));else ;
if((first<(d*d)))(first=(d*d));else ;
for(uint64_t m=first;(m<=hi);(m=(m+d)))((flags[(m-lo)])=0);}
uint64_t count=0;
for(uint64_t i=0;(i<length);(++i)){if(((claims[i])==(flags[i])));else return 0;
(count=(count+(flags[i])));}
return (count+1);}
