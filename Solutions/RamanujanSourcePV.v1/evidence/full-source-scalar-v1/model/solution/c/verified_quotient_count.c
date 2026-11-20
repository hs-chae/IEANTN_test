/*
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
*/
#include <stdint.h>

uint64_t rpc_isqrt(uint64_t n){uint64_t r=0;
while(((r+1)<=(n/(r+1)))){(++r);}
return r;}

uint64_t rpc_quotient_count(uint64_t n,uint64_t capacity,uint64_t* small,uint64_t* large){if((n<2))return 0;else ;
if((n>2000000000000))return 0;else ;
uint64_t r=rpc_isqrt(n);
if((capacity<=r))return 0;else ;
for(uint64_t i=1;(i<=r);(++i)){((small[i])=(i-1));
((large[i])=((n/i)-1));}
for(uint64_t p=2;(p<=r);(++p))if(((small[p])==(small[(p-1)])));else {uint64_t before=(small[(p-1)]);
uint64_t stop=r;
if(((n/(p*p))<r))(stop=(n/(p*p)));else ;
for(uint64_t i=1;(i<=stop);(++i)){uint64_t ip=(i*p);
uint64_t sub=0;
if((ip<=r))(sub=(large[ip]));else (sub=(small[(n/ip)]));
if((sub<before))return 0;else ;
if(((large[i])<(sub-before)))return 0;else ;
((large[i])=((large[i])-(sub-before)));}
uint64_t square=(p*p);
if((square<=r)){uint64_t v=r;
while((square<=v)){uint64_t sub=(small[(v/p)]);
if((sub<before))return 0;else ;
if(((small[v])<(sub-before)))return 0;else ;
((small[v])=((small[v])-(sub-before)));
(--v);}}else ;}
return (large[1]);}
