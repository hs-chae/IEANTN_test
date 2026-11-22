#include <stdint.h>

uint64_t rh_coeff(uint64_t n){uint64_t lhs=1;
uint64_t f=1;
for(uint64_t j=1;(j<=n);(++j)){(lhs=((j*lhs)+1));
(f=(f*j));}
uint64_t rhs=f;
uint64_t a=1;
uint64_t b=f;
for(uint64_t i=1;(i<=n);(++i)){(a=(a*i));
(b=(b/((n+1)-i)));
(rhs=(rhs+(a*b)));}
return (lhs-rhs);}
