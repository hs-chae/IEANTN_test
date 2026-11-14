static RI expPoint(Q q){S ceil=ceilQ(qabs(q));
N m=na((ceil.mag),nu(1));
unsigned int k=small(keep(lean_nat_log2(m)));
if((k>=32))fail();else ;
unsigned int power=(1u<<k);
Q reduced=qv(q,qi(power));
RI input=point(reduced);
return rpow(radd(taylor(expCoeffs,input),expRemainder(input)),power);}
