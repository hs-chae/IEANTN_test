static I divN(I a,unsigned int n){if((n==0))fail();else ;
I r={((a.lo)/n),ceilDiv((a.hi),n)};
return r;}
