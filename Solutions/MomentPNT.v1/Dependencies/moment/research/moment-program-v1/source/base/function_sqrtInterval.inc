static I sqrtInterval(I x){if((((x.lo)>(x.hi))||((x.hi)>(16*S))))fail();else ;
U n[2]={mulU((x.lo),S),mulU((x.hi),S)};
U result[2];
unsigned int i=0;
while((i<2)){U lo=0;
U hi=(4*S);
while((lo<hi)){U mid=((lo+((hi-lo)/2))+1);
if((mulU(mid,mid)<=(n[i])))(lo=mid);else (hi=(mid-1));}
((result[i])=lo);
(i=(i+1));}
if((mulU((result[1]),(result[1]))!=(n[1])))((result[1])=addU((result[1]),1));else ;
I out={(result[0]),(result[1])};
return out;}
