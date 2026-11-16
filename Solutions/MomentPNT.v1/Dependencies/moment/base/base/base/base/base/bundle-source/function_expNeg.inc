static I expNeg(I x){if((((x.lo)>(x.hi))||((x.hi)>(64*S))))fail();else ;
I z=divN(x,64);
I p=unit();
unsigned int k=48;
while((k>0)){(p=positiveSub(unit(),divN(mul(z,p),k)));
(k=(k-1));}
I r={(((p.lo)>0)?((p.lo)-1):0),addU((p.hi),1)};
(k=0);
while((k<6)){(r=mul(r,r));
(k=(k+1));}
return r;}
