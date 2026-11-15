static I logPos(I x){if((((x.lo)<S)||((x.lo)>(x.hi))))fail();else ;
I m=x;
unsigned int k=0;
while(((m.lo)>(2*S))){(m=divN(m,2));
(k=(k+1));
if((k>384))fail();else ;}
if(((m.hi)>(3*S)))fail();else ;
I r=divI(positiveSub(m,unit()),add(m,unit()));
return add(atanh2(r),mul(rat(k,1),ln2));}
