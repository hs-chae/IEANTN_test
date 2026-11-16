static I atanh2(I r){if((((r.lo)>(r.hi))||((r.hi)>(S/2))))fail();else ;
I rr=mul(r,r);
I term=r;
I sum=zero();
unsigned int k=0;
while((k<80)){(sum=add(sum,divN(term,((2*k)+1))));
(term=mul(term,rr));
(k=(k+1));}
I result=add(sum,sum);
((result.hi)=addU((result.hi),1));
return result;}
