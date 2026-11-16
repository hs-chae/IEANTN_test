static I paired(I D,unsigned int L){I Lbox=rat(L,1);
if(((D.hi)>=(Lbox.lo)))fail();else ;
I difference=positiveSub(Lbox,D);
I e=expNegAny(divN(difference,8));
return add(e,divI(mul(Lbox,positiveSub(unit(),e)),difference));}
