extern "C" int __wrap_main(){initializePointConstants();
const unsigned int cells=768;
I h=logTight(rat(((((((U)0)*((U)1000000000))+((U)3000))*((U)1000000000))+((U)0)),1));
I span=positiveSub(rat(60,1),h);
I total=zero();
unsigned int i=0;
while((i<cells)){I left=pointEdge(h,span,i,cells);
I right=pointEdge(h,span,(i+1),cells);
I c;
I D;
pointHeight(right,(&c),(&D));
(c=add(c,rat(21600,1)));
I fc={(c.hi),(c.hi)};
I fd={(D.hi),(D.hi)};
I w=positiveSub(expNeg(left),expNeg(right));
(total=add(total,mul(rat(2,1),mul(w,fc))));
emitU((c.hi));
emitU((D.hi));
(i=(i+1));}
emitI(total);
if((fflush(stdout)!=0))fail();else ;
return 0;}
