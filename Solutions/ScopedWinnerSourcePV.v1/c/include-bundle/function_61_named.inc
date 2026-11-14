static I named(unsigned int c){RI r;
if((c==0)){((r.lo)=qm(smake(decimal("31415926535897932"),0),decimal("10000000000000000")));
((r.hi)=qm(smake(decimal("31415926535897933"),0),decimal("10000000000000000")));}else {((r.lo)=qv(qi(5722),qi(10000)));
((r.hi)=qv(qi(5823),qi(10000)));}
return fromRI(r,1);}
