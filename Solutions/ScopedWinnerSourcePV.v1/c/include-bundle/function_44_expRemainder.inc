static RI expRemainder(RI a){Q r=qmax(qabs((a.lo)),qabs((a.hi)));
S ceil=ceilQ(r);
if((ceil.neg))fail();else ;
unsigned int c=small((ceil.mag));
if((c==4294967295u))fail();else ;
Q fact=qi(1);
unsigned int k=1;
while((k<=(depth+1))){(fact=qt(fact,qi(k)));
(k=(k+1));}
Q error=qv(qt(qpow(qi(3),(c+1)),qpow(r,(depth+1))),fact);
RI out={qn(error),error};
return out;}
