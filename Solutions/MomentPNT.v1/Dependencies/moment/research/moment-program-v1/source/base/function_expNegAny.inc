static I expNegAny(I x){if(((x.lo)>(x.hi)))fail();else ;
unsigned int shifts=0;
while(((x.hi)>(64*S))){(x=divN(x,2));
(shifts=(shifts+1));
if((shifts>64))fail();else ;}
I value=expNeg(x);
while((shifts>0)){(value=mul(value,value));
(shifts=(shifts-1));}
return value;}
