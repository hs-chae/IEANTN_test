static RI rpow(RI a,unsigned int n){if((n==0))return point(qi(1));else ;
unsigned int bit=1;
while((bit<=(n/2)))(bit=(bit*2));
RI result=a;
(bit=(bit/2));
while((bit>0)){(result=rmul(result,result));
if((((n/bit)%2)==1))(result=rmul(a,result));else ;
(bit=(bit/2));}
return result;}
