static Q qpow(Q a,unsigned int n){Q result=qi(1);
while((n>0)){if(((n%2)==1))(result=qt(result,a));else ;
(n=(n/2));
if((n>0))(a=qt(a,a));else ;}
return result;}
