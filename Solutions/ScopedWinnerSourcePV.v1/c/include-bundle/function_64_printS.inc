static void printS(S a){char digits[1024];
unsigned int count=0;
if((a.neg))putchar('-');else ;
N x=(a.mag);
unsigned int first=1;
while((first||(!nz(x)))){(first=0);
if((count>=1024))fail();else ;
((digits[count])=((char)('0'+small(nr(x,nu(10))))));
(count=(count+1));
(x=nd(x,nu(10)));}
while((count>0)){(count=(count-1));
putchar((digits[count]));}}
