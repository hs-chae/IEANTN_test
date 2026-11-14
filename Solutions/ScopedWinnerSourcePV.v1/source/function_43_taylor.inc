static RI taylor(const Q* coeffs,RI a){RI result=point(qi(0));
unsigned int k=(depth+1);
while((k>0)){(k=(k-1));
(result=radd(point((coeffs[k])),rmul(result,a)));}
return result;}
