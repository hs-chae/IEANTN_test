static RI logPoint(Q q){if((qc(q,qi(0))<=0)){RI wide={qn(qi(1000)),qi(1000)};
return wide;}else ;
unsigned int a=small(keep(lean_nat_log2(((q.num).mag))));
unsigned int b=small(keep(lean_nat_log2((q.den))));
if(((a>2147483647u)||(b>2147483647u)))fail();else ;
int k=(((int)a)-((int)b));
Q m=q;
if((k>=0))(m=qv(q,qpow(qi(2),((unsigned int)k))));else (m=qt(q,qpow(qi(2),((unsigned int)(-k)))));
Q y=qv(qs(m,qi(1)),qa(m,qi(1)));
Q factor=qi(((unsigned int)((k<0)?(-k):k)));
if((k<0))(factor=qn(factor));else ;
return radd(rmul(point(qi(2)),atanhPoint(y)),rmul(point(factor),preparedLn2));}
