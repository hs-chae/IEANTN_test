static RI atanhPoint(Q q){Q r=qabs(q);
if((qc(r,qi(1))>=0)){RI wide={qn(qi(1000)),qi(1000)};
return wide;}else ;
Q error=qv(qpow(r,(depth+1)),qs(qi(1),r));
RI remainder={qn(error),error};
return radd(taylor(atanhCoeffs,point(q)),remainder);}
