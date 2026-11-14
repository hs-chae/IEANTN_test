static void prepare(unsigned int d){if((d>64))fail();else ;
(depth=d);
(scale100=nl(nu(1),nu(100)));
((expCoeffs[0])=qi(1));
((atanhCoeffs[0])=qi(0));
unsigned int k=1;
while((k<=depth)){((expCoeffs[k])=qv((expCoeffs[(k-1)]),qi(k)));
((atanhCoeffs[k])=(((k%2)==1)?qv(qi(1),qi(k)):qi(0)));
(k=(k+1));}
(preparedLn2=rmul(point(qi(2)),atanhPoint(qv(qi(1),qi(3)))));}
