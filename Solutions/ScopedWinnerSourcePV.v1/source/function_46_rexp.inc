static RI rexp(RI a){if(((qc((a.hi),qi(0))<=0)||(qc(qi(0),(a.lo))<=0)))return rhull(expPoint((a.lo)),expPoint((a.hi)));else ;
return radd(taylor(expCoeffs,a),expRemainder(a));}
