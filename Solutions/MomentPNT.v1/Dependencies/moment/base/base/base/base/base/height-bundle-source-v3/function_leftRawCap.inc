static I leftRawCap(I t,I T){I a1=rat(611,1000);
I eps=rat(1,10000);
I eta=rat(7,10000);
I m1=add(divI(rat(6,1),squareI(piBox)),divI(rat(131,125),t));
I m2=add(add(divI(mul(mul(piBox,m0Box),rat(31,50)),t),divI(mul(rat(6,1),m0Box),mul(piBox,T))),divI(mul(mul(piBox,m0Box),rat(131,125)),mul(T,t)));
I scale=mul(mul(a1,expPositive(divN(t,6))),t);
I r=divI(rat(1461,1000),scale);
I J=add(add(rat(373,200),mul(divI(rat(2,1),t),rat(1273,2000))),divI(rat(129,250),squareI(t)));
I C=add(mul(m1,J),mul(m2,peakBox));
I G=add(mul(m1,gaussianBox),m2);
I mixed=add(mul(add(unit(),eta),C),mul(mul(add(unit(),inverseI(eta)),squareI(r)),G));
I mainTerm=mul(mul(mul(add(unit(),eps),squareI(scale)),mul(T,t)),mixed);
I unitTerm=mul(mul(add(unit(),inverseI(eps)),T),gaussianBox);
I omega=expPositive(divI(alphaBox,mul(rat(2,1),squareI(T))));
return mul(mul(rat(2,1),omega),add(mainTerm,unitTerm));}
