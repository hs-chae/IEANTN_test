static void heightPair(I t,I* c,I* D){I T=expPositive(t);
I left=leftRawCap(t,T);
I right=rightRawCap(t,T);
I ll=logTight(left);
I lr=logTight(right);
I width=add(rat(1,2),divI(deltaBox,t));
I theta=divI(add(rat(1,8),divI(add(dBox,deltaBox),t)),width);
if(((theta.hi)>S))fail();else ;
I exponent=add(mul(theta,ll),mul(positiveSub(unit(),theta),lr));
I prefactor=divI(mul(mul(smoothingBox,expPositive(mul(rat(2,1),alphaBox))),t),mul(mul(rat(2,1),piBox),dBox));
((*c)=mul(prefactor,expPositive(exponent)));
((*D)=divI(positiveSub(ll,lr),width));}
