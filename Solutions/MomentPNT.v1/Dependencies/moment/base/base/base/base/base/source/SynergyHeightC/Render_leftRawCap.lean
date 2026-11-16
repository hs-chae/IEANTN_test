import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_leftRawCap : renderFunction f_leftRawCap = some "static I leftRawCap(I t,I T){I a1=rat(611,1000);\nI eps=rat(1,10000);\nI eta=rat(7,10000);\nI m1=add(divI(rat(6,1),squareI(piBox)),divI(rat(131,125),t));\nI m2=add(add(divI(mul(mul(piBox,m0Box),rat(31,50)),t),divI(mul(rat(6,1),m0Box),mul(piBox,T))),divI(mul(mul(piBox,m0Box),rat(131,125)),mul(T,t)));\nI scale=mul(mul(a1,expPositive(divN(t,6))),t);\nI r=divI(rat(1461,1000),scale);\nI J=add(add(rat(373,200),mul(divI(rat(2,1),t),rat(1273,2000))),divI(rat(129,250),squareI(t)));\nI C=add(mul(m1,J),mul(m2,peakBox));\nI G=add(mul(m1,gaussianBox),m2);\nI mixed=add(mul(add(unit(),eta),C),mul(mul(add(unit(),inverseI(eta)),squareI(r)),G));\nI mainTerm=mul(mul(mul(add(unit(),eps),squareI(scale)),mul(T,t)),mixed);\nI unitTerm=mul(mul(add(unit(),inverseI(eps)),T),gaussianBox);\nI omega=expPositive(divI(alphaBox,mul(rat(2,1),squareI(T))));\nreturn mul(mul(rat(2,1),omega),add(mainTerm,unitTerm));}\n" := by decide +kernel
#print axioms render_leftRawCap
end SynergyHeightC.Generated
