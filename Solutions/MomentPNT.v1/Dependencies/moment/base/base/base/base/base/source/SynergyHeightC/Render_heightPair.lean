import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_heightPair : renderFunction f_heightPair = some "static void heightPair(I t,I* c,I* D){I T=expPositive(t);\nI left=leftRawCap(t,T);\nI right=rightRawCap(t,T);\nI ll=logTight(left);\nI lr=logTight(right);\nI width=add(rat(1,2),divI(deltaBox,t));\nI theta=divI(add(rat(1,8),divI(add(dBox,deltaBox),t)),width);\nif(((theta.hi)>S))fail();else ;\nI exponent=add(mul(theta,ll),mul(positiveSub(unit(),theta),lr));\nI prefactor=divI(mul(mul(smoothingBox,expPositive(mul(rat(2,1),alphaBox))),t),mul(mul(rat(2,1),piBox),dBox));\n((*c)=mul(prefactor,expPositive(exponent)));\n((*D)=divI(positiveSub(ll,lr),width));}\n" := by decide +kernel
#print axioms render_heightPair
end SynergyHeightC.Generated
