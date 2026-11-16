import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_rightRawCap : renderFunction f_rightRawCap = some "static I rightRawCap(I t,I T){I five=mul(divI(mul(mul(piBox,m0Box),rat(529,1000)),mul(rat(2,1),deltaBox)),mul(squareI(add(unit(),divI(mul(rat(2,1),deltaBox),t))),expPositive(divI(mul(mul(rat(2,1),deltaBox),rat(289,500)),t))));\nI six=add(mul(divI(rat(529,1000),mul(mul(rat(5,1),deltaBox),expPositive(deltaBox))),squareI(add(unit(),divI(deltaBox,t)))),divI(mul(rat(121,200),expNeg(mul(rat(2,1),deltaBox))),squareI(t)));\nI vertical=expPositive(mul(mul(rat(2,1),alphaBox),squareI(divI(add(unit(),divI(deltaBox,t)),T))));\nI first=divI(add(five,divI(mul(mul(six,piBox),m0Box),T)),mul(rat(4,1),alphaBox));\nI second=divI(mul(six,sqrtPi),mul(mul(rat(8,1),alphaBox),sqrt2Alpha));\nI V=mul(mul(mul(rat(8,1),alphaBox),vertical),add(first,second));\nreturn mul(V,squareI(t));}\n" := by decide +kernel
#print axioms render_rightRawCap
end SynergyHeightC.Generated
