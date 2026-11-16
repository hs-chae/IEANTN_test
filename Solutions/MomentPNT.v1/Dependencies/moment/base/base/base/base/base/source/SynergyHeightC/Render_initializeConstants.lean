import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_initializeConstants : renderFunction f_initializeConstants = some "static void initializeConstants(){I pl=rat(((((((((U)0)*((U)1000000000))+((U)3))*((U)1000000000))+((U)141592653))*((U)1000000000))+((U)589793238)),((((((((U)0)*((U)1000000000))+((U)1))*((U)1000000000))+((U)0))*((U)1000000000))+((U)0)));\nI ph=rat(((((((((U)0)*((U)1000000000))+((U)3))*((U)1000000000))+((U)141592653))*((U)1000000000))+((U)589793239)),((((((((U)0)*((U)1000000000))+((U)1))*((U)1000000000))+((U)0))*((U)1000000000))+((U)0)));\n(piBox={(pl.lo),(ph.hi)});\n(alphaBox=rat(601,5000));\n(dBox=rat(3681,10000));\n(deltaBox=rat(3599,10000));\n(m0Box=sqrtInterval(add(unit(),mul(rat(2,3),sqrtInterval(rat(6,5))))));\n(gaussianBox=divN(sqrtInterval(divI(piBox,rat(601,2500))),2));\n(peakBox=expNeg(divN(add(unit(),logTight(mul(rat(6,1),rat(601,2500)))),6)));\n(sqrtPi=sqrtInterval(piBox));\n(sqrt2Alpha=sqrtInterval(mul(rat(2,1),alphaBox)));\nI hstar=positiveSub(rat(((((((U)0)*((U)1000000000))+((U)3000))*((U)1000000000))+((U)0)),1),unit());\n(smoothingBox=divI(rat(1,2),squareI(positiveSub(unit(),inverseI(hstar)))));}\n" := by decide +kernel
#print axioms render_initializeConstants
end SynergyHeightC.Generated
