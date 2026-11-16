import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_expNeg : renderFunction f_expNeg = some "static I expNeg(I x){if((((x.lo)>(x.hi))||((x.hi)>(64*S))))fail();else ;\nI z=divN(x,64);\nI p=unit();\nunsigned int k=48;\nwhile((k>0)){(p=positiveSub(unit(),divN(mul(z,p),k)));\n(k=(k-1));}\nI r={(((p.lo)>0)?((p.lo)-1):0),addU((p.hi),1)};\n(k=0);\nwhile((k<6)){(r=mul(r,r));\n(k=(k+1));}\nreturn r;}\n" := by decide +kernel
#print axioms render_expNeg
end SynergyHeightC.Generated
