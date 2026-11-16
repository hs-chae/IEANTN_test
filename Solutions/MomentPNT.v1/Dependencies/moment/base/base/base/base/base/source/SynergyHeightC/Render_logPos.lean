import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_logPos : renderFunction f_logPos = some "static I logPos(I x){if((((x.lo)<S)||((x.lo)>(x.hi))))fail();else ;\nI m=x;\nunsigned int k=0;\nwhile(((m.lo)>(2*S))){(m=divN(m,2));\n(k=(k+1));\nif((k>384))fail();else ;}\nif(((m.hi)>(3*S)))fail();else ;\nI r=divI(positiveSub(m,unit()),add(m,unit()));\nreturn add(atanh2(r),mul(rat(k,1),ln2));}\n" := by decide +kernel
#print axioms render_logPos
end SynergyHeightC.Generated
