import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_atanh2 : renderFunction f_atanh2 = some "static I atanh2(I r){if((((r.lo)>(r.hi))||((r.hi)>(S/2))))fail();else ;\nI rr=mul(r,r);\nI term=r;\nI sum=zero();\nunsigned int k=0;\nwhile((k<80)){(sum=add(sum,divN(term,((2*k)+1))));\n(term=mul(term,rr));\n(k=(k+1));}\nI result=add(sum,sum);\n((result.hi)=addU((result.hi),1));\nreturn result;}\n" := by decide +kernel
#print axioms render_atanh2
end SynergyHeightC.Generated
