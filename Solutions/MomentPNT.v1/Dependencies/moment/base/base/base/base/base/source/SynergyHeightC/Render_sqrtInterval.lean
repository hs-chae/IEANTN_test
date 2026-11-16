import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_sqrtInterval : renderFunction f_sqrtInterval = some "static I sqrtInterval(I x){if((((x.lo)>(x.hi))||((x.hi)>(16*S))))fail();else ;\nU n[2]={mulU((x.lo),S),mulU((x.hi),S)};\nU result[2];\nunsigned int i=0;\nwhile((i<2)){U lo=0;\nU hi=(4*S);\nwhile((lo<hi)){U mid=((lo+((hi-lo)/2))+1);\nif((mulU(mid,mid)<=(n[i])))(lo=mid);else (hi=(mid-1));}\n((result[i])=lo);\n(i=(i+1));}\nif((mulU((result[1]),(result[1]))!=(n[1])))((result[1])=addU((result[1]),1));else ;\nI out={(result[0]),(result[1])};\nreturn out;}\n" := by decide +kernel
#print axioms render_sqrtInterval
end SynergyHeightC.Generated
