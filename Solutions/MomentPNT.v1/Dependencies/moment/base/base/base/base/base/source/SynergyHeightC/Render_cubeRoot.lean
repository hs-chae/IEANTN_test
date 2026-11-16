import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_cubeRoot : renderFunction f_cubeRoot = some "static I cubeRoot(I x){if((((x.lo)>(x.hi))||((x.hi)>(16*S))))fail();else ;\nU a=floorCube(mulU((x.lo),mulU(S,S)));\nU n=mulU((x.hi),mulU(S,S));\nU b=floorCube(n);\nif((mulU(mulU(b,b),b)!=n))(b=addU(b,1));else ;\nI out={a,b};\nreturn out;}\n" := by decide +kernel
#print axioms render_cubeRoot
end SynergyHeightC.Generated
