import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_divN : renderFunction f_divN = some "static I divN(I a,unsigned int n){if((n==0))fail();else ;\nI r={((a.lo)/n),ceilDiv((a.hi),n)};\nreturn r;}\n" := by decide +kernel
#print axioms render_divN
end SynergyHeightC.Generated
