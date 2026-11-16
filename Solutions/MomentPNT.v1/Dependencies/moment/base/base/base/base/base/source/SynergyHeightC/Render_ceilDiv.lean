import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_ceilDiv : renderFunction f_ceilDiv = some "static U ceilDiv(U a,U b){if((b==0))fail();else ;\nreturn addU((a/b),((a%b)!=0));}\n" := by decide +kernel
#print axioms render_ceilDiv
end SynergyHeightC.Generated
