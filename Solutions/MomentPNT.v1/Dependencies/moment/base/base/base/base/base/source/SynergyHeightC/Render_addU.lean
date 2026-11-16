import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_addU : renderFunction f_addU = some "static U addU(U a,U b){if(((MAXU-a)<b))fail();else ;\nreturn (a+b);}\n" := by decide +kernel
#print axioms render_addU
end SynergyHeightC.Generated
