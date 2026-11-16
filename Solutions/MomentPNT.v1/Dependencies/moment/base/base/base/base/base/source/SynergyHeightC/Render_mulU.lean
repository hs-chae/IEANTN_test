import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_mulU : renderFunction f_mulU = some "static U mulU(U a,U b){if(((a!=0)&&((MAXU/a)<b)))fail();else ;\nreturn (a*b);}\n" := by decide +kernel
#print axioms render_mulU
end SynergyHeightC.Generated
