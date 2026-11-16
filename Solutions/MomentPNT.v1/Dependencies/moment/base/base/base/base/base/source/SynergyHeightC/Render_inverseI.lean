import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_inverseI : renderFunction f_inverseI = some "static I inverseI(I x){return divI(unit(),x);}\n" := by decide +kernel
#print axioms render_inverseI
end SynergyHeightC.Generated
