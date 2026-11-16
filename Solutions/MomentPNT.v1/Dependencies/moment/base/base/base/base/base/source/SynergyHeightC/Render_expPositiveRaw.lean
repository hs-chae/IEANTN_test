import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_expPositiveRaw : renderFunction f_expPositiveRaw = some "static I expPositiveRaw(I x){return divI(unit(),expNeg(x));}\n" := by decide +kernel
#print axioms render_expPositiveRaw
end SynergyHeightC.Generated
