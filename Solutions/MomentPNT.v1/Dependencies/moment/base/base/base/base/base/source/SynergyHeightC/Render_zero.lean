import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_zero : renderFunction f_zero = some "static I zero(){I r={0,0};\nreturn r;}\n" := by decide +kernel
#print axioms render_zero
end SynergyHeightC.Generated
