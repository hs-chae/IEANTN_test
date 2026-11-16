import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_unit : renderFunction f_unit = some "static I unit(){I r={S,S};\nreturn r;}\n" := by decide +kernel
#print axioms render_unit
end SynergyHeightC.Generated
