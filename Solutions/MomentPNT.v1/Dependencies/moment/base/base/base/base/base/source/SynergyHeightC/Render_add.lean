import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_add : renderFunction f_add = some "static I add(I a,I b){I r={addU((a.lo),(b.lo)),addU((a.hi),(b.hi))};\nreturn r;}\n" := by decide +kernel
#print axioms render_add
end SynergyHeightC.Generated
