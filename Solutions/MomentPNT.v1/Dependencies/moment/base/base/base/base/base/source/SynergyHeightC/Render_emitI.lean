import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_emitI : renderFunction f_emitI = some "static void emitI(I x){emitU((x.lo));\nemitU((x.hi));}\n" := by decide +kernel
#print axioms render_emitI
end SynergyHeightC.Generated
