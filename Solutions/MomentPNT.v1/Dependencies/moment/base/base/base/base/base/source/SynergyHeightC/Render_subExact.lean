import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_subExact : renderFunction f_subExact = some "static I subExact(I a,I b){if((((a.lo)<(b.hi))||((a.hi)<(b.lo))))fail();else ;\nI z={((a.lo)-(b.hi)),((a.hi)-(b.lo))};\nreturn z;}\n" := by decide +kernel
#print axioms render_subExact
end SynergyHeightC.Generated
