import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_mul : renderFunction f_mul = some "static I mul(I a,I b){I r={(mulU((a.lo),(b.lo))/S),ceilDiv(mulU((a.hi),(b.hi)),S)};\nreturn r;}\n" := by decide +kernel
#print axioms render_mul
end SynergyHeightC.Generated
