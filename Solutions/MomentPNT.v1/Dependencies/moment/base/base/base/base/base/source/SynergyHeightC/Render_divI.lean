import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_divI : renderFunction f_divI = some "static I divI(I a,I b){if(((b.lo)==0))fail();else ;\nI r={(mulU((a.lo),S)/(b.hi)),ceilDiv(mulU((a.hi),S),(b.lo))};\nreturn r;}\n" := by decide +kernel
#print axioms render_divI
end SynergyHeightC.Generated
