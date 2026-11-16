import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_positiveSub : renderFunction f_positiveSub = some "static I positiveSub(I a,I b){I r={(((a.lo)>(b.hi))?((a.lo)-(b.hi)):0),(((a.hi)>(b.lo))?((a.hi)-(b.lo)):0)};\nreturn r;}\n" := by decide +kernel
#print axioms render_positiveSub
end SynergyHeightC.Generated
