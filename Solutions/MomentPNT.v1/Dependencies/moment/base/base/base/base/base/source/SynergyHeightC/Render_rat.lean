import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_rat : renderFunction f_rat = some "static I rat(U n,U d){U a=mulU(n,S);\nI r={(a/d),ceilDiv(a,d)};\nreturn r;}\n" := by decide +kernel
#print axioms render_rat
end SynergyHeightC.Generated
