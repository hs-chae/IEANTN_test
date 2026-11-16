import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_logTight : renderFunction f_logTight = some "static I logTight(I x){if((((x.lo)<S)||((x.lo)>(x.hi))))fail();else ;\nI left={(x.lo),(x.lo)};\nI right={(x.hi),(x.hi)};\nI lower=logPos(left);\nI upper=logPos(right);\nI out={(lower.lo),(upper.hi)};\nreturn out;}\n" := by decide +kernel
#print axioms render_logTight
end SynergyHeightC.Generated
