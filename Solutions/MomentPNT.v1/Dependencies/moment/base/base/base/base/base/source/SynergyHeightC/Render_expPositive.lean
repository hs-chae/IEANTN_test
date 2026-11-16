import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_expPositive : renderFunction f_expPositive = some "static I expPositive(I x){if(((x.lo)>(x.hi)))fail();else ;\nI left={(x.lo),(x.lo)};\nI right={(x.hi),(x.hi)};\nI lower=expPositiveRaw(left);\nI upper=expPositiveRaw(right);\nI out={(lower.lo),(upper.hi)};\nreturn out;}\n" := by decide +kernel
#print axioms render_expPositive
end SynergyHeightC.Generated
