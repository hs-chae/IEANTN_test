import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_sqrtMatch : renderFunction f_sqrtMatch = some "static I sqrtMatch(I a){I z=sqrtInterval(a);\nif((mulU((z.hi),(z.hi))==mulU((a.hi),S)))((z.hi)=addU((z.hi),1));else ;\nreturn z;}\n" := by decide +kernel
#print axioms render_sqrtMatch
end SynergyHeightC.Generated
