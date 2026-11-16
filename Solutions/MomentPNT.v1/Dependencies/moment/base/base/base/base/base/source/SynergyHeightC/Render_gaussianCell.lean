import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_gaussianCell : renderFunction f_gaussianCell = some "static I gaussianCell(I left,I right,I width){I q=rat(601,2500);\nreturn mul(width,mul(expNeg(mul(q,mul(left,left))),cubeRoot(right)));}\n" := by decide +kernel
#print axioms render_gaussianCell
end SynergyHeightC.Generated
