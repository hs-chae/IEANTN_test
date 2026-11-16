import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_squareI : renderFunction f_squareI = some "static I squareI(I x){return mul(x,x);}\n" := by decide +kernel
#print axioms render_squareI
end SynergyHeightC.Generated
