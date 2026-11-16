import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_fail : renderFunction f_fail = some "static void fail(){fputs(\"basis arithmetic/domain failure\\n\",stderr);\nexit(3);}\n" := by decide +kernel
#print axioms render_fail
end SynergyHeightC.Generated
