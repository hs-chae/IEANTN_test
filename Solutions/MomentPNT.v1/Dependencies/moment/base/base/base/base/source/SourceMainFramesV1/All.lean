import SourceMainFramesV1.Block00
import SourceMainFramesV1.Block01
import SourceMainFramesV1.Block02
import SourceMainFramesV1.Block03
import SourceMainFramesV1.Block04
import SourceMainFramesV1.Block05
import SourceMainFramesV1.Block06
import SourceMainFramesV1.Block07
import SourceMainFramesV1.Block08
import SourceMainFramesV1.Block09
import SourceMainFramesV1.Block10
import SourceMainFramesV1.Block11
import SourceMainFramesV1.Block12
import SourceMainFramesV1.Block13
import SourceMainFramesV1.Block14
import SourceMainFramesV1.Block15
import SourceMainFramesV1.Block16
import SourceMainFramesV1.Block17
import SourceMainFramesV1.Block18
import SourceMainFramesV1.Block19
import SourceMainFramesV1.Block20
import SourceMainFramesV1.Block21
import SourceMainFramesV1.Block22
import SourceMainFramesV1.Block23
import SourceHeightPointsV2.OutputFamily
import Lean.Elab.Tactic.Omega
namespace SourceMainFramesV1.All
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- Each point executes actual C in its actual main heap, for any accumulated total.
Input construction, accumulation and output are separately proved components. -/
theorem outputs (total : ProofBox) : SourcePointOutputFamily := by
 intro i hi
 change i < 768 at hi
 let j := i / 32
 have hj : j < 24 := by dsimp [j]; omega
 have lower : 32*j ≤ i := by dsimp [j]; omega
 have upper : i < 32*(j+1) := by dsimp [j]; omega
 interval_cases j
 · exact SourceMainFramesV1.Block00.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block01.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block02.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block03.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block04.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block05.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block06.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block07.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block08.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block09.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block10.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block11.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block12.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block13.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block14.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block15.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block16.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block17.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block18.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block19.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block20.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block21.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block22.outputs total i (by omega) (by omega)
 · exact SourceMainFramesV1.Block23.outputs total i (by omega) (by omega)
end SourceMainFramesV1.All
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.All.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing all frame provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"FRAME_ALL_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
