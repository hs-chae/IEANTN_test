import SourceHeightPointsV2.Block00
import SourceHeightPointsV2.Block01
import SourceHeightPointsV2.Block02
import SourceHeightPointsV2.Block03
import SourceHeightPointsV2.Block04
import SourceHeightPointsV2.Block05
import SourceHeightPointsV2.Block06
import SourceHeightPointsV2.Block07
import SourceHeightPointsV2.Block08
import SourceHeightPointsV2.Block09
import SourceHeightPointsV2.Block10
import SourceHeightPointsV2.Block11
import SourceHeightPointsV2.Block12
import SourceHeightPointsV2.Block13
import SourceHeightPointsV2.Block14
import SourceHeightPointsV2.Block15
import SourceHeightPointsV2.Block16
import SourceHeightPointsV2.Block17
import SourceHeightPointsV2.Block18
import SourceHeightPointsV2.Block19
import SourceHeightPointsV2.Block20
import SourceHeightPointsV2.Block21
import SourceHeightPointsV2.Block22
import SourceHeightPointsV2.Block23
import Lean.Elab.Tactic.Omega
namespace SourceHeightPointsV2.All
open ScopedC ScopedC.Machine
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All768 actual C calls and the same-pointer/model identities are proved;
there is no unproved numerical provider argument left in this component. -/
theorem outputs : SourcePointOutputsProvider
 (SynergyHeightC.InitCacheProposal.postState NatArena.empty) := by
 intro i hi
 change i < 768 at hi
 let j := i / 32
 have hj : j < 24 := by dsimp [j]; omega
 have lower : 32*j ≤ i := by dsimp [j]; omega
 have upper : i < 32*(j+1) := by dsimp [j]; omega
 interval_cases j
 · exact SourceHeightPointsV2.Block00.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block01.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block02.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block03.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block04.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block05.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block06.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block07.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block08.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block09.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block10.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block11.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block12.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block13.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block14.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block15.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block16.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block17.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block18.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block19.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block20.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block21.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block22.outputs i (by omega) (by omega)
 · exact SourceHeightPointsV2.Block23.outputs i (by omega) (by omega)
end SourceHeightPointsV2.All
open Lean Elab
run_elab do
 let env ← getEnv
 let n := `SourceHeightPointsV2.All.outputs
 let some ci := env.find? n | throwError "missing all768 provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"ALL_SOURCE_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
