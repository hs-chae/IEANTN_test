/- Actual unchanged C point 327/768, proved-subroutine evaluation. -/
import SynergyHeightC.FullContractPointExecute
import SynergyAnalytic.HeightPointLogGridDefs
import SynergyHeightC.InitCacheProposal
import Lean.Util.CollectAxioms
namespace SourceHeightPointsV2.Point0326
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def input : ProofBox := (SynergyAnalytic.HeightPoint.logCell 327).getD ⟨0,0⟩
theorem input_defined : SynergyAnalytic.HeightPoint.logCell 327=some input := by decide +kernel
theorem checked : SynergyHeightC.FullContractPointExecute.checkedModel
 (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input=true := by decide +kernel
theorem source_outputs : ∃ c d,
 SynergyHeightC.PointExecuteAPI.modelOutputs input=some (c,d) ∧
 SynergyHeightC.PointExecuteAPI.SourcePointOutputs
  (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d :=
 SynergyHeightC.FullContractPointExecute.source_outputs_of_checkedModel checked
end SourceHeightPointsV2.Point0326
open Lean Elab
run_elab do
 let env ← getEnv
 for n in ([`SourceHeightPointsV2.Point0326.input_defined,`SourceHeightPointsV2.Point0326.checked,`SourceHeightPointsV2.Point0326.source_outputs] : List Name) do
  let some ci := env.find? n | throwError "missing sourcepoint {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"SOURCE_POINT_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
