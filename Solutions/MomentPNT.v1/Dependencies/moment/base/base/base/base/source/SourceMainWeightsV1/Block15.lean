import SynergyHeightC.MainWeightModel
import Lean.Util.CollectAxioms
namespace SourceMainWeightsV1.Block15
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def result : ProofBox := ⟨36017671106349881097019908489727432,36017671106349881097033917381023674⟩
theorem exact_sum : block 480 32=some result := by decide +kernel
theorem domains : ((List.range 32).all (fun j=>cellDomain (480+j)))=true := by decide +kernel
end SourceMainWeightsV1.Block15
open Lean Elab
run_elab do
 for n in ([`SourceMainWeightsV1.Block15.exact_sum,`SourceMainWeightsV1.Block15.domains] : List Name) do
  let env ← getEnv
  let some ci := env.find? n | throwError "missing numerical root"
  let ax ← Lean.collectAxioms n
  logInfo m!"MAIN_WEIGHT_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
