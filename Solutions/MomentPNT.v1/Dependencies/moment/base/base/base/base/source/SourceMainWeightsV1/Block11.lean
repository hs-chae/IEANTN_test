import SynergyHeightC.MainWeightModel
import Lean.Util.CollectAxioms
namespace SourceMainWeightsV1.Block11
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def result : ProofBox := ⟨88350043066929500827304078717333340,88350043066929500827309189522772004⟩
theorem exact_sum : block 352 32=some result := by decide +kernel
theorem domains : ((List.range 32).all (fun j=>cellDomain (352+j)))=true := by decide +kernel
end SourceMainWeightsV1.Block11
open Lean Elab
run_elab do
 for n in ([`SourceMainWeightsV1.Block11.exact_sum,`SourceMainWeightsV1.Block11.domains] : List Name) do
  let env ← getEnv
  let some ci := env.find? n | throwError "missing numerical root"
  let ax ← Lean.collectAxioms n
  logInfo m!"MAIN_WEIGHT_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
