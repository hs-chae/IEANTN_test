import SynergyHeightC.MainWeightModel
import Lean.Util.CollectAxioms
namespace SourceMainWeightsV1.Block19
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def result : ProofBox := ⟨8121538925681403348096644890498506,8121538925681403348168214343982491⟩
theorem exact_sum : block 608 32=some result := by decide +kernel
theorem domains : ((List.range 32).all (fun j=>cellDomain (608+j)))=true := by decide +kernel
end SourceMainWeightsV1.Block19
open Lean Elab
run_elab do
 for n in ([`SourceMainWeightsV1.Block19.exact_sum,`SourceMainWeightsV1.Block19.domains] : List Name) do
  let env ← getEnv
  let some ci := env.find? n | throwError "missing numerical root"
  let ax ← Lean.collectAxioms n
  logInfo m!"MAIN_WEIGHT_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
