import SynergyHeightC.MainWeightModel
import Lean.Util.CollectAxioms
namespace SourceMainWeightsV1.Block21
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def result : ProofBox := ⟨2076135290948876748227176769719655,2076135290948876748543236277078506⟩
theorem exact_sum : block 672 32=some result := by decide +kernel
theorem domains : ((List.range 32).all (fun j=>cellDomain (672+j)))=true := by decide +kernel
end SourceMainWeightsV1.Block21
open Lean Elab
run_elab do
 for n in ([`SourceMainWeightsV1.Block21.exact_sum,`SourceMainWeightsV1.Block21.domains] : List Name) do
  let env ← getEnv
  let some ci := env.find? n | throwError "missing numerical root"
  let ax ← Lean.collectAxioms n
  logInfo m!"MAIN_WEIGHT_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
