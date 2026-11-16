import SynergyHeightC.MainWeightModel
import Lean.Util.CollectAxioms
namespace SourceMainWeightsV1.Block01
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def result : ProofBox := ⟨339480716744452677465288989858467211,339480716744452677465290052339181729⟩
theorem exact_sum : block 32 32=some result := by decide +kernel
theorem domains : ((List.range 32).all (fun j=>cellDomain (32+j)))=true := by decide +kernel
end SourceMainWeightsV1.Block01
open Lean Elab
run_elab do
 for n in ([`SourceMainWeightsV1.Block01.exact_sum,`SourceMainWeightsV1.Block01.domains] : List Name) do
  let env ← getEnv
  let some ci := env.find? n | throwError "missing numerical root"
  let ax ← Lean.collectAxioms n
  logInfo m!"MAIN_WEIGHT_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
