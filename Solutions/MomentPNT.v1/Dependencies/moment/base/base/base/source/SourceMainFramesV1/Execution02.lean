import SourceMainFramesV1.Point0064
import SourceMainFramesV1.Point0065
import SourceMainFramesV1.Point0066
import SourceMainFramesV1.Point0067
import SourceMainFramesV1.Point0068
import SourceMainFramesV1.Point0069
import SourceMainFramesV1.Point0070
import SourceMainFramesV1.Point0071
import SourceMainFramesV1.Point0072
import SourceMainFramesV1.Point0073
import SourceMainFramesV1.Point0074
import SourceMainFramesV1.Point0075
import SourceMainFramesV1.Point0076
import SourceMainFramesV1.Point0077
import SourceMainFramesV1.Point0078
import SourceMainFramesV1.Point0079
import SourceMainFramesV1.Point0080
import SourceMainFramesV1.Point0081
import SourceMainFramesV1.Point0082
import SourceMainFramesV1.Point0083
import SourceMainFramesV1.Point0084
import SourceMainFramesV1.Point0085
import SourceMainFramesV1.Point0086
import SourceMainFramesV1.Point0087
import SourceMainFramesV1.Point0088
import SourceMainFramesV1.Point0089
import SourceMainFramesV1.Point0090
import SourceMainFramesV1.Point0091
import SourceMainFramesV1.Point0092
import SourceMainFramesV1.Point0093
import SourceMainFramesV1.Point0094
import SourceMainFramesV1.Point0095
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution02
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 64 ≤ i) (upper : i < 96) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0064.input,SourceMainFramesV1.Point0064.outputs,SourceMainFramesV1.Point0064.input_defined,SourceMainFramesV1.Point0064.outputs_defined,SourceMainFramesV1.Point0064.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0065.input,SourceMainFramesV1.Point0065.outputs,SourceMainFramesV1.Point0065.input_defined,SourceMainFramesV1.Point0065.outputs_defined,SourceMainFramesV1.Point0065.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0066.input,SourceMainFramesV1.Point0066.outputs,SourceMainFramesV1.Point0066.input_defined,SourceMainFramesV1.Point0066.outputs_defined,SourceMainFramesV1.Point0066.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0067.input,SourceMainFramesV1.Point0067.outputs,SourceMainFramesV1.Point0067.input_defined,SourceMainFramesV1.Point0067.outputs_defined,SourceMainFramesV1.Point0067.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0068.input,SourceMainFramesV1.Point0068.outputs,SourceMainFramesV1.Point0068.input_defined,SourceMainFramesV1.Point0068.outputs_defined,SourceMainFramesV1.Point0068.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0069.input,SourceMainFramesV1.Point0069.outputs,SourceMainFramesV1.Point0069.input_defined,SourceMainFramesV1.Point0069.outputs_defined,SourceMainFramesV1.Point0069.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0070.input,SourceMainFramesV1.Point0070.outputs,SourceMainFramesV1.Point0070.input_defined,SourceMainFramesV1.Point0070.outputs_defined,SourceMainFramesV1.Point0070.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0071.input,SourceMainFramesV1.Point0071.outputs,SourceMainFramesV1.Point0071.input_defined,SourceMainFramesV1.Point0071.outputs_defined,SourceMainFramesV1.Point0071.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0072.input,SourceMainFramesV1.Point0072.outputs,SourceMainFramesV1.Point0072.input_defined,SourceMainFramesV1.Point0072.outputs_defined,SourceMainFramesV1.Point0072.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0073.input,SourceMainFramesV1.Point0073.outputs,SourceMainFramesV1.Point0073.input_defined,SourceMainFramesV1.Point0073.outputs_defined,SourceMainFramesV1.Point0073.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0074.input,SourceMainFramesV1.Point0074.outputs,SourceMainFramesV1.Point0074.input_defined,SourceMainFramesV1.Point0074.outputs_defined,SourceMainFramesV1.Point0074.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0075.input,SourceMainFramesV1.Point0075.outputs,SourceMainFramesV1.Point0075.input_defined,SourceMainFramesV1.Point0075.outputs_defined,SourceMainFramesV1.Point0075.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0076.input,SourceMainFramesV1.Point0076.outputs,SourceMainFramesV1.Point0076.input_defined,SourceMainFramesV1.Point0076.outputs_defined,SourceMainFramesV1.Point0076.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0077.input,SourceMainFramesV1.Point0077.outputs,SourceMainFramesV1.Point0077.input_defined,SourceMainFramesV1.Point0077.outputs_defined,SourceMainFramesV1.Point0077.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0078.input,SourceMainFramesV1.Point0078.outputs,SourceMainFramesV1.Point0078.input_defined,SourceMainFramesV1.Point0078.outputs_defined,SourceMainFramesV1.Point0078.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0079.input,SourceMainFramesV1.Point0079.outputs,SourceMainFramesV1.Point0079.input_defined,SourceMainFramesV1.Point0079.outputs_defined,SourceMainFramesV1.Point0079.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0080.input,SourceMainFramesV1.Point0080.outputs,SourceMainFramesV1.Point0080.input_defined,SourceMainFramesV1.Point0080.outputs_defined,SourceMainFramesV1.Point0080.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0081.input,SourceMainFramesV1.Point0081.outputs,SourceMainFramesV1.Point0081.input_defined,SourceMainFramesV1.Point0081.outputs_defined,SourceMainFramesV1.Point0081.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0082.input,SourceMainFramesV1.Point0082.outputs,SourceMainFramesV1.Point0082.input_defined,SourceMainFramesV1.Point0082.outputs_defined,SourceMainFramesV1.Point0082.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0083.input,SourceMainFramesV1.Point0083.outputs,SourceMainFramesV1.Point0083.input_defined,SourceMainFramesV1.Point0083.outputs_defined,SourceMainFramesV1.Point0083.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0084.input,SourceMainFramesV1.Point0084.outputs,SourceMainFramesV1.Point0084.input_defined,SourceMainFramesV1.Point0084.outputs_defined,SourceMainFramesV1.Point0084.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0085.input,SourceMainFramesV1.Point0085.outputs,SourceMainFramesV1.Point0085.input_defined,SourceMainFramesV1.Point0085.outputs_defined,SourceMainFramesV1.Point0085.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0086.input,SourceMainFramesV1.Point0086.outputs,SourceMainFramesV1.Point0086.input_defined,SourceMainFramesV1.Point0086.outputs_defined,SourceMainFramesV1.Point0086.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0087.input,SourceMainFramesV1.Point0087.outputs,SourceMainFramesV1.Point0087.input_defined,SourceMainFramesV1.Point0087.outputs_defined,SourceMainFramesV1.Point0087.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0088.input,SourceMainFramesV1.Point0088.outputs,SourceMainFramesV1.Point0088.input_defined,SourceMainFramesV1.Point0088.outputs_defined,SourceMainFramesV1.Point0088.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0089.input,SourceMainFramesV1.Point0089.outputs,SourceMainFramesV1.Point0089.input_defined,SourceMainFramesV1.Point0089.outputs_defined,SourceMainFramesV1.Point0089.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0090.input,SourceMainFramesV1.Point0090.outputs,SourceMainFramesV1.Point0090.input_defined,SourceMainFramesV1.Point0090.outputs_defined,SourceMainFramesV1.Point0090.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0091.input,SourceMainFramesV1.Point0091.outputs,SourceMainFramesV1.Point0091.input_defined,SourceMainFramesV1.Point0091.outputs_defined,SourceMainFramesV1.Point0091.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0092.input,SourceMainFramesV1.Point0092.outputs,SourceMainFramesV1.Point0092.input_defined,SourceMainFramesV1.Point0092.outputs_defined,SourceMainFramesV1.Point0092.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0093.input,SourceMainFramesV1.Point0093.outputs,SourceMainFramesV1.Point0093.input_defined,SourceMainFramesV1.Point0093.outputs_defined,SourceMainFramesV1.Point0093.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0094.input,SourceMainFramesV1.Point0094.outputs,SourceMainFramesV1.Point0094.input_defined,SourceMainFramesV1.Point0094.outputs_defined,SourceMainFramesV1.Point0094.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0095.input,SourceMainFramesV1.Point0095.outputs,SourceMainFramesV1.Point0095.input_defined,SourceMainFramesV1.Point0095.outputs_defined,SourceMainFramesV1.Point0095.execution total⟩
end SourceMainFramesV1.Execution02
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution02.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
