import SourceMainFramesV1.Point0224
import SourceMainFramesV1.Point0225
import SourceMainFramesV1.Point0226
import SourceMainFramesV1.Point0227
import SourceMainFramesV1.Point0228
import SourceMainFramesV1.Point0229
import SourceMainFramesV1.Point0230
import SourceMainFramesV1.Point0231
import SourceMainFramesV1.Point0232
import SourceMainFramesV1.Point0233
import SourceMainFramesV1.Point0234
import SourceMainFramesV1.Point0235
import SourceMainFramesV1.Point0236
import SourceMainFramesV1.Point0237
import SourceMainFramesV1.Point0238
import SourceMainFramesV1.Point0239
import SourceMainFramesV1.Point0240
import SourceMainFramesV1.Point0241
import SourceMainFramesV1.Point0242
import SourceMainFramesV1.Point0243
import SourceMainFramesV1.Point0244
import SourceMainFramesV1.Point0245
import SourceMainFramesV1.Point0246
import SourceMainFramesV1.Point0247
import SourceMainFramesV1.Point0248
import SourceMainFramesV1.Point0249
import SourceMainFramesV1.Point0250
import SourceMainFramesV1.Point0251
import SourceMainFramesV1.Point0252
import SourceMainFramesV1.Point0253
import SourceMainFramesV1.Point0254
import SourceMainFramesV1.Point0255
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution07
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 224 ≤ i) (upper : i < 256) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0224.input,SourceMainFramesV1.Point0224.outputs,SourceMainFramesV1.Point0224.input_defined,SourceMainFramesV1.Point0224.outputs_defined,SourceMainFramesV1.Point0224.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0225.input,SourceMainFramesV1.Point0225.outputs,SourceMainFramesV1.Point0225.input_defined,SourceMainFramesV1.Point0225.outputs_defined,SourceMainFramesV1.Point0225.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0226.input,SourceMainFramesV1.Point0226.outputs,SourceMainFramesV1.Point0226.input_defined,SourceMainFramesV1.Point0226.outputs_defined,SourceMainFramesV1.Point0226.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0227.input,SourceMainFramesV1.Point0227.outputs,SourceMainFramesV1.Point0227.input_defined,SourceMainFramesV1.Point0227.outputs_defined,SourceMainFramesV1.Point0227.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0228.input,SourceMainFramesV1.Point0228.outputs,SourceMainFramesV1.Point0228.input_defined,SourceMainFramesV1.Point0228.outputs_defined,SourceMainFramesV1.Point0228.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0229.input,SourceMainFramesV1.Point0229.outputs,SourceMainFramesV1.Point0229.input_defined,SourceMainFramesV1.Point0229.outputs_defined,SourceMainFramesV1.Point0229.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0230.input,SourceMainFramesV1.Point0230.outputs,SourceMainFramesV1.Point0230.input_defined,SourceMainFramesV1.Point0230.outputs_defined,SourceMainFramesV1.Point0230.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0231.input,SourceMainFramesV1.Point0231.outputs,SourceMainFramesV1.Point0231.input_defined,SourceMainFramesV1.Point0231.outputs_defined,SourceMainFramesV1.Point0231.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0232.input,SourceMainFramesV1.Point0232.outputs,SourceMainFramesV1.Point0232.input_defined,SourceMainFramesV1.Point0232.outputs_defined,SourceMainFramesV1.Point0232.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0233.input,SourceMainFramesV1.Point0233.outputs,SourceMainFramesV1.Point0233.input_defined,SourceMainFramesV1.Point0233.outputs_defined,SourceMainFramesV1.Point0233.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0234.input,SourceMainFramesV1.Point0234.outputs,SourceMainFramesV1.Point0234.input_defined,SourceMainFramesV1.Point0234.outputs_defined,SourceMainFramesV1.Point0234.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0235.input,SourceMainFramesV1.Point0235.outputs,SourceMainFramesV1.Point0235.input_defined,SourceMainFramesV1.Point0235.outputs_defined,SourceMainFramesV1.Point0235.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0236.input,SourceMainFramesV1.Point0236.outputs,SourceMainFramesV1.Point0236.input_defined,SourceMainFramesV1.Point0236.outputs_defined,SourceMainFramesV1.Point0236.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0237.input,SourceMainFramesV1.Point0237.outputs,SourceMainFramesV1.Point0237.input_defined,SourceMainFramesV1.Point0237.outputs_defined,SourceMainFramesV1.Point0237.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0238.input,SourceMainFramesV1.Point0238.outputs,SourceMainFramesV1.Point0238.input_defined,SourceMainFramesV1.Point0238.outputs_defined,SourceMainFramesV1.Point0238.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0239.input,SourceMainFramesV1.Point0239.outputs,SourceMainFramesV1.Point0239.input_defined,SourceMainFramesV1.Point0239.outputs_defined,SourceMainFramesV1.Point0239.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0240.input,SourceMainFramesV1.Point0240.outputs,SourceMainFramesV1.Point0240.input_defined,SourceMainFramesV1.Point0240.outputs_defined,SourceMainFramesV1.Point0240.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0241.input,SourceMainFramesV1.Point0241.outputs,SourceMainFramesV1.Point0241.input_defined,SourceMainFramesV1.Point0241.outputs_defined,SourceMainFramesV1.Point0241.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0242.input,SourceMainFramesV1.Point0242.outputs,SourceMainFramesV1.Point0242.input_defined,SourceMainFramesV1.Point0242.outputs_defined,SourceMainFramesV1.Point0242.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0243.input,SourceMainFramesV1.Point0243.outputs,SourceMainFramesV1.Point0243.input_defined,SourceMainFramesV1.Point0243.outputs_defined,SourceMainFramesV1.Point0243.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0244.input,SourceMainFramesV1.Point0244.outputs,SourceMainFramesV1.Point0244.input_defined,SourceMainFramesV1.Point0244.outputs_defined,SourceMainFramesV1.Point0244.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0245.input,SourceMainFramesV1.Point0245.outputs,SourceMainFramesV1.Point0245.input_defined,SourceMainFramesV1.Point0245.outputs_defined,SourceMainFramesV1.Point0245.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0246.input,SourceMainFramesV1.Point0246.outputs,SourceMainFramesV1.Point0246.input_defined,SourceMainFramesV1.Point0246.outputs_defined,SourceMainFramesV1.Point0246.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0247.input,SourceMainFramesV1.Point0247.outputs,SourceMainFramesV1.Point0247.input_defined,SourceMainFramesV1.Point0247.outputs_defined,SourceMainFramesV1.Point0247.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0248.input,SourceMainFramesV1.Point0248.outputs,SourceMainFramesV1.Point0248.input_defined,SourceMainFramesV1.Point0248.outputs_defined,SourceMainFramesV1.Point0248.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0249.input,SourceMainFramesV1.Point0249.outputs,SourceMainFramesV1.Point0249.input_defined,SourceMainFramesV1.Point0249.outputs_defined,SourceMainFramesV1.Point0249.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0250.input,SourceMainFramesV1.Point0250.outputs,SourceMainFramesV1.Point0250.input_defined,SourceMainFramesV1.Point0250.outputs_defined,SourceMainFramesV1.Point0250.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0251.input,SourceMainFramesV1.Point0251.outputs,SourceMainFramesV1.Point0251.input_defined,SourceMainFramesV1.Point0251.outputs_defined,SourceMainFramesV1.Point0251.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0252.input,SourceMainFramesV1.Point0252.outputs,SourceMainFramesV1.Point0252.input_defined,SourceMainFramesV1.Point0252.outputs_defined,SourceMainFramesV1.Point0252.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0253.input,SourceMainFramesV1.Point0253.outputs,SourceMainFramesV1.Point0253.input_defined,SourceMainFramesV1.Point0253.outputs_defined,SourceMainFramesV1.Point0253.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0254.input,SourceMainFramesV1.Point0254.outputs,SourceMainFramesV1.Point0254.input_defined,SourceMainFramesV1.Point0254.outputs_defined,SourceMainFramesV1.Point0254.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0255.input,SourceMainFramesV1.Point0255.outputs,SourceMainFramesV1.Point0255.input_defined,SourceMainFramesV1.Point0255.outputs_defined,SourceMainFramesV1.Point0255.execution total⟩
end SourceMainFramesV1.Execution07
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution07.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
