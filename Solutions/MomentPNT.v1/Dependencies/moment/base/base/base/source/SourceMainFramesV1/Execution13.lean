import SourceMainFramesV1.Point0416
import SourceMainFramesV1.Point0417
import SourceMainFramesV1.Point0418
import SourceMainFramesV1.Point0419
import SourceMainFramesV1.Point0420
import SourceMainFramesV1.Point0421
import SourceMainFramesV1.Point0422
import SourceMainFramesV1.Point0423
import SourceMainFramesV1.Point0424
import SourceMainFramesV1.Point0425
import SourceMainFramesV1.Point0426
import SourceMainFramesV1.Point0427
import SourceMainFramesV1.Point0428
import SourceMainFramesV1.Point0429
import SourceMainFramesV1.Point0430
import SourceMainFramesV1.Point0431
import SourceMainFramesV1.Point0432
import SourceMainFramesV1.Point0433
import SourceMainFramesV1.Point0434
import SourceMainFramesV1.Point0435
import SourceMainFramesV1.Point0436
import SourceMainFramesV1.Point0437
import SourceMainFramesV1.Point0438
import SourceMainFramesV1.Point0439
import SourceMainFramesV1.Point0440
import SourceMainFramesV1.Point0441
import SourceMainFramesV1.Point0442
import SourceMainFramesV1.Point0443
import SourceMainFramesV1.Point0444
import SourceMainFramesV1.Point0445
import SourceMainFramesV1.Point0446
import SourceMainFramesV1.Point0447
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution13
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 416 ≤ i) (upper : i < 448) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0416.input,SourceMainFramesV1.Point0416.outputs,SourceMainFramesV1.Point0416.input_defined,SourceMainFramesV1.Point0416.outputs_defined,SourceMainFramesV1.Point0416.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0417.input,SourceMainFramesV1.Point0417.outputs,SourceMainFramesV1.Point0417.input_defined,SourceMainFramesV1.Point0417.outputs_defined,SourceMainFramesV1.Point0417.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0418.input,SourceMainFramesV1.Point0418.outputs,SourceMainFramesV1.Point0418.input_defined,SourceMainFramesV1.Point0418.outputs_defined,SourceMainFramesV1.Point0418.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0419.input,SourceMainFramesV1.Point0419.outputs,SourceMainFramesV1.Point0419.input_defined,SourceMainFramesV1.Point0419.outputs_defined,SourceMainFramesV1.Point0419.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0420.input,SourceMainFramesV1.Point0420.outputs,SourceMainFramesV1.Point0420.input_defined,SourceMainFramesV1.Point0420.outputs_defined,SourceMainFramesV1.Point0420.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0421.input,SourceMainFramesV1.Point0421.outputs,SourceMainFramesV1.Point0421.input_defined,SourceMainFramesV1.Point0421.outputs_defined,SourceMainFramesV1.Point0421.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0422.input,SourceMainFramesV1.Point0422.outputs,SourceMainFramesV1.Point0422.input_defined,SourceMainFramesV1.Point0422.outputs_defined,SourceMainFramesV1.Point0422.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0423.input,SourceMainFramesV1.Point0423.outputs,SourceMainFramesV1.Point0423.input_defined,SourceMainFramesV1.Point0423.outputs_defined,SourceMainFramesV1.Point0423.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0424.input,SourceMainFramesV1.Point0424.outputs,SourceMainFramesV1.Point0424.input_defined,SourceMainFramesV1.Point0424.outputs_defined,SourceMainFramesV1.Point0424.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0425.input,SourceMainFramesV1.Point0425.outputs,SourceMainFramesV1.Point0425.input_defined,SourceMainFramesV1.Point0425.outputs_defined,SourceMainFramesV1.Point0425.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0426.input,SourceMainFramesV1.Point0426.outputs,SourceMainFramesV1.Point0426.input_defined,SourceMainFramesV1.Point0426.outputs_defined,SourceMainFramesV1.Point0426.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0427.input,SourceMainFramesV1.Point0427.outputs,SourceMainFramesV1.Point0427.input_defined,SourceMainFramesV1.Point0427.outputs_defined,SourceMainFramesV1.Point0427.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0428.input,SourceMainFramesV1.Point0428.outputs,SourceMainFramesV1.Point0428.input_defined,SourceMainFramesV1.Point0428.outputs_defined,SourceMainFramesV1.Point0428.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0429.input,SourceMainFramesV1.Point0429.outputs,SourceMainFramesV1.Point0429.input_defined,SourceMainFramesV1.Point0429.outputs_defined,SourceMainFramesV1.Point0429.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0430.input,SourceMainFramesV1.Point0430.outputs,SourceMainFramesV1.Point0430.input_defined,SourceMainFramesV1.Point0430.outputs_defined,SourceMainFramesV1.Point0430.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0431.input,SourceMainFramesV1.Point0431.outputs,SourceMainFramesV1.Point0431.input_defined,SourceMainFramesV1.Point0431.outputs_defined,SourceMainFramesV1.Point0431.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0432.input,SourceMainFramesV1.Point0432.outputs,SourceMainFramesV1.Point0432.input_defined,SourceMainFramesV1.Point0432.outputs_defined,SourceMainFramesV1.Point0432.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0433.input,SourceMainFramesV1.Point0433.outputs,SourceMainFramesV1.Point0433.input_defined,SourceMainFramesV1.Point0433.outputs_defined,SourceMainFramesV1.Point0433.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0434.input,SourceMainFramesV1.Point0434.outputs,SourceMainFramesV1.Point0434.input_defined,SourceMainFramesV1.Point0434.outputs_defined,SourceMainFramesV1.Point0434.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0435.input,SourceMainFramesV1.Point0435.outputs,SourceMainFramesV1.Point0435.input_defined,SourceMainFramesV1.Point0435.outputs_defined,SourceMainFramesV1.Point0435.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0436.input,SourceMainFramesV1.Point0436.outputs,SourceMainFramesV1.Point0436.input_defined,SourceMainFramesV1.Point0436.outputs_defined,SourceMainFramesV1.Point0436.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0437.input,SourceMainFramesV1.Point0437.outputs,SourceMainFramesV1.Point0437.input_defined,SourceMainFramesV1.Point0437.outputs_defined,SourceMainFramesV1.Point0437.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0438.input,SourceMainFramesV1.Point0438.outputs,SourceMainFramesV1.Point0438.input_defined,SourceMainFramesV1.Point0438.outputs_defined,SourceMainFramesV1.Point0438.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0439.input,SourceMainFramesV1.Point0439.outputs,SourceMainFramesV1.Point0439.input_defined,SourceMainFramesV1.Point0439.outputs_defined,SourceMainFramesV1.Point0439.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0440.input,SourceMainFramesV1.Point0440.outputs,SourceMainFramesV1.Point0440.input_defined,SourceMainFramesV1.Point0440.outputs_defined,SourceMainFramesV1.Point0440.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0441.input,SourceMainFramesV1.Point0441.outputs,SourceMainFramesV1.Point0441.input_defined,SourceMainFramesV1.Point0441.outputs_defined,SourceMainFramesV1.Point0441.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0442.input,SourceMainFramesV1.Point0442.outputs,SourceMainFramesV1.Point0442.input_defined,SourceMainFramesV1.Point0442.outputs_defined,SourceMainFramesV1.Point0442.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0443.input,SourceMainFramesV1.Point0443.outputs,SourceMainFramesV1.Point0443.input_defined,SourceMainFramesV1.Point0443.outputs_defined,SourceMainFramesV1.Point0443.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0444.input,SourceMainFramesV1.Point0444.outputs,SourceMainFramesV1.Point0444.input_defined,SourceMainFramesV1.Point0444.outputs_defined,SourceMainFramesV1.Point0444.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0445.input,SourceMainFramesV1.Point0445.outputs,SourceMainFramesV1.Point0445.input_defined,SourceMainFramesV1.Point0445.outputs_defined,SourceMainFramesV1.Point0445.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0446.input,SourceMainFramesV1.Point0446.outputs,SourceMainFramesV1.Point0446.input_defined,SourceMainFramesV1.Point0446.outputs_defined,SourceMainFramesV1.Point0446.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0447.input,SourceMainFramesV1.Point0447.outputs,SourceMainFramesV1.Point0447.input_defined,SourceMainFramesV1.Point0447.outputs_defined,SourceMainFramesV1.Point0447.execution total⟩
end SourceMainFramesV1.Execution13
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution13.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
