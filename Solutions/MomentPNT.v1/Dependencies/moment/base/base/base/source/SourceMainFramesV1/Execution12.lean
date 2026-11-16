import SourceMainFramesV1.Point0384
import SourceMainFramesV1.Point0385
import SourceMainFramesV1.Point0386
import SourceMainFramesV1.Point0387
import SourceMainFramesV1.Point0388
import SourceMainFramesV1.Point0389
import SourceMainFramesV1.Point0390
import SourceMainFramesV1.Point0391
import SourceMainFramesV1.Point0392
import SourceMainFramesV1.Point0393
import SourceMainFramesV1.Point0394
import SourceMainFramesV1.Point0395
import SourceMainFramesV1.Point0396
import SourceMainFramesV1.Point0397
import SourceMainFramesV1.Point0398
import SourceMainFramesV1.Point0399
import SourceMainFramesV1.Point0400
import SourceMainFramesV1.Point0401
import SourceMainFramesV1.Point0402
import SourceMainFramesV1.Point0403
import SourceMainFramesV1.Point0404
import SourceMainFramesV1.Point0405
import SourceMainFramesV1.Point0406
import SourceMainFramesV1.Point0407
import SourceMainFramesV1.Point0408
import SourceMainFramesV1.Point0409
import SourceMainFramesV1.Point0410
import SourceMainFramesV1.Point0411
import SourceMainFramesV1.Point0412
import SourceMainFramesV1.Point0413
import SourceMainFramesV1.Point0414
import SourceMainFramesV1.Point0415
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution12
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 384 ≤ i) (upper : i < 416) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0384.input,SourceMainFramesV1.Point0384.outputs,SourceMainFramesV1.Point0384.input_defined,SourceMainFramesV1.Point0384.outputs_defined,SourceMainFramesV1.Point0384.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0385.input,SourceMainFramesV1.Point0385.outputs,SourceMainFramesV1.Point0385.input_defined,SourceMainFramesV1.Point0385.outputs_defined,SourceMainFramesV1.Point0385.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0386.input,SourceMainFramesV1.Point0386.outputs,SourceMainFramesV1.Point0386.input_defined,SourceMainFramesV1.Point0386.outputs_defined,SourceMainFramesV1.Point0386.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0387.input,SourceMainFramesV1.Point0387.outputs,SourceMainFramesV1.Point0387.input_defined,SourceMainFramesV1.Point0387.outputs_defined,SourceMainFramesV1.Point0387.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0388.input,SourceMainFramesV1.Point0388.outputs,SourceMainFramesV1.Point0388.input_defined,SourceMainFramesV1.Point0388.outputs_defined,SourceMainFramesV1.Point0388.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0389.input,SourceMainFramesV1.Point0389.outputs,SourceMainFramesV1.Point0389.input_defined,SourceMainFramesV1.Point0389.outputs_defined,SourceMainFramesV1.Point0389.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0390.input,SourceMainFramesV1.Point0390.outputs,SourceMainFramesV1.Point0390.input_defined,SourceMainFramesV1.Point0390.outputs_defined,SourceMainFramesV1.Point0390.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0391.input,SourceMainFramesV1.Point0391.outputs,SourceMainFramesV1.Point0391.input_defined,SourceMainFramesV1.Point0391.outputs_defined,SourceMainFramesV1.Point0391.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0392.input,SourceMainFramesV1.Point0392.outputs,SourceMainFramesV1.Point0392.input_defined,SourceMainFramesV1.Point0392.outputs_defined,SourceMainFramesV1.Point0392.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0393.input,SourceMainFramesV1.Point0393.outputs,SourceMainFramesV1.Point0393.input_defined,SourceMainFramesV1.Point0393.outputs_defined,SourceMainFramesV1.Point0393.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0394.input,SourceMainFramesV1.Point0394.outputs,SourceMainFramesV1.Point0394.input_defined,SourceMainFramesV1.Point0394.outputs_defined,SourceMainFramesV1.Point0394.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0395.input,SourceMainFramesV1.Point0395.outputs,SourceMainFramesV1.Point0395.input_defined,SourceMainFramesV1.Point0395.outputs_defined,SourceMainFramesV1.Point0395.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0396.input,SourceMainFramesV1.Point0396.outputs,SourceMainFramesV1.Point0396.input_defined,SourceMainFramesV1.Point0396.outputs_defined,SourceMainFramesV1.Point0396.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0397.input,SourceMainFramesV1.Point0397.outputs,SourceMainFramesV1.Point0397.input_defined,SourceMainFramesV1.Point0397.outputs_defined,SourceMainFramesV1.Point0397.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0398.input,SourceMainFramesV1.Point0398.outputs,SourceMainFramesV1.Point0398.input_defined,SourceMainFramesV1.Point0398.outputs_defined,SourceMainFramesV1.Point0398.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0399.input,SourceMainFramesV1.Point0399.outputs,SourceMainFramesV1.Point0399.input_defined,SourceMainFramesV1.Point0399.outputs_defined,SourceMainFramesV1.Point0399.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0400.input,SourceMainFramesV1.Point0400.outputs,SourceMainFramesV1.Point0400.input_defined,SourceMainFramesV1.Point0400.outputs_defined,SourceMainFramesV1.Point0400.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0401.input,SourceMainFramesV1.Point0401.outputs,SourceMainFramesV1.Point0401.input_defined,SourceMainFramesV1.Point0401.outputs_defined,SourceMainFramesV1.Point0401.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0402.input,SourceMainFramesV1.Point0402.outputs,SourceMainFramesV1.Point0402.input_defined,SourceMainFramesV1.Point0402.outputs_defined,SourceMainFramesV1.Point0402.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0403.input,SourceMainFramesV1.Point0403.outputs,SourceMainFramesV1.Point0403.input_defined,SourceMainFramesV1.Point0403.outputs_defined,SourceMainFramesV1.Point0403.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0404.input,SourceMainFramesV1.Point0404.outputs,SourceMainFramesV1.Point0404.input_defined,SourceMainFramesV1.Point0404.outputs_defined,SourceMainFramesV1.Point0404.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0405.input,SourceMainFramesV1.Point0405.outputs,SourceMainFramesV1.Point0405.input_defined,SourceMainFramesV1.Point0405.outputs_defined,SourceMainFramesV1.Point0405.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0406.input,SourceMainFramesV1.Point0406.outputs,SourceMainFramesV1.Point0406.input_defined,SourceMainFramesV1.Point0406.outputs_defined,SourceMainFramesV1.Point0406.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0407.input,SourceMainFramesV1.Point0407.outputs,SourceMainFramesV1.Point0407.input_defined,SourceMainFramesV1.Point0407.outputs_defined,SourceMainFramesV1.Point0407.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0408.input,SourceMainFramesV1.Point0408.outputs,SourceMainFramesV1.Point0408.input_defined,SourceMainFramesV1.Point0408.outputs_defined,SourceMainFramesV1.Point0408.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0409.input,SourceMainFramesV1.Point0409.outputs,SourceMainFramesV1.Point0409.input_defined,SourceMainFramesV1.Point0409.outputs_defined,SourceMainFramesV1.Point0409.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0410.input,SourceMainFramesV1.Point0410.outputs,SourceMainFramesV1.Point0410.input_defined,SourceMainFramesV1.Point0410.outputs_defined,SourceMainFramesV1.Point0410.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0411.input,SourceMainFramesV1.Point0411.outputs,SourceMainFramesV1.Point0411.input_defined,SourceMainFramesV1.Point0411.outputs_defined,SourceMainFramesV1.Point0411.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0412.input,SourceMainFramesV1.Point0412.outputs,SourceMainFramesV1.Point0412.input_defined,SourceMainFramesV1.Point0412.outputs_defined,SourceMainFramesV1.Point0412.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0413.input,SourceMainFramesV1.Point0413.outputs,SourceMainFramesV1.Point0413.input_defined,SourceMainFramesV1.Point0413.outputs_defined,SourceMainFramesV1.Point0413.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0414.input,SourceMainFramesV1.Point0414.outputs,SourceMainFramesV1.Point0414.input_defined,SourceMainFramesV1.Point0414.outputs_defined,SourceMainFramesV1.Point0414.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0415.input,SourceMainFramesV1.Point0415.outputs,SourceMainFramesV1.Point0415.input_defined,SourceMainFramesV1.Point0415.outputs_defined,SourceMainFramesV1.Point0415.execution total⟩
end SourceMainFramesV1.Execution12
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution12.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
