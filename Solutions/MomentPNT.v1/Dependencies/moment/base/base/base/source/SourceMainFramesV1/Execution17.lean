import SourceMainFramesV1.Point0544
import SourceMainFramesV1.Point0545
import SourceMainFramesV1.Point0546
import SourceMainFramesV1.Point0547
import SourceMainFramesV1.Point0548
import SourceMainFramesV1.Point0549
import SourceMainFramesV1.Point0550
import SourceMainFramesV1.Point0551
import SourceMainFramesV1.Point0552
import SourceMainFramesV1.Point0553
import SourceMainFramesV1.Point0554
import SourceMainFramesV1.Point0555
import SourceMainFramesV1.Point0556
import SourceMainFramesV1.Point0557
import SourceMainFramesV1.Point0558
import SourceMainFramesV1.Point0559
import SourceMainFramesV1.Point0560
import SourceMainFramesV1.Point0561
import SourceMainFramesV1.Point0562
import SourceMainFramesV1.Point0563
import SourceMainFramesV1.Point0564
import SourceMainFramesV1.Point0565
import SourceMainFramesV1.Point0566
import SourceMainFramesV1.Point0567
import SourceMainFramesV1.Point0568
import SourceMainFramesV1.Point0569
import SourceMainFramesV1.Point0570
import SourceMainFramesV1.Point0571
import SourceMainFramesV1.Point0572
import SourceMainFramesV1.Point0573
import SourceMainFramesV1.Point0574
import SourceMainFramesV1.Point0575
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution17
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 544 ≤ i) (upper : i < 576) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0544.input,SourceMainFramesV1.Point0544.outputs,SourceMainFramesV1.Point0544.input_defined,SourceMainFramesV1.Point0544.outputs_defined,SourceMainFramesV1.Point0544.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0545.input,SourceMainFramesV1.Point0545.outputs,SourceMainFramesV1.Point0545.input_defined,SourceMainFramesV1.Point0545.outputs_defined,SourceMainFramesV1.Point0545.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0546.input,SourceMainFramesV1.Point0546.outputs,SourceMainFramesV1.Point0546.input_defined,SourceMainFramesV1.Point0546.outputs_defined,SourceMainFramesV1.Point0546.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0547.input,SourceMainFramesV1.Point0547.outputs,SourceMainFramesV1.Point0547.input_defined,SourceMainFramesV1.Point0547.outputs_defined,SourceMainFramesV1.Point0547.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0548.input,SourceMainFramesV1.Point0548.outputs,SourceMainFramesV1.Point0548.input_defined,SourceMainFramesV1.Point0548.outputs_defined,SourceMainFramesV1.Point0548.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0549.input,SourceMainFramesV1.Point0549.outputs,SourceMainFramesV1.Point0549.input_defined,SourceMainFramesV1.Point0549.outputs_defined,SourceMainFramesV1.Point0549.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0550.input,SourceMainFramesV1.Point0550.outputs,SourceMainFramesV1.Point0550.input_defined,SourceMainFramesV1.Point0550.outputs_defined,SourceMainFramesV1.Point0550.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0551.input,SourceMainFramesV1.Point0551.outputs,SourceMainFramesV1.Point0551.input_defined,SourceMainFramesV1.Point0551.outputs_defined,SourceMainFramesV1.Point0551.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0552.input,SourceMainFramesV1.Point0552.outputs,SourceMainFramesV1.Point0552.input_defined,SourceMainFramesV1.Point0552.outputs_defined,SourceMainFramesV1.Point0552.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0553.input,SourceMainFramesV1.Point0553.outputs,SourceMainFramesV1.Point0553.input_defined,SourceMainFramesV1.Point0553.outputs_defined,SourceMainFramesV1.Point0553.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0554.input,SourceMainFramesV1.Point0554.outputs,SourceMainFramesV1.Point0554.input_defined,SourceMainFramesV1.Point0554.outputs_defined,SourceMainFramesV1.Point0554.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0555.input,SourceMainFramesV1.Point0555.outputs,SourceMainFramesV1.Point0555.input_defined,SourceMainFramesV1.Point0555.outputs_defined,SourceMainFramesV1.Point0555.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0556.input,SourceMainFramesV1.Point0556.outputs,SourceMainFramesV1.Point0556.input_defined,SourceMainFramesV1.Point0556.outputs_defined,SourceMainFramesV1.Point0556.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0557.input,SourceMainFramesV1.Point0557.outputs,SourceMainFramesV1.Point0557.input_defined,SourceMainFramesV1.Point0557.outputs_defined,SourceMainFramesV1.Point0557.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0558.input,SourceMainFramesV1.Point0558.outputs,SourceMainFramesV1.Point0558.input_defined,SourceMainFramesV1.Point0558.outputs_defined,SourceMainFramesV1.Point0558.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0559.input,SourceMainFramesV1.Point0559.outputs,SourceMainFramesV1.Point0559.input_defined,SourceMainFramesV1.Point0559.outputs_defined,SourceMainFramesV1.Point0559.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0560.input,SourceMainFramesV1.Point0560.outputs,SourceMainFramesV1.Point0560.input_defined,SourceMainFramesV1.Point0560.outputs_defined,SourceMainFramesV1.Point0560.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0561.input,SourceMainFramesV1.Point0561.outputs,SourceMainFramesV1.Point0561.input_defined,SourceMainFramesV1.Point0561.outputs_defined,SourceMainFramesV1.Point0561.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0562.input,SourceMainFramesV1.Point0562.outputs,SourceMainFramesV1.Point0562.input_defined,SourceMainFramesV1.Point0562.outputs_defined,SourceMainFramesV1.Point0562.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0563.input,SourceMainFramesV1.Point0563.outputs,SourceMainFramesV1.Point0563.input_defined,SourceMainFramesV1.Point0563.outputs_defined,SourceMainFramesV1.Point0563.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0564.input,SourceMainFramesV1.Point0564.outputs,SourceMainFramesV1.Point0564.input_defined,SourceMainFramesV1.Point0564.outputs_defined,SourceMainFramesV1.Point0564.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0565.input,SourceMainFramesV1.Point0565.outputs,SourceMainFramesV1.Point0565.input_defined,SourceMainFramesV1.Point0565.outputs_defined,SourceMainFramesV1.Point0565.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0566.input,SourceMainFramesV1.Point0566.outputs,SourceMainFramesV1.Point0566.input_defined,SourceMainFramesV1.Point0566.outputs_defined,SourceMainFramesV1.Point0566.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0567.input,SourceMainFramesV1.Point0567.outputs,SourceMainFramesV1.Point0567.input_defined,SourceMainFramesV1.Point0567.outputs_defined,SourceMainFramesV1.Point0567.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0568.input,SourceMainFramesV1.Point0568.outputs,SourceMainFramesV1.Point0568.input_defined,SourceMainFramesV1.Point0568.outputs_defined,SourceMainFramesV1.Point0568.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0569.input,SourceMainFramesV1.Point0569.outputs,SourceMainFramesV1.Point0569.input_defined,SourceMainFramesV1.Point0569.outputs_defined,SourceMainFramesV1.Point0569.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0570.input,SourceMainFramesV1.Point0570.outputs,SourceMainFramesV1.Point0570.input_defined,SourceMainFramesV1.Point0570.outputs_defined,SourceMainFramesV1.Point0570.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0571.input,SourceMainFramesV1.Point0571.outputs,SourceMainFramesV1.Point0571.input_defined,SourceMainFramesV1.Point0571.outputs_defined,SourceMainFramesV1.Point0571.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0572.input,SourceMainFramesV1.Point0572.outputs,SourceMainFramesV1.Point0572.input_defined,SourceMainFramesV1.Point0572.outputs_defined,SourceMainFramesV1.Point0572.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0573.input,SourceMainFramesV1.Point0573.outputs,SourceMainFramesV1.Point0573.input_defined,SourceMainFramesV1.Point0573.outputs_defined,SourceMainFramesV1.Point0573.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0574.input,SourceMainFramesV1.Point0574.outputs,SourceMainFramesV1.Point0574.input_defined,SourceMainFramesV1.Point0574.outputs_defined,SourceMainFramesV1.Point0574.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0575.input,SourceMainFramesV1.Point0575.outputs,SourceMainFramesV1.Point0575.input_defined,SourceMainFramesV1.Point0575.outputs_defined,SourceMainFramesV1.Point0575.execution total⟩
end SourceMainFramesV1.Execution17
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution17.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
