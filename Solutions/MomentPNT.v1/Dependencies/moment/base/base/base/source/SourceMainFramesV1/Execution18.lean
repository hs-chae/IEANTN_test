import SourceMainFramesV1.Point0576
import SourceMainFramesV1.Point0577
import SourceMainFramesV1.Point0578
import SourceMainFramesV1.Point0579
import SourceMainFramesV1.Point0580
import SourceMainFramesV1.Point0581
import SourceMainFramesV1.Point0582
import SourceMainFramesV1.Point0583
import SourceMainFramesV1.Point0584
import SourceMainFramesV1.Point0585
import SourceMainFramesV1.Point0586
import SourceMainFramesV1.Point0587
import SourceMainFramesV1.Point0588
import SourceMainFramesV1.Point0589
import SourceMainFramesV1.Point0590
import SourceMainFramesV1.Point0591
import SourceMainFramesV1.Point0592
import SourceMainFramesV1.Point0593
import SourceMainFramesV1.Point0594
import SourceMainFramesV1.Point0595
import SourceMainFramesV1.Point0596
import SourceMainFramesV1.Point0597
import SourceMainFramesV1.Point0598
import SourceMainFramesV1.Point0599
import SourceMainFramesV1.Point0600
import SourceMainFramesV1.Point0601
import SourceMainFramesV1.Point0602
import SourceMainFramesV1.Point0603
import SourceMainFramesV1.Point0604
import SourceMainFramesV1.Point0605
import SourceMainFramesV1.Point0606
import SourceMainFramesV1.Point0607
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution18
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 576 ≤ i) (upper : i < 608) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0576.input,SourceMainFramesV1.Point0576.outputs,SourceMainFramesV1.Point0576.input_defined,SourceMainFramesV1.Point0576.outputs_defined,SourceMainFramesV1.Point0576.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0577.input,SourceMainFramesV1.Point0577.outputs,SourceMainFramesV1.Point0577.input_defined,SourceMainFramesV1.Point0577.outputs_defined,SourceMainFramesV1.Point0577.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0578.input,SourceMainFramesV1.Point0578.outputs,SourceMainFramesV1.Point0578.input_defined,SourceMainFramesV1.Point0578.outputs_defined,SourceMainFramesV1.Point0578.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0579.input,SourceMainFramesV1.Point0579.outputs,SourceMainFramesV1.Point0579.input_defined,SourceMainFramesV1.Point0579.outputs_defined,SourceMainFramesV1.Point0579.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0580.input,SourceMainFramesV1.Point0580.outputs,SourceMainFramesV1.Point0580.input_defined,SourceMainFramesV1.Point0580.outputs_defined,SourceMainFramesV1.Point0580.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0581.input,SourceMainFramesV1.Point0581.outputs,SourceMainFramesV1.Point0581.input_defined,SourceMainFramesV1.Point0581.outputs_defined,SourceMainFramesV1.Point0581.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0582.input,SourceMainFramesV1.Point0582.outputs,SourceMainFramesV1.Point0582.input_defined,SourceMainFramesV1.Point0582.outputs_defined,SourceMainFramesV1.Point0582.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0583.input,SourceMainFramesV1.Point0583.outputs,SourceMainFramesV1.Point0583.input_defined,SourceMainFramesV1.Point0583.outputs_defined,SourceMainFramesV1.Point0583.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0584.input,SourceMainFramesV1.Point0584.outputs,SourceMainFramesV1.Point0584.input_defined,SourceMainFramesV1.Point0584.outputs_defined,SourceMainFramesV1.Point0584.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0585.input,SourceMainFramesV1.Point0585.outputs,SourceMainFramesV1.Point0585.input_defined,SourceMainFramesV1.Point0585.outputs_defined,SourceMainFramesV1.Point0585.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0586.input,SourceMainFramesV1.Point0586.outputs,SourceMainFramesV1.Point0586.input_defined,SourceMainFramesV1.Point0586.outputs_defined,SourceMainFramesV1.Point0586.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0587.input,SourceMainFramesV1.Point0587.outputs,SourceMainFramesV1.Point0587.input_defined,SourceMainFramesV1.Point0587.outputs_defined,SourceMainFramesV1.Point0587.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0588.input,SourceMainFramesV1.Point0588.outputs,SourceMainFramesV1.Point0588.input_defined,SourceMainFramesV1.Point0588.outputs_defined,SourceMainFramesV1.Point0588.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0589.input,SourceMainFramesV1.Point0589.outputs,SourceMainFramesV1.Point0589.input_defined,SourceMainFramesV1.Point0589.outputs_defined,SourceMainFramesV1.Point0589.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0590.input,SourceMainFramesV1.Point0590.outputs,SourceMainFramesV1.Point0590.input_defined,SourceMainFramesV1.Point0590.outputs_defined,SourceMainFramesV1.Point0590.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0591.input,SourceMainFramesV1.Point0591.outputs,SourceMainFramesV1.Point0591.input_defined,SourceMainFramesV1.Point0591.outputs_defined,SourceMainFramesV1.Point0591.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0592.input,SourceMainFramesV1.Point0592.outputs,SourceMainFramesV1.Point0592.input_defined,SourceMainFramesV1.Point0592.outputs_defined,SourceMainFramesV1.Point0592.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0593.input,SourceMainFramesV1.Point0593.outputs,SourceMainFramesV1.Point0593.input_defined,SourceMainFramesV1.Point0593.outputs_defined,SourceMainFramesV1.Point0593.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0594.input,SourceMainFramesV1.Point0594.outputs,SourceMainFramesV1.Point0594.input_defined,SourceMainFramesV1.Point0594.outputs_defined,SourceMainFramesV1.Point0594.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0595.input,SourceMainFramesV1.Point0595.outputs,SourceMainFramesV1.Point0595.input_defined,SourceMainFramesV1.Point0595.outputs_defined,SourceMainFramesV1.Point0595.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0596.input,SourceMainFramesV1.Point0596.outputs,SourceMainFramesV1.Point0596.input_defined,SourceMainFramesV1.Point0596.outputs_defined,SourceMainFramesV1.Point0596.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0597.input,SourceMainFramesV1.Point0597.outputs,SourceMainFramesV1.Point0597.input_defined,SourceMainFramesV1.Point0597.outputs_defined,SourceMainFramesV1.Point0597.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0598.input,SourceMainFramesV1.Point0598.outputs,SourceMainFramesV1.Point0598.input_defined,SourceMainFramesV1.Point0598.outputs_defined,SourceMainFramesV1.Point0598.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0599.input,SourceMainFramesV1.Point0599.outputs,SourceMainFramesV1.Point0599.input_defined,SourceMainFramesV1.Point0599.outputs_defined,SourceMainFramesV1.Point0599.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0600.input,SourceMainFramesV1.Point0600.outputs,SourceMainFramesV1.Point0600.input_defined,SourceMainFramesV1.Point0600.outputs_defined,SourceMainFramesV1.Point0600.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0601.input,SourceMainFramesV1.Point0601.outputs,SourceMainFramesV1.Point0601.input_defined,SourceMainFramesV1.Point0601.outputs_defined,SourceMainFramesV1.Point0601.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0602.input,SourceMainFramesV1.Point0602.outputs,SourceMainFramesV1.Point0602.input_defined,SourceMainFramesV1.Point0602.outputs_defined,SourceMainFramesV1.Point0602.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0603.input,SourceMainFramesV1.Point0603.outputs,SourceMainFramesV1.Point0603.input_defined,SourceMainFramesV1.Point0603.outputs_defined,SourceMainFramesV1.Point0603.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0604.input,SourceMainFramesV1.Point0604.outputs,SourceMainFramesV1.Point0604.input_defined,SourceMainFramesV1.Point0604.outputs_defined,SourceMainFramesV1.Point0604.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0605.input,SourceMainFramesV1.Point0605.outputs,SourceMainFramesV1.Point0605.input_defined,SourceMainFramesV1.Point0605.outputs_defined,SourceMainFramesV1.Point0605.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0606.input,SourceMainFramesV1.Point0606.outputs,SourceMainFramesV1.Point0606.input_defined,SourceMainFramesV1.Point0606.outputs_defined,SourceMainFramesV1.Point0606.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0607.input,SourceMainFramesV1.Point0607.outputs,SourceMainFramesV1.Point0607.input_defined,SourceMainFramesV1.Point0607.outputs_defined,SourceMainFramesV1.Point0607.execution total⟩
end SourceMainFramesV1.Execution18
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution18.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
