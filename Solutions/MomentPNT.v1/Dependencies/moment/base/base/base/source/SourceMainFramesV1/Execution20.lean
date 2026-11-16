import SourceMainFramesV1.Point0640
import SourceMainFramesV1.Point0641
import SourceMainFramesV1.Point0642
import SourceMainFramesV1.Point0643
import SourceMainFramesV1.Point0644
import SourceMainFramesV1.Point0645
import SourceMainFramesV1.Point0646
import SourceMainFramesV1.Point0647
import SourceMainFramesV1.Point0648
import SourceMainFramesV1.Point0649
import SourceMainFramesV1.Point0650
import SourceMainFramesV1.Point0651
import SourceMainFramesV1.Point0652
import SourceMainFramesV1.Point0653
import SourceMainFramesV1.Point0654
import SourceMainFramesV1.Point0655
import SourceMainFramesV1.Point0656
import SourceMainFramesV1.Point0657
import SourceMainFramesV1.Point0658
import SourceMainFramesV1.Point0659
import SourceMainFramesV1.Point0660
import SourceMainFramesV1.Point0661
import SourceMainFramesV1.Point0662
import SourceMainFramesV1.Point0663
import SourceMainFramesV1.Point0664
import SourceMainFramesV1.Point0665
import SourceMainFramesV1.Point0666
import SourceMainFramesV1.Point0667
import SourceMainFramesV1.Point0668
import SourceMainFramesV1.Point0669
import SourceMainFramesV1.Point0670
import SourceMainFramesV1.Point0671
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution20
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 640 ≤ i) (upper : i < 672) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0640.input,SourceMainFramesV1.Point0640.outputs,SourceMainFramesV1.Point0640.input_defined,SourceMainFramesV1.Point0640.outputs_defined,SourceMainFramesV1.Point0640.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0641.input,SourceMainFramesV1.Point0641.outputs,SourceMainFramesV1.Point0641.input_defined,SourceMainFramesV1.Point0641.outputs_defined,SourceMainFramesV1.Point0641.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0642.input,SourceMainFramesV1.Point0642.outputs,SourceMainFramesV1.Point0642.input_defined,SourceMainFramesV1.Point0642.outputs_defined,SourceMainFramesV1.Point0642.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0643.input,SourceMainFramesV1.Point0643.outputs,SourceMainFramesV1.Point0643.input_defined,SourceMainFramesV1.Point0643.outputs_defined,SourceMainFramesV1.Point0643.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0644.input,SourceMainFramesV1.Point0644.outputs,SourceMainFramesV1.Point0644.input_defined,SourceMainFramesV1.Point0644.outputs_defined,SourceMainFramesV1.Point0644.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0645.input,SourceMainFramesV1.Point0645.outputs,SourceMainFramesV1.Point0645.input_defined,SourceMainFramesV1.Point0645.outputs_defined,SourceMainFramesV1.Point0645.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0646.input,SourceMainFramesV1.Point0646.outputs,SourceMainFramesV1.Point0646.input_defined,SourceMainFramesV1.Point0646.outputs_defined,SourceMainFramesV1.Point0646.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0647.input,SourceMainFramesV1.Point0647.outputs,SourceMainFramesV1.Point0647.input_defined,SourceMainFramesV1.Point0647.outputs_defined,SourceMainFramesV1.Point0647.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0648.input,SourceMainFramesV1.Point0648.outputs,SourceMainFramesV1.Point0648.input_defined,SourceMainFramesV1.Point0648.outputs_defined,SourceMainFramesV1.Point0648.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0649.input,SourceMainFramesV1.Point0649.outputs,SourceMainFramesV1.Point0649.input_defined,SourceMainFramesV1.Point0649.outputs_defined,SourceMainFramesV1.Point0649.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0650.input,SourceMainFramesV1.Point0650.outputs,SourceMainFramesV1.Point0650.input_defined,SourceMainFramesV1.Point0650.outputs_defined,SourceMainFramesV1.Point0650.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0651.input,SourceMainFramesV1.Point0651.outputs,SourceMainFramesV1.Point0651.input_defined,SourceMainFramesV1.Point0651.outputs_defined,SourceMainFramesV1.Point0651.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0652.input,SourceMainFramesV1.Point0652.outputs,SourceMainFramesV1.Point0652.input_defined,SourceMainFramesV1.Point0652.outputs_defined,SourceMainFramesV1.Point0652.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0653.input,SourceMainFramesV1.Point0653.outputs,SourceMainFramesV1.Point0653.input_defined,SourceMainFramesV1.Point0653.outputs_defined,SourceMainFramesV1.Point0653.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0654.input,SourceMainFramesV1.Point0654.outputs,SourceMainFramesV1.Point0654.input_defined,SourceMainFramesV1.Point0654.outputs_defined,SourceMainFramesV1.Point0654.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0655.input,SourceMainFramesV1.Point0655.outputs,SourceMainFramesV1.Point0655.input_defined,SourceMainFramesV1.Point0655.outputs_defined,SourceMainFramesV1.Point0655.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0656.input,SourceMainFramesV1.Point0656.outputs,SourceMainFramesV1.Point0656.input_defined,SourceMainFramesV1.Point0656.outputs_defined,SourceMainFramesV1.Point0656.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0657.input,SourceMainFramesV1.Point0657.outputs,SourceMainFramesV1.Point0657.input_defined,SourceMainFramesV1.Point0657.outputs_defined,SourceMainFramesV1.Point0657.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0658.input,SourceMainFramesV1.Point0658.outputs,SourceMainFramesV1.Point0658.input_defined,SourceMainFramesV1.Point0658.outputs_defined,SourceMainFramesV1.Point0658.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0659.input,SourceMainFramesV1.Point0659.outputs,SourceMainFramesV1.Point0659.input_defined,SourceMainFramesV1.Point0659.outputs_defined,SourceMainFramesV1.Point0659.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0660.input,SourceMainFramesV1.Point0660.outputs,SourceMainFramesV1.Point0660.input_defined,SourceMainFramesV1.Point0660.outputs_defined,SourceMainFramesV1.Point0660.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0661.input,SourceMainFramesV1.Point0661.outputs,SourceMainFramesV1.Point0661.input_defined,SourceMainFramesV1.Point0661.outputs_defined,SourceMainFramesV1.Point0661.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0662.input,SourceMainFramesV1.Point0662.outputs,SourceMainFramesV1.Point0662.input_defined,SourceMainFramesV1.Point0662.outputs_defined,SourceMainFramesV1.Point0662.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0663.input,SourceMainFramesV1.Point0663.outputs,SourceMainFramesV1.Point0663.input_defined,SourceMainFramesV1.Point0663.outputs_defined,SourceMainFramesV1.Point0663.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0664.input,SourceMainFramesV1.Point0664.outputs,SourceMainFramesV1.Point0664.input_defined,SourceMainFramesV1.Point0664.outputs_defined,SourceMainFramesV1.Point0664.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0665.input,SourceMainFramesV1.Point0665.outputs,SourceMainFramesV1.Point0665.input_defined,SourceMainFramesV1.Point0665.outputs_defined,SourceMainFramesV1.Point0665.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0666.input,SourceMainFramesV1.Point0666.outputs,SourceMainFramesV1.Point0666.input_defined,SourceMainFramesV1.Point0666.outputs_defined,SourceMainFramesV1.Point0666.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0667.input,SourceMainFramesV1.Point0667.outputs,SourceMainFramesV1.Point0667.input_defined,SourceMainFramesV1.Point0667.outputs_defined,SourceMainFramesV1.Point0667.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0668.input,SourceMainFramesV1.Point0668.outputs,SourceMainFramesV1.Point0668.input_defined,SourceMainFramesV1.Point0668.outputs_defined,SourceMainFramesV1.Point0668.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0669.input,SourceMainFramesV1.Point0669.outputs,SourceMainFramesV1.Point0669.input_defined,SourceMainFramesV1.Point0669.outputs_defined,SourceMainFramesV1.Point0669.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0670.input,SourceMainFramesV1.Point0670.outputs,SourceMainFramesV1.Point0670.input_defined,SourceMainFramesV1.Point0670.outputs_defined,SourceMainFramesV1.Point0670.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0671.input,SourceMainFramesV1.Point0671.outputs,SourceMainFramesV1.Point0671.input_defined,SourceMainFramesV1.Point0671.outputs_defined,SourceMainFramesV1.Point0671.execution total⟩
end SourceMainFramesV1.Execution20
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution20.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
