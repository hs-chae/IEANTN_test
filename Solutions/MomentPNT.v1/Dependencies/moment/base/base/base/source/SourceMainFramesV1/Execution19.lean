import SourceMainFramesV1.Point0608
import SourceMainFramesV1.Point0609
import SourceMainFramesV1.Point0610
import SourceMainFramesV1.Point0611
import SourceMainFramesV1.Point0612
import SourceMainFramesV1.Point0613
import SourceMainFramesV1.Point0614
import SourceMainFramesV1.Point0615
import SourceMainFramesV1.Point0616
import SourceMainFramesV1.Point0617
import SourceMainFramesV1.Point0618
import SourceMainFramesV1.Point0619
import SourceMainFramesV1.Point0620
import SourceMainFramesV1.Point0621
import SourceMainFramesV1.Point0622
import SourceMainFramesV1.Point0623
import SourceMainFramesV1.Point0624
import SourceMainFramesV1.Point0625
import SourceMainFramesV1.Point0626
import SourceMainFramesV1.Point0627
import SourceMainFramesV1.Point0628
import SourceMainFramesV1.Point0629
import SourceMainFramesV1.Point0630
import SourceMainFramesV1.Point0631
import SourceMainFramesV1.Point0632
import SourceMainFramesV1.Point0633
import SourceMainFramesV1.Point0634
import SourceMainFramesV1.Point0635
import SourceMainFramesV1.Point0636
import SourceMainFramesV1.Point0637
import SourceMainFramesV1.Point0638
import SourceMainFramesV1.Point0639
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution19
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 608 ≤ i) (upper : i < 640) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0608.input,SourceMainFramesV1.Point0608.outputs,SourceMainFramesV1.Point0608.input_defined,SourceMainFramesV1.Point0608.outputs_defined,SourceMainFramesV1.Point0608.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0609.input,SourceMainFramesV1.Point0609.outputs,SourceMainFramesV1.Point0609.input_defined,SourceMainFramesV1.Point0609.outputs_defined,SourceMainFramesV1.Point0609.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0610.input,SourceMainFramesV1.Point0610.outputs,SourceMainFramesV1.Point0610.input_defined,SourceMainFramesV1.Point0610.outputs_defined,SourceMainFramesV1.Point0610.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0611.input,SourceMainFramesV1.Point0611.outputs,SourceMainFramesV1.Point0611.input_defined,SourceMainFramesV1.Point0611.outputs_defined,SourceMainFramesV1.Point0611.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0612.input,SourceMainFramesV1.Point0612.outputs,SourceMainFramesV1.Point0612.input_defined,SourceMainFramesV1.Point0612.outputs_defined,SourceMainFramesV1.Point0612.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0613.input,SourceMainFramesV1.Point0613.outputs,SourceMainFramesV1.Point0613.input_defined,SourceMainFramesV1.Point0613.outputs_defined,SourceMainFramesV1.Point0613.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0614.input,SourceMainFramesV1.Point0614.outputs,SourceMainFramesV1.Point0614.input_defined,SourceMainFramesV1.Point0614.outputs_defined,SourceMainFramesV1.Point0614.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0615.input,SourceMainFramesV1.Point0615.outputs,SourceMainFramesV1.Point0615.input_defined,SourceMainFramesV1.Point0615.outputs_defined,SourceMainFramesV1.Point0615.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0616.input,SourceMainFramesV1.Point0616.outputs,SourceMainFramesV1.Point0616.input_defined,SourceMainFramesV1.Point0616.outputs_defined,SourceMainFramesV1.Point0616.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0617.input,SourceMainFramesV1.Point0617.outputs,SourceMainFramesV1.Point0617.input_defined,SourceMainFramesV1.Point0617.outputs_defined,SourceMainFramesV1.Point0617.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0618.input,SourceMainFramesV1.Point0618.outputs,SourceMainFramesV1.Point0618.input_defined,SourceMainFramesV1.Point0618.outputs_defined,SourceMainFramesV1.Point0618.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0619.input,SourceMainFramesV1.Point0619.outputs,SourceMainFramesV1.Point0619.input_defined,SourceMainFramesV1.Point0619.outputs_defined,SourceMainFramesV1.Point0619.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0620.input,SourceMainFramesV1.Point0620.outputs,SourceMainFramesV1.Point0620.input_defined,SourceMainFramesV1.Point0620.outputs_defined,SourceMainFramesV1.Point0620.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0621.input,SourceMainFramesV1.Point0621.outputs,SourceMainFramesV1.Point0621.input_defined,SourceMainFramesV1.Point0621.outputs_defined,SourceMainFramesV1.Point0621.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0622.input,SourceMainFramesV1.Point0622.outputs,SourceMainFramesV1.Point0622.input_defined,SourceMainFramesV1.Point0622.outputs_defined,SourceMainFramesV1.Point0622.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0623.input,SourceMainFramesV1.Point0623.outputs,SourceMainFramesV1.Point0623.input_defined,SourceMainFramesV1.Point0623.outputs_defined,SourceMainFramesV1.Point0623.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0624.input,SourceMainFramesV1.Point0624.outputs,SourceMainFramesV1.Point0624.input_defined,SourceMainFramesV1.Point0624.outputs_defined,SourceMainFramesV1.Point0624.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0625.input,SourceMainFramesV1.Point0625.outputs,SourceMainFramesV1.Point0625.input_defined,SourceMainFramesV1.Point0625.outputs_defined,SourceMainFramesV1.Point0625.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0626.input,SourceMainFramesV1.Point0626.outputs,SourceMainFramesV1.Point0626.input_defined,SourceMainFramesV1.Point0626.outputs_defined,SourceMainFramesV1.Point0626.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0627.input,SourceMainFramesV1.Point0627.outputs,SourceMainFramesV1.Point0627.input_defined,SourceMainFramesV1.Point0627.outputs_defined,SourceMainFramesV1.Point0627.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0628.input,SourceMainFramesV1.Point0628.outputs,SourceMainFramesV1.Point0628.input_defined,SourceMainFramesV1.Point0628.outputs_defined,SourceMainFramesV1.Point0628.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0629.input,SourceMainFramesV1.Point0629.outputs,SourceMainFramesV1.Point0629.input_defined,SourceMainFramesV1.Point0629.outputs_defined,SourceMainFramesV1.Point0629.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0630.input,SourceMainFramesV1.Point0630.outputs,SourceMainFramesV1.Point0630.input_defined,SourceMainFramesV1.Point0630.outputs_defined,SourceMainFramesV1.Point0630.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0631.input,SourceMainFramesV1.Point0631.outputs,SourceMainFramesV1.Point0631.input_defined,SourceMainFramesV1.Point0631.outputs_defined,SourceMainFramesV1.Point0631.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0632.input,SourceMainFramesV1.Point0632.outputs,SourceMainFramesV1.Point0632.input_defined,SourceMainFramesV1.Point0632.outputs_defined,SourceMainFramesV1.Point0632.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0633.input,SourceMainFramesV1.Point0633.outputs,SourceMainFramesV1.Point0633.input_defined,SourceMainFramesV1.Point0633.outputs_defined,SourceMainFramesV1.Point0633.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0634.input,SourceMainFramesV1.Point0634.outputs,SourceMainFramesV1.Point0634.input_defined,SourceMainFramesV1.Point0634.outputs_defined,SourceMainFramesV1.Point0634.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0635.input,SourceMainFramesV1.Point0635.outputs,SourceMainFramesV1.Point0635.input_defined,SourceMainFramesV1.Point0635.outputs_defined,SourceMainFramesV1.Point0635.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0636.input,SourceMainFramesV1.Point0636.outputs,SourceMainFramesV1.Point0636.input_defined,SourceMainFramesV1.Point0636.outputs_defined,SourceMainFramesV1.Point0636.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0637.input,SourceMainFramesV1.Point0637.outputs,SourceMainFramesV1.Point0637.input_defined,SourceMainFramesV1.Point0637.outputs_defined,SourceMainFramesV1.Point0637.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0638.input,SourceMainFramesV1.Point0638.outputs,SourceMainFramesV1.Point0638.input_defined,SourceMainFramesV1.Point0638.outputs_defined,SourceMainFramesV1.Point0638.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0639.input,SourceMainFramesV1.Point0639.outputs,SourceMainFramesV1.Point0639.input_defined,SourceMainFramesV1.Point0639.outputs_defined,SourceMainFramesV1.Point0639.execution total⟩
end SourceMainFramesV1.Execution19
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution19.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
