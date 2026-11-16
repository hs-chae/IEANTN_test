import SourceMainFramesV1.Point0704
import SourceMainFramesV1.Point0705
import SourceMainFramesV1.Point0706
import SourceMainFramesV1.Point0707
import SourceMainFramesV1.Point0708
import SourceMainFramesV1.Point0709
import SourceMainFramesV1.Point0710
import SourceMainFramesV1.Point0711
import SourceMainFramesV1.Point0712
import SourceMainFramesV1.Point0713
import SourceMainFramesV1.Point0714
import SourceMainFramesV1.Point0715
import SourceMainFramesV1.Point0716
import SourceMainFramesV1.Point0717
import SourceMainFramesV1.Point0718
import SourceMainFramesV1.Point0719
import SourceMainFramesV1.Point0720
import SourceMainFramesV1.Point0721
import SourceMainFramesV1.Point0722
import SourceMainFramesV1.Point0723
import SourceMainFramesV1.Point0724
import SourceMainFramesV1.Point0725
import SourceMainFramesV1.Point0726
import SourceMainFramesV1.Point0727
import SourceMainFramesV1.Point0728
import SourceMainFramesV1.Point0729
import SourceMainFramesV1.Point0730
import SourceMainFramesV1.Point0731
import SourceMainFramesV1.Point0732
import SourceMainFramesV1.Point0733
import SourceMainFramesV1.Point0734
import SourceMainFramesV1.Point0735
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution22
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 704 ≤ i) (upper : i < 736) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0704.input,SourceMainFramesV1.Point0704.outputs,SourceMainFramesV1.Point0704.input_defined,SourceMainFramesV1.Point0704.outputs_defined,SourceMainFramesV1.Point0704.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0705.input,SourceMainFramesV1.Point0705.outputs,SourceMainFramesV1.Point0705.input_defined,SourceMainFramesV1.Point0705.outputs_defined,SourceMainFramesV1.Point0705.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0706.input,SourceMainFramesV1.Point0706.outputs,SourceMainFramesV1.Point0706.input_defined,SourceMainFramesV1.Point0706.outputs_defined,SourceMainFramesV1.Point0706.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0707.input,SourceMainFramesV1.Point0707.outputs,SourceMainFramesV1.Point0707.input_defined,SourceMainFramesV1.Point0707.outputs_defined,SourceMainFramesV1.Point0707.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0708.input,SourceMainFramesV1.Point0708.outputs,SourceMainFramesV1.Point0708.input_defined,SourceMainFramesV1.Point0708.outputs_defined,SourceMainFramesV1.Point0708.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0709.input,SourceMainFramesV1.Point0709.outputs,SourceMainFramesV1.Point0709.input_defined,SourceMainFramesV1.Point0709.outputs_defined,SourceMainFramesV1.Point0709.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0710.input,SourceMainFramesV1.Point0710.outputs,SourceMainFramesV1.Point0710.input_defined,SourceMainFramesV1.Point0710.outputs_defined,SourceMainFramesV1.Point0710.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0711.input,SourceMainFramesV1.Point0711.outputs,SourceMainFramesV1.Point0711.input_defined,SourceMainFramesV1.Point0711.outputs_defined,SourceMainFramesV1.Point0711.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0712.input,SourceMainFramesV1.Point0712.outputs,SourceMainFramesV1.Point0712.input_defined,SourceMainFramesV1.Point0712.outputs_defined,SourceMainFramesV1.Point0712.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0713.input,SourceMainFramesV1.Point0713.outputs,SourceMainFramesV1.Point0713.input_defined,SourceMainFramesV1.Point0713.outputs_defined,SourceMainFramesV1.Point0713.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0714.input,SourceMainFramesV1.Point0714.outputs,SourceMainFramesV1.Point0714.input_defined,SourceMainFramesV1.Point0714.outputs_defined,SourceMainFramesV1.Point0714.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0715.input,SourceMainFramesV1.Point0715.outputs,SourceMainFramesV1.Point0715.input_defined,SourceMainFramesV1.Point0715.outputs_defined,SourceMainFramesV1.Point0715.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0716.input,SourceMainFramesV1.Point0716.outputs,SourceMainFramesV1.Point0716.input_defined,SourceMainFramesV1.Point0716.outputs_defined,SourceMainFramesV1.Point0716.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0717.input,SourceMainFramesV1.Point0717.outputs,SourceMainFramesV1.Point0717.input_defined,SourceMainFramesV1.Point0717.outputs_defined,SourceMainFramesV1.Point0717.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0718.input,SourceMainFramesV1.Point0718.outputs,SourceMainFramesV1.Point0718.input_defined,SourceMainFramesV1.Point0718.outputs_defined,SourceMainFramesV1.Point0718.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0719.input,SourceMainFramesV1.Point0719.outputs,SourceMainFramesV1.Point0719.input_defined,SourceMainFramesV1.Point0719.outputs_defined,SourceMainFramesV1.Point0719.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0720.input,SourceMainFramesV1.Point0720.outputs,SourceMainFramesV1.Point0720.input_defined,SourceMainFramesV1.Point0720.outputs_defined,SourceMainFramesV1.Point0720.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0721.input,SourceMainFramesV1.Point0721.outputs,SourceMainFramesV1.Point0721.input_defined,SourceMainFramesV1.Point0721.outputs_defined,SourceMainFramesV1.Point0721.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0722.input,SourceMainFramesV1.Point0722.outputs,SourceMainFramesV1.Point0722.input_defined,SourceMainFramesV1.Point0722.outputs_defined,SourceMainFramesV1.Point0722.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0723.input,SourceMainFramesV1.Point0723.outputs,SourceMainFramesV1.Point0723.input_defined,SourceMainFramesV1.Point0723.outputs_defined,SourceMainFramesV1.Point0723.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0724.input,SourceMainFramesV1.Point0724.outputs,SourceMainFramesV1.Point0724.input_defined,SourceMainFramesV1.Point0724.outputs_defined,SourceMainFramesV1.Point0724.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0725.input,SourceMainFramesV1.Point0725.outputs,SourceMainFramesV1.Point0725.input_defined,SourceMainFramesV1.Point0725.outputs_defined,SourceMainFramesV1.Point0725.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0726.input,SourceMainFramesV1.Point0726.outputs,SourceMainFramesV1.Point0726.input_defined,SourceMainFramesV1.Point0726.outputs_defined,SourceMainFramesV1.Point0726.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0727.input,SourceMainFramesV1.Point0727.outputs,SourceMainFramesV1.Point0727.input_defined,SourceMainFramesV1.Point0727.outputs_defined,SourceMainFramesV1.Point0727.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0728.input,SourceMainFramesV1.Point0728.outputs,SourceMainFramesV1.Point0728.input_defined,SourceMainFramesV1.Point0728.outputs_defined,SourceMainFramesV1.Point0728.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0729.input,SourceMainFramesV1.Point0729.outputs,SourceMainFramesV1.Point0729.input_defined,SourceMainFramesV1.Point0729.outputs_defined,SourceMainFramesV1.Point0729.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0730.input,SourceMainFramesV1.Point0730.outputs,SourceMainFramesV1.Point0730.input_defined,SourceMainFramesV1.Point0730.outputs_defined,SourceMainFramesV1.Point0730.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0731.input,SourceMainFramesV1.Point0731.outputs,SourceMainFramesV1.Point0731.input_defined,SourceMainFramesV1.Point0731.outputs_defined,SourceMainFramesV1.Point0731.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0732.input,SourceMainFramesV1.Point0732.outputs,SourceMainFramesV1.Point0732.input_defined,SourceMainFramesV1.Point0732.outputs_defined,SourceMainFramesV1.Point0732.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0733.input,SourceMainFramesV1.Point0733.outputs,SourceMainFramesV1.Point0733.input_defined,SourceMainFramesV1.Point0733.outputs_defined,SourceMainFramesV1.Point0733.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0734.input,SourceMainFramesV1.Point0734.outputs,SourceMainFramesV1.Point0734.input_defined,SourceMainFramesV1.Point0734.outputs_defined,SourceMainFramesV1.Point0734.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0735.input,SourceMainFramesV1.Point0735.outputs,SourceMainFramesV1.Point0735.input_defined,SourceMainFramesV1.Point0735.outputs_defined,SourceMainFramesV1.Point0735.execution total⟩
end SourceMainFramesV1.Execution22
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution22.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
