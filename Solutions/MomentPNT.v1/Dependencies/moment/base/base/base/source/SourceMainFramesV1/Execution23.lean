import SourceMainFramesV1.Point0736
import SourceMainFramesV1.Point0737
import SourceMainFramesV1.Point0738
import SourceMainFramesV1.Point0739
import SourceMainFramesV1.Point0740
import SourceMainFramesV1.Point0741
import SourceMainFramesV1.Point0742
import SourceMainFramesV1.Point0743
import SourceMainFramesV1.Point0744
import SourceMainFramesV1.Point0745
import SourceMainFramesV1.Point0746
import SourceMainFramesV1.Point0747
import SourceMainFramesV1.Point0748
import SourceMainFramesV1.Point0749
import SourceMainFramesV1.Point0750
import SourceMainFramesV1.Point0751
import SourceMainFramesV1.Point0752
import SourceMainFramesV1.Point0753
import SourceMainFramesV1.Point0754
import SourceMainFramesV1.Point0755
import SourceMainFramesV1.Point0756
import SourceMainFramesV1.Point0757
import SourceMainFramesV1.Point0758
import SourceMainFramesV1.Point0759
import SourceMainFramesV1.Point0760
import SourceMainFramesV1.Point0761
import SourceMainFramesV1.Point0762
import SourceMainFramesV1.Point0763
import SourceMainFramesV1.Point0764
import SourceMainFramesV1.Point0765
import SourceMainFramesV1.Point0766
import SourceMainFramesV1.Point0767
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution23
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 736 ≤ i) (upper : i < 768) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0736.input,SourceMainFramesV1.Point0736.outputs,SourceMainFramesV1.Point0736.input_defined,SourceMainFramesV1.Point0736.outputs_defined,SourceMainFramesV1.Point0736.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0737.input,SourceMainFramesV1.Point0737.outputs,SourceMainFramesV1.Point0737.input_defined,SourceMainFramesV1.Point0737.outputs_defined,SourceMainFramesV1.Point0737.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0738.input,SourceMainFramesV1.Point0738.outputs,SourceMainFramesV1.Point0738.input_defined,SourceMainFramesV1.Point0738.outputs_defined,SourceMainFramesV1.Point0738.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0739.input,SourceMainFramesV1.Point0739.outputs,SourceMainFramesV1.Point0739.input_defined,SourceMainFramesV1.Point0739.outputs_defined,SourceMainFramesV1.Point0739.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0740.input,SourceMainFramesV1.Point0740.outputs,SourceMainFramesV1.Point0740.input_defined,SourceMainFramesV1.Point0740.outputs_defined,SourceMainFramesV1.Point0740.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0741.input,SourceMainFramesV1.Point0741.outputs,SourceMainFramesV1.Point0741.input_defined,SourceMainFramesV1.Point0741.outputs_defined,SourceMainFramesV1.Point0741.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0742.input,SourceMainFramesV1.Point0742.outputs,SourceMainFramesV1.Point0742.input_defined,SourceMainFramesV1.Point0742.outputs_defined,SourceMainFramesV1.Point0742.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0743.input,SourceMainFramesV1.Point0743.outputs,SourceMainFramesV1.Point0743.input_defined,SourceMainFramesV1.Point0743.outputs_defined,SourceMainFramesV1.Point0743.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0744.input,SourceMainFramesV1.Point0744.outputs,SourceMainFramesV1.Point0744.input_defined,SourceMainFramesV1.Point0744.outputs_defined,SourceMainFramesV1.Point0744.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0745.input,SourceMainFramesV1.Point0745.outputs,SourceMainFramesV1.Point0745.input_defined,SourceMainFramesV1.Point0745.outputs_defined,SourceMainFramesV1.Point0745.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0746.input,SourceMainFramesV1.Point0746.outputs,SourceMainFramesV1.Point0746.input_defined,SourceMainFramesV1.Point0746.outputs_defined,SourceMainFramesV1.Point0746.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0747.input,SourceMainFramesV1.Point0747.outputs,SourceMainFramesV1.Point0747.input_defined,SourceMainFramesV1.Point0747.outputs_defined,SourceMainFramesV1.Point0747.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0748.input,SourceMainFramesV1.Point0748.outputs,SourceMainFramesV1.Point0748.input_defined,SourceMainFramesV1.Point0748.outputs_defined,SourceMainFramesV1.Point0748.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0749.input,SourceMainFramesV1.Point0749.outputs,SourceMainFramesV1.Point0749.input_defined,SourceMainFramesV1.Point0749.outputs_defined,SourceMainFramesV1.Point0749.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0750.input,SourceMainFramesV1.Point0750.outputs,SourceMainFramesV1.Point0750.input_defined,SourceMainFramesV1.Point0750.outputs_defined,SourceMainFramesV1.Point0750.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0751.input,SourceMainFramesV1.Point0751.outputs,SourceMainFramesV1.Point0751.input_defined,SourceMainFramesV1.Point0751.outputs_defined,SourceMainFramesV1.Point0751.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0752.input,SourceMainFramesV1.Point0752.outputs,SourceMainFramesV1.Point0752.input_defined,SourceMainFramesV1.Point0752.outputs_defined,SourceMainFramesV1.Point0752.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0753.input,SourceMainFramesV1.Point0753.outputs,SourceMainFramesV1.Point0753.input_defined,SourceMainFramesV1.Point0753.outputs_defined,SourceMainFramesV1.Point0753.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0754.input,SourceMainFramesV1.Point0754.outputs,SourceMainFramesV1.Point0754.input_defined,SourceMainFramesV1.Point0754.outputs_defined,SourceMainFramesV1.Point0754.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0755.input,SourceMainFramesV1.Point0755.outputs,SourceMainFramesV1.Point0755.input_defined,SourceMainFramesV1.Point0755.outputs_defined,SourceMainFramesV1.Point0755.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0756.input,SourceMainFramesV1.Point0756.outputs,SourceMainFramesV1.Point0756.input_defined,SourceMainFramesV1.Point0756.outputs_defined,SourceMainFramesV1.Point0756.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0757.input,SourceMainFramesV1.Point0757.outputs,SourceMainFramesV1.Point0757.input_defined,SourceMainFramesV1.Point0757.outputs_defined,SourceMainFramesV1.Point0757.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0758.input,SourceMainFramesV1.Point0758.outputs,SourceMainFramesV1.Point0758.input_defined,SourceMainFramesV1.Point0758.outputs_defined,SourceMainFramesV1.Point0758.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0759.input,SourceMainFramesV1.Point0759.outputs,SourceMainFramesV1.Point0759.input_defined,SourceMainFramesV1.Point0759.outputs_defined,SourceMainFramesV1.Point0759.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0760.input,SourceMainFramesV1.Point0760.outputs,SourceMainFramesV1.Point0760.input_defined,SourceMainFramesV1.Point0760.outputs_defined,SourceMainFramesV1.Point0760.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0761.input,SourceMainFramesV1.Point0761.outputs,SourceMainFramesV1.Point0761.input_defined,SourceMainFramesV1.Point0761.outputs_defined,SourceMainFramesV1.Point0761.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0762.input,SourceMainFramesV1.Point0762.outputs,SourceMainFramesV1.Point0762.input_defined,SourceMainFramesV1.Point0762.outputs_defined,SourceMainFramesV1.Point0762.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0763.input,SourceMainFramesV1.Point0763.outputs,SourceMainFramesV1.Point0763.input_defined,SourceMainFramesV1.Point0763.outputs_defined,SourceMainFramesV1.Point0763.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0764.input,SourceMainFramesV1.Point0764.outputs,SourceMainFramesV1.Point0764.input_defined,SourceMainFramesV1.Point0764.outputs_defined,SourceMainFramesV1.Point0764.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0765.input,SourceMainFramesV1.Point0765.outputs,SourceMainFramesV1.Point0765.input_defined,SourceMainFramesV1.Point0765.outputs_defined,SourceMainFramesV1.Point0765.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0766.input,SourceMainFramesV1.Point0766.outputs,SourceMainFramesV1.Point0766.input_defined,SourceMainFramesV1.Point0766.outputs_defined,SourceMainFramesV1.Point0766.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0767.input,SourceMainFramesV1.Point0767.outputs,SourceMainFramesV1.Point0767.input_defined,SourceMainFramesV1.Point0767.outputs_defined,SourceMainFramesV1.Point0767.execution total⟩
end SourceMainFramesV1.Execution23
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution23.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
