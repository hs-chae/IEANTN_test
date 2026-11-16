import SourceMainFramesV1.Point0672
import SourceMainFramesV1.Point0673
import SourceMainFramesV1.Point0674
import SourceMainFramesV1.Point0675
import SourceMainFramesV1.Point0676
import SourceMainFramesV1.Point0677
import SourceMainFramesV1.Point0678
import SourceMainFramesV1.Point0679
import SourceMainFramesV1.Point0680
import SourceMainFramesV1.Point0681
import SourceMainFramesV1.Point0682
import SourceMainFramesV1.Point0683
import SourceMainFramesV1.Point0684
import SourceMainFramesV1.Point0685
import SourceMainFramesV1.Point0686
import SourceMainFramesV1.Point0687
import SourceMainFramesV1.Point0688
import SourceMainFramesV1.Point0689
import SourceMainFramesV1.Point0690
import SourceMainFramesV1.Point0691
import SourceMainFramesV1.Point0692
import SourceMainFramesV1.Point0693
import SourceMainFramesV1.Point0694
import SourceMainFramesV1.Point0695
import SourceMainFramesV1.Point0696
import SourceMainFramesV1.Point0697
import SourceMainFramesV1.Point0698
import SourceMainFramesV1.Point0699
import SourceMainFramesV1.Point0700
import SourceMainFramesV1.Point0701
import SourceMainFramesV1.Point0702
import SourceMainFramesV1.Point0703
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution21
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 672 ≤ i) (upper : i < 704) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0672.input,SourceMainFramesV1.Point0672.outputs,SourceMainFramesV1.Point0672.input_defined,SourceMainFramesV1.Point0672.outputs_defined,SourceMainFramesV1.Point0672.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0673.input,SourceMainFramesV1.Point0673.outputs,SourceMainFramesV1.Point0673.input_defined,SourceMainFramesV1.Point0673.outputs_defined,SourceMainFramesV1.Point0673.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0674.input,SourceMainFramesV1.Point0674.outputs,SourceMainFramesV1.Point0674.input_defined,SourceMainFramesV1.Point0674.outputs_defined,SourceMainFramesV1.Point0674.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0675.input,SourceMainFramesV1.Point0675.outputs,SourceMainFramesV1.Point0675.input_defined,SourceMainFramesV1.Point0675.outputs_defined,SourceMainFramesV1.Point0675.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0676.input,SourceMainFramesV1.Point0676.outputs,SourceMainFramesV1.Point0676.input_defined,SourceMainFramesV1.Point0676.outputs_defined,SourceMainFramesV1.Point0676.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0677.input,SourceMainFramesV1.Point0677.outputs,SourceMainFramesV1.Point0677.input_defined,SourceMainFramesV1.Point0677.outputs_defined,SourceMainFramesV1.Point0677.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0678.input,SourceMainFramesV1.Point0678.outputs,SourceMainFramesV1.Point0678.input_defined,SourceMainFramesV1.Point0678.outputs_defined,SourceMainFramesV1.Point0678.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0679.input,SourceMainFramesV1.Point0679.outputs,SourceMainFramesV1.Point0679.input_defined,SourceMainFramesV1.Point0679.outputs_defined,SourceMainFramesV1.Point0679.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0680.input,SourceMainFramesV1.Point0680.outputs,SourceMainFramesV1.Point0680.input_defined,SourceMainFramesV1.Point0680.outputs_defined,SourceMainFramesV1.Point0680.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0681.input,SourceMainFramesV1.Point0681.outputs,SourceMainFramesV1.Point0681.input_defined,SourceMainFramesV1.Point0681.outputs_defined,SourceMainFramesV1.Point0681.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0682.input,SourceMainFramesV1.Point0682.outputs,SourceMainFramesV1.Point0682.input_defined,SourceMainFramesV1.Point0682.outputs_defined,SourceMainFramesV1.Point0682.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0683.input,SourceMainFramesV1.Point0683.outputs,SourceMainFramesV1.Point0683.input_defined,SourceMainFramesV1.Point0683.outputs_defined,SourceMainFramesV1.Point0683.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0684.input,SourceMainFramesV1.Point0684.outputs,SourceMainFramesV1.Point0684.input_defined,SourceMainFramesV1.Point0684.outputs_defined,SourceMainFramesV1.Point0684.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0685.input,SourceMainFramesV1.Point0685.outputs,SourceMainFramesV1.Point0685.input_defined,SourceMainFramesV1.Point0685.outputs_defined,SourceMainFramesV1.Point0685.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0686.input,SourceMainFramesV1.Point0686.outputs,SourceMainFramesV1.Point0686.input_defined,SourceMainFramesV1.Point0686.outputs_defined,SourceMainFramesV1.Point0686.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0687.input,SourceMainFramesV1.Point0687.outputs,SourceMainFramesV1.Point0687.input_defined,SourceMainFramesV1.Point0687.outputs_defined,SourceMainFramesV1.Point0687.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0688.input,SourceMainFramesV1.Point0688.outputs,SourceMainFramesV1.Point0688.input_defined,SourceMainFramesV1.Point0688.outputs_defined,SourceMainFramesV1.Point0688.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0689.input,SourceMainFramesV1.Point0689.outputs,SourceMainFramesV1.Point0689.input_defined,SourceMainFramesV1.Point0689.outputs_defined,SourceMainFramesV1.Point0689.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0690.input,SourceMainFramesV1.Point0690.outputs,SourceMainFramesV1.Point0690.input_defined,SourceMainFramesV1.Point0690.outputs_defined,SourceMainFramesV1.Point0690.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0691.input,SourceMainFramesV1.Point0691.outputs,SourceMainFramesV1.Point0691.input_defined,SourceMainFramesV1.Point0691.outputs_defined,SourceMainFramesV1.Point0691.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0692.input,SourceMainFramesV1.Point0692.outputs,SourceMainFramesV1.Point0692.input_defined,SourceMainFramesV1.Point0692.outputs_defined,SourceMainFramesV1.Point0692.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0693.input,SourceMainFramesV1.Point0693.outputs,SourceMainFramesV1.Point0693.input_defined,SourceMainFramesV1.Point0693.outputs_defined,SourceMainFramesV1.Point0693.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0694.input,SourceMainFramesV1.Point0694.outputs,SourceMainFramesV1.Point0694.input_defined,SourceMainFramesV1.Point0694.outputs_defined,SourceMainFramesV1.Point0694.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0695.input,SourceMainFramesV1.Point0695.outputs,SourceMainFramesV1.Point0695.input_defined,SourceMainFramesV1.Point0695.outputs_defined,SourceMainFramesV1.Point0695.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0696.input,SourceMainFramesV1.Point0696.outputs,SourceMainFramesV1.Point0696.input_defined,SourceMainFramesV1.Point0696.outputs_defined,SourceMainFramesV1.Point0696.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0697.input,SourceMainFramesV1.Point0697.outputs,SourceMainFramesV1.Point0697.input_defined,SourceMainFramesV1.Point0697.outputs_defined,SourceMainFramesV1.Point0697.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0698.input,SourceMainFramesV1.Point0698.outputs,SourceMainFramesV1.Point0698.input_defined,SourceMainFramesV1.Point0698.outputs_defined,SourceMainFramesV1.Point0698.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0699.input,SourceMainFramesV1.Point0699.outputs,SourceMainFramesV1.Point0699.input_defined,SourceMainFramesV1.Point0699.outputs_defined,SourceMainFramesV1.Point0699.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0700.input,SourceMainFramesV1.Point0700.outputs,SourceMainFramesV1.Point0700.input_defined,SourceMainFramesV1.Point0700.outputs_defined,SourceMainFramesV1.Point0700.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0701.input,SourceMainFramesV1.Point0701.outputs,SourceMainFramesV1.Point0701.input_defined,SourceMainFramesV1.Point0701.outputs_defined,SourceMainFramesV1.Point0701.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0702.input,SourceMainFramesV1.Point0702.outputs,SourceMainFramesV1.Point0702.input_defined,SourceMainFramesV1.Point0702.outputs_defined,SourceMainFramesV1.Point0702.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0703.input,SourceMainFramesV1.Point0703.outputs,SourceMainFramesV1.Point0703.input_defined,SourceMainFramesV1.Point0703.outputs_defined,SourceMainFramesV1.Point0703.execution total⟩
end SourceMainFramesV1.Execution21
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution21.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
