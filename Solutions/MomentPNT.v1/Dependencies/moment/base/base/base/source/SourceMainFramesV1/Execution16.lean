import SourceMainFramesV1.Point0512
import SourceMainFramesV1.Point0513
import SourceMainFramesV1.Point0514
import SourceMainFramesV1.Point0515
import SourceMainFramesV1.Point0516
import SourceMainFramesV1.Point0517
import SourceMainFramesV1.Point0518
import SourceMainFramesV1.Point0519
import SourceMainFramesV1.Point0520
import SourceMainFramesV1.Point0521
import SourceMainFramesV1.Point0522
import SourceMainFramesV1.Point0523
import SourceMainFramesV1.Point0524
import SourceMainFramesV1.Point0525
import SourceMainFramesV1.Point0526
import SourceMainFramesV1.Point0527
import SourceMainFramesV1.Point0528
import SourceMainFramesV1.Point0529
import SourceMainFramesV1.Point0530
import SourceMainFramesV1.Point0531
import SourceMainFramesV1.Point0532
import SourceMainFramesV1.Point0533
import SourceMainFramesV1.Point0534
import SourceMainFramesV1.Point0535
import SourceMainFramesV1.Point0536
import SourceMainFramesV1.Point0537
import SourceMainFramesV1.Point0538
import SourceMainFramesV1.Point0539
import SourceMainFramesV1.Point0540
import SourceMainFramesV1.Point0541
import SourceMainFramesV1.Point0542
import SourceMainFramesV1.Point0543
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution16
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 512 ≤ i) (upper : i < 544) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0512.input,SourceMainFramesV1.Point0512.outputs,SourceMainFramesV1.Point0512.input_defined,SourceMainFramesV1.Point0512.outputs_defined,SourceMainFramesV1.Point0512.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0513.input,SourceMainFramesV1.Point0513.outputs,SourceMainFramesV1.Point0513.input_defined,SourceMainFramesV1.Point0513.outputs_defined,SourceMainFramesV1.Point0513.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0514.input,SourceMainFramesV1.Point0514.outputs,SourceMainFramesV1.Point0514.input_defined,SourceMainFramesV1.Point0514.outputs_defined,SourceMainFramesV1.Point0514.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0515.input,SourceMainFramesV1.Point0515.outputs,SourceMainFramesV1.Point0515.input_defined,SourceMainFramesV1.Point0515.outputs_defined,SourceMainFramesV1.Point0515.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0516.input,SourceMainFramesV1.Point0516.outputs,SourceMainFramesV1.Point0516.input_defined,SourceMainFramesV1.Point0516.outputs_defined,SourceMainFramesV1.Point0516.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0517.input,SourceMainFramesV1.Point0517.outputs,SourceMainFramesV1.Point0517.input_defined,SourceMainFramesV1.Point0517.outputs_defined,SourceMainFramesV1.Point0517.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0518.input,SourceMainFramesV1.Point0518.outputs,SourceMainFramesV1.Point0518.input_defined,SourceMainFramesV1.Point0518.outputs_defined,SourceMainFramesV1.Point0518.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0519.input,SourceMainFramesV1.Point0519.outputs,SourceMainFramesV1.Point0519.input_defined,SourceMainFramesV1.Point0519.outputs_defined,SourceMainFramesV1.Point0519.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0520.input,SourceMainFramesV1.Point0520.outputs,SourceMainFramesV1.Point0520.input_defined,SourceMainFramesV1.Point0520.outputs_defined,SourceMainFramesV1.Point0520.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0521.input,SourceMainFramesV1.Point0521.outputs,SourceMainFramesV1.Point0521.input_defined,SourceMainFramesV1.Point0521.outputs_defined,SourceMainFramesV1.Point0521.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0522.input,SourceMainFramesV1.Point0522.outputs,SourceMainFramesV1.Point0522.input_defined,SourceMainFramesV1.Point0522.outputs_defined,SourceMainFramesV1.Point0522.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0523.input,SourceMainFramesV1.Point0523.outputs,SourceMainFramesV1.Point0523.input_defined,SourceMainFramesV1.Point0523.outputs_defined,SourceMainFramesV1.Point0523.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0524.input,SourceMainFramesV1.Point0524.outputs,SourceMainFramesV1.Point0524.input_defined,SourceMainFramesV1.Point0524.outputs_defined,SourceMainFramesV1.Point0524.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0525.input,SourceMainFramesV1.Point0525.outputs,SourceMainFramesV1.Point0525.input_defined,SourceMainFramesV1.Point0525.outputs_defined,SourceMainFramesV1.Point0525.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0526.input,SourceMainFramesV1.Point0526.outputs,SourceMainFramesV1.Point0526.input_defined,SourceMainFramesV1.Point0526.outputs_defined,SourceMainFramesV1.Point0526.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0527.input,SourceMainFramesV1.Point0527.outputs,SourceMainFramesV1.Point0527.input_defined,SourceMainFramesV1.Point0527.outputs_defined,SourceMainFramesV1.Point0527.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0528.input,SourceMainFramesV1.Point0528.outputs,SourceMainFramesV1.Point0528.input_defined,SourceMainFramesV1.Point0528.outputs_defined,SourceMainFramesV1.Point0528.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0529.input,SourceMainFramesV1.Point0529.outputs,SourceMainFramesV1.Point0529.input_defined,SourceMainFramesV1.Point0529.outputs_defined,SourceMainFramesV1.Point0529.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0530.input,SourceMainFramesV1.Point0530.outputs,SourceMainFramesV1.Point0530.input_defined,SourceMainFramesV1.Point0530.outputs_defined,SourceMainFramesV1.Point0530.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0531.input,SourceMainFramesV1.Point0531.outputs,SourceMainFramesV1.Point0531.input_defined,SourceMainFramesV1.Point0531.outputs_defined,SourceMainFramesV1.Point0531.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0532.input,SourceMainFramesV1.Point0532.outputs,SourceMainFramesV1.Point0532.input_defined,SourceMainFramesV1.Point0532.outputs_defined,SourceMainFramesV1.Point0532.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0533.input,SourceMainFramesV1.Point0533.outputs,SourceMainFramesV1.Point0533.input_defined,SourceMainFramesV1.Point0533.outputs_defined,SourceMainFramesV1.Point0533.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0534.input,SourceMainFramesV1.Point0534.outputs,SourceMainFramesV1.Point0534.input_defined,SourceMainFramesV1.Point0534.outputs_defined,SourceMainFramesV1.Point0534.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0535.input,SourceMainFramesV1.Point0535.outputs,SourceMainFramesV1.Point0535.input_defined,SourceMainFramesV1.Point0535.outputs_defined,SourceMainFramesV1.Point0535.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0536.input,SourceMainFramesV1.Point0536.outputs,SourceMainFramesV1.Point0536.input_defined,SourceMainFramesV1.Point0536.outputs_defined,SourceMainFramesV1.Point0536.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0537.input,SourceMainFramesV1.Point0537.outputs,SourceMainFramesV1.Point0537.input_defined,SourceMainFramesV1.Point0537.outputs_defined,SourceMainFramesV1.Point0537.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0538.input,SourceMainFramesV1.Point0538.outputs,SourceMainFramesV1.Point0538.input_defined,SourceMainFramesV1.Point0538.outputs_defined,SourceMainFramesV1.Point0538.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0539.input,SourceMainFramesV1.Point0539.outputs,SourceMainFramesV1.Point0539.input_defined,SourceMainFramesV1.Point0539.outputs_defined,SourceMainFramesV1.Point0539.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0540.input,SourceMainFramesV1.Point0540.outputs,SourceMainFramesV1.Point0540.input_defined,SourceMainFramesV1.Point0540.outputs_defined,SourceMainFramesV1.Point0540.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0541.input,SourceMainFramesV1.Point0541.outputs,SourceMainFramesV1.Point0541.input_defined,SourceMainFramesV1.Point0541.outputs_defined,SourceMainFramesV1.Point0541.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0542.input,SourceMainFramesV1.Point0542.outputs,SourceMainFramesV1.Point0542.input_defined,SourceMainFramesV1.Point0542.outputs_defined,SourceMainFramesV1.Point0542.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0543.input,SourceMainFramesV1.Point0543.outputs,SourceMainFramesV1.Point0543.input_defined,SourceMainFramesV1.Point0543.outputs_defined,SourceMainFramesV1.Point0543.execution total⟩
end SourceMainFramesV1.Execution16
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution16.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
