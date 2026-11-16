import SourceMainFramesV1.Point0352
import SourceMainFramesV1.Point0353
import SourceMainFramesV1.Point0354
import SourceMainFramesV1.Point0355
import SourceMainFramesV1.Point0356
import SourceMainFramesV1.Point0357
import SourceMainFramesV1.Point0358
import SourceMainFramesV1.Point0359
import SourceMainFramesV1.Point0360
import SourceMainFramesV1.Point0361
import SourceMainFramesV1.Point0362
import SourceMainFramesV1.Point0363
import SourceMainFramesV1.Point0364
import SourceMainFramesV1.Point0365
import SourceMainFramesV1.Point0366
import SourceMainFramesV1.Point0367
import SourceMainFramesV1.Point0368
import SourceMainFramesV1.Point0369
import SourceMainFramesV1.Point0370
import SourceMainFramesV1.Point0371
import SourceMainFramesV1.Point0372
import SourceMainFramesV1.Point0373
import SourceMainFramesV1.Point0374
import SourceMainFramesV1.Point0375
import SourceMainFramesV1.Point0376
import SourceMainFramesV1.Point0377
import SourceMainFramesV1.Point0378
import SourceMainFramesV1.Point0379
import SourceMainFramesV1.Point0380
import SourceMainFramesV1.Point0381
import SourceMainFramesV1.Point0382
import SourceMainFramesV1.Point0383
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution11
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 352 ≤ i) (upper : i < 384) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0352.input,SourceMainFramesV1.Point0352.outputs,SourceMainFramesV1.Point0352.input_defined,SourceMainFramesV1.Point0352.outputs_defined,SourceMainFramesV1.Point0352.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0353.input,SourceMainFramesV1.Point0353.outputs,SourceMainFramesV1.Point0353.input_defined,SourceMainFramesV1.Point0353.outputs_defined,SourceMainFramesV1.Point0353.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0354.input,SourceMainFramesV1.Point0354.outputs,SourceMainFramesV1.Point0354.input_defined,SourceMainFramesV1.Point0354.outputs_defined,SourceMainFramesV1.Point0354.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0355.input,SourceMainFramesV1.Point0355.outputs,SourceMainFramesV1.Point0355.input_defined,SourceMainFramesV1.Point0355.outputs_defined,SourceMainFramesV1.Point0355.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0356.input,SourceMainFramesV1.Point0356.outputs,SourceMainFramesV1.Point0356.input_defined,SourceMainFramesV1.Point0356.outputs_defined,SourceMainFramesV1.Point0356.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0357.input,SourceMainFramesV1.Point0357.outputs,SourceMainFramesV1.Point0357.input_defined,SourceMainFramesV1.Point0357.outputs_defined,SourceMainFramesV1.Point0357.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0358.input,SourceMainFramesV1.Point0358.outputs,SourceMainFramesV1.Point0358.input_defined,SourceMainFramesV1.Point0358.outputs_defined,SourceMainFramesV1.Point0358.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0359.input,SourceMainFramesV1.Point0359.outputs,SourceMainFramesV1.Point0359.input_defined,SourceMainFramesV1.Point0359.outputs_defined,SourceMainFramesV1.Point0359.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0360.input,SourceMainFramesV1.Point0360.outputs,SourceMainFramesV1.Point0360.input_defined,SourceMainFramesV1.Point0360.outputs_defined,SourceMainFramesV1.Point0360.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0361.input,SourceMainFramesV1.Point0361.outputs,SourceMainFramesV1.Point0361.input_defined,SourceMainFramesV1.Point0361.outputs_defined,SourceMainFramesV1.Point0361.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0362.input,SourceMainFramesV1.Point0362.outputs,SourceMainFramesV1.Point0362.input_defined,SourceMainFramesV1.Point0362.outputs_defined,SourceMainFramesV1.Point0362.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0363.input,SourceMainFramesV1.Point0363.outputs,SourceMainFramesV1.Point0363.input_defined,SourceMainFramesV1.Point0363.outputs_defined,SourceMainFramesV1.Point0363.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0364.input,SourceMainFramesV1.Point0364.outputs,SourceMainFramesV1.Point0364.input_defined,SourceMainFramesV1.Point0364.outputs_defined,SourceMainFramesV1.Point0364.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0365.input,SourceMainFramesV1.Point0365.outputs,SourceMainFramesV1.Point0365.input_defined,SourceMainFramesV1.Point0365.outputs_defined,SourceMainFramesV1.Point0365.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0366.input,SourceMainFramesV1.Point0366.outputs,SourceMainFramesV1.Point0366.input_defined,SourceMainFramesV1.Point0366.outputs_defined,SourceMainFramesV1.Point0366.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0367.input,SourceMainFramesV1.Point0367.outputs,SourceMainFramesV1.Point0367.input_defined,SourceMainFramesV1.Point0367.outputs_defined,SourceMainFramesV1.Point0367.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0368.input,SourceMainFramesV1.Point0368.outputs,SourceMainFramesV1.Point0368.input_defined,SourceMainFramesV1.Point0368.outputs_defined,SourceMainFramesV1.Point0368.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0369.input,SourceMainFramesV1.Point0369.outputs,SourceMainFramesV1.Point0369.input_defined,SourceMainFramesV1.Point0369.outputs_defined,SourceMainFramesV1.Point0369.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0370.input,SourceMainFramesV1.Point0370.outputs,SourceMainFramesV1.Point0370.input_defined,SourceMainFramesV1.Point0370.outputs_defined,SourceMainFramesV1.Point0370.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0371.input,SourceMainFramesV1.Point0371.outputs,SourceMainFramesV1.Point0371.input_defined,SourceMainFramesV1.Point0371.outputs_defined,SourceMainFramesV1.Point0371.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0372.input,SourceMainFramesV1.Point0372.outputs,SourceMainFramesV1.Point0372.input_defined,SourceMainFramesV1.Point0372.outputs_defined,SourceMainFramesV1.Point0372.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0373.input,SourceMainFramesV1.Point0373.outputs,SourceMainFramesV1.Point0373.input_defined,SourceMainFramesV1.Point0373.outputs_defined,SourceMainFramesV1.Point0373.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0374.input,SourceMainFramesV1.Point0374.outputs,SourceMainFramesV1.Point0374.input_defined,SourceMainFramesV1.Point0374.outputs_defined,SourceMainFramesV1.Point0374.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0375.input,SourceMainFramesV1.Point0375.outputs,SourceMainFramesV1.Point0375.input_defined,SourceMainFramesV1.Point0375.outputs_defined,SourceMainFramesV1.Point0375.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0376.input,SourceMainFramesV1.Point0376.outputs,SourceMainFramesV1.Point0376.input_defined,SourceMainFramesV1.Point0376.outputs_defined,SourceMainFramesV1.Point0376.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0377.input,SourceMainFramesV1.Point0377.outputs,SourceMainFramesV1.Point0377.input_defined,SourceMainFramesV1.Point0377.outputs_defined,SourceMainFramesV1.Point0377.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0378.input,SourceMainFramesV1.Point0378.outputs,SourceMainFramesV1.Point0378.input_defined,SourceMainFramesV1.Point0378.outputs_defined,SourceMainFramesV1.Point0378.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0379.input,SourceMainFramesV1.Point0379.outputs,SourceMainFramesV1.Point0379.input_defined,SourceMainFramesV1.Point0379.outputs_defined,SourceMainFramesV1.Point0379.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0380.input,SourceMainFramesV1.Point0380.outputs,SourceMainFramesV1.Point0380.input_defined,SourceMainFramesV1.Point0380.outputs_defined,SourceMainFramesV1.Point0380.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0381.input,SourceMainFramesV1.Point0381.outputs,SourceMainFramesV1.Point0381.input_defined,SourceMainFramesV1.Point0381.outputs_defined,SourceMainFramesV1.Point0381.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0382.input,SourceMainFramesV1.Point0382.outputs,SourceMainFramesV1.Point0382.input_defined,SourceMainFramesV1.Point0382.outputs_defined,SourceMainFramesV1.Point0382.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0383.input,SourceMainFramesV1.Point0383.outputs,SourceMainFramesV1.Point0383.input_defined,SourceMainFramesV1.Point0383.outputs_defined,SourceMainFramesV1.Point0383.execution total⟩
end SourceMainFramesV1.Execution11
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution11.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
