import SourceMainFramesV1.Point0480
import SourceMainFramesV1.Point0481
import SourceMainFramesV1.Point0482
import SourceMainFramesV1.Point0483
import SourceMainFramesV1.Point0484
import SourceMainFramesV1.Point0485
import SourceMainFramesV1.Point0486
import SourceMainFramesV1.Point0487
import SourceMainFramesV1.Point0488
import SourceMainFramesV1.Point0489
import SourceMainFramesV1.Point0490
import SourceMainFramesV1.Point0491
import SourceMainFramesV1.Point0492
import SourceMainFramesV1.Point0493
import SourceMainFramesV1.Point0494
import SourceMainFramesV1.Point0495
import SourceMainFramesV1.Point0496
import SourceMainFramesV1.Point0497
import SourceMainFramesV1.Point0498
import SourceMainFramesV1.Point0499
import SourceMainFramesV1.Point0500
import SourceMainFramesV1.Point0501
import SourceMainFramesV1.Point0502
import SourceMainFramesV1.Point0503
import SourceMainFramesV1.Point0504
import SourceMainFramesV1.Point0505
import SourceMainFramesV1.Point0506
import SourceMainFramesV1.Point0507
import SourceMainFramesV1.Point0508
import SourceMainFramesV1.Point0509
import SourceMainFramesV1.Point0510
import SourceMainFramesV1.Point0511
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution15
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 480 ≤ i) (upper : i < 512) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0480.input,SourceMainFramesV1.Point0480.outputs,SourceMainFramesV1.Point0480.input_defined,SourceMainFramesV1.Point0480.outputs_defined,SourceMainFramesV1.Point0480.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0481.input,SourceMainFramesV1.Point0481.outputs,SourceMainFramesV1.Point0481.input_defined,SourceMainFramesV1.Point0481.outputs_defined,SourceMainFramesV1.Point0481.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0482.input,SourceMainFramesV1.Point0482.outputs,SourceMainFramesV1.Point0482.input_defined,SourceMainFramesV1.Point0482.outputs_defined,SourceMainFramesV1.Point0482.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0483.input,SourceMainFramesV1.Point0483.outputs,SourceMainFramesV1.Point0483.input_defined,SourceMainFramesV1.Point0483.outputs_defined,SourceMainFramesV1.Point0483.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0484.input,SourceMainFramesV1.Point0484.outputs,SourceMainFramesV1.Point0484.input_defined,SourceMainFramesV1.Point0484.outputs_defined,SourceMainFramesV1.Point0484.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0485.input,SourceMainFramesV1.Point0485.outputs,SourceMainFramesV1.Point0485.input_defined,SourceMainFramesV1.Point0485.outputs_defined,SourceMainFramesV1.Point0485.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0486.input,SourceMainFramesV1.Point0486.outputs,SourceMainFramesV1.Point0486.input_defined,SourceMainFramesV1.Point0486.outputs_defined,SourceMainFramesV1.Point0486.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0487.input,SourceMainFramesV1.Point0487.outputs,SourceMainFramesV1.Point0487.input_defined,SourceMainFramesV1.Point0487.outputs_defined,SourceMainFramesV1.Point0487.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0488.input,SourceMainFramesV1.Point0488.outputs,SourceMainFramesV1.Point0488.input_defined,SourceMainFramesV1.Point0488.outputs_defined,SourceMainFramesV1.Point0488.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0489.input,SourceMainFramesV1.Point0489.outputs,SourceMainFramesV1.Point0489.input_defined,SourceMainFramesV1.Point0489.outputs_defined,SourceMainFramesV1.Point0489.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0490.input,SourceMainFramesV1.Point0490.outputs,SourceMainFramesV1.Point0490.input_defined,SourceMainFramesV1.Point0490.outputs_defined,SourceMainFramesV1.Point0490.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0491.input,SourceMainFramesV1.Point0491.outputs,SourceMainFramesV1.Point0491.input_defined,SourceMainFramesV1.Point0491.outputs_defined,SourceMainFramesV1.Point0491.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0492.input,SourceMainFramesV1.Point0492.outputs,SourceMainFramesV1.Point0492.input_defined,SourceMainFramesV1.Point0492.outputs_defined,SourceMainFramesV1.Point0492.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0493.input,SourceMainFramesV1.Point0493.outputs,SourceMainFramesV1.Point0493.input_defined,SourceMainFramesV1.Point0493.outputs_defined,SourceMainFramesV1.Point0493.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0494.input,SourceMainFramesV1.Point0494.outputs,SourceMainFramesV1.Point0494.input_defined,SourceMainFramesV1.Point0494.outputs_defined,SourceMainFramesV1.Point0494.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0495.input,SourceMainFramesV1.Point0495.outputs,SourceMainFramesV1.Point0495.input_defined,SourceMainFramesV1.Point0495.outputs_defined,SourceMainFramesV1.Point0495.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0496.input,SourceMainFramesV1.Point0496.outputs,SourceMainFramesV1.Point0496.input_defined,SourceMainFramesV1.Point0496.outputs_defined,SourceMainFramesV1.Point0496.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0497.input,SourceMainFramesV1.Point0497.outputs,SourceMainFramesV1.Point0497.input_defined,SourceMainFramesV1.Point0497.outputs_defined,SourceMainFramesV1.Point0497.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0498.input,SourceMainFramesV1.Point0498.outputs,SourceMainFramesV1.Point0498.input_defined,SourceMainFramesV1.Point0498.outputs_defined,SourceMainFramesV1.Point0498.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0499.input,SourceMainFramesV1.Point0499.outputs,SourceMainFramesV1.Point0499.input_defined,SourceMainFramesV1.Point0499.outputs_defined,SourceMainFramesV1.Point0499.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0500.input,SourceMainFramesV1.Point0500.outputs,SourceMainFramesV1.Point0500.input_defined,SourceMainFramesV1.Point0500.outputs_defined,SourceMainFramesV1.Point0500.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0501.input,SourceMainFramesV1.Point0501.outputs,SourceMainFramesV1.Point0501.input_defined,SourceMainFramesV1.Point0501.outputs_defined,SourceMainFramesV1.Point0501.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0502.input,SourceMainFramesV1.Point0502.outputs,SourceMainFramesV1.Point0502.input_defined,SourceMainFramesV1.Point0502.outputs_defined,SourceMainFramesV1.Point0502.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0503.input,SourceMainFramesV1.Point0503.outputs,SourceMainFramesV1.Point0503.input_defined,SourceMainFramesV1.Point0503.outputs_defined,SourceMainFramesV1.Point0503.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0504.input,SourceMainFramesV1.Point0504.outputs,SourceMainFramesV1.Point0504.input_defined,SourceMainFramesV1.Point0504.outputs_defined,SourceMainFramesV1.Point0504.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0505.input,SourceMainFramesV1.Point0505.outputs,SourceMainFramesV1.Point0505.input_defined,SourceMainFramesV1.Point0505.outputs_defined,SourceMainFramesV1.Point0505.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0506.input,SourceMainFramesV1.Point0506.outputs,SourceMainFramesV1.Point0506.input_defined,SourceMainFramesV1.Point0506.outputs_defined,SourceMainFramesV1.Point0506.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0507.input,SourceMainFramesV1.Point0507.outputs,SourceMainFramesV1.Point0507.input_defined,SourceMainFramesV1.Point0507.outputs_defined,SourceMainFramesV1.Point0507.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0508.input,SourceMainFramesV1.Point0508.outputs,SourceMainFramesV1.Point0508.input_defined,SourceMainFramesV1.Point0508.outputs_defined,SourceMainFramesV1.Point0508.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0509.input,SourceMainFramesV1.Point0509.outputs,SourceMainFramesV1.Point0509.input_defined,SourceMainFramesV1.Point0509.outputs_defined,SourceMainFramesV1.Point0509.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0510.input,SourceMainFramesV1.Point0510.outputs,SourceMainFramesV1.Point0510.input_defined,SourceMainFramesV1.Point0510.outputs_defined,SourceMainFramesV1.Point0510.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0511.input,SourceMainFramesV1.Point0511.outputs,SourceMainFramesV1.Point0511.input_defined,SourceMainFramesV1.Point0511.outputs_defined,SourceMainFramesV1.Point0511.execution total⟩
end SourceMainFramesV1.Execution15
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution15.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
