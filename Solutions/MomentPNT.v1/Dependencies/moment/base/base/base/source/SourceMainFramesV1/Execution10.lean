import SourceMainFramesV1.Point0320
import SourceMainFramesV1.Point0321
import SourceMainFramesV1.Point0322
import SourceMainFramesV1.Point0323
import SourceMainFramesV1.Point0324
import SourceMainFramesV1.Point0325
import SourceMainFramesV1.Point0326
import SourceMainFramesV1.Point0327
import SourceMainFramesV1.Point0328
import SourceMainFramesV1.Point0329
import SourceMainFramesV1.Point0330
import SourceMainFramesV1.Point0331
import SourceMainFramesV1.Point0332
import SourceMainFramesV1.Point0333
import SourceMainFramesV1.Point0334
import SourceMainFramesV1.Point0335
import SourceMainFramesV1.Point0336
import SourceMainFramesV1.Point0337
import SourceMainFramesV1.Point0338
import SourceMainFramesV1.Point0339
import SourceMainFramesV1.Point0340
import SourceMainFramesV1.Point0341
import SourceMainFramesV1.Point0342
import SourceMainFramesV1.Point0343
import SourceMainFramesV1.Point0344
import SourceMainFramesV1.Point0345
import SourceMainFramesV1.Point0346
import SourceMainFramesV1.Point0347
import SourceMainFramesV1.Point0348
import SourceMainFramesV1.Point0349
import SourceMainFramesV1.Point0350
import SourceMainFramesV1.Point0351
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution10
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 320 ≤ i) (upper : i < 352) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0320.input,SourceMainFramesV1.Point0320.outputs,SourceMainFramesV1.Point0320.input_defined,SourceMainFramesV1.Point0320.outputs_defined,SourceMainFramesV1.Point0320.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0321.input,SourceMainFramesV1.Point0321.outputs,SourceMainFramesV1.Point0321.input_defined,SourceMainFramesV1.Point0321.outputs_defined,SourceMainFramesV1.Point0321.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0322.input,SourceMainFramesV1.Point0322.outputs,SourceMainFramesV1.Point0322.input_defined,SourceMainFramesV1.Point0322.outputs_defined,SourceMainFramesV1.Point0322.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0323.input,SourceMainFramesV1.Point0323.outputs,SourceMainFramesV1.Point0323.input_defined,SourceMainFramesV1.Point0323.outputs_defined,SourceMainFramesV1.Point0323.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0324.input,SourceMainFramesV1.Point0324.outputs,SourceMainFramesV1.Point0324.input_defined,SourceMainFramesV1.Point0324.outputs_defined,SourceMainFramesV1.Point0324.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0325.input,SourceMainFramesV1.Point0325.outputs,SourceMainFramesV1.Point0325.input_defined,SourceMainFramesV1.Point0325.outputs_defined,SourceMainFramesV1.Point0325.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0326.input,SourceMainFramesV1.Point0326.outputs,SourceMainFramesV1.Point0326.input_defined,SourceMainFramesV1.Point0326.outputs_defined,SourceMainFramesV1.Point0326.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0327.input,SourceMainFramesV1.Point0327.outputs,SourceMainFramesV1.Point0327.input_defined,SourceMainFramesV1.Point0327.outputs_defined,SourceMainFramesV1.Point0327.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0328.input,SourceMainFramesV1.Point0328.outputs,SourceMainFramesV1.Point0328.input_defined,SourceMainFramesV1.Point0328.outputs_defined,SourceMainFramesV1.Point0328.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0329.input,SourceMainFramesV1.Point0329.outputs,SourceMainFramesV1.Point0329.input_defined,SourceMainFramesV1.Point0329.outputs_defined,SourceMainFramesV1.Point0329.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0330.input,SourceMainFramesV1.Point0330.outputs,SourceMainFramesV1.Point0330.input_defined,SourceMainFramesV1.Point0330.outputs_defined,SourceMainFramesV1.Point0330.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0331.input,SourceMainFramesV1.Point0331.outputs,SourceMainFramesV1.Point0331.input_defined,SourceMainFramesV1.Point0331.outputs_defined,SourceMainFramesV1.Point0331.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0332.input,SourceMainFramesV1.Point0332.outputs,SourceMainFramesV1.Point0332.input_defined,SourceMainFramesV1.Point0332.outputs_defined,SourceMainFramesV1.Point0332.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0333.input,SourceMainFramesV1.Point0333.outputs,SourceMainFramesV1.Point0333.input_defined,SourceMainFramesV1.Point0333.outputs_defined,SourceMainFramesV1.Point0333.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0334.input,SourceMainFramesV1.Point0334.outputs,SourceMainFramesV1.Point0334.input_defined,SourceMainFramesV1.Point0334.outputs_defined,SourceMainFramesV1.Point0334.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0335.input,SourceMainFramesV1.Point0335.outputs,SourceMainFramesV1.Point0335.input_defined,SourceMainFramesV1.Point0335.outputs_defined,SourceMainFramesV1.Point0335.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0336.input,SourceMainFramesV1.Point0336.outputs,SourceMainFramesV1.Point0336.input_defined,SourceMainFramesV1.Point0336.outputs_defined,SourceMainFramesV1.Point0336.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0337.input,SourceMainFramesV1.Point0337.outputs,SourceMainFramesV1.Point0337.input_defined,SourceMainFramesV1.Point0337.outputs_defined,SourceMainFramesV1.Point0337.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0338.input,SourceMainFramesV1.Point0338.outputs,SourceMainFramesV1.Point0338.input_defined,SourceMainFramesV1.Point0338.outputs_defined,SourceMainFramesV1.Point0338.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0339.input,SourceMainFramesV1.Point0339.outputs,SourceMainFramesV1.Point0339.input_defined,SourceMainFramesV1.Point0339.outputs_defined,SourceMainFramesV1.Point0339.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0340.input,SourceMainFramesV1.Point0340.outputs,SourceMainFramesV1.Point0340.input_defined,SourceMainFramesV1.Point0340.outputs_defined,SourceMainFramesV1.Point0340.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0341.input,SourceMainFramesV1.Point0341.outputs,SourceMainFramesV1.Point0341.input_defined,SourceMainFramesV1.Point0341.outputs_defined,SourceMainFramesV1.Point0341.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0342.input,SourceMainFramesV1.Point0342.outputs,SourceMainFramesV1.Point0342.input_defined,SourceMainFramesV1.Point0342.outputs_defined,SourceMainFramesV1.Point0342.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0343.input,SourceMainFramesV1.Point0343.outputs,SourceMainFramesV1.Point0343.input_defined,SourceMainFramesV1.Point0343.outputs_defined,SourceMainFramesV1.Point0343.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0344.input,SourceMainFramesV1.Point0344.outputs,SourceMainFramesV1.Point0344.input_defined,SourceMainFramesV1.Point0344.outputs_defined,SourceMainFramesV1.Point0344.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0345.input,SourceMainFramesV1.Point0345.outputs,SourceMainFramesV1.Point0345.input_defined,SourceMainFramesV1.Point0345.outputs_defined,SourceMainFramesV1.Point0345.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0346.input,SourceMainFramesV1.Point0346.outputs,SourceMainFramesV1.Point0346.input_defined,SourceMainFramesV1.Point0346.outputs_defined,SourceMainFramesV1.Point0346.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0347.input,SourceMainFramesV1.Point0347.outputs,SourceMainFramesV1.Point0347.input_defined,SourceMainFramesV1.Point0347.outputs_defined,SourceMainFramesV1.Point0347.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0348.input,SourceMainFramesV1.Point0348.outputs,SourceMainFramesV1.Point0348.input_defined,SourceMainFramesV1.Point0348.outputs_defined,SourceMainFramesV1.Point0348.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0349.input,SourceMainFramesV1.Point0349.outputs,SourceMainFramesV1.Point0349.input_defined,SourceMainFramesV1.Point0349.outputs_defined,SourceMainFramesV1.Point0349.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0350.input,SourceMainFramesV1.Point0350.outputs,SourceMainFramesV1.Point0350.input_defined,SourceMainFramesV1.Point0350.outputs_defined,SourceMainFramesV1.Point0350.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0351.input,SourceMainFramesV1.Point0351.outputs,SourceMainFramesV1.Point0351.input_defined,SourceMainFramesV1.Point0351.outputs_defined,SourceMainFramesV1.Point0351.execution total⟩
end SourceMainFramesV1.Execution10
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution10.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
