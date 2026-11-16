import SourceMainFramesV1.Point0288
import SourceMainFramesV1.Point0289
import SourceMainFramesV1.Point0290
import SourceMainFramesV1.Point0291
import SourceMainFramesV1.Point0292
import SourceMainFramesV1.Point0293
import SourceMainFramesV1.Point0294
import SourceMainFramesV1.Point0295
import SourceMainFramesV1.Point0296
import SourceMainFramesV1.Point0297
import SourceMainFramesV1.Point0298
import SourceMainFramesV1.Point0299
import SourceMainFramesV1.Point0300
import SourceMainFramesV1.Point0301
import SourceMainFramesV1.Point0302
import SourceMainFramesV1.Point0303
import SourceMainFramesV1.Point0304
import SourceMainFramesV1.Point0305
import SourceMainFramesV1.Point0306
import SourceMainFramesV1.Point0307
import SourceMainFramesV1.Point0308
import SourceMainFramesV1.Point0309
import SourceMainFramesV1.Point0310
import SourceMainFramesV1.Point0311
import SourceMainFramesV1.Point0312
import SourceMainFramesV1.Point0313
import SourceMainFramesV1.Point0314
import SourceMainFramesV1.Point0315
import SourceMainFramesV1.Point0316
import SourceMainFramesV1.Point0317
import SourceMainFramesV1.Point0318
import SourceMainFramesV1.Point0319
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution09
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 288 ≤ i) (upper : i < 320) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0288.input,SourceMainFramesV1.Point0288.outputs,SourceMainFramesV1.Point0288.input_defined,SourceMainFramesV1.Point0288.outputs_defined,SourceMainFramesV1.Point0288.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0289.input,SourceMainFramesV1.Point0289.outputs,SourceMainFramesV1.Point0289.input_defined,SourceMainFramesV1.Point0289.outputs_defined,SourceMainFramesV1.Point0289.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0290.input,SourceMainFramesV1.Point0290.outputs,SourceMainFramesV1.Point0290.input_defined,SourceMainFramesV1.Point0290.outputs_defined,SourceMainFramesV1.Point0290.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0291.input,SourceMainFramesV1.Point0291.outputs,SourceMainFramesV1.Point0291.input_defined,SourceMainFramesV1.Point0291.outputs_defined,SourceMainFramesV1.Point0291.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0292.input,SourceMainFramesV1.Point0292.outputs,SourceMainFramesV1.Point0292.input_defined,SourceMainFramesV1.Point0292.outputs_defined,SourceMainFramesV1.Point0292.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0293.input,SourceMainFramesV1.Point0293.outputs,SourceMainFramesV1.Point0293.input_defined,SourceMainFramesV1.Point0293.outputs_defined,SourceMainFramesV1.Point0293.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0294.input,SourceMainFramesV1.Point0294.outputs,SourceMainFramesV1.Point0294.input_defined,SourceMainFramesV1.Point0294.outputs_defined,SourceMainFramesV1.Point0294.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0295.input,SourceMainFramesV1.Point0295.outputs,SourceMainFramesV1.Point0295.input_defined,SourceMainFramesV1.Point0295.outputs_defined,SourceMainFramesV1.Point0295.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0296.input,SourceMainFramesV1.Point0296.outputs,SourceMainFramesV1.Point0296.input_defined,SourceMainFramesV1.Point0296.outputs_defined,SourceMainFramesV1.Point0296.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0297.input,SourceMainFramesV1.Point0297.outputs,SourceMainFramesV1.Point0297.input_defined,SourceMainFramesV1.Point0297.outputs_defined,SourceMainFramesV1.Point0297.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0298.input,SourceMainFramesV1.Point0298.outputs,SourceMainFramesV1.Point0298.input_defined,SourceMainFramesV1.Point0298.outputs_defined,SourceMainFramesV1.Point0298.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0299.input,SourceMainFramesV1.Point0299.outputs,SourceMainFramesV1.Point0299.input_defined,SourceMainFramesV1.Point0299.outputs_defined,SourceMainFramesV1.Point0299.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0300.input,SourceMainFramesV1.Point0300.outputs,SourceMainFramesV1.Point0300.input_defined,SourceMainFramesV1.Point0300.outputs_defined,SourceMainFramesV1.Point0300.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0301.input,SourceMainFramesV1.Point0301.outputs,SourceMainFramesV1.Point0301.input_defined,SourceMainFramesV1.Point0301.outputs_defined,SourceMainFramesV1.Point0301.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0302.input,SourceMainFramesV1.Point0302.outputs,SourceMainFramesV1.Point0302.input_defined,SourceMainFramesV1.Point0302.outputs_defined,SourceMainFramesV1.Point0302.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0303.input,SourceMainFramesV1.Point0303.outputs,SourceMainFramesV1.Point0303.input_defined,SourceMainFramesV1.Point0303.outputs_defined,SourceMainFramesV1.Point0303.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0304.input,SourceMainFramesV1.Point0304.outputs,SourceMainFramesV1.Point0304.input_defined,SourceMainFramesV1.Point0304.outputs_defined,SourceMainFramesV1.Point0304.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0305.input,SourceMainFramesV1.Point0305.outputs,SourceMainFramesV1.Point0305.input_defined,SourceMainFramesV1.Point0305.outputs_defined,SourceMainFramesV1.Point0305.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0306.input,SourceMainFramesV1.Point0306.outputs,SourceMainFramesV1.Point0306.input_defined,SourceMainFramesV1.Point0306.outputs_defined,SourceMainFramesV1.Point0306.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0307.input,SourceMainFramesV1.Point0307.outputs,SourceMainFramesV1.Point0307.input_defined,SourceMainFramesV1.Point0307.outputs_defined,SourceMainFramesV1.Point0307.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0308.input,SourceMainFramesV1.Point0308.outputs,SourceMainFramesV1.Point0308.input_defined,SourceMainFramesV1.Point0308.outputs_defined,SourceMainFramesV1.Point0308.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0309.input,SourceMainFramesV1.Point0309.outputs,SourceMainFramesV1.Point0309.input_defined,SourceMainFramesV1.Point0309.outputs_defined,SourceMainFramesV1.Point0309.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0310.input,SourceMainFramesV1.Point0310.outputs,SourceMainFramesV1.Point0310.input_defined,SourceMainFramesV1.Point0310.outputs_defined,SourceMainFramesV1.Point0310.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0311.input,SourceMainFramesV1.Point0311.outputs,SourceMainFramesV1.Point0311.input_defined,SourceMainFramesV1.Point0311.outputs_defined,SourceMainFramesV1.Point0311.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0312.input,SourceMainFramesV1.Point0312.outputs,SourceMainFramesV1.Point0312.input_defined,SourceMainFramesV1.Point0312.outputs_defined,SourceMainFramesV1.Point0312.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0313.input,SourceMainFramesV1.Point0313.outputs,SourceMainFramesV1.Point0313.input_defined,SourceMainFramesV1.Point0313.outputs_defined,SourceMainFramesV1.Point0313.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0314.input,SourceMainFramesV1.Point0314.outputs,SourceMainFramesV1.Point0314.input_defined,SourceMainFramesV1.Point0314.outputs_defined,SourceMainFramesV1.Point0314.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0315.input,SourceMainFramesV1.Point0315.outputs,SourceMainFramesV1.Point0315.input_defined,SourceMainFramesV1.Point0315.outputs_defined,SourceMainFramesV1.Point0315.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0316.input,SourceMainFramesV1.Point0316.outputs,SourceMainFramesV1.Point0316.input_defined,SourceMainFramesV1.Point0316.outputs_defined,SourceMainFramesV1.Point0316.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0317.input,SourceMainFramesV1.Point0317.outputs,SourceMainFramesV1.Point0317.input_defined,SourceMainFramesV1.Point0317.outputs_defined,SourceMainFramesV1.Point0317.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0318.input,SourceMainFramesV1.Point0318.outputs,SourceMainFramesV1.Point0318.input_defined,SourceMainFramesV1.Point0318.outputs_defined,SourceMainFramesV1.Point0318.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0319.input,SourceMainFramesV1.Point0319.outputs,SourceMainFramesV1.Point0319.input_defined,SourceMainFramesV1.Point0319.outputs_defined,SourceMainFramesV1.Point0319.execution total⟩
end SourceMainFramesV1.Execution09
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution09.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
