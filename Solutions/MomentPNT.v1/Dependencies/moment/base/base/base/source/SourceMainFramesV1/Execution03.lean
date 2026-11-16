import SourceMainFramesV1.Point0096
import SourceMainFramesV1.Point0097
import SourceMainFramesV1.Point0098
import SourceMainFramesV1.Point0099
import SourceMainFramesV1.Point0100
import SourceMainFramesV1.Point0101
import SourceMainFramesV1.Point0102
import SourceMainFramesV1.Point0103
import SourceMainFramesV1.Point0104
import SourceMainFramesV1.Point0105
import SourceMainFramesV1.Point0106
import SourceMainFramesV1.Point0107
import SourceMainFramesV1.Point0108
import SourceMainFramesV1.Point0109
import SourceMainFramesV1.Point0110
import SourceMainFramesV1.Point0111
import SourceMainFramesV1.Point0112
import SourceMainFramesV1.Point0113
import SourceMainFramesV1.Point0114
import SourceMainFramesV1.Point0115
import SourceMainFramesV1.Point0116
import SourceMainFramesV1.Point0117
import SourceMainFramesV1.Point0118
import SourceMainFramesV1.Point0119
import SourceMainFramesV1.Point0120
import SourceMainFramesV1.Point0121
import SourceMainFramesV1.Point0122
import SourceMainFramesV1.Point0123
import SourceMainFramesV1.Point0124
import SourceMainFramesV1.Point0125
import SourceMainFramesV1.Point0126
import SourceMainFramesV1.Point0127
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution03
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 96 ≤ i) (upper : i < 128) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0096.input,SourceMainFramesV1.Point0096.outputs,SourceMainFramesV1.Point0096.input_defined,SourceMainFramesV1.Point0096.outputs_defined,SourceMainFramesV1.Point0096.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0097.input,SourceMainFramesV1.Point0097.outputs,SourceMainFramesV1.Point0097.input_defined,SourceMainFramesV1.Point0097.outputs_defined,SourceMainFramesV1.Point0097.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0098.input,SourceMainFramesV1.Point0098.outputs,SourceMainFramesV1.Point0098.input_defined,SourceMainFramesV1.Point0098.outputs_defined,SourceMainFramesV1.Point0098.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0099.input,SourceMainFramesV1.Point0099.outputs,SourceMainFramesV1.Point0099.input_defined,SourceMainFramesV1.Point0099.outputs_defined,SourceMainFramesV1.Point0099.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0100.input,SourceMainFramesV1.Point0100.outputs,SourceMainFramesV1.Point0100.input_defined,SourceMainFramesV1.Point0100.outputs_defined,SourceMainFramesV1.Point0100.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0101.input,SourceMainFramesV1.Point0101.outputs,SourceMainFramesV1.Point0101.input_defined,SourceMainFramesV1.Point0101.outputs_defined,SourceMainFramesV1.Point0101.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0102.input,SourceMainFramesV1.Point0102.outputs,SourceMainFramesV1.Point0102.input_defined,SourceMainFramesV1.Point0102.outputs_defined,SourceMainFramesV1.Point0102.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0103.input,SourceMainFramesV1.Point0103.outputs,SourceMainFramesV1.Point0103.input_defined,SourceMainFramesV1.Point0103.outputs_defined,SourceMainFramesV1.Point0103.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0104.input,SourceMainFramesV1.Point0104.outputs,SourceMainFramesV1.Point0104.input_defined,SourceMainFramesV1.Point0104.outputs_defined,SourceMainFramesV1.Point0104.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0105.input,SourceMainFramesV1.Point0105.outputs,SourceMainFramesV1.Point0105.input_defined,SourceMainFramesV1.Point0105.outputs_defined,SourceMainFramesV1.Point0105.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0106.input,SourceMainFramesV1.Point0106.outputs,SourceMainFramesV1.Point0106.input_defined,SourceMainFramesV1.Point0106.outputs_defined,SourceMainFramesV1.Point0106.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0107.input,SourceMainFramesV1.Point0107.outputs,SourceMainFramesV1.Point0107.input_defined,SourceMainFramesV1.Point0107.outputs_defined,SourceMainFramesV1.Point0107.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0108.input,SourceMainFramesV1.Point0108.outputs,SourceMainFramesV1.Point0108.input_defined,SourceMainFramesV1.Point0108.outputs_defined,SourceMainFramesV1.Point0108.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0109.input,SourceMainFramesV1.Point0109.outputs,SourceMainFramesV1.Point0109.input_defined,SourceMainFramesV1.Point0109.outputs_defined,SourceMainFramesV1.Point0109.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0110.input,SourceMainFramesV1.Point0110.outputs,SourceMainFramesV1.Point0110.input_defined,SourceMainFramesV1.Point0110.outputs_defined,SourceMainFramesV1.Point0110.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0111.input,SourceMainFramesV1.Point0111.outputs,SourceMainFramesV1.Point0111.input_defined,SourceMainFramesV1.Point0111.outputs_defined,SourceMainFramesV1.Point0111.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0112.input,SourceMainFramesV1.Point0112.outputs,SourceMainFramesV1.Point0112.input_defined,SourceMainFramesV1.Point0112.outputs_defined,SourceMainFramesV1.Point0112.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0113.input,SourceMainFramesV1.Point0113.outputs,SourceMainFramesV1.Point0113.input_defined,SourceMainFramesV1.Point0113.outputs_defined,SourceMainFramesV1.Point0113.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0114.input,SourceMainFramesV1.Point0114.outputs,SourceMainFramesV1.Point0114.input_defined,SourceMainFramesV1.Point0114.outputs_defined,SourceMainFramesV1.Point0114.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0115.input,SourceMainFramesV1.Point0115.outputs,SourceMainFramesV1.Point0115.input_defined,SourceMainFramesV1.Point0115.outputs_defined,SourceMainFramesV1.Point0115.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0116.input,SourceMainFramesV1.Point0116.outputs,SourceMainFramesV1.Point0116.input_defined,SourceMainFramesV1.Point0116.outputs_defined,SourceMainFramesV1.Point0116.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0117.input,SourceMainFramesV1.Point0117.outputs,SourceMainFramesV1.Point0117.input_defined,SourceMainFramesV1.Point0117.outputs_defined,SourceMainFramesV1.Point0117.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0118.input,SourceMainFramesV1.Point0118.outputs,SourceMainFramesV1.Point0118.input_defined,SourceMainFramesV1.Point0118.outputs_defined,SourceMainFramesV1.Point0118.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0119.input,SourceMainFramesV1.Point0119.outputs,SourceMainFramesV1.Point0119.input_defined,SourceMainFramesV1.Point0119.outputs_defined,SourceMainFramesV1.Point0119.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0120.input,SourceMainFramesV1.Point0120.outputs,SourceMainFramesV1.Point0120.input_defined,SourceMainFramesV1.Point0120.outputs_defined,SourceMainFramesV1.Point0120.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0121.input,SourceMainFramesV1.Point0121.outputs,SourceMainFramesV1.Point0121.input_defined,SourceMainFramesV1.Point0121.outputs_defined,SourceMainFramesV1.Point0121.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0122.input,SourceMainFramesV1.Point0122.outputs,SourceMainFramesV1.Point0122.input_defined,SourceMainFramesV1.Point0122.outputs_defined,SourceMainFramesV1.Point0122.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0123.input,SourceMainFramesV1.Point0123.outputs,SourceMainFramesV1.Point0123.input_defined,SourceMainFramesV1.Point0123.outputs_defined,SourceMainFramesV1.Point0123.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0124.input,SourceMainFramesV1.Point0124.outputs,SourceMainFramesV1.Point0124.input_defined,SourceMainFramesV1.Point0124.outputs_defined,SourceMainFramesV1.Point0124.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0125.input,SourceMainFramesV1.Point0125.outputs,SourceMainFramesV1.Point0125.input_defined,SourceMainFramesV1.Point0125.outputs_defined,SourceMainFramesV1.Point0125.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0126.input,SourceMainFramesV1.Point0126.outputs,SourceMainFramesV1.Point0126.input_defined,SourceMainFramesV1.Point0126.outputs_defined,SourceMainFramesV1.Point0126.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0127.input,SourceMainFramesV1.Point0127.outputs,SourceMainFramesV1.Point0127.input_defined,SourceMainFramesV1.Point0127.outputs_defined,SourceMainFramesV1.Point0127.execution total⟩
end SourceMainFramesV1.Execution03
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution03.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
