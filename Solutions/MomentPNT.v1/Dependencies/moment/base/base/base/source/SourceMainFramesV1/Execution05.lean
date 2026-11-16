import SourceMainFramesV1.Point0160
import SourceMainFramesV1.Point0161
import SourceMainFramesV1.Point0162
import SourceMainFramesV1.Point0163
import SourceMainFramesV1.Point0164
import SourceMainFramesV1.Point0165
import SourceMainFramesV1.Point0166
import SourceMainFramesV1.Point0167
import SourceMainFramesV1.Point0168
import SourceMainFramesV1.Point0169
import SourceMainFramesV1.Point0170
import SourceMainFramesV1.Point0171
import SourceMainFramesV1.Point0172
import SourceMainFramesV1.Point0173
import SourceMainFramesV1.Point0174
import SourceMainFramesV1.Point0175
import SourceMainFramesV1.Point0176
import SourceMainFramesV1.Point0177
import SourceMainFramesV1.Point0178
import SourceMainFramesV1.Point0179
import SourceMainFramesV1.Point0180
import SourceMainFramesV1.Point0181
import SourceMainFramesV1.Point0182
import SourceMainFramesV1.Point0183
import SourceMainFramesV1.Point0184
import SourceMainFramesV1.Point0185
import SourceMainFramesV1.Point0186
import SourceMainFramesV1.Point0187
import SourceMainFramesV1.Point0188
import SourceMainFramesV1.Point0189
import SourceMainFramesV1.Point0190
import SourceMainFramesV1.Point0191
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution05
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 160 ≤ i) (upper : i < 192) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0160.input,SourceMainFramesV1.Point0160.outputs,SourceMainFramesV1.Point0160.input_defined,SourceMainFramesV1.Point0160.outputs_defined,SourceMainFramesV1.Point0160.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0161.input,SourceMainFramesV1.Point0161.outputs,SourceMainFramesV1.Point0161.input_defined,SourceMainFramesV1.Point0161.outputs_defined,SourceMainFramesV1.Point0161.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0162.input,SourceMainFramesV1.Point0162.outputs,SourceMainFramesV1.Point0162.input_defined,SourceMainFramesV1.Point0162.outputs_defined,SourceMainFramesV1.Point0162.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0163.input,SourceMainFramesV1.Point0163.outputs,SourceMainFramesV1.Point0163.input_defined,SourceMainFramesV1.Point0163.outputs_defined,SourceMainFramesV1.Point0163.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0164.input,SourceMainFramesV1.Point0164.outputs,SourceMainFramesV1.Point0164.input_defined,SourceMainFramesV1.Point0164.outputs_defined,SourceMainFramesV1.Point0164.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0165.input,SourceMainFramesV1.Point0165.outputs,SourceMainFramesV1.Point0165.input_defined,SourceMainFramesV1.Point0165.outputs_defined,SourceMainFramesV1.Point0165.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0166.input,SourceMainFramesV1.Point0166.outputs,SourceMainFramesV1.Point0166.input_defined,SourceMainFramesV1.Point0166.outputs_defined,SourceMainFramesV1.Point0166.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0167.input,SourceMainFramesV1.Point0167.outputs,SourceMainFramesV1.Point0167.input_defined,SourceMainFramesV1.Point0167.outputs_defined,SourceMainFramesV1.Point0167.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0168.input,SourceMainFramesV1.Point0168.outputs,SourceMainFramesV1.Point0168.input_defined,SourceMainFramesV1.Point0168.outputs_defined,SourceMainFramesV1.Point0168.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0169.input,SourceMainFramesV1.Point0169.outputs,SourceMainFramesV1.Point0169.input_defined,SourceMainFramesV1.Point0169.outputs_defined,SourceMainFramesV1.Point0169.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0170.input,SourceMainFramesV1.Point0170.outputs,SourceMainFramesV1.Point0170.input_defined,SourceMainFramesV1.Point0170.outputs_defined,SourceMainFramesV1.Point0170.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0171.input,SourceMainFramesV1.Point0171.outputs,SourceMainFramesV1.Point0171.input_defined,SourceMainFramesV1.Point0171.outputs_defined,SourceMainFramesV1.Point0171.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0172.input,SourceMainFramesV1.Point0172.outputs,SourceMainFramesV1.Point0172.input_defined,SourceMainFramesV1.Point0172.outputs_defined,SourceMainFramesV1.Point0172.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0173.input,SourceMainFramesV1.Point0173.outputs,SourceMainFramesV1.Point0173.input_defined,SourceMainFramesV1.Point0173.outputs_defined,SourceMainFramesV1.Point0173.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0174.input,SourceMainFramesV1.Point0174.outputs,SourceMainFramesV1.Point0174.input_defined,SourceMainFramesV1.Point0174.outputs_defined,SourceMainFramesV1.Point0174.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0175.input,SourceMainFramesV1.Point0175.outputs,SourceMainFramesV1.Point0175.input_defined,SourceMainFramesV1.Point0175.outputs_defined,SourceMainFramesV1.Point0175.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0176.input,SourceMainFramesV1.Point0176.outputs,SourceMainFramesV1.Point0176.input_defined,SourceMainFramesV1.Point0176.outputs_defined,SourceMainFramesV1.Point0176.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0177.input,SourceMainFramesV1.Point0177.outputs,SourceMainFramesV1.Point0177.input_defined,SourceMainFramesV1.Point0177.outputs_defined,SourceMainFramesV1.Point0177.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0178.input,SourceMainFramesV1.Point0178.outputs,SourceMainFramesV1.Point0178.input_defined,SourceMainFramesV1.Point0178.outputs_defined,SourceMainFramesV1.Point0178.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0179.input,SourceMainFramesV1.Point0179.outputs,SourceMainFramesV1.Point0179.input_defined,SourceMainFramesV1.Point0179.outputs_defined,SourceMainFramesV1.Point0179.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0180.input,SourceMainFramesV1.Point0180.outputs,SourceMainFramesV1.Point0180.input_defined,SourceMainFramesV1.Point0180.outputs_defined,SourceMainFramesV1.Point0180.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0181.input,SourceMainFramesV1.Point0181.outputs,SourceMainFramesV1.Point0181.input_defined,SourceMainFramesV1.Point0181.outputs_defined,SourceMainFramesV1.Point0181.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0182.input,SourceMainFramesV1.Point0182.outputs,SourceMainFramesV1.Point0182.input_defined,SourceMainFramesV1.Point0182.outputs_defined,SourceMainFramesV1.Point0182.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0183.input,SourceMainFramesV1.Point0183.outputs,SourceMainFramesV1.Point0183.input_defined,SourceMainFramesV1.Point0183.outputs_defined,SourceMainFramesV1.Point0183.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0184.input,SourceMainFramesV1.Point0184.outputs,SourceMainFramesV1.Point0184.input_defined,SourceMainFramesV1.Point0184.outputs_defined,SourceMainFramesV1.Point0184.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0185.input,SourceMainFramesV1.Point0185.outputs,SourceMainFramesV1.Point0185.input_defined,SourceMainFramesV1.Point0185.outputs_defined,SourceMainFramesV1.Point0185.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0186.input,SourceMainFramesV1.Point0186.outputs,SourceMainFramesV1.Point0186.input_defined,SourceMainFramesV1.Point0186.outputs_defined,SourceMainFramesV1.Point0186.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0187.input,SourceMainFramesV1.Point0187.outputs,SourceMainFramesV1.Point0187.input_defined,SourceMainFramesV1.Point0187.outputs_defined,SourceMainFramesV1.Point0187.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0188.input,SourceMainFramesV1.Point0188.outputs,SourceMainFramesV1.Point0188.input_defined,SourceMainFramesV1.Point0188.outputs_defined,SourceMainFramesV1.Point0188.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0189.input,SourceMainFramesV1.Point0189.outputs,SourceMainFramesV1.Point0189.input_defined,SourceMainFramesV1.Point0189.outputs_defined,SourceMainFramesV1.Point0189.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0190.input,SourceMainFramesV1.Point0190.outputs,SourceMainFramesV1.Point0190.input_defined,SourceMainFramesV1.Point0190.outputs_defined,SourceMainFramesV1.Point0190.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0191.input,SourceMainFramesV1.Point0191.outputs,SourceMainFramesV1.Point0191.input_defined,SourceMainFramesV1.Point0191.outputs_defined,SourceMainFramesV1.Point0191.execution total⟩
end SourceMainFramesV1.Execution05
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution05.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
