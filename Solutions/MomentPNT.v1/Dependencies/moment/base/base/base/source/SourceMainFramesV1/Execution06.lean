import SourceMainFramesV1.Point0192
import SourceMainFramesV1.Point0193
import SourceMainFramesV1.Point0194
import SourceMainFramesV1.Point0195
import SourceMainFramesV1.Point0196
import SourceMainFramesV1.Point0197
import SourceMainFramesV1.Point0198
import SourceMainFramesV1.Point0199
import SourceMainFramesV1.Point0200
import SourceMainFramesV1.Point0201
import SourceMainFramesV1.Point0202
import SourceMainFramesV1.Point0203
import SourceMainFramesV1.Point0204
import SourceMainFramesV1.Point0205
import SourceMainFramesV1.Point0206
import SourceMainFramesV1.Point0207
import SourceMainFramesV1.Point0208
import SourceMainFramesV1.Point0209
import SourceMainFramesV1.Point0210
import SourceMainFramesV1.Point0211
import SourceMainFramesV1.Point0212
import SourceMainFramesV1.Point0213
import SourceMainFramesV1.Point0214
import SourceMainFramesV1.Point0215
import SourceMainFramesV1.Point0216
import SourceMainFramesV1.Point0217
import SourceMainFramesV1.Point0218
import SourceMainFramesV1.Point0219
import SourceMainFramesV1.Point0220
import SourceMainFramesV1.Point0221
import SourceMainFramesV1.Point0222
import SourceMainFramesV1.Point0223
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution06
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 192 ≤ i) (upper : i < 224) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0192.input,SourceMainFramesV1.Point0192.outputs,SourceMainFramesV1.Point0192.input_defined,SourceMainFramesV1.Point0192.outputs_defined,SourceMainFramesV1.Point0192.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0193.input,SourceMainFramesV1.Point0193.outputs,SourceMainFramesV1.Point0193.input_defined,SourceMainFramesV1.Point0193.outputs_defined,SourceMainFramesV1.Point0193.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0194.input,SourceMainFramesV1.Point0194.outputs,SourceMainFramesV1.Point0194.input_defined,SourceMainFramesV1.Point0194.outputs_defined,SourceMainFramesV1.Point0194.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0195.input,SourceMainFramesV1.Point0195.outputs,SourceMainFramesV1.Point0195.input_defined,SourceMainFramesV1.Point0195.outputs_defined,SourceMainFramesV1.Point0195.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0196.input,SourceMainFramesV1.Point0196.outputs,SourceMainFramesV1.Point0196.input_defined,SourceMainFramesV1.Point0196.outputs_defined,SourceMainFramesV1.Point0196.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0197.input,SourceMainFramesV1.Point0197.outputs,SourceMainFramesV1.Point0197.input_defined,SourceMainFramesV1.Point0197.outputs_defined,SourceMainFramesV1.Point0197.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0198.input,SourceMainFramesV1.Point0198.outputs,SourceMainFramesV1.Point0198.input_defined,SourceMainFramesV1.Point0198.outputs_defined,SourceMainFramesV1.Point0198.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0199.input,SourceMainFramesV1.Point0199.outputs,SourceMainFramesV1.Point0199.input_defined,SourceMainFramesV1.Point0199.outputs_defined,SourceMainFramesV1.Point0199.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0200.input,SourceMainFramesV1.Point0200.outputs,SourceMainFramesV1.Point0200.input_defined,SourceMainFramesV1.Point0200.outputs_defined,SourceMainFramesV1.Point0200.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0201.input,SourceMainFramesV1.Point0201.outputs,SourceMainFramesV1.Point0201.input_defined,SourceMainFramesV1.Point0201.outputs_defined,SourceMainFramesV1.Point0201.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0202.input,SourceMainFramesV1.Point0202.outputs,SourceMainFramesV1.Point0202.input_defined,SourceMainFramesV1.Point0202.outputs_defined,SourceMainFramesV1.Point0202.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0203.input,SourceMainFramesV1.Point0203.outputs,SourceMainFramesV1.Point0203.input_defined,SourceMainFramesV1.Point0203.outputs_defined,SourceMainFramesV1.Point0203.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0204.input,SourceMainFramesV1.Point0204.outputs,SourceMainFramesV1.Point0204.input_defined,SourceMainFramesV1.Point0204.outputs_defined,SourceMainFramesV1.Point0204.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0205.input,SourceMainFramesV1.Point0205.outputs,SourceMainFramesV1.Point0205.input_defined,SourceMainFramesV1.Point0205.outputs_defined,SourceMainFramesV1.Point0205.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0206.input,SourceMainFramesV1.Point0206.outputs,SourceMainFramesV1.Point0206.input_defined,SourceMainFramesV1.Point0206.outputs_defined,SourceMainFramesV1.Point0206.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0207.input,SourceMainFramesV1.Point0207.outputs,SourceMainFramesV1.Point0207.input_defined,SourceMainFramesV1.Point0207.outputs_defined,SourceMainFramesV1.Point0207.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0208.input,SourceMainFramesV1.Point0208.outputs,SourceMainFramesV1.Point0208.input_defined,SourceMainFramesV1.Point0208.outputs_defined,SourceMainFramesV1.Point0208.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0209.input,SourceMainFramesV1.Point0209.outputs,SourceMainFramesV1.Point0209.input_defined,SourceMainFramesV1.Point0209.outputs_defined,SourceMainFramesV1.Point0209.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0210.input,SourceMainFramesV1.Point0210.outputs,SourceMainFramesV1.Point0210.input_defined,SourceMainFramesV1.Point0210.outputs_defined,SourceMainFramesV1.Point0210.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0211.input,SourceMainFramesV1.Point0211.outputs,SourceMainFramesV1.Point0211.input_defined,SourceMainFramesV1.Point0211.outputs_defined,SourceMainFramesV1.Point0211.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0212.input,SourceMainFramesV1.Point0212.outputs,SourceMainFramesV1.Point0212.input_defined,SourceMainFramesV1.Point0212.outputs_defined,SourceMainFramesV1.Point0212.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0213.input,SourceMainFramesV1.Point0213.outputs,SourceMainFramesV1.Point0213.input_defined,SourceMainFramesV1.Point0213.outputs_defined,SourceMainFramesV1.Point0213.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0214.input,SourceMainFramesV1.Point0214.outputs,SourceMainFramesV1.Point0214.input_defined,SourceMainFramesV1.Point0214.outputs_defined,SourceMainFramesV1.Point0214.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0215.input,SourceMainFramesV1.Point0215.outputs,SourceMainFramesV1.Point0215.input_defined,SourceMainFramesV1.Point0215.outputs_defined,SourceMainFramesV1.Point0215.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0216.input,SourceMainFramesV1.Point0216.outputs,SourceMainFramesV1.Point0216.input_defined,SourceMainFramesV1.Point0216.outputs_defined,SourceMainFramesV1.Point0216.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0217.input,SourceMainFramesV1.Point0217.outputs,SourceMainFramesV1.Point0217.input_defined,SourceMainFramesV1.Point0217.outputs_defined,SourceMainFramesV1.Point0217.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0218.input,SourceMainFramesV1.Point0218.outputs,SourceMainFramesV1.Point0218.input_defined,SourceMainFramesV1.Point0218.outputs_defined,SourceMainFramesV1.Point0218.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0219.input,SourceMainFramesV1.Point0219.outputs,SourceMainFramesV1.Point0219.input_defined,SourceMainFramesV1.Point0219.outputs_defined,SourceMainFramesV1.Point0219.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0220.input,SourceMainFramesV1.Point0220.outputs,SourceMainFramesV1.Point0220.input_defined,SourceMainFramesV1.Point0220.outputs_defined,SourceMainFramesV1.Point0220.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0221.input,SourceMainFramesV1.Point0221.outputs,SourceMainFramesV1.Point0221.input_defined,SourceMainFramesV1.Point0221.outputs_defined,SourceMainFramesV1.Point0221.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0222.input,SourceMainFramesV1.Point0222.outputs,SourceMainFramesV1.Point0222.input_defined,SourceMainFramesV1.Point0222.outputs_defined,SourceMainFramesV1.Point0222.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0223.input,SourceMainFramesV1.Point0223.outputs,SourceMainFramesV1.Point0223.input_defined,SourceMainFramesV1.Point0223.outputs_defined,SourceMainFramesV1.Point0223.execution total⟩
end SourceMainFramesV1.Execution06
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution06.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
