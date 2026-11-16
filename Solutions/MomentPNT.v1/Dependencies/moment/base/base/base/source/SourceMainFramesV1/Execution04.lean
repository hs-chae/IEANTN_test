import SourceMainFramesV1.Point0128
import SourceMainFramesV1.Point0129
import SourceMainFramesV1.Point0130
import SourceMainFramesV1.Point0131
import SourceMainFramesV1.Point0132
import SourceMainFramesV1.Point0133
import SourceMainFramesV1.Point0134
import SourceMainFramesV1.Point0135
import SourceMainFramesV1.Point0136
import SourceMainFramesV1.Point0137
import SourceMainFramesV1.Point0138
import SourceMainFramesV1.Point0139
import SourceMainFramesV1.Point0140
import SourceMainFramesV1.Point0141
import SourceMainFramesV1.Point0142
import SourceMainFramesV1.Point0143
import SourceMainFramesV1.Point0144
import SourceMainFramesV1.Point0145
import SourceMainFramesV1.Point0146
import SourceMainFramesV1.Point0147
import SourceMainFramesV1.Point0148
import SourceMainFramesV1.Point0149
import SourceMainFramesV1.Point0150
import SourceMainFramesV1.Point0151
import SourceMainFramesV1.Point0152
import SourceMainFramesV1.Point0153
import SourceMainFramesV1.Point0154
import SourceMainFramesV1.Point0155
import SourceMainFramesV1.Point0156
import SourceMainFramesV1.Point0157
import SourceMainFramesV1.Point0158
import SourceMainFramesV1.Point0159
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution04
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 128 ≤ i) (upper : i < 160) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0128.input,SourceMainFramesV1.Point0128.outputs,SourceMainFramesV1.Point0128.input_defined,SourceMainFramesV1.Point0128.outputs_defined,SourceMainFramesV1.Point0128.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0129.input,SourceMainFramesV1.Point0129.outputs,SourceMainFramesV1.Point0129.input_defined,SourceMainFramesV1.Point0129.outputs_defined,SourceMainFramesV1.Point0129.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0130.input,SourceMainFramesV1.Point0130.outputs,SourceMainFramesV1.Point0130.input_defined,SourceMainFramesV1.Point0130.outputs_defined,SourceMainFramesV1.Point0130.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0131.input,SourceMainFramesV1.Point0131.outputs,SourceMainFramesV1.Point0131.input_defined,SourceMainFramesV1.Point0131.outputs_defined,SourceMainFramesV1.Point0131.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0132.input,SourceMainFramesV1.Point0132.outputs,SourceMainFramesV1.Point0132.input_defined,SourceMainFramesV1.Point0132.outputs_defined,SourceMainFramesV1.Point0132.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0133.input,SourceMainFramesV1.Point0133.outputs,SourceMainFramesV1.Point0133.input_defined,SourceMainFramesV1.Point0133.outputs_defined,SourceMainFramesV1.Point0133.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0134.input,SourceMainFramesV1.Point0134.outputs,SourceMainFramesV1.Point0134.input_defined,SourceMainFramesV1.Point0134.outputs_defined,SourceMainFramesV1.Point0134.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0135.input,SourceMainFramesV1.Point0135.outputs,SourceMainFramesV1.Point0135.input_defined,SourceMainFramesV1.Point0135.outputs_defined,SourceMainFramesV1.Point0135.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0136.input,SourceMainFramesV1.Point0136.outputs,SourceMainFramesV1.Point0136.input_defined,SourceMainFramesV1.Point0136.outputs_defined,SourceMainFramesV1.Point0136.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0137.input,SourceMainFramesV1.Point0137.outputs,SourceMainFramesV1.Point0137.input_defined,SourceMainFramesV1.Point0137.outputs_defined,SourceMainFramesV1.Point0137.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0138.input,SourceMainFramesV1.Point0138.outputs,SourceMainFramesV1.Point0138.input_defined,SourceMainFramesV1.Point0138.outputs_defined,SourceMainFramesV1.Point0138.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0139.input,SourceMainFramesV1.Point0139.outputs,SourceMainFramesV1.Point0139.input_defined,SourceMainFramesV1.Point0139.outputs_defined,SourceMainFramesV1.Point0139.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0140.input,SourceMainFramesV1.Point0140.outputs,SourceMainFramesV1.Point0140.input_defined,SourceMainFramesV1.Point0140.outputs_defined,SourceMainFramesV1.Point0140.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0141.input,SourceMainFramesV1.Point0141.outputs,SourceMainFramesV1.Point0141.input_defined,SourceMainFramesV1.Point0141.outputs_defined,SourceMainFramesV1.Point0141.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0142.input,SourceMainFramesV1.Point0142.outputs,SourceMainFramesV1.Point0142.input_defined,SourceMainFramesV1.Point0142.outputs_defined,SourceMainFramesV1.Point0142.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0143.input,SourceMainFramesV1.Point0143.outputs,SourceMainFramesV1.Point0143.input_defined,SourceMainFramesV1.Point0143.outputs_defined,SourceMainFramesV1.Point0143.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0144.input,SourceMainFramesV1.Point0144.outputs,SourceMainFramesV1.Point0144.input_defined,SourceMainFramesV1.Point0144.outputs_defined,SourceMainFramesV1.Point0144.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0145.input,SourceMainFramesV1.Point0145.outputs,SourceMainFramesV1.Point0145.input_defined,SourceMainFramesV1.Point0145.outputs_defined,SourceMainFramesV1.Point0145.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0146.input,SourceMainFramesV1.Point0146.outputs,SourceMainFramesV1.Point0146.input_defined,SourceMainFramesV1.Point0146.outputs_defined,SourceMainFramesV1.Point0146.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0147.input,SourceMainFramesV1.Point0147.outputs,SourceMainFramesV1.Point0147.input_defined,SourceMainFramesV1.Point0147.outputs_defined,SourceMainFramesV1.Point0147.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0148.input,SourceMainFramesV1.Point0148.outputs,SourceMainFramesV1.Point0148.input_defined,SourceMainFramesV1.Point0148.outputs_defined,SourceMainFramesV1.Point0148.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0149.input,SourceMainFramesV1.Point0149.outputs,SourceMainFramesV1.Point0149.input_defined,SourceMainFramesV1.Point0149.outputs_defined,SourceMainFramesV1.Point0149.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0150.input,SourceMainFramesV1.Point0150.outputs,SourceMainFramesV1.Point0150.input_defined,SourceMainFramesV1.Point0150.outputs_defined,SourceMainFramesV1.Point0150.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0151.input,SourceMainFramesV1.Point0151.outputs,SourceMainFramesV1.Point0151.input_defined,SourceMainFramesV1.Point0151.outputs_defined,SourceMainFramesV1.Point0151.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0152.input,SourceMainFramesV1.Point0152.outputs,SourceMainFramesV1.Point0152.input_defined,SourceMainFramesV1.Point0152.outputs_defined,SourceMainFramesV1.Point0152.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0153.input,SourceMainFramesV1.Point0153.outputs,SourceMainFramesV1.Point0153.input_defined,SourceMainFramesV1.Point0153.outputs_defined,SourceMainFramesV1.Point0153.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0154.input,SourceMainFramesV1.Point0154.outputs,SourceMainFramesV1.Point0154.input_defined,SourceMainFramesV1.Point0154.outputs_defined,SourceMainFramesV1.Point0154.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0155.input,SourceMainFramesV1.Point0155.outputs,SourceMainFramesV1.Point0155.input_defined,SourceMainFramesV1.Point0155.outputs_defined,SourceMainFramesV1.Point0155.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0156.input,SourceMainFramesV1.Point0156.outputs,SourceMainFramesV1.Point0156.input_defined,SourceMainFramesV1.Point0156.outputs_defined,SourceMainFramesV1.Point0156.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0157.input,SourceMainFramesV1.Point0157.outputs,SourceMainFramesV1.Point0157.input_defined,SourceMainFramesV1.Point0157.outputs_defined,SourceMainFramesV1.Point0157.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0158.input,SourceMainFramesV1.Point0158.outputs,SourceMainFramesV1.Point0158.input_defined,SourceMainFramesV1.Point0158.outputs_defined,SourceMainFramesV1.Point0158.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0159.input,SourceMainFramesV1.Point0159.outputs,SourceMainFramesV1.Point0159.input_defined,SourceMainFramesV1.Point0159.outputs_defined,SourceMainFramesV1.Point0159.execution total⟩
end SourceMainFramesV1.Execution04
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution04.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
