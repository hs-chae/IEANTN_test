import SourceMainFramesV1.Point0032
import SourceMainFramesV1.Point0033
import SourceMainFramesV1.Point0034
import SourceMainFramesV1.Point0035
import SourceMainFramesV1.Point0036
import SourceMainFramesV1.Point0037
import SourceMainFramesV1.Point0038
import SourceMainFramesV1.Point0039
import SourceMainFramesV1.Point0040
import SourceMainFramesV1.Point0041
import SourceMainFramesV1.Point0042
import SourceMainFramesV1.Point0043
import SourceMainFramesV1.Point0044
import SourceMainFramesV1.Point0045
import SourceMainFramesV1.Point0046
import SourceMainFramesV1.Point0047
import SourceMainFramesV1.Point0048
import SourceMainFramesV1.Point0049
import SourceMainFramesV1.Point0050
import SourceMainFramesV1.Point0051
import SourceMainFramesV1.Point0052
import SourceMainFramesV1.Point0053
import SourceMainFramesV1.Point0054
import SourceMainFramesV1.Point0055
import SourceMainFramesV1.Point0056
import SourceMainFramesV1.Point0057
import SourceMainFramesV1.Point0058
import SourceMainFramesV1.Point0059
import SourceMainFramesV1.Point0060
import SourceMainFramesV1.Point0061
import SourceMainFramesV1.Point0062
import SourceMainFramesV1.Point0063
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution01
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 32 ≤ i) (upper : i < 64) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0032.input,SourceMainFramesV1.Point0032.outputs,SourceMainFramesV1.Point0032.input_defined,SourceMainFramesV1.Point0032.outputs_defined,SourceMainFramesV1.Point0032.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0033.input,SourceMainFramesV1.Point0033.outputs,SourceMainFramesV1.Point0033.input_defined,SourceMainFramesV1.Point0033.outputs_defined,SourceMainFramesV1.Point0033.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0034.input,SourceMainFramesV1.Point0034.outputs,SourceMainFramesV1.Point0034.input_defined,SourceMainFramesV1.Point0034.outputs_defined,SourceMainFramesV1.Point0034.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0035.input,SourceMainFramesV1.Point0035.outputs,SourceMainFramesV1.Point0035.input_defined,SourceMainFramesV1.Point0035.outputs_defined,SourceMainFramesV1.Point0035.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0036.input,SourceMainFramesV1.Point0036.outputs,SourceMainFramesV1.Point0036.input_defined,SourceMainFramesV1.Point0036.outputs_defined,SourceMainFramesV1.Point0036.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0037.input,SourceMainFramesV1.Point0037.outputs,SourceMainFramesV1.Point0037.input_defined,SourceMainFramesV1.Point0037.outputs_defined,SourceMainFramesV1.Point0037.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0038.input,SourceMainFramesV1.Point0038.outputs,SourceMainFramesV1.Point0038.input_defined,SourceMainFramesV1.Point0038.outputs_defined,SourceMainFramesV1.Point0038.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0039.input,SourceMainFramesV1.Point0039.outputs,SourceMainFramesV1.Point0039.input_defined,SourceMainFramesV1.Point0039.outputs_defined,SourceMainFramesV1.Point0039.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0040.input,SourceMainFramesV1.Point0040.outputs,SourceMainFramesV1.Point0040.input_defined,SourceMainFramesV1.Point0040.outputs_defined,SourceMainFramesV1.Point0040.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0041.input,SourceMainFramesV1.Point0041.outputs,SourceMainFramesV1.Point0041.input_defined,SourceMainFramesV1.Point0041.outputs_defined,SourceMainFramesV1.Point0041.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0042.input,SourceMainFramesV1.Point0042.outputs,SourceMainFramesV1.Point0042.input_defined,SourceMainFramesV1.Point0042.outputs_defined,SourceMainFramesV1.Point0042.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0043.input,SourceMainFramesV1.Point0043.outputs,SourceMainFramesV1.Point0043.input_defined,SourceMainFramesV1.Point0043.outputs_defined,SourceMainFramesV1.Point0043.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0044.input,SourceMainFramesV1.Point0044.outputs,SourceMainFramesV1.Point0044.input_defined,SourceMainFramesV1.Point0044.outputs_defined,SourceMainFramesV1.Point0044.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0045.input,SourceMainFramesV1.Point0045.outputs,SourceMainFramesV1.Point0045.input_defined,SourceMainFramesV1.Point0045.outputs_defined,SourceMainFramesV1.Point0045.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0046.input,SourceMainFramesV1.Point0046.outputs,SourceMainFramesV1.Point0046.input_defined,SourceMainFramesV1.Point0046.outputs_defined,SourceMainFramesV1.Point0046.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0047.input,SourceMainFramesV1.Point0047.outputs,SourceMainFramesV1.Point0047.input_defined,SourceMainFramesV1.Point0047.outputs_defined,SourceMainFramesV1.Point0047.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0048.input,SourceMainFramesV1.Point0048.outputs,SourceMainFramesV1.Point0048.input_defined,SourceMainFramesV1.Point0048.outputs_defined,SourceMainFramesV1.Point0048.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0049.input,SourceMainFramesV1.Point0049.outputs,SourceMainFramesV1.Point0049.input_defined,SourceMainFramesV1.Point0049.outputs_defined,SourceMainFramesV1.Point0049.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0050.input,SourceMainFramesV1.Point0050.outputs,SourceMainFramesV1.Point0050.input_defined,SourceMainFramesV1.Point0050.outputs_defined,SourceMainFramesV1.Point0050.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0051.input,SourceMainFramesV1.Point0051.outputs,SourceMainFramesV1.Point0051.input_defined,SourceMainFramesV1.Point0051.outputs_defined,SourceMainFramesV1.Point0051.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0052.input,SourceMainFramesV1.Point0052.outputs,SourceMainFramesV1.Point0052.input_defined,SourceMainFramesV1.Point0052.outputs_defined,SourceMainFramesV1.Point0052.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0053.input,SourceMainFramesV1.Point0053.outputs,SourceMainFramesV1.Point0053.input_defined,SourceMainFramesV1.Point0053.outputs_defined,SourceMainFramesV1.Point0053.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0054.input,SourceMainFramesV1.Point0054.outputs,SourceMainFramesV1.Point0054.input_defined,SourceMainFramesV1.Point0054.outputs_defined,SourceMainFramesV1.Point0054.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0055.input,SourceMainFramesV1.Point0055.outputs,SourceMainFramesV1.Point0055.input_defined,SourceMainFramesV1.Point0055.outputs_defined,SourceMainFramesV1.Point0055.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0056.input,SourceMainFramesV1.Point0056.outputs,SourceMainFramesV1.Point0056.input_defined,SourceMainFramesV1.Point0056.outputs_defined,SourceMainFramesV1.Point0056.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0057.input,SourceMainFramesV1.Point0057.outputs,SourceMainFramesV1.Point0057.input_defined,SourceMainFramesV1.Point0057.outputs_defined,SourceMainFramesV1.Point0057.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0058.input,SourceMainFramesV1.Point0058.outputs,SourceMainFramesV1.Point0058.input_defined,SourceMainFramesV1.Point0058.outputs_defined,SourceMainFramesV1.Point0058.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0059.input,SourceMainFramesV1.Point0059.outputs,SourceMainFramesV1.Point0059.input_defined,SourceMainFramesV1.Point0059.outputs_defined,SourceMainFramesV1.Point0059.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0060.input,SourceMainFramesV1.Point0060.outputs,SourceMainFramesV1.Point0060.input_defined,SourceMainFramesV1.Point0060.outputs_defined,SourceMainFramesV1.Point0060.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0061.input,SourceMainFramesV1.Point0061.outputs,SourceMainFramesV1.Point0061.input_defined,SourceMainFramesV1.Point0061.outputs_defined,SourceMainFramesV1.Point0061.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0062.input,SourceMainFramesV1.Point0062.outputs,SourceMainFramesV1.Point0062.input_defined,SourceMainFramesV1.Point0062.outputs_defined,SourceMainFramesV1.Point0062.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0063.input,SourceMainFramesV1.Point0063.outputs,SourceMainFramesV1.Point0063.input_defined,SourceMainFramesV1.Point0063.outputs_defined,SourceMainFramesV1.Point0063.execution total⟩
end SourceMainFramesV1.Execution01
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution01.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
