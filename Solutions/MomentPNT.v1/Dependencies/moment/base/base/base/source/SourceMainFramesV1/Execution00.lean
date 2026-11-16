import SourceMainFramesV1.Point0000
import SourceMainFramesV1.Point0001
import SourceMainFramesV1.Point0002
import SourceMainFramesV1.Point0003
import SourceMainFramesV1.Point0004
import SourceMainFramesV1.Point0005
import SourceMainFramesV1.Point0006
import SourceMainFramesV1.Point0007
import SourceMainFramesV1.Point0008
import SourceMainFramesV1.Point0009
import SourceMainFramesV1.Point0010
import SourceMainFramesV1.Point0011
import SourceMainFramesV1.Point0012
import SourceMainFramesV1.Point0013
import SourceMainFramesV1.Point0014
import SourceMainFramesV1.Point0015
import SourceMainFramesV1.Point0016
import SourceMainFramesV1.Point0017
import SourceMainFramesV1.Point0018
import SourceMainFramesV1.Point0019
import SourceMainFramesV1.Point0020
import SourceMainFramesV1.Point0021
import SourceMainFramesV1.Point0022
import SourceMainFramesV1.Point0023
import SourceMainFramesV1.Point0024
import SourceMainFramesV1.Point0025
import SourceMainFramesV1.Point0026
import SourceMainFramesV1.Point0027
import SourceMainFramesV1.Point0028
import SourceMainFramesV1.Point0029
import SourceMainFramesV1.Point0030
import SourceMainFramesV1.Point0031
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution00
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 0 ≤ i) (upper : i < 32) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0000.input,SourceMainFramesV1.Point0000.outputs,SourceMainFramesV1.Point0000.input_defined,SourceMainFramesV1.Point0000.outputs_defined,SourceMainFramesV1.Point0000.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0001.input,SourceMainFramesV1.Point0001.outputs,SourceMainFramesV1.Point0001.input_defined,SourceMainFramesV1.Point0001.outputs_defined,SourceMainFramesV1.Point0001.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0002.input,SourceMainFramesV1.Point0002.outputs,SourceMainFramesV1.Point0002.input_defined,SourceMainFramesV1.Point0002.outputs_defined,SourceMainFramesV1.Point0002.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0003.input,SourceMainFramesV1.Point0003.outputs,SourceMainFramesV1.Point0003.input_defined,SourceMainFramesV1.Point0003.outputs_defined,SourceMainFramesV1.Point0003.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0004.input,SourceMainFramesV1.Point0004.outputs,SourceMainFramesV1.Point0004.input_defined,SourceMainFramesV1.Point0004.outputs_defined,SourceMainFramesV1.Point0004.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0005.input,SourceMainFramesV1.Point0005.outputs,SourceMainFramesV1.Point0005.input_defined,SourceMainFramesV1.Point0005.outputs_defined,SourceMainFramesV1.Point0005.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0006.input,SourceMainFramesV1.Point0006.outputs,SourceMainFramesV1.Point0006.input_defined,SourceMainFramesV1.Point0006.outputs_defined,SourceMainFramesV1.Point0006.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0007.input,SourceMainFramesV1.Point0007.outputs,SourceMainFramesV1.Point0007.input_defined,SourceMainFramesV1.Point0007.outputs_defined,SourceMainFramesV1.Point0007.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0008.input,SourceMainFramesV1.Point0008.outputs,SourceMainFramesV1.Point0008.input_defined,SourceMainFramesV1.Point0008.outputs_defined,SourceMainFramesV1.Point0008.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0009.input,SourceMainFramesV1.Point0009.outputs,SourceMainFramesV1.Point0009.input_defined,SourceMainFramesV1.Point0009.outputs_defined,SourceMainFramesV1.Point0009.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0010.input,SourceMainFramesV1.Point0010.outputs,SourceMainFramesV1.Point0010.input_defined,SourceMainFramesV1.Point0010.outputs_defined,SourceMainFramesV1.Point0010.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0011.input,SourceMainFramesV1.Point0011.outputs,SourceMainFramesV1.Point0011.input_defined,SourceMainFramesV1.Point0011.outputs_defined,SourceMainFramesV1.Point0011.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0012.input,SourceMainFramesV1.Point0012.outputs,SourceMainFramesV1.Point0012.input_defined,SourceMainFramesV1.Point0012.outputs_defined,SourceMainFramesV1.Point0012.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0013.input,SourceMainFramesV1.Point0013.outputs,SourceMainFramesV1.Point0013.input_defined,SourceMainFramesV1.Point0013.outputs_defined,SourceMainFramesV1.Point0013.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0014.input,SourceMainFramesV1.Point0014.outputs,SourceMainFramesV1.Point0014.input_defined,SourceMainFramesV1.Point0014.outputs_defined,SourceMainFramesV1.Point0014.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0015.input,SourceMainFramesV1.Point0015.outputs,SourceMainFramesV1.Point0015.input_defined,SourceMainFramesV1.Point0015.outputs_defined,SourceMainFramesV1.Point0015.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0016.input,SourceMainFramesV1.Point0016.outputs,SourceMainFramesV1.Point0016.input_defined,SourceMainFramesV1.Point0016.outputs_defined,SourceMainFramesV1.Point0016.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0017.input,SourceMainFramesV1.Point0017.outputs,SourceMainFramesV1.Point0017.input_defined,SourceMainFramesV1.Point0017.outputs_defined,SourceMainFramesV1.Point0017.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0018.input,SourceMainFramesV1.Point0018.outputs,SourceMainFramesV1.Point0018.input_defined,SourceMainFramesV1.Point0018.outputs_defined,SourceMainFramesV1.Point0018.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0019.input,SourceMainFramesV1.Point0019.outputs,SourceMainFramesV1.Point0019.input_defined,SourceMainFramesV1.Point0019.outputs_defined,SourceMainFramesV1.Point0019.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0020.input,SourceMainFramesV1.Point0020.outputs,SourceMainFramesV1.Point0020.input_defined,SourceMainFramesV1.Point0020.outputs_defined,SourceMainFramesV1.Point0020.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0021.input,SourceMainFramesV1.Point0021.outputs,SourceMainFramesV1.Point0021.input_defined,SourceMainFramesV1.Point0021.outputs_defined,SourceMainFramesV1.Point0021.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0022.input,SourceMainFramesV1.Point0022.outputs,SourceMainFramesV1.Point0022.input_defined,SourceMainFramesV1.Point0022.outputs_defined,SourceMainFramesV1.Point0022.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0023.input,SourceMainFramesV1.Point0023.outputs,SourceMainFramesV1.Point0023.input_defined,SourceMainFramesV1.Point0023.outputs_defined,SourceMainFramesV1.Point0023.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0024.input,SourceMainFramesV1.Point0024.outputs,SourceMainFramesV1.Point0024.input_defined,SourceMainFramesV1.Point0024.outputs_defined,SourceMainFramesV1.Point0024.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0025.input,SourceMainFramesV1.Point0025.outputs,SourceMainFramesV1.Point0025.input_defined,SourceMainFramesV1.Point0025.outputs_defined,SourceMainFramesV1.Point0025.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0026.input,SourceMainFramesV1.Point0026.outputs,SourceMainFramesV1.Point0026.input_defined,SourceMainFramesV1.Point0026.outputs_defined,SourceMainFramesV1.Point0026.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0027.input,SourceMainFramesV1.Point0027.outputs,SourceMainFramesV1.Point0027.input_defined,SourceMainFramesV1.Point0027.outputs_defined,SourceMainFramesV1.Point0027.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0028.input,SourceMainFramesV1.Point0028.outputs,SourceMainFramesV1.Point0028.input_defined,SourceMainFramesV1.Point0028.outputs_defined,SourceMainFramesV1.Point0028.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0029.input,SourceMainFramesV1.Point0029.outputs,SourceMainFramesV1.Point0029.input_defined,SourceMainFramesV1.Point0029.outputs_defined,SourceMainFramesV1.Point0029.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0030.input,SourceMainFramesV1.Point0030.outputs,SourceMainFramesV1.Point0030.input_defined,SourceMainFramesV1.Point0030.outputs_defined,SourceMainFramesV1.Point0030.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0031.input,SourceMainFramesV1.Point0031.outputs,SourceMainFramesV1.Point0031.input_defined,SourceMainFramesV1.Point0031.outputs_defined,SourceMainFramesV1.Point0031.execution total⟩
end SourceMainFramesV1.Execution00
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution00.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
