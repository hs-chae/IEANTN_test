import SourceMainFramesV1.Execution00
import SourceMainFramesV1.Execution01
import SourceMainFramesV1.Execution02
import SourceMainFramesV1.Execution03
import SourceMainFramesV1.Execution04
import SourceMainFramesV1.Execution05
import SourceMainFramesV1.Execution06
import SourceMainFramesV1.Execution07
import SourceMainFramesV1.Execution08
import SourceMainFramesV1.Execution09
import SourceMainFramesV1.Execution10
import SourceMainFramesV1.Execution11
import SourceMainFramesV1.Execution12
import SourceMainFramesV1.Execution13
import SourceMainFramesV1.Execution14
import SourceMainFramesV1.Execution15
import SourceMainFramesV1.Execution16
import SourceMainFramesV1.Execution17
import SourceMainFramesV1.Execution18
import SourceMainFramesV1.Execution19
import SourceMainFramesV1.Execution20
import SourceMainFramesV1.Execution21
import SourceMainFramesV1.Execution22
import SourceMainFramesV1.Execution23
import Lean.Elab.Tactic.Omega
namespace SourceMainFramesV1.AllExecution
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (hi : i < logCellCount) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 change i < 768 at hi
 let j := i / 32
 have hj : j < 24 := by dsimp [j]; omega
 have lower : 32*j ≤ i := by dsimp [j]; omega
 have upper : i < 32*(j+1) := by dsimp [j]; omega
 interval_cases j
 · exact SourceMainFramesV1.Execution00.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution01.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution02.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution03.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution04.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution05.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution06.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution07.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution08.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution09.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution10.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution11.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution12.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution13.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution14.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution15.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution16.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution17.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution18.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution19.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution20.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution21.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution22.executions i (by omega) (by omega) total
 · exact SourceMainFramesV1.Execution23.executions i (by omega) (by omega) total
end SourceMainFramesV1.AllExecution
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.AllExecution.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
