import SourceMainFramesV1.Point0256
import SourceMainFramesV1.Point0257
import SourceMainFramesV1.Point0258
import SourceMainFramesV1.Point0259
import SourceMainFramesV1.Point0260
import SourceMainFramesV1.Point0261
import SourceMainFramesV1.Point0262
import SourceMainFramesV1.Point0263
import SourceMainFramesV1.Point0264
import SourceMainFramesV1.Point0265
import SourceMainFramesV1.Point0266
import SourceMainFramesV1.Point0267
import SourceMainFramesV1.Point0268
import SourceMainFramesV1.Point0269
import SourceMainFramesV1.Point0270
import SourceMainFramesV1.Point0271
import SourceMainFramesV1.Point0272
import SourceMainFramesV1.Point0273
import SourceMainFramesV1.Point0274
import SourceMainFramesV1.Point0275
import SourceMainFramesV1.Point0276
import SourceMainFramesV1.Point0277
import SourceMainFramesV1.Point0278
import SourceMainFramesV1.Point0279
import SourceMainFramesV1.Point0280
import SourceMainFramesV1.Point0281
import SourceMainFramesV1.Point0282
import SourceMainFramesV1.Point0283
import SourceMainFramesV1.Point0284
import SourceMainFramesV1.Point0285
import SourceMainFramesV1.Point0286
import SourceMainFramesV1.Point0287
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Execution08
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem executions (i : Nat) (lower : 256 ≤ i) (upper : i < 288) (total : ProofBox) :
 ∃ input pair, logCell (i+1)=some input ∧ modelOutputs input=some pair ∧
  FullContractPointExecute.run (FullMainFrame.base total i) input=
   some (.unit,filled (FullMainFrame.base total i) pair.1 pair.2) := by
 interval_cases i
 · exact ⟨SourceMainFramesV1.Point0256.input,SourceMainFramesV1.Point0256.outputs,SourceMainFramesV1.Point0256.input_defined,SourceMainFramesV1.Point0256.outputs_defined,SourceMainFramesV1.Point0256.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0257.input,SourceMainFramesV1.Point0257.outputs,SourceMainFramesV1.Point0257.input_defined,SourceMainFramesV1.Point0257.outputs_defined,SourceMainFramesV1.Point0257.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0258.input,SourceMainFramesV1.Point0258.outputs,SourceMainFramesV1.Point0258.input_defined,SourceMainFramesV1.Point0258.outputs_defined,SourceMainFramesV1.Point0258.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0259.input,SourceMainFramesV1.Point0259.outputs,SourceMainFramesV1.Point0259.input_defined,SourceMainFramesV1.Point0259.outputs_defined,SourceMainFramesV1.Point0259.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0260.input,SourceMainFramesV1.Point0260.outputs,SourceMainFramesV1.Point0260.input_defined,SourceMainFramesV1.Point0260.outputs_defined,SourceMainFramesV1.Point0260.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0261.input,SourceMainFramesV1.Point0261.outputs,SourceMainFramesV1.Point0261.input_defined,SourceMainFramesV1.Point0261.outputs_defined,SourceMainFramesV1.Point0261.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0262.input,SourceMainFramesV1.Point0262.outputs,SourceMainFramesV1.Point0262.input_defined,SourceMainFramesV1.Point0262.outputs_defined,SourceMainFramesV1.Point0262.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0263.input,SourceMainFramesV1.Point0263.outputs,SourceMainFramesV1.Point0263.input_defined,SourceMainFramesV1.Point0263.outputs_defined,SourceMainFramesV1.Point0263.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0264.input,SourceMainFramesV1.Point0264.outputs,SourceMainFramesV1.Point0264.input_defined,SourceMainFramesV1.Point0264.outputs_defined,SourceMainFramesV1.Point0264.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0265.input,SourceMainFramesV1.Point0265.outputs,SourceMainFramesV1.Point0265.input_defined,SourceMainFramesV1.Point0265.outputs_defined,SourceMainFramesV1.Point0265.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0266.input,SourceMainFramesV1.Point0266.outputs,SourceMainFramesV1.Point0266.input_defined,SourceMainFramesV1.Point0266.outputs_defined,SourceMainFramesV1.Point0266.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0267.input,SourceMainFramesV1.Point0267.outputs,SourceMainFramesV1.Point0267.input_defined,SourceMainFramesV1.Point0267.outputs_defined,SourceMainFramesV1.Point0267.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0268.input,SourceMainFramesV1.Point0268.outputs,SourceMainFramesV1.Point0268.input_defined,SourceMainFramesV1.Point0268.outputs_defined,SourceMainFramesV1.Point0268.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0269.input,SourceMainFramesV1.Point0269.outputs,SourceMainFramesV1.Point0269.input_defined,SourceMainFramesV1.Point0269.outputs_defined,SourceMainFramesV1.Point0269.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0270.input,SourceMainFramesV1.Point0270.outputs,SourceMainFramesV1.Point0270.input_defined,SourceMainFramesV1.Point0270.outputs_defined,SourceMainFramesV1.Point0270.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0271.input,SourceMainFramesV1.Point0271.outputs,SourceMainFramesV1.Point0271.input_defined,SourceMainFramesV1.Point0271.outputs_defined,SourceMainFramesV1.Point0271.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0272.input,SourceMainFramesV1.Point0272.outputs,SourceMainFramesV1.Point0272.input_defined,SourceMainFramesV1.Point0272.outputs_defined,SourceMainFramesV1.Point0272.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0273.input,SourceMainFramesV1.Point0273.outputs,SourceMainFramesV1.Point0273.input_defined,SourceMainFramesV1.Point0273.outputs_defined,SourceMainFramesV1.Point0273.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0274.input,SourceMainFramesV1.Point0274.outputs,SourceMainFramesV1.Point0274.input_defined,SourceMainFramesV1.Point0274.outputs_defined,SourceMainFramesV1.Point0274.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0275.input,SourceMainFramesV1.Point0275.outputs,SourceMainFramesV1.Point0275.input_defined,SourceMainFramesV1.Point0275.outputs_defined,SourceMainFramesV1.Point0275.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0276.input,SourceMainFramesV1.Point0276.outputs,SourceMainFramesV1.Point0276.input_defined,SourceMainFramesV1.Point0276.outputs_defined,SourceMainFramesV1.Point0276.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0277.input,SourceMainFramesV1.Point0277.outputs,SourceMainFramesV1.Point0277.input_defined,SourceMainFramesV1.Point0277.outputs_defined,SourceMainFramesV1.Point0277.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0278.input,SourceMainFramesV1.Point0278.outputs,SourceMainFramesV1.Point0278.input_defined,SourceMainFramesV1.Point0278.outputs_defined,SourceMainFramesV1.Point0278.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0279.input,SourceMainFramesV1.Point0279.outputs,SourceMainFramesV1.Point0279.input_defined,SourceMainFramesV1.Point0279.outputs_defined,SourceMainFramesV1.Point0279.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0280.input,SourceMainFramesV1.Point0280.outputs,SourceMainFramesV1.Point0280.input_defined,SourceMainFramesV1.Point0280.outputs_defined,SourceMainFramesV1.Point0280.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0281.input,SourceMainFramesV1.Point0281.outputs,SourceMainFramesV1.Point0281.input_defined,SourceMainFramesV1.Point0281.outputs_defined,SourceMainFramesV1.Point0281.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0282.input,SourceMainFramesV1.Point0282.outputs,SourceMainFramesV1.Point0282.input_defined,SourceMainFramesV1.Point0282.outputs_defined,SourceMainFramesV1.Point0282.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0283.input,SourceMainFramesV1.Point0283.outputs,SourceMainFramesV1.Point0283.input_defined,SourceMainFramesV1.Point0283.outputs_defined,SourceMainFramesV1.Point0283.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0284.input,SourceMainFramesV1.Point0284.outputs,SourceMainFramesV1.Point0284.input_defined,SourceMainFramesV1.Point0284.outputs_defined,SourceMainFramesV1.Point0284.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0285.input,SourceMainFramesV1.Point0285.outputs,SourceMainFramesV1.Point0285.input_defined,SourceMainFramesV1.Point0285.outputs_defined,SourceMainFramesV1.Point0285.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0286.input,SourceMainFramesV1.Point0286.outputs,SourceMainFramesV1.Point0286.input_defined,SourceMainFramesV1.Point0286.outputs_defined,SourceMainFramesV1.Point0286.execution total⟩
 · exact ⟨SourceMainFramesV1.Point0287.input,SourceMainFramesV1.Point0287.outputs,SourceMainFramesV1.Point0287.input_defined,SourceMainFramesV1.Point0287.outputs_defined,SourceMainFramesV1.Point0287.execution total⟩
end SourceMainFramesV1.Execution08
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Execution08.executions
 let env ← getEnv
 let some ci := env.find? n | throwError "missing execution provider"
 let ax ← Lean.collectAxioms n
 logInfo m!"EXECUTION_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
