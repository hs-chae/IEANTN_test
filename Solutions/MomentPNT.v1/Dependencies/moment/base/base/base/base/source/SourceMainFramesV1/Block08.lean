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
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block08
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 256 ≤ i) (upper : i < 288) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=256) (base:=SynergyHeightC.FullMainFrame.base total 256) (input:=SourceMainFramesV1.Point0256.input) (pair:=SourceMainFramesV1.Point0256.outputs) SourceMainFramesV1.Point0256.input_defined SourceMainFramesV1.Point0256.outputs_defined (SourceMainFramesV1.Point0256.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=257) (base:=SynergyHeightC.FullMainFrame.base total 257) (input:=SourceMainFramesV1.Point0257.input) (pair:=SourceMainFramesV1.Point0257.outputs) SourceMainFramesV1.Point0257.input_defined SourceMainFramesV1.Point0257.outputs_defined (SourceMainFramesV1.Point0257.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=258) (base:=SynergyHeightC.FullMainFrame.base total 258) (input:=SourceMainFramesV1.Point0258.input) (pair:=SourceMainFramesV1.Point0258.outputs) SourceMainFramesV1.Point0258.input_defined SourceMainFramesV1.Point0258.outputs_defined (SourceMainFramesV1.Point0258.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=259) (base:=SynergyHeightC.FullMainFrame.base total 259) (input:=SourceMainFramesV1.Point0259.input) (pair:=SourceMainFramesV1.Point0259.outputs) SourceMainFramesV1.Point0259.input_defined SourceMainFramesV1.Point0259.outputs_defined (SourceMainFramesV1.Point0259.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=260) (base:=SynergyHeightC.FullMainFrame.base total 260) (input:=SourceMainFramesV1.Point0260.input) (pair:=SourceMainFramesV1.Point0260.outputs) SourceMainFramesV1.Point0260.input_defined SourceMainFramesV1.Point0260.outputs_defined (SourceMainFramesV1.Point0260.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=261) (base:=SynergyHeightC.FullMainFrame.base total 261) (input:=SourceMainFramesV1.Point0261.input) (pair:=SourceMainFramesV1.Point0261.outputs) SourceMainFramesV1.Point0261.input_defined SourceMainFramesV1.Point0261.outputs_defined (SourceMainFramesV1.Point0261.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=262) (base:=SynergyHeightC.FullMainFrame.base total 262) (input:=SourceMainFramesV1.Point0262.input) (pair:=SourceMainFramesV1.Point0262.outputs) SourceMainFramesV1.Point0262.input_defined SourceMainFramesV1.Point0262.outputs_defined (SourceMainFramesV1.Point0262.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=263) (base:=SynergyHeightC.FullMainFrame.base total 263) (input:=SourceMainFramesV1.Point0263.input) (pair:=SourceMainFramesV1.Point0263.outputs) SourceMainFramesV1.Point0263.input_defined SourceMainFramesV1.Point0263.outputs_defined (SourceMainFramesV1.Point0263.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=264) (base:=SynergyHeightC.FullMainFrame.base total 264) (input:=SourceMainFramesV1.Point0264.input) (pair:=SourceMainFramesV1.Point0264.outputs) SourceMainFramesV1.Point0264.input_defined SourceMainFramesV1.Point0264.outputs_defined (SourceMainFramesV1.Point0264.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=265) (base:=SynergyHeightC.FullMainFrame.base total 265) (input:=SourceMainFramesV1.Point0265.input) (pair:=SourceMainFramesV1.Point0265.outputs) SourceMainFramesV1.Point0265.input_defined SourceMainFramesV1.Point0265.outputs_defined (SourceMainFramesV1.Point0265.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=266) (base:=SynergyHeightC.FullMainFrame.base total 266) (input:=SourceMainFramesV1.Point0266.input) (pair:=SourceMainFramesV1.Point0266.outputs) SourceMainFramesV1.Point0266.input_defined SourceMainFramesV1.Point0266.outputs_defined (SourceMainFramesV1.Point0266.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=267) (base:=SynergyHeightC.FullMainFrame.base total 267) (input:=SourceMainFramesV1.Point0267.input) (pair:=SourceMainFramesV1.Point0267.outputs) SourceMainFramesV1.Point0267.input_defined SourceMainFramesV1.Point0267.outputs_defined (SourceMainFramesV1.Point0267.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=268) (base:=SynergyHeightC.FullMainFrame.base total 268) (input:=SourceMainFramesV1.Point0268.input) (pair:=SourceMainFramesV1.Point0268.outputs) SourceMainFramesV1.Point0268.input_defined SourceMainFramesV1.Point0268.outputs_defined (SourceMainFramesV1.Point0268.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=269) (base:=SynergyHeightC.FullMainFrame.base total 269) (input:=SourceMainFramesV1.Point0269.input) (pair:=SourceMainFramesV1.Point0269.outputs) SourceMainFramesV1.Point0269.input_defined SourceMainFramesV1.Point0269.outputs_defined (SourceMainFramesV1.Point0269.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=270) (base:=SynergyHeightC.FullMainFrame.base total 270) (input:=SourceMainFramesV1.Point0270.input) (pair:=SourceMainFramesV1.Point0270.outputs) SourceMainFramesV1.Point0270.input_defined SourceMainFramesV1.Point0270.outputs_defined (SourceMainFramesV1.Point0270.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=271) (base:=SynergyHeightC.FullMainFrame.base total 271) (input:=SourceMainFramesV1.Point0271.input) (pair:=SourceMainFramesV1.Point0271.outputs) SourceMainFramesV1.Point0271.input_defined SourceMainFramesV1.Point0271.outputs_defined (SourceMainFramesV1.Point0271.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=272) (base:=SynergyHeightC.FullMainFrame.base total 272) (input:=SourceMainFramesV1.Point0272.input) (pair:=SourceMainFramesV1.Point0272.outputs) SourceMainFramesV1.Point0272.input_defined SourceMainFramesV1.Point0272.outputs_defined (SourceMainFramesV1.Point0272.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=273) (base:=SynergyHeightC.FullMainFrame.base total 273) (input:=SourceMainFramesV1.Point0273.input) (pair:=SourceMainFramesV1.Point0273.outputs) SourceMainFramesV1.Point0273.input_defined SourceMainFramesV1.Point0273.outputs_defined (SourceMainFramesV1.Point0273.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=274) (base:=SynergyHeightC.FullMainFrame.base total 274) (input:=SourceMainFramesV1.Point0274.input) (pair:=SourceMainFramesV1.Point0274.outputs) SourceMainFramesV1.Point0274.input_defined SourceMainFramesV1.Point0274.outputs_defined (SourceMainFramesV1.Point0274.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=275) (base:=SynergyHeightC.FullMainFrame.base total 275) (input:=SourceMainFramesV1.Point0275.input) (pair:=SourceMainFramesV1.Point0275.outputs) SourceMainFramesV1.Point0275.input_defined SourceMainFramesV1.Point0275.outputs_defined (SourceMainFramesV1.Point0275.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=276) (base:=SynergyHeightC.FullMainFrame.base total 276) (input:=SourceMainFramesV1.Point0276.input) (pair:=SourceMainFramesV1.Point0276.outputs) SourceMainFramesV1.Point0276.input_defined SourceMainFramesV1.Point0276.outputs_defined (SourceMainFramesV1.Point0276.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=277) (base:=SynergyHeightC.FullMainFrame.base total 277) (input:=SourceMainFramesV1.Point0277.input) (pair:=SourceMainFramesV1.Point0277.outputs) SourceMainFramesV1.Point0277.input_defined SourceMainFramesV1.Point0277.outputs_defined (SourceMainFramesV1.Point0277.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=278) (base:=SynergyHeightC.FullMainFrame.base total 278) (input:=SourceMainFramesV1.Point0278.input) (pair:=SourceMainFramesV1.Point0278.outputs) SourceMainFramesV1.Point0278.input_defined SourceMainFramesV1.Point0278.outputs_defined (SourceMainFramesV1.Point0278.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=279) (base:=SynergyHeightC.FullMainFrame.base total 279) (input:=SourceMainFramesV1.Point0279.input) (pair:=SourceMainFramesV1.Point0279.outputs) SourceMainFramesV1.Point0279.input_defined SourceMainFramesV1.Point0279.outputs_defined (SourceMainFramesV1.Point0279.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=280) (base:=SynergyHeightC.FullMainFrame.base total 280) (input:=SourceMainFramesV1.Point0280.input) (pair:=SourceMainFramesV1.Point0280.outputs) SourceMainFramesV1.Point0280.input_defined SourceMainFramesV1.Point0280.outputs_defined (SourceMainFramesV1.Point0280.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=281) (base:=SynergyHeightC.FullMainFrame.base total 281) (input:=SourceMainFramesV1.Point0281.input) (pair:=SourceMainFramesV1.Point0281.outputs) SourceMainFramesV1.Point0281.input_defined SourceMainFramesV1.Point0281.outputs_defined (SourceMainFramesV1.Point0281.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=282) (base:=SynergyHeightC.FullMainFrame.base total 282) (input:=SourceMainFramesV1.Point0282.input) (pair:=SourceMainFramesV1.Point0282.outputs) SourceMainFramesV1.Point0282.input_defined SourceMainFramesV1.Point0282.outputs_defined (SourceMainFramesV1.Point0282.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=283) (base:=SynergyHeightC.FullMainFrame.base total 283) (input:=SourceMainFramesV1.Point0283.input) (pair:=SourceMainFramesV1.Point0283.outputs) SourceMainFramesV1.Point0283.input_defined SourceMainFramesV1.Point0283.outputs_defined (SourceMainFramesV1.Point0283.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=284) (base:=SynergyHeightC.FullMainFrame.base total 284) (input:=SourceMainFramesV1.Point0284.input) (pair:=SourceMainFramesV1.Point0284.outputs) SourceMainFramesV1.Point0284.input_defined SourceMainFramesV1.Point0284.outputs_defined (SourceMainFramesV1.Point0284.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=285) (base:=SynergyHeightC.FullMainFrame.base total 285) (input:=SourceMainFramesV1.Point0285.input) (pair:=SourceMainFramesV1.Point0285.outputs) SourceMainFramesV1.Point0285.input_defined SourceMainFramesV1.Point0285.outputs_defined (SourceMainFramesV1.Point0285.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=286) (base:=SynergyHeightC.FullMainFrame.base total 286) (input:=SourceMainFramesV1.Point0286.input) (pair:=SourceMainFramesV1.Point0286.outputs) SourceMainFramesV1.Point0286.input_defined SourceMainFramesV1.Point0286.outputs_defined (SourceMainFramesV1.Point0286.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=287) (base:=SynergyHeightC.FullMainFrame.base total 287) (input:=SourceMainFramesV1.Point0287.input) (pair:=SourceMainFramesV1.Point0287.outputs) SourceMainFramesV1.Point0287.input_defined SourceMainFramesV1.Point0287.outputs_defined (SourceMainFramesV1.Point0287.source_outputs total)
end SourceMainFramesV1.Block08
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block08.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
