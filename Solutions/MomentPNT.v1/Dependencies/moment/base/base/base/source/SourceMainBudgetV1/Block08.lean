import SourceMainBudgetV1.Cell0256
import SourceHeightEdgesV1.Edge0256
import SourceMainBudgetV1.Cell0257
import SourceHeightEdgesV1.Edge0257
import SourceMainBudgetV1.Cell0258
import SourceHeightEdgesV1.Edge0258
import SourceMainBudgetV1.Cell0259
import SourceHeightEdgesV1.Edge0259
import SourceMainBudgetV1.Cell0260
import SourceHeightEdgesV1.Edge0260
import SourceMainBudgetV1.Cell0261
import SourceHeightEdgesV1.Edge0261
import SourceMainBudgetV1.Cell0262
import SourceHeightEdgesV1.Edge0262
import SourceMainBudgetV1.Cell0263
import SourceHeightEdgesV1.Edge0263
import SourceMainBudgetV1.Cell0264
import SourceHeightEdgesV1.Edge0264
import SourceMainBudgetV1.Cell0265
import SourceHeightEdgesV1.Edge0265
import SourceMainBudgetV1.Cell0266
import SourceHeightEdgesV1.Edge0266
import SourceMainBudgetV1.Cell0267
import SourceHeightEdgesV1.Edge0267
import SourceMainBudgetV1.Cell0268
import SourceHeightEdgesV1.Edge0268
import SourceMainBudgetV1.Cell0269
import SourceHeightEdgesV1.Edge0269
import SourceMainBudgetV1.Cell0270
import SourceHeightEdgesV1.Edge0270
import SourceMainBudgetV1.Cell0271
import SourceHeightEdgesV1.Edge0271
import SourceMainBudgetV1.Cell0272
import SourceHeightEdgesV1.Edge0272
import SourceMainBudgetV1.Cell0273
import SourceHeightEdgesV1.Edge0273
import SourceMainBudgetV1.Cell0274
import SourceHeightEdgesV1.Edge0274
import SourceMainBudgetV1.Cell0275
import SourceHeightEdgesV1.Edge0275
import SourceMainBudgetV1.Cell0276
import SourceHeightEdgesV1.Edge0276
import SourceMainBudgetV1.Cell0277
import SourceHeightEdgesV1.Edge0277
import SourceMainBudgetV1.Cell0278
import SourceHeightEdgesV1.Edge0278
import SourceMainBudgetV1.Cell0279
import SourceHeightEdgesV1.Edge0279
import SourceMainBudgetV1.Cell0280
import SourceHeightEdgesV1.Edge0280
import SourceMainBudgetV1.Cell0281
import SourceHeightEdgesV1.Edge0281
import SourceMainBudgetV1.Cell0282
import SourceHeightEdgesV1.Edge0282
import SourceMainBudgetV1.Cell0283
import SourceHeightEdgesV1.Edge0283
import SourceMainBudgetV1.Cell0284
import SourceHeightEdgesV1.Edge0284
import SourceMainBudgetV1.Cell0285
import SourceHeightEdgesV1.Edge0285
import SourceMainBudgetV1.Cell0286
import SourceHeightEdgesV1.Edge0286
import SourceMainBudgetV1.Cell0287
import SourceHeightEdgesV1.Edge0287
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block08
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 256 ≤ i) (upper : i < 288) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=256) (input:=SourceMainFramesV1.Point0256.input) (pair:=SourceMainFramesV1.Point0256.outputs) SourceHeightEdgesV1.Edge0256.left_defined SourceMainFramesV1.Point0256.input_defined SourceMainFramesV1.Point0256.outputs_defined SourceMainBudgetV1.Cell0256.execution SourceMainBudgetV1.Cell0256.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=257) (input:=SourceMainFramesV1.Point0257.input) (pair:=SourceMainFramesV1.Point0257.outputs) SourceHeightEdgesV1.Edge0257.left_defined SourceMainFramesV1.Point0257.input_defined SourceMainFramesV1.Point0257.outputs_defined SourceMainBudgetV1.Cell0257.execution SourceMainBudgetV1.Cell0257.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=258) (input:=SourceMainFramesV1.Point0258.input) (pair:=SourceMainFramesV1.Point0258.outputs) SourceHeightEdgesV1.Edge0258.left_defined SourceMainFramesV1.Point0258.input_defined SourceMainFramesV1.Point0258.outputs_defined SourceMainBudgetV1.Cell0258.execution SourceMainBudgetV1.Cell0258.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=259) (input:=SourceMainFramesV1.Point0259.input) (pair:=SourceMainFramesV1.Point0259.outputs) SourceHeightEdgesV1.Edge0259.left_defined SourceMainFramesV1.Point0259.input_defined SourceMainFramesV1.Point0259.outputs_defined SourceMainBudgetV1.Cell0259.execution SourceMainBudgetV1.Cell0259.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=260) (input:=SourceMainFramesV1.Point0260.input) (pair:=SourceMainFramesV1.Point0260.outputs) SourceHeightEdgesV1.Edge0260.left_defined SourceMainFramesV1.Point0260.input_defined SourceMainFramesV1.Point0260.outputs_defined SourceMainBudgetV1.Cell0260.execution SourceMainBudgetV1.Cell0260.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=261) (input:=SourceMainFramesV1.Point0261.input) (pair:=SourceMainFramesV1.Point0261.outputs) SourceHeightEdgesV1.Edge0261.left_defined SourceMainFramesV1.Point0261.input_defined SourceMainFramesV1.Point0261.outputs_defined SourceMainBudgetV1.Cell0261.execution SourceMainBudgetV1.Cell0261.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=262) (input:=SourceMainFramesV1.Point0262.input) (pair:=SourceMainFramesV1.Point0262.outputs) SourceHeightEdgesV1.Edge0262.left_defined SourceMainFramesV1.Point0262.input_defined SourceMainFramesV1.Point0262.outputs_defined SourceMainBudgetV1.Cell0262.execution SourceMainBudgetV1.Cell0262.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=263) (input:=SourceMainFramesV1.Point0263.input) (pair:=SourceMainFramesV1.Point0263.outputs) SourceHeightEdgesV1.Edge0263.left_defined SourceMainFramesV1.Point0263.input_defined SourceMainFramesV1.Point0263.outputs_defined SourceMainBudgetV1.Cell0263.execution SourceMainBudgetV1.Cell0263.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=264) (input:=SourceMainFramesV1.Point0264.input) (pair:=SourceMainFramesV1.Point0264.outputs) SourceHeightEdgesV1.Edge0264.left_defined SourceMainFramesV1.Point0264.input_defined SourceMainFramesV1.Point0264.outputs_defined SourceMainBudgetV1.Cell0264.execution SourceMainBudgetV1.Cell0264.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=265) (input:=SourceMainFramesV1.Point0265.input) (pair:=SourceMainFramesV1.Point0265.outputs) SourceHeightEdgesV1.Edge0265.left_defined SourceMainFramesV1.Point0265.input_defined SourceMainFramesV1.Point0265.outputs_defined SourceMainBudgetV1.Cell0265.execution SourceMainBudgetV1.Cell0265.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=266) (input:=SourceMainFramesV1.Point0266.input) (pair:=SourceMainFramesV1.Point0266.outputs) SourceHeightEdgesV1.Edge0266.left_defined SourceMainFramesV1.Point0266.input_defined SourceMainFramesV1.Point0266.outputs_defined SourceMainBudgetV1.Cell0266.execution SourceMainBudgetV1.Cell0266.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=267) (input:=SourceMainFramesV1.Point0267.input) (pair:=SourceMainFramesV1.Point0267.outputs) SourceHeightEdgesV1.Edge0267.left_defined SourceMainFramesV1.Point0267.input_defined SourceMainFramesV1.Point0267.outputs_defined SourceMainBudgetV1.Cell0267.execution SourceMainBudgetV1.Cell0267.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=268) (input:=SourceMainFramesV1.Point0268.input) (pair:=SourceMainFramesV1.Point0268.outputs) SourceHeightEdgesV1.Edge0268.left_defined SourceMainFramesV1.Point0268.input_defined SourceMainFramesV1.Point0268.outputs_defined SourceMainBudgetV1.Cell0268.execution SourceMainBudgetV1.Cell0268.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=269) (input:=SourceMainFramesV1.Point0269.input) (pair:=SourceMainFramesV1.Point0269.outputs) SourceHeightEdgesV1.Edge0269.left_defined SourceMainFramesV1.Point0269.input_defined SourceMainFramesV1.Point0269.outputs_defined SourceMainBudgetV1.Cell0269.execution SourceMainBudgetV1.Cell0269.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=270) (input:=SourceMainFramesV1.Point0270.input) (pair:=SourceMainFramesV1.Point0270.outputs) SourceHeightEdgesV1.Edge0270.left_defined SourceMainFramesV1.Point0270.input_defined SourceMainFramesV1.Point0270.outputs_defined SourceMainBudgetV1.Cell0270.execution SourceMainBudgetV1.Cell0270.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=271) (input:=SourceMainFramesV1.Point0271.input) (pair:=SourceMainFramesV1.Point0271.outputs) SourceHeightEdgesV1.Edge0271.left_defined SourceMainFramesV1.Point0271.input_defined SourceMainFramesV1.Point0271.outputs_defined SourceMainBudgetV1.Cell0271.execution SourceMainBudgetV1.Cell0271.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=272) (input:=SourceMainFramesV1.Point0272.input) (pair:=SourceMainFramesV1.Point0272.outputs) SourceHeightEdgesV1.Edge0272.left_defined SourceMainFramesV1.Point0272.input_defined SourceMainFramesV1.Point0272.outputs_defined SourceMainBudgetV1.Cell0272.execution SourceMainBudgetV1.Cell0272.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=273) (input:=SourceMainFramesV1.Point0273.input) (pair:=SourceMainFramesV1.Point0273.outputs) SourceHeightEdgesV1.Edge0273.left_defined SourceMainFramesV1.Point0273.input_defined SourceMainFramesV1.Point0273.outputs_defined SourceMainBudgetV1.Cell0273.execution SourceMainBudgetV1.Cell0273.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=274) (input:=SourceMainFramesV1.Point0274.input) (pair:=SourceMainFramesV1.Point0274.outputs) SourceHeightEdgesV1.Edge0274.left_defined SourceMainFramesV1.Point0274.input_defined SourceMainFramesV1.Point0274.outputs_defined SourceMainBudgetV1.Cell0274.execution SourceMainBudgetV1.Cell0274.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=275) (input:=SourceMainFramesV1.Point0275.input) (pair:=SourceMainFramesV1.Point0275.outputs) SourceHeightEdgesV1.Edge0275.left_defined SourceMainFramesV1.Point0275.input_defined SourceMainFramesV1.Point0275.outputs_defined SourceMainBudgetV1.Cell0275.execution SourceMainBudgetV1.Cell0275.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=276) (input:=SourceMainFramesV1.Point0276.input) (pair:=SourceMainFramesV1.Point0276.outputs) SourceHeightEdgesV1.Edge0276.left_defined SourceMainFramesV1.Point0276.input_defined SourceMainFramesV1.Point0276.outputs_defined SourceMainBudgetV1.Cell0276.execution SourceMainBudgetV1.Cell0276.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=277) (input:=SourceMainFramesV1.Point0277.input) (pair:=SourceMainFramesV1.Point0277.outputs) SourceHeightEdgesV1.Edge0277.left_defined SourceMainFramesV1.Point0277.input_defined SourceMainFramesV1.Point0277.outputs_defined SourceMainBudgetV1.Cell0277.execution SourceMainBudgetV1.Cell0277.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=278) (input:=SourceMainFramesV1.Point0278.input) (pair:=SourceMainFramesV1.Point0278.outputs) SourceHeightEdgesV1.Edge0278.left_defined SourceMainFramesV1.Point0278.input_defined SourceMainFramesV1.Point0278.outputs_defined SourceMainBudgetV1.Cell0278.execution SourceMainBudgetV1.Cell0278.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=279) (input:=SourceMainFramesV1.Point0279.input) (pair:=SourceMainFramesV1.Point0279.outputs) SourceHeightEdgesV1.Edge0279.left_defined SourceMainFramesV1.Point0279.input_defined SourceMainFramesV1.Point0279.outputs_defined SourceMainBudgetV1.Cell0279.execution SourceMainBudgetV1.Cell0279.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=280) (input:=SourceMainFramesV1.Point0280.input) (pair:=SourceMainFramesV1.Point0280.outputs) SourceHeightEdgesV1.Edge0280.left_defined SourceMainFramesV1.Point0280.input_defined SourceMainFramesV1.Point0280.outputs_defined SourceMainBudgetV1.Cell0280.execution SourceMainBudgetV1.Cell0280.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=281) (input:=SourceMainFramesV1.Point0281.input) (pair:=SourceMainFramesV1.Point0281.outputs) SourceHeightEdgesV1.Edge0281.left_defined SourceMainFramesV1.Point0281.input_defined SourceMainFramesV1.Point0281.outputs_defined SourceMainBudgetV1.Cell0281.execution SourceMainBudgetV1.Cell0281.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=282) (input:=SourceMainFramesV1.Point0282.input) (pair:=SourceMainFramesV1.Point0282.outputs) SourceHeightEdgesV1.Edge0282.left_defined SourceMainFramesV1.Point0282.input_defined SourceMainFramesV1.Point0282.outputs_defined SourceMainBudgetV1.Cell0282.execution SourceMainBudgetV1.Cell0282.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=283) (input:=SourceMainFramesV1.Point0283.input) (pair:=SourceMainFramesV1.Point0283.outputs) SourceHeightEdgesV1.Edge0283.left_defined SourceMainFramesV1.Point0283.input_defined SourceMainFramesV1.Point0283.outputs_defined SourceMainBudgetV1.Cell0283.execution SourceMainBudgetV1.Cell0283.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=284) (input:=SourceMainFramesV1.Point0284.input) (pair:=SourceMainFramesV1.Point0284.outputs) SourceHeightEdgesV1.Edge0284.left_defined SourceMainFramesV1.Point0284.input_defined SourceMainFramesV1.Point0284.outputs_defined SourceMainBudgetV1.Cell0284.execution SourceMainBudgetV1.Cell0284.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=285) (input:=SourceMainFramesV1.Point0285.input) (pair:=SourceMainFramesV1.Point0285.outputs) SourceHeightEdgesV1.Edge0285.left_defined SourceMainFramesV1.Point0285.input_defined SourceMainFramesV1.Point0285.outputs_defined SourceMainBudgetV1.Cell0285.execution SourceMainBudgetV1.Cell0285.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=286) (input:=SourceMainFramesV1.Point0286.input) (pair:=SourceMainFramesV1.Point0286.outputs) SourceHeightEdgesV1.Edge0286.left_defined SourceMainFramesV1.Point0286.input_defined SourceMainFramesV1.Point0286.outputs_defined SourceMainBudgetV1.Cell0286.execution SourceMainBudgetV1.Cell0286.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=287) (input:=SourceMainFramesV1.Point0287.input) (pair:=SourceMainFramesV1.Point0287.outputs) SourceHeightEdgesV1.Edge0287.left_defined SourceMainFramesV1.Point0287.input_defined SourceMainFramesV1.Point0287.outputs_defined SourceMainBudgetV1.Cell0287.execution SourceMainBudgetV1.Cell0287.next_total
end SourceMainBudgetV1.Block08
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block08.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
