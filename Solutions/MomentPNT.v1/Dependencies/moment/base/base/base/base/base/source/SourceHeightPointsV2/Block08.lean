import SourceHeightPointsV2.Point0256
import SourceHeightPointsV2.Point0257
import SourceHeightPointsV2.Point0258
import SourceHeightPointsV2.Point0259
import SourceHeightPointsV2.Point0260
import SourceHeightPointsV2.Point0261
import SourceHeightPointsV2.Point0262
import SourceHeightPointsV2.Point0263
import SourceHeightPointsV2.Point0264
import SourceHeightPointsV2.Point0265
import SourceHeightPointsV2.Point0266
import SourceHeightPointsV2.Point0267
import SourceHeightPointsV2.Point0268
import SourceHeightPointsV2.Point0269
import SourceHeightPointsV2.Point0270
import SourceHeightPointsV2.Point0271
import SourceHeightPointsV2.Point0272
import SourceHeightPointsV2.Point0273
import SourceHeightPointsV2.Point0274
import SourceHeightPointsV2.Point0275
import SourceHeightPointsV2.Point0276
import SourceHeightPointsV2.Point0277
import SourceHeightPointsV2.Point0278
import SourceHeightPointsV2.Point0279
import SourceHeightPointsV2.Point0280
import SourceHeightPointsV2.Point0281
import SourceHeightPointsV2.Point0282
import SourceHeightPointsV2.Point0283
import SourceHeightPointsV2.Point0284
import SourceHeightPointsV2.Point0285
import SourceHeightPointsV2.Point0286
import SourceHeightPointsV2.Point0287
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block08
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 256 ≤ i) (upper : i < 288) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0256.source_outputs
   exact ⟨SourceHeightPointsV2.Point0256.input,c,d,SourceHeightPointsV2.Point0256.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0257.source_outputs
   exact ⟨SourceHeightPointsV2.Point0257.input,c,d,SourceHeightPointsV2.Point0257.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0258.source_outputs
   exact ⟨SourceHeightPointsV2.Point0258.input,c,d,SourceHeightPointsV2.Point0258.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0259.source_outputs
   exact ⟨SourceHeightPointsV2.Point0259.input,c,d,SourceHeightPointsV2.Point0259.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0260.source_outputs
   exact ⟨SourceHeightPointsV2.Point0260.input,c,d,SourceHeightPointsV2.Point0260.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0261.source_outputs
   exact ⟨SourceHeightPointsV2.Point0261.input,c,d,SourceHeightPointsV2.Point0261.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0262.source_outputs
   exact ⟨SourceHeightPointsV2.Point0262.input,c,d,SourceHeightPointsV2.Point0262.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0263.source_outputs
   exact ⟨SourceHeightPointsV2.Point0263.input,c,d,SourceHeightPointsV2.Point0263.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0264.source_outputs
   exact ⟨SourceHeightPointsV2.Point0264.input,c,d,SourceHeightPointsV2.Point0264.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0265.source_outputs
   exact ⟨SourceHeightPointsV2.Point0265.input,c,d,SourceHeightPointsV2.Point0265.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0266.source_outputs
   exact ⟨SourceHeightPointsV2.Point0266.input,c,d,SourceHeightPointsV2.Point0266.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0267.source_outputs
   exact ⟨SourceHeightPointsV2.Point0267.input,c,d,SourceHeightPointsV2.Point0267.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0268.source_outputs
   exact ⟨SourceHeightPointsV2.Point0268.input,c,d,SourceHeightPointsV2.Point0268.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0269.source_outputs
   exact ⟨SourceHeightPointsV2.Point0269.input,c,d,SourceHeightPointsV2.Point0269.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0270.source_outputs
   exact ⟨SourceHeightPointsV2.Point0270.input,c,d,SourceHeightPointsV2.Point0270.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0271.source_outputs
   exact ⟨SourceHeightPointsV2.Point0271.input,c,d,SourceHeightPointsV2.Point0271.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0272.source_outputs
   exact ⟨SourceHeightPointsV2.Point0272.input,c,d,SourceHeightPointsV2.Point0272.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0273.source_outputs
   exact ⟨SourceHeightPointsV2.Point0273.input,c,d,SourceHeightPointsV2.Point0273.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0274.source_outputs
   exact ⟨SourceHeightPointsV2.Point0274.input,c,d,SourceHeightPointsV2.Point0274.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0275.source_outputs
   exact ⟨SourceHeightPointsV2.Point0275.input,c,d,SourceHeightPointsV2.Point0275.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0276.source_outputs
   exact ⟨SourceHeightPointsV2.Point0276.input,c,d,SourceHeightPointsV2.Point0276.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0277.source_outputs
   exact ⟨SourceHeightPointsV2.Point0277.input,c,d,SourceHeightPointsV2.Point0277.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0278.source_outputs
   exact ⟨SourceHeightPointsV2.Point0278.input,c,d,SourceHeightPointsV2.Point0278.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0279.source_outputs
   exact ⟨SourceHeightPointsV2.Point0279.input,c,d,SourceHeightPointsV2.Point0279.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0280.source_outputs
   exact ⟨SourceHeightPointsV2.Point0280.input,c,d,SourceHeightPointsV2.Point0280.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0281.source_outputs
   exact ⟨SourceHeightPointsV2.Point0281.input,c,d,SourceHeightPointsV2.Point0281.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0282.source_outputs
   exact ⟨SourceHeightPointsV2.Point0282.input,c,d,SourceHeightPointsV2.Point0282.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0283.source_outputs
   exact ⟨SourceHeightPointsV2.Point0283.input,c,d,SourceHeightPointsV2.Point0283.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0284.source_outputs
   exact ⟨SourceHeightPointsV2.Point0284.input,c,d,SourceHeightPointsV2.Point0284.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0285.source_outputs
   exact ⟨SourceHeightPointsV2.Point0285.input,c,d,SourceHeightPointsV2.Point0285.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0286.source_outputs
   exact ⟨SourceHeightPointsV2.Point0286.input,c,d,SourceHeightPointsV2.Point0286.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0287.source_outputs
   exact ⟨SourceHeightPointsV2.Point0287.input,c,d,SourceHeightPointsV2.Point0287.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block08
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block08.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
