import SourceHeightPointsV2.Point0288
import SourceHeightPointsV2.Point0289
import SourceHeightPointsV2.Point0290
import SourceHeightPointsV2.Point0291
import SourceHeightPointsV2.Point0292
import SourceHeightPointsV2.Point0293
import SourceHeightPointsV2.Point0294
import SourceHeightPointsV2.Point0295
import SourceHeightPointsV2.Point0296
import SourceHeightPointsV2.Point0297
import SourceHeightPointsV2.Point0298
import SourceHeightPointsV2.Point0299
import SourceHeightPointsV2.Point0300
import SourceHeightPointsV2.Point0301
import SourceHeightPointsV2.Point0302
import SourceHeightPointsV2.Point0303
import SourceHeightPointsV2.Point0304
import SourceHeightPointsV2.Point0305
import SourceHeightPointsV2.Point0306
import SourceHeightPointsV2.Point0307
import SourceHeightPointsV2.Point0308
import SourceHeightPointsV2.Point0309
import SourceHeightPointsV2.Point0310
import SourceHeightPointsV2.Point0311
import SourceHeightPointsV2.Point0312
import SourceHeightPointsV2.Point0313
import SourceHeightPointsV2.Point0314
import SourceHeightPointsV2.Point0315
import SourceHeightPointsV2.Point0316
import SourceHeightPointsV2.Point0317
import SourceHeightPointsV2.Point0318
import SourceHeightPointsV2.Point0319
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block09
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 288 ≤ i) (upper : i < 320) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0288.source_outputs
   exact ⟨SourceHeightPointsV2.Point0288.input,c,d,SourceHeightPointsV2.Point0288.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0289.source_outputs
   exact ⟨SourceHeightPointsV2.Point0289.input,c,d,SourceHeightPointsV2.Point0289.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0290.source_outputs
   exact ⟨SourceHeightPointsV2.Point0290.input,c,d,SourceHeightPointsV2.Point0290.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0291.source_outputs
   exact ⟨SourceHeightPointsV2.Point0291.input,c,d,SourceHeightPointsV2.Point0291.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0292.source_outputs
   exact ⟨SourceHeightPointsV2.Point0292.input,c,d,SourceHeightPointsV2.Point0292.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0293.source_outputs
   exact ⟨SourceHeightPointsV2.Point0293.input,c,d,SourceHeightPointsV2.Point0293.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0294.source_outputs
   exact ⟨SourceHeightPointsV2.Point0294.input,c,d,SourceHeightPointsV2.Point0294.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0295.source_outputs
   exact ⟨SourceHeightPointsV2.Point0295.input,c,d,SourceHeightPointsV2.Point0295.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0296.source_outputs
   exact ⟨SourceHeightPointsV2.Point0296.input,c,d,SourceHeightPointsV2.Point0296.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0297.source_outputs
   exact ⟨SourceHeightPointsV2.Point0297.input,c,d,SourceHeightPointsV2.Point0297.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0298.source_outputs
   exact ⟨SourceHeightPointsV2.Point0298.input,c,d,SourceHeightPointsV2.Point0298.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0299.source_outputs
   exact ⟨SourceHeightPointsV2.Point0299.input,c,d,SourceHeightPointsV2.Point0299.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0300.source_outputs
   exact ⟨SourceHeightPointsV2.Point0300.input,c,d,SourceHeightPointsV2.Point0300.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0301.source_outputs
   exact ⟨SourceHeightPointsV2.Point0301.input,c,d,SourceHeightPointsV2.Point0301.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0302.source_outputs
   exact ⟨SourceHeightPointsV2.Point0302.input,c,d,SourceHeightPointsV2.Point0302.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0303.source_outputs
   exact ⟨SourceHeightPointsV2.Point0303.input,c,d,SourceHeightPointsV2.Point0303.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0304.source_outputs
   exact ⟨SourceHeightPointsV2.Point0304.input,c,d,SourceHeightPointsV2.Point0304.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0305.source_outputs
   exact ⟨SourceHeightPointsV2.Point0305.input,c,d,SourceHeightPointsV2.Point0305.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0306.source_outputs
   exact ⟨SourceHeightPointsV2.Point0306.input,c,d,SourceHeightPointsV2.Point0306.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0307.source_outputs
   exact ⟨SourceHeightPointsV2.Point0307.input,c,d,SourceHeightPointsV2.Point0307.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0308.source_outputs
   exact ⟨SourceHeightPointsV2.Point0308.input,c,d,SourceHeightPointsV2.Point0308.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0309.source_outputs
   exact ⟨SourceHeightPointsV2.Point0309.input,c,d,SourceHeightPointsV2.Point0309.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0310.source_outputs
   exact ⟨SourceHeightPointsV2.Point0310.input,c,d,SourceHeightPointsV2.Point0310.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0311.source_outputs
   exact ⟨SourceHeightPointsV2.Point0311.input,c,d,SourceHeightPointsV2.Point0311.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0312.source_outputs
   exact ⟨SourceHeightPointsV2.Point0312.input,c,d,SourceHeightPointsV2.Point0312.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0313.source_outputs
   exact ⟨SourceHeightPointsV2.Point0313.input,c,d,SourceHeightPointsV2.Point0313.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0314.source_outputs
   exact ⟨SourceHeightPointsV2.Point0314.input,c,d,SourceHeightPointsV2.Point0314.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0315.source_outputs
   exact ⟨SourceHeightPointsV2.Point0315.input,c,d,SourceHeightPointsV2.Point0315.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0316.source_outputs
   exact ⟨SourceHeightPointsV2.Point0316.input,c,d,SourceHeightPointsV2.Point0316.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0317.source_outputs
   exact ⟨SourceHeightPointsV2.Point0317.input,c,d,SourceHeightPointsV2.Point0317.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0318.source_outputs
   exact ⟨SourceHeightPointsV2.Point0318.input,c,d,SourceHeightPointsV2.Point0318.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0319.source_outputs
   exact ⟨SourceHeightPointsV2.Point0319.input,c,d,SourceHeightPointsV2.Point0319.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block09
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block09.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
