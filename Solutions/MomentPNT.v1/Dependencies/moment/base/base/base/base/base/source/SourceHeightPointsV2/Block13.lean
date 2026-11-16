import SourceHeightPointsV2.Point0416
import SourceHeightPointsV2.Point0417
import SourceHeightPointsV2.Point0418
import SourceHeightPointsV2.Point0419
import SourceHeightPointsV2.Point0420
import SourceHeightPointsV2.Point0421
import SourceHeightPointsV2.Point0422
import SourceHeightPointsV2.Point0423
import SourceHeightPointsV2.Point0424
import SourceHeightPointsV2.Point0425
import SourceHeightPointsV2.Point0426
import SourceHeightPointsV2.Point0427
import SourceHeightPointsV2.Point0428
import SourceHeightPointsV2.Point0429
import SourceHeightPointsV2.Point0430
import SourceHeightPointsV2.Point0431
import SourceHeightPointsV2.Point0432
import SourceHeightPointsV2.Point0433
import SourceHeightPointsV2.Point0434
import SourceHeightPointsV2.Point0435
import SourceHeightPointsV2.Point0436
import SourceHeightPointsV2.Point0437
import SourceHeightPointsV2.Point0438
import SourceHeightPointsV2.Point0439
import SourceHeightPointsV2.Point0440
import SourceHeightPointsV2.Point0441
import SourceHeightPointsV2.Point0442
import SourceHeightPointsV2.Point0443
import SourceHeightPointsV2.Point0444
import SourceHeightPointsV2.Point0445
import SourceHeightPointsV2.Point0446
import SourceHeightPointsV2.Point0447
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block13
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 416 ≤ i) (upper : i < 448) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0416.source_outputs
   exact ⟨SourceHeightPointsV2.Point0416.input,c,d,SourceHeightPointsV2.Point0416.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0417.source_outputs
   exact ⟨SourceHeightPointsV2.Point0417.input,c,d,SourceHeightPointsV2.Point0417.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0418.source_outputs
   exact ⟨SourceHeightPointsV2.Point0418.input,c,d,SourceHeightPointsV2.Point0418.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0419.source_outputs
   exact ⟨SourceHeightPointsV2.Point0419.input,c,d,SourceHeightPointsV2.Point0419.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0420.source_outputs
   exact ⟨SourceHeightPointsV2.Point0420.input,c,d,SourceHeightPointsV2.Point0420.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0421.source_outputs
   exact ⟨SourceHeightPointsV2.Point0421.input,c,d,SourceHeightPointsV2.Point0421.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0422.source_outputs
   exact ⟨SourceHeightPointsV2.Point0422.input,c,d,SourceHeightPointsV2.Point0422.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0423.source_outputs
   exact ⟨SourceHeightPointsV2.Point0423.input,c,d,SourceHeightPointsV2.Point0423.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0424.source_outputs
   exact ⟨SourceHeightPointsV2.Point0424.input,c,d,SourceHeightPointsV2.Point0424.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0425.source_outputs
   exact ⟨SourceHeightPointsV2.Point0425.input,c,d,SourceHeightPointsV2.Point0425.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0426.source_outputs
   exact ⟨SourceHeightPointsV2.Point0426.input,c,d,SourceHeightPointsV2.Point0426.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0427.source_outputs
   exact ⟨SourceHeightPointsV2.Point0427.input,c,d,SourceHeightPointsV2.Point0427.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0428.source_outputs
   exact ⟨SourceHeightPointsV2.Point0428.input,c,d,SourceHeightPointsV2.Point0428.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0429.source_outputs
   exact ⟨SourceHeightPointsV2.Point0429.input,c,d,SourceHeightPointsV2.Point0429.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0430.source_outputs
   exact ⟨SourceHeightPointsV2.Point0430.input,c,d,SourceHeightPointsV2.Point0430.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0431.source_outputs
   exact ⟨SourceHeightPointsV2.Point0431.input,c,d,SourceHeightPointsV2.Point0431.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0432.source_outputs
   exact ⟨SourceHeightPointsV2.Point0432.input,c,d,SourceHeightPointsV2.Point0432.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0433.source_outputs
   exact ⟨SourceHeightPointsV2.Point0433.input,c,d,SourceHeightPointsV2.Point0433.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0434.source_outputs
   exact ⟨SourceHeightPointsV2.Point0434.input,c,d,SourceHeightPointsV2.Point0434.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0435.source_outputs
   exact ⟨SourceHeightPointsV2.Point0435.input,c,d,SourceHeightPointsV2.Point0435.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0436.source_outputs
   exact ⟨SourceHeightPointsV2.Point0436.input,c,d,SourceHeightPointsV2.Point0436.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0437.source_outputs
   exact ⟨SourceHeightPointsV2.Point0437.input,c,d,SourceHeightPointsV2.Point0437.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0438.source_outputs
   exact ⟨SourceHeightPointsV2.Point0438.input,c,d,SourceHeightPointsV2.Point0438.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0439.source_outputs
   exact ⟨SourceHeightPointsV2.Point0439.input,c,d,SourceHeightPointsV2.Point0439.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0440.source_outputs
   exact ⟨SourceHeightPointsV2.Point0440.input,c,d,SourceHeightPointsV2.Point0440.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0441.source_outputs
   exact ⟨SourceHeightPointsV2.Point0441.input,c,d,SourceHeightPointsV2.Point0441.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0442.source_outputs
   exact ⟨SourceHeightPointsV2.Point0442.input,c,d,SourceHeightPointsV2.Point0442.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0443.source_outputs
   exact ⟨SourceHeightPointsV2.Point0443.input,c,d,SourceHeightPointsV2.Point0443.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0444.source_outputs
   exact ⟨SourceHeightPointsV2.Point0444.input,c,d,SourceHeightPointsV2.Point0444.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0445.source_outputs
   exact ⟨SourceHeightPointsV2.Point0445.input,c,d,SourceHeightPointsV2.Point0445.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0446.source_outputs
   exact ⟨SourceHeightPointsV2.Point0446.input,c,d,SourceHeightPointsV2.Point0446.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0447.source_outputs
   exact ⟨SourceHeightPointsV2.Point0447.input,c,d,SourceHeightPointsV2.Point0447.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block13
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block13.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
