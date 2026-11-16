import SourceHeightPointsV2.Point0384
import SourceHeightPointsV2.Point0385
import SourceHeightPointsV2.Point0386
import SourceHeightPointsV2.Point0387
import SourceHeightPointsV2.Point0388
import SourceHeightPointsV2.Point0389
import SourceHeightPointsV2.Point0390
import SourceHeightPointsV2.Point0391
import SourceHeightPointsV2.Point0392
import SourceHeightPointsV2.Point0393
import SourceHeightPointsV2.Point0394
import SourceHeightPointsV2.Point0395
import SourceHeightPointsV2.Point0396
import SourceHeightPointsV2.Point0397
import SourceHeightPointsV2.Point0398
import SourceHeightPointsV2.Point0399
import SourceHeightPointsV2.Point0400
import SourceHeightPointsV2.Point0401
import SourceHeightPointsV2.Point0402
import SourceHeightPointsV2.Point0403
import SourceHeightPointsV2.Point0404
import SourceHeightPointsV2.Point0405
import SourceHeightPointsV2.Point0406
import SourceHeightPointsV2.Point0407
import SourceHeightPointsV2.Point0408
import SourceHeightPointsV2.Point0409
import SourceHeightPointsV2.Point0410
import SourceHeightPointsV2.Point0411
import SourceHeightPointsV2.Point0412
import SourceHeightPointsV2.Point0413
import SourceHeightPointsV2.Point0414
import SourceHeightPointsV2.Point0415
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block12
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 384 ≤ i) (upper : i < 416) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0384.source_outputs
   exact ⟨SourceHeightPointsV2.Point0384.input,c,d,SourceHeightPointsV2.Point0384.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0385.source_outputs
   exact ⟨SourceHeightPointsV2.Point0385.input,c,d,SourceHeightPointsV2.Point0385.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0386.source_outputs
   exact ⟨SourceHeightPointsV2.Point0386.input,c,d,SourceHeightPointsV2.Point0386.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0387.source_outputs
   exact ⟨SourceHeightPointsV2.Point0387.input,c,d,SourceHeightPointsV2.Point0387.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0388.source_outputs
   exact ⟨SourceHeightPointsV2.Point0388.input,c,d,SourceHeightPointsV2.Point0388.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0389.source_outputs
   exact ⟨SourceHeightPointsV2.Point0389.input,c,d,SourceHeightPointsV2.Point0389.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0390.source_outputs
   exact ⟨SourceHeightPointsV2.Point0390.input,c,d,SourceHeightPointsV2.Point0390.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0391.source_outputs
   exact ⟨SourceHeightPointsV2.Point0391.input,c,d,SourceHeightPointsV2.Point0391.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0392.source_outputs
   exact ⟨SourceHeightPointsV2.Point0392.input,c,d,SourceHeightPointsV2.Point0392.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0393.source_outputs
   exact ⟨SourceHeightPointsV2.Point0393.input,c,d,SourceHeightPointsV2.Point0393.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0394.source_outputs
   exact ⟨SourceHeightPointsV2.Point0394.input,c,d,SourceHeightPointsV2.Point0394.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0395.source_outputs
   exact ⟨SourceHeightPointsV2.Point0395.input,c,d,SourceHeightPointsV2.Point0395.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0396.source_outputs
   exact ⟨SourceHeightPointsV2.Point0396.input,c,d,SourceHeightPointsV2.Point0396.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0397.source_outputs
   exact ⟨SourceHeightPointsV2.Point0397.input,c,d,SourceHeightPointsV2.Point0397.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0398.source_outputs
   exact ⟨SourceHeightPointsV2.Point0398.input,c,d,SourceHeightPointsV2.Point0398.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0399.source_outputs
   exact ⟨SourceHeightPointsV2.Point0399.input,c,d,SourceHeightPointsV2.Point0399.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0400.source_outputs
   exact ⟨SourceHeightPointsV2.Point0400.input,c,d,SourceHeightPointsV2.Point0400.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0401.source_outputs
   exact ⟨SourceHeightPointsV2.Point0401.input,c,d,SourceHeightPointsV2.Point0401.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0402.source_outputs
   exact ⟨SourceHeightPointsV2.Point0402.input,c,d,SourceHeightPointsV2.Point0402.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0403.source_outputs
   exact ⟨SourceHeightPointsV2.Point0403.input,c,d,SourceHeightPointsV2.Point0403.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0404.source_outputs
   exact ⟨SourceHeightPointsV2.Point0404.input,c,d,SourceHeightPointsV2.Point0404.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0405.source_outputs
   exact ⟨SourceHeightPointsV2.Point0405.input,c,d,SourceHeightPointsV2.Point0405.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0406.source_outputs
   exact ⟨SourceHeightPointsV2.Point0406.input,c,d,SourceHeightPointsV2.Point0406.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0407.source_outputs
   exact ⟨SourceHeightPointsV2.Point0407.input,c,d,SourceHeightPointsV2.Point0407.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0408.source_outputs
   exact ⟨SourceHeightPointsV2.Point0408.input,c,d,SourceHeightPointsV2.Point0408.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0409.source_outputs
   exact ⟨SourceHeightPointsV2.Point0409.input,c,d,SourceHeightPointsV2.Point0409.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0410.source_outputs
   exact ⟨SourceHeightPointsV2.Point0410.input,c,d,SourceHeightPointsV2.Point0410.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0411.source_outputs
   exact ⟨SourceHeightPointsV2.Point0411.input,c,d,SourceHeightPointsV2.Point0411.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0412.source_outputs
   exact ⟨SourceHeightPointsV2.Point0412.input,c,d,SourceHeightPointsV2.Point0412.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0413.source_outputs
   exact ⟨SourceHeightPointsV2.Point0413.input,c,d,SourceHeightPointsV2.Point0413.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0414.source_outputs
   exact ⟨SourceHeightPointsV2.Point0414.input,c,d,SourceHeightPointsV2.Point0414.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0415.source_outputs
   exact ⟨SourceHeightPointsV2.Point0415.input,c,d,SourceHeightPointsV2.Point0415.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block12
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block12.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
