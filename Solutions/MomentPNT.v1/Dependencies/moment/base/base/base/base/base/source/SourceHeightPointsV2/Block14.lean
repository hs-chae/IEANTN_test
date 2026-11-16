import SourceHeightPointsV2.Point0448
import SourceHeightPointsV2.Point0449
import SourceHeightPointsV2.Point0450
import SourceHeightPointsV2.Point0451
import SourceHeightPointsV2.Point0452
import SourceHeightPointsV2.Point0453
import SourceHeightPointsV2.Point0454
import SourceHeightPointsV2.Point0455
import SourceHeightPointsV2.Point0456
import SourceHeightPointsV2.Point0457
import SourceHeightPointsV2.Point0458
import SourceHeightPointsV2.Point0459
import SourceHeightPointsV2.Point0460
import SourceHeightPointsV2.Point0461
import SourceHeightPointsV2.Point0462
import SourceHeightPointsV2.Point0463
import SourceHeightPointsV2.Point0464
import SourceHeightPointsV2.Point0465
import SourceHeightPointsV2.Point0466
import SourceHeightPointsV2.Point0467
import SourceHeightPointsV2.Point0468
import SourceHeightPointsV2.Point0469
import SourceHeightPointsV2.Point0470
import SourceHeightPointsV2.Point0471
import SourceHeightPointsV2.Point0472
import SourceHeightPointsV2.Point0473
import SourceHeightPointsV2.Point0474
import SourceHeightPointsV2.Point0475
import SourceHeightPointsV2.Point0476
import SourceHeightPointsV2.Point0477
import SourceHeightPointsV2.Point0478
import SourceHeightPointsV2.Point0479
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block14
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 448 ≤ i) (upper : i < 480) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0448.source_outputs
   exact ⟨SourceHeightPointsV2.Point0448.input,c,d,SourceHeightPointsV2.Point0448.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0449.source_outputs
   exact ⟨SourceHeightPointsV2.Point0449.input,c,d,SourceHeightPointsV2.Point0449.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0450.source_outputs
   exact ⟨SourceHeightPointsV2.Point0450.input,c,d,SourceHeightPointsV2.Point0450.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0451.source_outputs
   exact ⟨SourceHeightPointsV2.Point0451.input,c,d,SourceHeightPointsV2.Point0451.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0452.source_outputs
   exact ⟨SourceHeightPointsV2.Point0452.input,c,d,SourceHeightPointsV2.Point0452.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0453.source_outputs
   exact ⟨SourceHeightPointsV2.Point0453.input,c,d,SourceHeightPointsV2.Point0453.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0454.source_outputs
   exact ⟨SourceHeightPointsV2.Point0454.input,c,d,SourceHeightPointsV2.Point0454.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0455.source_outputs
   exact ⟨SourceHeightPointsV2.Point0455.input,c,d,SourceHeightPointsV2.Point0455.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0456.source_outputs
   exact ⟨SourceHeightPointsV2.Point0456.input,c,d,SourceHeightPointsV2.Point0456.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0457.source_outputs
   exact ⟨SourceHeightPointsV2.Point0457.input,c,d,SourceHeightPointsV2.Point0457.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0458.source_outputs
   exact ⟨SourceHeightPointsV2.Point0458.input,c,d,SourceHeightPointsV2.Point0458.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0459.source_outputs
   exact ⟨SourceHeightPointsV2.Point0459.input,c,d,SourceHeightPointsV2.Point0459.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0460.source_outputs
   exact ⟨SourceHeightPointsV2.Point0460.input,c,d,SourceHeightPointsV2.Point0460.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0461.source_outputs
   exact ⟨SourceHeightPointsV2.Point0461.input,c,d,SourceHeightPointsV2.Point0461.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0462.source_outputs
   exact ⟨SourceHeightPointsV2.Point0462.input,c,d,SourceHeightPointsV2.Point0462.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0463.source_outputs
   exact ⟨SourceHeightPointsV2.Point0463.input,c,d,SourceHeightPointsV2.Point0463.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0464.source_outputs
   exact ⟨SourceHeightPointsV2.Point0464.input,c,d,SourceHeightPointsV2.Point0464.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0465.source_outputs
   exact ⟨SourceHeightPointsV2.Point0465.input,c,d,SourceHeightPointsV2.Point0465.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0466.source_outputs
   exact ⟨SourceHeightPointsV2.Point0466.input,c,d,SourceHeightPointsV2.Point0466.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0467.source_outputs
   exact ⟨SourceHeightPointsV2.Point0467.input,c,d,SourceHeightPointsV2.Point0467.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0468.source_outputs
   exact ⟨SourceHeightPointsV2.Point0468.input,c,d,SourceHeightPointsV2.Point0468.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0469.source_outputs
   exact ⟨SourceHeightPointsV2.Point0469.input,c,d,SourceHeightPointsV2.Point0469.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0470.source_outputs
   exact ⟨SourceHeightPointsV2.Point0470.input,c,d,SourceHeightPointsV2.Point0470.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0471.source_outputs
   exact ⟨SourceHeightPointsV2.Point0471.input,c,d,SourceHeightPointsV2.Point0471.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0472.source_outputs
   exact ⟨SourceHeightPointsV2.Point0472.input,c,d,SourceHeightPointsV2.Point0472.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0473.source_outputs
   exact ⟨SourceHeightPointsV2.Point0473.input,c,d,SourceHeightPointsV2.Point0473.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0474.source_outputs
   exact ⟨SourceHeightPointsV2.Point0474.input,c,d,SourceHeightPointsV2.Point0474.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0475.source_outputs
   exact ⟨SourceHeightPointsV2.Point0475.input,c,d,SourceHeightPointsV2.Point0475.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0476.source_outputs
   exact ⟨SourceHeightPointsV2.Point0476.input,c,d,SourceHeightPointsV2.Point0476.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0477.source_outputs
   exact ⟨SourceHeightPointsV2.Point0477.input,c,d,SourceHeightPointsV2.Point0477.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0478.source_outputs
   exact ⟨SourceHeightPointsV2.Point0478.input,c,d,SourceHeightPointsV2.Point0478.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0479.source_outputs
   exact ⟨SourceHeightPointsV2.Point0479.input,c,d,SourceHeightPointsV2.Point0479.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block14
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block14.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
