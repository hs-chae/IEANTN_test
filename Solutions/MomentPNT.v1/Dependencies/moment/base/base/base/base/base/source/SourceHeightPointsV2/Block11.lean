import SourceHeightPointsV2.Point0352
import SourceHeightPointsV2.Point0353
import SourceHeightPointsV2.Point0354
import SourceHeightPointsV2.Point0355
import SourceHeightPointsV2.Point0356
import SourceHeightPointsV2.Point0357
import SourceHeightPointsV2.Point0358
import SourceHeightPointsV2.Point0359
import SourceHeightPointsV2.Point0360
import SourceHeightPointsV2.Point0361
import SourceHeightPointsV2.Point0362
import SourceHeightPointsV2.Point0363
import SourceHeightPointsV2.Point0364
import SourceHeightPointsV2.Point0365
import SourceHeightPointsV2.Point0366
import SourceHeightPointsV2.Point0367
import SourceHeightPointsV2.Point0368
import SourceHeightPointsV2.Point0369
import SourceHeightPointsV2.Point0370
import SourceHeightPointsV2.Point0371
import SourceHeightPointsV2.Point0372
import SourceHeightPointsV2.Point0373
import SourceHeightPointsV2.Point0374
import SourceHeightPointsV2.Point0375
import SourceHeightPointsV2.Point0376
import SourceHeightPointsV2.Point0377
import SourceHeightPointsV2.Point0378
import SourceHeightPointsV2.Point0379
import SourceHeightPointsV2.Point0380
import SourceHeightPointsV2.Point0381
import SourceHeightPointsV2.Point0382
import SourceHeightPointsV2.Point0383
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block11
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 352 ≤ i) (upper : i < 384) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0352.source_outputs
   exact ⟨SourceHeightPointsV2.Point0352.input,c,d,SourceHeightPointsV2.Point0352.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0353.source_outputs
   exact ⟨SourceHeightPointsV2.Point0353.input,c,d,SourceHeightPointsV2.Point0353.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0354.source_outputs
   exact ⟨SourceHeightPointsV2.Point0354.input,c,d,SourceHeightPointsV2.Point0354.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0355.source_outputs
   exact ⟨SourceHeightPointsV2.Point0355.input,c,d,SourceHeightPointsV2.Point0355.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0356.source_outputs
   exact ⟨SourceHeightPointsV2.Point0356.input,c,d,SourceHeightPointsV2.Point0356.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0357.source_outputs
   exact ⟨SourceHeightPointsV2.Point0357.input,c,d,SourceHeightPointsV2.Point0357.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0358.source_outputs
   exact ⟨SourceHeightPointsV2.Point0358.input,c,d,SourceHeightPointsV2.Point0358.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0359.source_outputs
   exact ⟨SourceHeightPointsV2.Point0359.input,c,d,SourceHeightPointsV2.Point0359.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0360.source_outputs
   exact ⟨SourceHeightPointsV2.Point0360.input,c,d,SourceHeightPointsV2.Point0360.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0361.source_outputs
   exact ⟨SourceHeightPointsV2.Point0361.input,c,d,SourceHeightPointsV2.Point0361.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0362.source_outputs
   exact ⟨SourceHeightPointsV2.Point0362.input,c,d,SourceHeightPointsV2.Point0362.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0363.source_outputs
   exact ⟨SourceHeightPointsV2.Point0363.input,c,d,SourceHeightPointsV2.Point0363.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0364.source_outputs
   exact ⟨SourceHeightPointsV2.Point0364.input,c,d,SourceHeightPointsV2.Point0364.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0365.source_outputs
   exact ⟨SourceHeightPointsV2.Point0365.input,c,d,SourceHeightPointsV2.Point0365.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0366.source_outputs
   exact ⟨SourceHeightPointsV2.Point0366.input,c,d,SourceHeightPointsV2.Point0366.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0367.source_outputs
   exact ⟨SourceHeightPointsV2.Point0367.input,c,d,SourceHeightPointsV2.Point0367.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0368.source_outputs
   exact ⟨SourceHeightPointsV2.Point0368.input,c,d,SourceHeightPointsV2.Point0368.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0369.source_outputs
   exact ⟨SourceHeightPointsV2.Point0369.input,c,d,SourceHeightPointsV2.Point0369.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0370.source_outputs
   exact ⟨SourceHeightPointsV2.Point0370.input,c,d,SourceHeightPointsV2.Point0370.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0371.source_outputs
   exact ⟨SourceHeightPointsV2.Point0371.input,c,d,SourceHeightPointsV2.Point0371.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0372.source_outputs
   exact ⟨SourceHeightPointsV2.Point0372.input,c,d,SourceHeightPointsV2.Point0372.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0373.source_outputs
   exact ⟨SourceHeightPointsV2.Point0373.input,c,d,SourceHeightPointsV2.Point0373.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0374.source_outputs
   exact ⟨SourceHeightPointsV2.Point0374.input,c,d,SourceHeightPointsV2.Point0374.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0375.source_outputs
   exact ⟨SourceHeightPointsV2.Point0375.input,c,d,SourceHeightPointsV2.Point0375.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0376.source_outputs
   exact ⟨SourceHeightPointsV2.Point0376.input,c,d,SourceHeightPointsV2.Point0376.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0377.source_outputs
   exact ⟨SourceHeightPointsV2.Point0377.input,c,d,SourceHeightPointsV2.Point0377.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0378.source_outputs
   exact ⟨SourceHeightPointsV2.Point0378.input,c,d,SourceHeightPointsV2.Point0378.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0379.source_outputs
   exact ⟨SourceHeightPointsV2.Point0379.input,c,d,SourceHeightPointsV2.Point0379.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0380.source_outputs
   exact ⟨SourceHeightPointsV2.Point0380.input,c,d,SourceHeightPointsV2.Point0380.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0381.source_outputs
   exact ⟨SourceHeightPointsV2.Point0381.input,c,d,SourceHeightPointsV2.Point0381.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0382.source_outputs
   exact ⟨SourceHeightPointsV2.Point0382.input,c,d,SourceHeightPointsV2.Point0382.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0383.source_outputs
   exact ⟨SourceHeightPointsV2.Point0383.input,c,d,SourceHeightPointsV2.Point0383.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block11
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block11.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
