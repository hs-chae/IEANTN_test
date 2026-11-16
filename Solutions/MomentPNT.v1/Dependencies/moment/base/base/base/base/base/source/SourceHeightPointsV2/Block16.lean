import SourceHeightPointsV2.Point0512
import SourceHeightPointsV2.Point0513
import SourceHeightPointsV2.Point0514
import SourceHeightPointsV2.Point0515
import SourceHeightPointsV2.Point0516
import SourceHeightPointsV2.Point0517
import SourceHeightPointsV2.Point0518
import SourceHeightPointsV2.Point0519
import SourceHeightPointsV2.Point0520
import SourceHeightPointsV2.Point0521
import SourceHeightPointsV2.Point0522
import SourceHeightPointsV2.Point0523
import SourceHeightPointsV2.Point0524
import SourceHeightPointsV2.Point0525
import SourceHeightPointsV2.Point0526
import SourceHeightPointsV2.Point0527
import SourceHeightPointsV2.Point0528
import SourceHeightPointsV2.Point0529
import SourceHeightPointsV2.Point0530
import SourceHeightPointsV2.Point0531
import SourceHeightPointsV2.Point0532
import SourceHeightPointsV2.Point0533
import SourceHeightPointsV2.Point0534
import SourceHeightPointsV2.Point0535
import SourceHeightPointsV2.Point0536
import SourceHeightPointsV2.Point0537
import SourceHeightPointsV2.Point0538
import SourceHeightPointsV2.Point0539
import SourceHeightPointsV2.Point0540
import SourceHeightPointsV2.Point0541
import SourceHeightPointsV2.Point0542
import SourceHeightPointsV2.Point0543
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block16
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 512 ≤ i) (upper : i < 544) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0512.source_outputs
   exact ⟨SourceHeightPointsV2.Point0512.input,c,d,SourceHeightPointsV2.Point0512.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0513.source_outputs
   exact ⟨SourceHeightPointsV2.Point0513.input,c,d,SourceHeightPointsV2.Point0513.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0514.source_outputs
   exact ⟨SourceHeightPointsV2.Point0514.input,c,d,SourceHeightPointsV2.Point0514.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0515.source_outputs
   exact ⟨SourceHeightPointsV2.Point0515.input,c,d,SourceHeightPointsV2.Point0515.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0516.source_outputs
   exact ⟨SourceHeightPointsV2.Point0516.input,c,d,SourceHeightPointsV2.Point0516.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0517.source_outputs
   exact ⟨SourceHeightPointsV2.Point0517.input,c,d,SourceHeightPointsV2.Point0517.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0518.source_outputs
   exact ⟨SourceHeightPointsV2.Point0518.input,c,d,SourceHeightPointsV2.Point0518.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0519.source_outputs
   exact ⟨SourceHeightPointsV2.Point0519.input,c,d,SourceHeightPointsV2.Point0519.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0520.source_outputs
   exact ⟨SourceHeightPointsV2.Point0520.input,c,d,SourceHeightPointsV2.Point0520.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0521.source_outputs
   exact ⟨SourceHeightPointsV2.Point0521.input,c,d,SourceHeightPointsV2.Point0521.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0522.source_outputs
   exact ⟨SourceHeightPointsV2.Point0522.input,c,d,SourceHeightPointsV2.Point0522.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0523.source_outputs
   exact ⟨SourceHeightPointsV2.Point0523.input,c,d,SourceHeightPointsV2.Point0523.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0524.source_outputs
   exact ⟨SourceHeightPointsV2.Point0524.input,c,d,SourceHeightPointsV2.Point0524.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0525.source_outputs
   exact ⟨SourceHeightPointsV2.Point0525.input,c,d,SourceHeightPointsV2.Point0525.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0526.source_outputs
   exact ⟨SourceHeightPointsV2.Point0526.input,c,d,SourceHeightPointsV2.Point0526.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0527.source_outputs
   exact ⟨SourceHeightPointsV2.Point0527.input,c,d,SourceHeightPointsV2.Point0527.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0528.source_outputs
   exact ⟨SourceHeightPointsV2.Point0528.input,c,d,SourceHeightPointsV2.Point0528.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0529.source_outputs
   exact ⟨SourceHeightPointsV2.Point0529.input,c,d,SourceHeightPointsV2.Point0529.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0530.source_outputs
   exact ⟨SourceHeightPointsV2.Point0530.input,c,d,SourceHeightPointsV2.Point0530.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0531.source_outputs
   exact ⟨SourceHeightPointsV2.Point0531.input,c,d,SourceHeightPointsV2.Point0531.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0532.source_outputs
   exact ⟨SourceHeightPointsV2.Point0532.input,c,d,SourceHeightPointsV2.Point0532.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0533.source_outputs
   exact ⟨SourceHeightPointsV2.Point0533.input,c,d,SourceHeightPointsV2.Point0533.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0534.source_outputs
   exact ⟨SourceHeightPointsV2.Point0534.input,c,d,SourceHeightPointsV2.Point0534.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0535.source_outputs
   exact ⟨SourceHeightPointsV2.Point0535.input,c,d,SourceHeightPointsV2.Point0535.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0536.source_outputs
   exact ⟨SourceHeightPointsV2.Point0536.input,c,d,SourceHeightPointsV2.Point0536.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0537.source_outputs
   exact ⟨SourceHeightPointsV2.Point0537.input,c,d,SourceHeightPointsV2.Point0537.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0538.source_outputs
   exact ⟨SourceHeightPointsV2.Point0538.input,c,d,SourceHeightPointsV2.Point0538.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0539.source_outputs
   exact ⟨SourceHeightPointsV2.Point0539.input,c,d,SourceHeightPointsV2.Point0539.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0540.source_outputs
   exact ⟨SourceHeightPointsV2.Point0540.input,c,d,SourceHeightPointsV2.Point0540.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0541.source_outputs
   exact ⟨SourceHeightPointsV2.Point0541.input,c,d,SourceHeightPointsV2.Point0541.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0542.source_outputs
   exact ⟨SourceHeightPointsV2.Point0542.input,c,d,SourceHeightPointsV2.Point0542.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0543.source_outputs
   exact ⟨SourceHeightPointsV2.Point0543.input,c,d,SourceHeightPointsV2.Point0543.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block16
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block16.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
