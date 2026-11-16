import SourceHeightPointsV2.Point0576
import SourceHeightPointsV2.Point0577
import SourceHeightPointsV2.Point0578
import SourceHeightPointsV2.Point0579
import SourceHeightPointsV2.Point0580
import SourceHeightPointsV2.Point0581
import SourceHeightPointsV2.Point0582
import SourceHeightPointsV2.Point0583
import SourceHeightPointsV2.Point0584
import SourceHeightPointsV2.Point0585
import SourceHeightPointsV2.Point0586
import SourceHeightPointsV2.Point0587
import SourceHeightPointsV2.Point0588
import SourceHeightPointsV2.Point0589
import SourceHeightPointsV2.Point0590
import SourceHeightPointsV2.Point0591
import SourceHeightPointsV2.Point0592
import SourceHeightPointsV2.Point0593
import SourceHeightPointsV2.Point0594
import SourceHeightPointsV2.Point0595
import SourceHeightPointsV2.Point0596
import SourceHeightPointsV2.Point0597
import SourceHeightPointsV2.Point0598
import SourceHeightPointsV2.Point0599
import SourceHeightPointsV2.Point0600
import SourceHeightPointsV2.Point0601
import SourceHeightPointsV2.Point0602
import SourceHeightPointsV2.Point0603
import SourceHeightPointsV2.Point0604
import SourceHeightPointsV2.Point0605
import SourceHeightPointsV2.Point0606
import SourceHeightPointsV2.Point0607
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block18
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 576 ≤ i) (upper : i < 608) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0576.source_outputs
   exact ⟨SourceHeightPointsV2.Point0576.input,c,d,SourceHeightPointsV2.Point0576.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0577.source_outputs
   exact ⟨SourceHeightPointsV2.Point0577.input,c,d,SourceHeightPointsV2.Point0577.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0578.source_outputs
   exact ⟨SourceHeightPointsV2.Point0578.input,c,d,SourceHeightPointsV2.Point0578.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0579.source_outputs
   exact ⟨SourceHeightPointsV2.Point0579.input,c,d,SourceHeightPointsV2.Point0579.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0580.source_outputs
   exact ⟨SourceHeightPointsV2.Point0580.input,c,d,SourceHeightPointsV2.Point0580.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0581.source_outputs
   exact ⟨SourceHeightPointsV2.Point0581.input,c,d,SourceHeightPointsV2.Point0581.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0582.source_outputs
   exact ⟨SourceHeightPointsV2.Point0582.input,c,d,SourceHeightPointsV2.Point0582.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0583.source_outputs
   exact ⟨SourceHeightPointsV2.Point0583.input,c,d,SourceHeightPointsV2.Point0583.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0584.source_outputs
   exact ⟨SourceHeightPointsV2.Point0584.input,c,d,SourceHeightPointsV2.Point0584.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0585.source_outputs
   exact ⟨SourceHeightPointsV2.Point0585.input,c,d,SourceHeightPointsV2.Point0585.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0586.source_outputs
   exact ⟨SourceHeightPointsV2.Point0586.input,c,d,SourceHeightPointsV2.Point0586.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0587.source_outputs
   exact ⟨SourceHeightPointsV2.Point0587.input,c,d,SourceHeightPointsV2.Point0587.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0588.source_outputs
   exact ⟨SourceHeightPointsV2.Point0588.input,c,d,SourceHeightPointsV2.Point0588.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0589.source_outputs
   exact ⟨SourceHeightPointsV2.Point0589.input,c,d,SourceHeightPointsV2.Point0589.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0590.source_outputs
   exact ⟨SourceHeightPointsV2.Point0590.input,c,d,SourceHeightPointsV2.Point0590.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0591.source_outputs
   exact ⟨SourceHeightPointsV2.Point0591.input,c,d,SourceHeightPointsV2.Point0591.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0592.source_outputs
   exact ⟨SourceHeightPointsV2.Point0592.input,c,d,SourceHeightPointsV2.Point0592.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0593.source_outputs
   exact ⟨SourceHeightPointsV2.Point0593.input,c,d,SourceHeightPointsV2.Point0593.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0594.source_outputs
   exact ⟨SourceHeightPointsV2.Point0594.input,c,d,SourceHeightPointsV2.Point0594.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0595.source_outputs
   exact ⟨SourceHeightPointsV2.Point0595.input,c,d,SourceHeightPointsV2.Point0595.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0596.source_outputs
   exact ⟨SourceHeightPointsV2.Point0596.input,c,d,SourceHeightPointsV2.Point0596.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0597.source_outputs
   exact ⟨SourceHeightPointsV2.Point0597.input,c,d,SourceHeightPointsV2.Point0597.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0598.source_outputs
   exact ⟨SourceHeightPointsV2.Point0598.input,c,d,SourceHeightPointsV2.Point0598.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0599.source_outputs
   exact ⟨SourceHeightPointsV2.Point0599.input,c,d,SourceHeightPointsV2.Point0599.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0600.source_outputs
   exact ⟨SourceHeightPointsV2.Point0600.input,c,d,SourceHeightPointsV2.Point0600.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0601.source_outputs
   exact ⟨SourceHeightPointsV2.Point0601.input,c,d,SourceHeightPointsV2.Point0601.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0602.source_outputs
   exact ⟨SourceHeightPointsV2.Point0602.input,c,d,SourceHeightPointsV2.Point0602.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0603.source_outputs
   exact ⟨SourceHeightPointsV2.Point0603.input,c,d,SourceHeightPointsV2.Point0603.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0604.source_outputs
   exact ⟨SourceHeightPointsV2.Point0604.input,c,d,SourceHeightPointsV2.Point0604.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0605.source_outputs
   exact ⟨SourceHeightPointsV2.Point0605.input,c,d,SourceHeightPointsV2.Point0605.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0606.source_outputs
   exact ⟨SourceHeightPointsV2.Point0606.input,c,d,SourceHeightPointsV2.Point0606.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0607.source_outputs
   exact ⟨SourceHeightPointsV2.Point0607.input,c,d,SourceHeightPointsV2.Point0607.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block18
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block18.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
