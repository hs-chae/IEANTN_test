import SourceHeightPointsV2.Point0608
import SourceHeightPointsV2.Point0609
import SourceHeightPointsV2.Point0610
import SourceHeightPointsV2.Point0611
import SourceHeightPointsV2.Point0612
import SourceHeightPointsV2.Point0613
import SourceHeightPointsV2.Point0614
import SourceHeightPointsV2.Point0615
import SourceHeightPointsV2.Point0616
import SourceHeightPointsV2.Point0617
import SourceHeightPointsV2.Point0618
import SourceHeightPointsV2.Point0619
import SourceHeightPointsV2.Point0620
import SourceHeightPointsV2.Point0621
import SourceHeightPointsV2.Point0622
import SourceHeightPointsV2.Point0623
import SourceHeightPointsV2.Point0624
import SourceHeightPointsV2.Point0625
import SourceHeightPointsV2.Point0626
import SourceHeightPointsV2.Point0627
import SourceHeightPointsV2.Point0628
import SourceHeightPointsV2.Point0629
import SourceHeightPointsV2.Point0630
import SourceHeightPointsV2.Point0631
import SourceHeightPointsV2.Point0632
import SourceHeightPointsV2.Point0633
import SourceHeightPointsV2.Point0634
import SourceHeightPointsV2.Point0635
import SourceHeightPointsV2.Point0636
import SourceHeightPointsV2.Point0637
import SourceHeightPointsV2.Point0638
import SourceHeightPointsV2.Point0639
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block19
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 608 ≤ i) (upper : i < 640) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0608.source_outputs
   exact ⟨SourceHeightPointsV2.Point0608.input,c,d,SourceHeightPointsV2.Point0608.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0609.source_outputs
   exact ⟨SourceHeightPointsV2.Point0609.input,c,d,SourceHeightPointsV2.Point0609.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0610.source_outputs
   exact ⟨SourceHeightPointsV2.Point0610.input,c,d,SourceHeightPointsV2.Point0610.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0611.source_outputs
   exact ⟨SourceHeightPointsV2.Point0611.input,c,d,SourceHeightPointsV2.Point0611.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0612.source_outputs
   exact ⟨SourceHeightPointsV2.Point0612.input,c,d,SourceHeightPointsV2.Point0612.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0613.source_outputs
   exact ⟨SourceHeightPointsV2.Point0613.input,c,d,SourceHeightPointsV2.Point0613.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0614.source_outputs
   exact ⟨SourceHeightPointsV2.Point0614.input,c,d,SourceHeightPointsV2.Point0614.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0615.source_outputs
   exact ⟨SourceHeightPointsV2.Point0615.input,c,d,SourceHeightPointsV2.Point0615.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0616.source_outputs
   exact ⟨SourceHeightPointsV2.Point0616.input,c,d,SourceHeightPointsV2.Point0616.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0617.source_outputs
   exact ⟨SourceHeightPointsV2.Point0617.input,c,d,SourceHeightPointsV2.Point0617.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0618.source_outputs
   exact ⟨SourceHeightPointsV2.Point0618.input,c,d,SourceHeightPointsV2.Point0618.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0619.source_outputs
   exact ⟨SourceHeightPointsV2.Point0619.input,c,d,SourceHeightPointsV2.Point0619.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0620.source_outputs
   exact ⟨SourceHeightPointsV2.Point0620.input,c,d,SourceHeightPointsV2.Point0620.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0621.source_outputs
   exact ⟨SourceHeightPointsV2.Point0621.input,c,d,SourceHeightPointsV2.Point0621.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0622.source_outputs
   exact ⟨SourceHeightPointsV2.Point0622.input,c,d,SourceHeightPointsV2.Point0622.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0623.source_outputs
   exact ⟨SourceHeightPointsV2.Point0623.input,c,d,SourceHeightPointsV2.Point0623.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0624.source_outputs
   exact ⟨SourceHeightPointsV2.Point0624.input,c,d,SourceHeightPointsV2.Point0624.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0625.source_outputs
   exact ⟨SourceHeightPointsV2.Point0625.input,c,d,SourceHeightPointsV2.Point0625.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0626.source_outputs
   exact ⟨SourceHeightPointsV2.Point0626.input,c,d,SourceHeightPointsV2.Point0626.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0627.source_outputs
   exact ⟨SourceHeightPointsV2.Point0627.input,c,d,SourceHeightPointsV2.Point0627.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0628.source_outputs
   exact ⟨SourceHeightPointsV2.Point0628.input,c,d,SourceHeightPointsV2.Point0628.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0629.source_outputs
   exact ⟨SourceHeightPointsV2.Point0629.input,c,d,SourceHeightPointsV2.Point0629.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0630.source_outputs
   exact ⟨SourceHeightPointsV2.Point0630.input,c,d,SourceHeightPointsV2.Point0630.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0631.source_outputs
   exact ⟨SourceHeightPointsV2.Point0631.input,c,d,SourceHeightPointsV2.Point0631.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0632.source_outputs
   exact ⟨SourceHeightPointsV2.Point0632.input,c,d,SourceHeightPointsV2.Point0632.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0633.source_outputs
   exact ⟨SourceHeightPointsV2.Point0633.input,c,d,SourceHeightPointsV2.Point0633.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0634.source_outputs
   exact ⟨SourceHeightPointsV2.Point0634.input,c,d,SourceHeightPointsV2.Point0634.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0635.source_outputs
   exact ⟨SourceHeightPointsV2.Point0635.input,c,d,SourceHeightPointsV2.Point0635.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0636.source_outputs
   exact ⟨SourceHeightPointsV2.Point0636.input,c,d,SourceHeightPointsV2.Point0636.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0637.source_outputs
   exact ⟨SourceHeightPointsV2.Point0637.input,c,d,SourceHeightPointsV2.Point0637.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0638.source_outputs
   exact ⟨SourceHeightPointsV2.Point0638.input,c,d,SourceHeightPointsV2.Point0638.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0639.source_outputs
   exact ⟨SourceHeightPointsV2.Point0639.input,c,d,SourceHeightPointsV2.Point0639.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block19
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block19.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
