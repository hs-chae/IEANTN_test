import SourceHeightPointsV2.Point0640
import SourceHeightPointsV2.Point0641
import SourceHeightPointsV2.Point0642
import SourceHeightPointsV2.Point0643
import SourceHeightPointsV2.Point0644
import SourceHeightPointsV2.Point0645
import SourceHeightPointsV2.Point0646
import SourceHeightPointsV2.Point0647
import SourceHeightPointsV2.Point0648
import SourceHeightPointsV2.Point0649
import SourceHeightPointsV2.Point0650
import SourceHeightPointsV2.Point0651
import SourceHeightPointsV2.Point0652
import SourceHeightPointsV2.Point0653
import SourceHeightPointsV2.Point0654
import SourceHeightPointsV2.Point0655
import SourceHeightPointsV2.Point0656
import SourceHeightPointsV2.Point0657
import SourceHeightPointsV2.Point0658
import SourceHeightPointsV2.Point0659
import SourceHeightPointsV2.Point0660
import SourceHeightPointsV2.Point0661
import SourceHeightPointsV2.Point0662
import SourceHeightPointsV2.Point0663
import SourceHeightPointsV2.Point0664
import SourceHeightPointsV2.Point0665
import SourceHeightPointsV2.Point0666
import SourceHeightPointsV2.Point0667
import SourceHeightPointsV2.Point0668
import SourceHeightPointsV2.Point0669
import SourceHeightPointsV2.Point0670
import SourceHeightPointsV2.Point0671
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block20
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 640 ≤ i) (upper : i < 672) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0640.source_outputs
   exact ⟨SourceHeightPointsV2.Point0640.input,c,d,SourceHeightPointsV2.Point0640.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0641.source_outputs
   exact ⟨SourceHeightPointsV2.Point0641.input,c,d,SourceHeightPointsV2.Point0641.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0642.source_outputs
   exact ⟨SourceHeightPointsV2.Point0642.input,c,d,SourceHeightPointsV2.Point0642.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0643.source_outputs
   exact ⟨SourceHeightPointsV2.Point0643.input,c,d,SourceHeightPointsV2.Point0643.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0644.source_outputs
   exact ⟨SourceHeightPointsV2.Point0644.input,c,d,SourceHeightPointsV2.Point0644.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0645.source_outputs
   exact ⟨SourceHeightPointsV2.Point0645.input,c,d,SourceHeightPointsV2.Point0645.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0646.source_outputs
   exact ⟨SourceHeightPointsV2.Point0646.input,c,d,SourceHeightPointsV2.Point0646.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0647.source_outputs
   exact ⟨SourceHeightPointsV2.Point0647.input,c,d,SourceHeightPointsV2.Point0647.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0648.source_outputs
   exact ⟨SourceHeightPointsV2.Point0648.input,c,d,SourceHeightPointsV2.Point0648.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0649.source_outputs
   exact ⟨SourceHeightPointsV2.Point0649.input,c,d,SourceHeightPointsV2.Point0649.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0650.source_outputs
   exact ⟨SourceHeightPointsV2.Point0650.input,c,d,SourceHeightPointsV2.Point0650.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0651.source_outputs
   exact ⟨SourceHeightPointsV2.Point0651.input,c,d,SourceHeightPointsV2.Point0651.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0652.source_outputs
   exact ⟨SourceHeightPointsV2.Point0652.input,c,d,SourceHeightPointsV2.Point0652.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0653.source_outputs
   exact ⟨SourceHeightPointsV2.Point0653.input,c,d,SourceHeightPointsV2.Point0653.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0654.source_outputs
   exact ⟨SourceHeightPointsV2.Point0654.input,c,d,SourceHeightPointsV2.Point0654.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0655.source_outputs
   exact ⟨SourceHeightPointsV2.Point0655.input,c,d,SourceHeightPointsV2.Point0655.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0656.source_outputs
   exact ⟨SourceHeightPointsV2.Point0656.input,c,d,SourceHeightPointsV2.Point0656.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0657.source_outputs
   exact ⟨SourceHeightPointsV2.Point0657.input,c,d,SourceHeightPointsV2.Point0657.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0658.source_outputs
   exact ⟨SourceHeightPointsV2.Point0658.input,c,d,SourceHeightPointsV2.Point0658.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0659.source_outputs
   exact ⟨SourceHeightPointsV2.Point0659.input,c,d,SourceHeightPointsV2.Point0659.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0660.source_outputs
   exact ⟨SourceHeightPointsV2.Point0660.input,c,d,SourceHeightPointsV2.Point0660.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0661.source_outputs
   exact ⟨SourceHeightPointsV2.Point0661.input,c,d,SourceHeightPointsV2.Point0661.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0662.source_outputs
   exact ⟨SourceHeightPointsV2.Point0662.input,c,d,SourceHeightPointsV2.Point0662.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0663.source_outputs
   exact ⟨SourceHeightPointsV2.Point0663.input,c,d,SourceHeightPointsV2.Point0663.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0664.source_outputs
   exact ⟨SourceHeightPointsV2.Point0664.input,c,d,SourceHeightPointsV2.Point0664.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0665.source_outputs
   exact ⟨SourceHeightPointsV2.Point0665.input,c,d,SourceHeightPointsV2.Point0665.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0666.source_outputs
   exact ⟨SourceHeightPointsV2.Point0666.input,c,d,SourceHeightPointsV2.Point0666.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0667.source_outputs
   exact ⟨SourceHeightPointsV2.Point0667.input,c,d,SourceHeightPointsV2.Point0667.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0668.source_outputs
   exact ⟨SourceHeightPointsV2.Point0668.input,c,d,SourceHeightPointsV2.Point0668.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0669.source_outputs
   exact ⟨SourceHeightPointsV2.Point0669.input,c,d,SourceHeightPointsV2.Point0669.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0670.source_outputs
   exact ⟨SourceHeightPointsV2.Point0670.input,c,d,SourceHeightPointsV2.Point0670.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0671.source_outputs
   exact ⟨SourceHeightPointsV2.Point0671.input,c,d,SourceHeightPointsV2.Point0671.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block20
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block20.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
