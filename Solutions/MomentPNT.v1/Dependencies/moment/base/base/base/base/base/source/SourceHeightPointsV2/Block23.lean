import SourceHeightPointsV2.Point0736
import SourceHeightPointsV2.Point0737
import SourceHeightPointsV2.Point0738
import SourceHeightPointsV2.Point0739
import SourceHeightPointsV2.Point0740
import SourceHeightPointsV2.Point0741
import SourceHeightPointsV2.Point0742
import SourceHeightPointsV2.Point0743
import SourceHeightPointsV2.Point0744
import SourceHeightPointsV2.Point0745
import SourceHeightPointsV2.Point0746
import SourceHeightPointsV2.Point0747
import SourceHeightPointsV2.Point0748
import SourceHeightPointsV2.Point0749
import SourceHeightPointsV2.Point0750
import SourceHeightPointsV2.Point0751
import SourceHeightPointsV2.Point0752
import SourceHeightPointsV2.Point0753
import SourceHeightPointsV2.Point0754
import SourceHeightPointsV2.Point0755
import SourceHeightPointsV2.Point0756
import SourceHeightPointsV2.Point0757
import SourceHeightPointsV2.Point0758
import SourceHeightPointsV2.Point0759
import SourceHeightPointsV2.Point0760
import SourceHeightPointsV2.Point0761
import SourceHeightPointsV2.Point0762
import SourceHeightPointsV2.Point0763
import SourceHeightPointsV2.Point0764
import SourceHeightPointsV2.Point0765
import SourceHeightPointsV2.Point0766
import SourceHeightPointsV2.Point0767
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block23
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 736 ≤ i) (upper : i < 768) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0736.source_outputs
   exact ⟨SourceHeightPointsV2.Point0736.input,c,d,SourceHeightPointsV2.Point0736.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0737.source_outputs
   exact ⟨SourceHeightPointsV2.Point0737.input,c,d,SourceHeightPointsV2.Point0737.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0738.source_outputs
   exact ⟨SourceHeightPointsV2.Point0738.input,c,d,SourceHeightPointsV2.Point0738.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0739.source_outputs
   exact ⟨SourceHeightPointsV2.Point0739.input,c,d,SourceHeightPointsV2.Point0739.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0740.source_outputs
   exact ⟨SourceHeightPointsV2.Point0740.input,c,d,SourceHeightPointsV2.Point0740.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0741.source_outputs
   exact ⟨SourceHeightPointsV2.Point0741.input,c,d,SourceHeightPointsV2.Point0741.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0742.source_outputs
   exact ⟨SourceHeightPointsV2.Point0742.input,c,d,SourceHeightPointsV2.Point0742.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0743.source_outputs
   exact ⟨SourceHeightPointsV2.Point0743.input,c,d,SourceHeightPointsV2.Point0743.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0744.source_outputs
   exact ⟨SourceHeightPointsV2.Point0744.input,c,d,SourceHeightPointsV2.Point0744.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0745.source_outputs
   exact ⟨SourceHeightPointsV2.Point0745.input,c,d,SourceHeightPointsV2.Point0745.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0746.source_outputs
   exact ⟨SourceHeightPointsV2.Point0746.input,c,d,SourceHeightPointsV2.Point0746.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0747.source_outputs
   exact ⟨SourceHeightPointsV2.Point0747.input,c,d,SourceHeightPointsV2.Point0747.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0748.source_outputs
   exact ⟨SourceHeightPointsV2.Point0748.input,c,d,SourceHeightPointsV2.Point0748.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0749.source_outputs
   exact ⟨SourceHeightPointsV2.Point0749.input,c,d,SourceHeightPointsV2.Point0749.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0750.source_outputs
   exact ⟨SourceHeightPointsV2.Point0750.input,c,d,SourceHeightPointsV2.Point0750.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0751.source_outputs
   exact ⟨SourceHeightPointsV2.Point0751.input,c,d,SourceHeightPointsV2.Point0751.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0752.source_outputs
   exact ⟨SourceHeightPointsV2.Point0752.input,c,d,SourceHeightPointsV2.Point0752.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0753.source_outputs
   exact ⟨SourceHeightPointsV2.Point0753.input,c,d,SourceHeightPointsV2.Point0753.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0754.source_outputs
   exact ⟨SourceHeightPointsV2.Point0754.input,c,d,SourceHeightPointsV2.Point0754.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0755.source_outputs
   exact ⟨SourceHeightPointsV2.Point0755.input,c,d,SourceHeightPointsV2.Point0755.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0756.source_outputs
   exact ⟨SourceHeightPointsV2.Point0756.input,c,d,SourceHeightPointsV2.Point0756.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0757.source_outputs
   exact ⟨SourceHeightPointsV2.Point0757.input,c,d,SourceHeightPointsV2.Point0757.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0758.source_outputs
   exact ⟨SourceHeightPointsV2.Point0758.input,c,d,SourceHeightPointsV2.Point0758.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0759.source_outputs
   exact ⟨SourceHeightPointsV2.Point0759.input,c,d,SourceHeightPointsV2.Point0759.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0760.source_outputs
   exact ⟨SourceHeightPointsV2.Point0760.input,c,d,SourceHeightPointsV2.Point0760.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0761.source_outputs
   exact ⟨SourceHeightPointsV2.Point0761.input,c,d,SourceHeightPointsV2.Point0761.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0762.source_outputs
   exact ⟨SourceHeightPointsV2.Point0762.input,c,d,SourceHeightPointsV2.Point0762.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0763.source_outputs
   exact ⟨SourceHeightPointsV2.Point0763.input,c,d,SourceHeightPointsV2.Point0763.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0764.source_outputs
   exact ⟨SourceHeightPointsV2.Point0764.input,c,d,SourceHeightPointsV2.Point0764.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0765.source_outputs
   exact ⟨SourceHeightPointsV2.Point0765.input,c,d,SourceHeightPointsV2.Point0765.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0766.source_outputs
   exact ⟨SourceHeightPointsV2.Point0766.input,c,d,SourceHeightPointsV2.Point0766.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0767.source_outputs
   exact ⟨SourceHeightPointsV2.Point0767.input,c,d,SourceHeightPointsV2.Point0767.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block23
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block23.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
