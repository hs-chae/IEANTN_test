import SourceHeightPointsV2.Point0704
import SourceHeightPointsV2.Point0705
import SourceHeightPointsV2.Point0706
import SourceHeightPointsV2.Point0707
import SourceHeightPointsV2.Point0708
import SourceHeightPointsV2.Point0709
import SourceHeightPointsV2.Point0710
import SourceHeightPointsV2.Point0711
import SourceHeightPointsV2.Point0712
import SourceHeightPointsV2.Point0713
import SourceHeightPointsV2.Point0714
import SourceHeightPointsV2.Point0715
import SourceHeightPointsV2.Point0716
import SourceHeightPointsV2.Point0717
import SourceHeightPointsV2.Point0718
import SourceHeightPointsV2.Point0719
import SourceHeightPointsV2.Point0720
import SourceHeightPointsV2.Point0721
import SourceHeightPointsV2.Point0722
import SourceHeightPointsV2.Point0723
import SourceHeightPointsV2.Point0724
import SourceHeightPointsV2.Point0725
import SourceHeightPointsV2.Point0726
import SourceHeightPointsV2.Point0727
import SourceHeightPointsV2.Point0728
import SourceHeightPointsV2.Point0729
import SourceHeightPointsV2.Point0730
import SourceHeightPointsV2.Point0731
import SourceHeightPointsV2.Point0732
import SourceHeightPointsV2.Point0733
import SourceHeightPointsV2.Point0734
import SourceHeightPointsV2.Point0735
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block22
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 704 ≤ i) (upper : i < 736) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0704.source_outputs
   exact ⟨SourceHeightPointsV2.Point0704.input,c,d,SourceHeightPointsV2.Point0704.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0705.source_outputs
   exact ⟨SourceHeightPointsV2.Point0705.input,c,d,SourceHeightPointsV2.Point0705.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0706.source_outputs
   exact ⟨SourceHeightPointsV2.Point0706.input,c,d,SourceHeightPointsV2.Point0706.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0707.source_outputs
   exact ⟨SourceHeightPointsV2.Point0707.input,c,d,SourceHeightPointsV2.Point0707.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0708.source_outputs
   exact ⟨SourceHeightPointsV2.Point0708.input,c,d,SourceHeightPointsV2.Point0708.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0709.source_outputs
   exact ⟨SourceHeightPointsV2.Point0709.input,c,d,SourceHeightPointsV2.Point0709.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0710.source_outputs
   exact ⟨SourceHeightPointsV2.Point0710.input,c,d,SourceHeightPointsV2.Point0710.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0711.source_outputs
   exact ⟨SourceHeightPointsV2.Point0711.input,c,d,SourceHeightPointsV2.Point0711.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0712.source_outputs
   exact ⟨SourceHeightPointsV2.Point0712.input,c,d,SourceHeightPointsV2.Point0712.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0713.source_outputs
   exact ⟨SourceHeightPointsV2.Point0713.input,c,d,SourceHeightPointsV2.Point0713.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0714.source_outputs
   exact ⟨SourceHeightPointsV2.Point0714.input,c,d,SourceHeightPointsV2.Point0714.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0715.source_outputs
   exact ⟨SourceHeightPointsV2.Point0715.input,c,d,SourceHeightPointsV2.Point0715.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0716.source_outputs
   exact ⟨SourceHeightPointsV2.Point0716.input,c,d,SourceHeightPointsV2.Point0716.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0717.source_outputs
   exact ⟨SourceHeightPointsV2.Point0717.input,c,d,SourceHeightPointsV2.Point0717.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0718.source_outputs
   exact ⟨SourceHeightPointsV2.Point0718.input,c,d,SourceHeightPointsV2.Point0718.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0719.source_outputs
   exact ⟨SourceHeightPointsV2.Point0719.input,c,d,SourceHeightPointsV2.Point0719.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0720.source_outputs
   exact ⟨SourceHeightPointsV2.Point0720.input,c,d,SourceHeightPointsV2.Point0720.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0721.source_outputs
   exact ⟨SourceHeightPointsV2.Point0721.input,c,d,SourceHeightPointsV2.Point0721.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0722.source_outputs
   exact ⟨SourceHeightPointsV2.Point0722.input,c,d,SourceHeightPointsV2.Point0722.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0723.source_outputs
   exact ⟨SourceHeightPointsV2.Point0723.input,c,d,SourceHeightPointsV2.Point0723.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0724.source_outputs
   exact ⟨SourceHeightPointsV2.Point0724.input,c,d,SourceHeightPointsV2.Point0724.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0725.source_outputs
   exact ⟨SourceHeightPointsV2.Point0725.input,c,d,SourceHeightPointsV2.Point0725.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0726.source_outputs
   exact ⟨SourceHeightPointsV2.Point0726.input,c,d,SourceHeightPointsV2.Point0726.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0727.source_outputs
   exact ⟨SourceHeightPointsV2.Point0727.input,c,d,SourceHeightPointsV2.Point0727.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0728.source_outputs
   exact ⟨SourceHeightPointsV2.Point0728.input,c,d,SourceHeightPointsV2.Point0728.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0729.source_outputs
   exact ⟨SourceHeightPointsV2.Point0729.input,c,d,SourceHeightPointsV2.Point0729.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0730.source_outputs
   exact ⟨SourceHeightPointsV2.Point0730.input,c,d,SourceHeightPointsV2.Point0730.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0731.source_outputs
   exact ⟨SourceHeightPointsV2.Point0731.input,c,d,SourceHeightPointsV2.Point0731.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0732.source_outputs
   exact ⟨SourceHeightPointsV2.Point0732.input,c,d,SourceHeightPointsV2.Point0732.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0733.source_outputs
   exact ⟨SourceHeightPointsV2.Point0733.input,c,d,SourceHeightPointsV2.Point0733.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0734.source_outputs
   exact ⟨SourceHeightPointsV2.Point0734.input,c,d,SourceHeightPointsV2.Point0734.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0735.source_outputs
   exact ⟨SourceHeightPointsV2.Point0735.input,c,d,SourceHeightPointsV2.Point0735.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block22
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block22.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
