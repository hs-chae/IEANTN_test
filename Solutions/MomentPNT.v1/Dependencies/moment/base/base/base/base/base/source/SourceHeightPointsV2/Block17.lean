import SourceHeightPointsV2.Point0544
import SourceHeightPointsV2.Point0545
import SourceHeightPointsV2.Point0546
import SourceHeightPointsV2.Point0547
import SourceHeightPointsV2.Point0548
import SourceHeightPointsV2.Point0549
import SourceHeightPointsV2.Point0550
import SourceHeightPointsV2.Point0551
import SourceHeightPointsV2.Point0552
import SourceHeightPointsV2.Point0553
import SourceHeightPointsV2.Point0554
import SourceHeightPointsV2.Point0555
import SourceHeightPointsV2.Point0556
import SourceHeightPointsV2.Point0557
import SourceHeightPointsV2.Point0558
import SourceHeightPointsV2.Point0559
import SourceHeightPointsV2.Point0560
import SourceHeightPointsV2.Point0561
import SourceHeightPointsV2.Point0562
import SourceHeightPointsV2.Point0563
import SourceHeightPointsV2.Point0564
import SourceHeightPointsV2.Point0565
import SourceHeightPointsV2.Point0566
import SourceHeightPointsV2.Point0567
import SourceHeightPointsV2.Point0568
import SourceHeightPointsV2.Point0569
import SourceHeightPointsV2.Point0570
import SourceHeightPointsV2.Point0571
import SourceHeightPointsV2.Point0572
import SourceHeightPointsV2.Point0573
import SourceHeightPointsV2.Point0574
import SourceHeightPointsV2.Point0575
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block17
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 544 ≤ i) (upper : i < 576) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0544.source_outputs
   exact ⟨SourceHeightPointsV2.Point0544.input,c,d,SourceHeightPointsV2.Point0544.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0545.source_outputs
   exact ⟨SourceHeightPointsV2.Point0545.input,c,d,SourceHeightPointsV2.Point0545.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0546.source_outputs
   exact ⟨SourceHeightPointsV2.Point0546.input,c,d,SourceHeightPointsV2.Point0546.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0547.source_outputs
   exact ⟨SourceHeightPointsV2.Point0547.input,c,d,SourceHeightPointsV2.Point0547.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0548.source_outputs
   exact ⟨SourceHeightPointsV2.Point0548.input,c,d,SourceHeightPointsV2.Point0548.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0549.source_outputs
   exact ⟨SourceHeightPointsV2.Point0549.input,c,d,SourceHeightPointsV2.Point0549.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0550.source_outputs
   exact ⟨SourceHeightPointsV2.Point0550.input,c,d,SourceHeightPointsV2.Point0550.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0551.source_outputs
   exact ⟨SourceHeightPointsV2.Point0551.input,c,d,SourceHeightPointsV2.Point0551.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0552.source_outputs
   exact ⟨SourceHeightPointsV2.Point0552.input,c,d,SourceHeightPointsV2.Point0552.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0553.source_outputs
   exact ⟨SourceHeightPointsV2.Point0553.input,c,d,SourceHeightPointsV2.Point0553.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0554.source_outputs
   exact ⟨SourceHeightPointsV2.Point0554.input,c,d,SourceHeightPointsV2.Point0554.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0555.source_outputs
   exact ⟨SourceHeightPointsV2.Point0555.input,c,d,SourceHeightPointsV2.Point0555.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0556.source_outputs
   exact ⟨SourceHeightPointsV2.Point0556.input,c,d,SourceHeightPointsV2.Point0556.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0557.source_outputs
   exact ⟨SourceHeightPointsV2.Point0557.input,c,d,SourceHeightPointsV2.Point0557.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0558.source_outputs
   exact ⟨SourceHeightPointsV2.Point0558.input,c,d,SourceHeightPointsV2.Point0558.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0559.source_outputs
   exact ⟨SourceHeightPointsV2.Point0559.input,c,d,SourceHeightPointsV2.Point0559.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0560.source_outputs
   exact ⟨SourceHeightPointsV2.Point0560.input,c,d,SourceHeightPointsV2.Point0560.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0561.source_outputs
   exact ⟨SourceHeightPointsV2.Point0561.input,c,d,SourceHeightPointsV2.Point0561.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0562.source_outputs
   exact ⟨SourceHeightPointsV2.Point0562.input,c,d,SourceHeightPointsV2.Point0562.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0563.source_outputs
   exact ⟨SourceHeightPointsV2.Point0563.input,c,d,SourceHeightPointsV2.Point0563.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0564.source_outputs
   exact ⟨SourceHeightPointsV2.Point0564.input,c,d,SourceHeightPointsV2.Point0564.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0565.source_outputs
   exact ⟨SourceHeightPointsV2.Point0565.input,c,d,SourceHeightPointsV2.Point0565.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0566.source_outputs
   exact ⟨SourceHeightPointsV2.Point0566.input,c,d,SourceHeightPointsV2.Point0566.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0567.source_outputs
   exact ⟨SourceHeightPointsV2.Point0567.input,c,d,SourceHeightPointsV2.Point0567.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0568.source_outputs
   exact ⟨SourceHeightPointsV2.Point0568.input,c,d,SourceHeightPointsV2.Point0568.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0569.source_outputs
   exact ⟨SourceHeightPointsV2.Point0569.input,c,d,SourceHeightPointsV2.Point0569.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0570.source_outputs
   exact ⟨SourceHeightPointsV2.Point0570.input,c,d,SourceHeightPointsV2.Point0570.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0571.source_outputs
   exact ⟨SourceHeightPointsV2.Point0571.input,c,d,SourceHeightPointsV2.Point0571.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0572.source_outputs
   exact ⟨SourceHeightPointsV2.Point0572.input,c,d,SourceHeightPointsV2.Point0572.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0573.source_outputs
   exact ⟨SourceHeightPointsV2.Point0573.input,c,d,SourceHeightPointsV2.Point0573.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0574.source_outputs
   exact ⟨SourceHeightPointsV2.Point0574.input,c,d,SourceHeightPointsV2.Point0574.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0575.source_outputs
   exact ⟨SourceHeightPointsV2.Point0575.input,c,d,SourceHeightPointsV2.Point0575.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block17
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block17.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
