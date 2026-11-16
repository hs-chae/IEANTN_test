import SourceHeightPointsV2.Point0064
import SourceHeightPointsV2.Point0065
import SourceHeightPointsV2.Point0066
import SourceHeightPointsV2.Point0067
import SourceHeightPointsV2.Point0068
import SourceHeightPointsV2.Point0069
import SourceHeightPointsV2.Point0070
import SourceHeightPointsV2.Point0071
import SourceHeightPointsV2.Point0072
import SourceHeightPointsV2.Point0073
import SourceHeightPointsV2.Point0074
import SourceHeightPointsV2.Point0075
import SourceHeightPointsV2.Point0076
import SourceHeightPointsV2.Point0077
import SourceHeightPointsV2.Point0078
import SourceHeightPointsV2.Point0079
import SourceHeightPointsV2.Point0080
import SourceHeightPointsV2.Point0081
import SourceHeightPointsV2.Point0082
import SourceHeightPointsV2.Point0083
import SourceHeightPointsV2.Point0084
import SourceHeightPointsV2.Point0085
import SourceHeightPointsV2.Point0086
import SourceHeightPointsV2.Point0087
import SourceHeightPointsV2.Point0088
import SourceHeightPointsV2.Point0089
import SourceHeightPointsV2.Point0090
import SourceHeightPointsV2.Point0091
import SourceHeightPointsV2.Point0092
import SourceHeightPointsV2.Point0093
import SourceHeightPointsV2.Point0094
import SourceHeightPointsV2.Point0095
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block02
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 64 ≤ i) (upper : i < 96) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0064.source_outputs
   exact ⟨SourceHeightPointsV2.Point0064.input,c,d,SourceHeightPointsV2.Point0064.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0065.source_outputs
   exact ⟨SourceHeightPointsV2.Point0065.input,c,d,SourceHeightPointsV2.Point0065.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0066.source_outputs
   exact ⟨SourceHeightPointsV2.Point0066.input,c,d,SourceHeightPointsV2.Point0066.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0067.source_outputs
   exact ⟨SourceHeightPointsV2.Point0067.input,c,d,SourceHeightPointsV2.Point0067.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0068.source_outputs
   exact ⟨SourceHeightPointsV2.Point0068.input,c,d,SourceHeightPointsV2.Point0068.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0069.source_outputs
   exact ⟨SourceHeightPointsV2.Point0069.input,c,d,SourceHeightPointsV2.Point0069.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0070.source_outputs
   exact ⟨SourceHeightPointsV2.Point0070.input,c,d,SourceHeightPointsV2.Point0070.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0071.source_outputs
   exact ⟨SourceHeightPointsV2.Point0071.input,c,d,SourceHeightPointsV2.Point0071.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0072.source_outputs
   exact ⟨SourceHeightPointsV2.Point0072.input,c,d,SourceHeightPointsV2.Point0072.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0073.source_outputs
   exact ⟨SourceHeightPointsV2.Point0073.input,c,d,SourceHeightPointsV2.Point0073.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0074.source_outputs
   exact ⟨SourceHeightPointsV2.Point0074.input,c,d,SourceHeightPointsV2.Point0074.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0075.source_outputs
   exact ⟨SourceHeightPointsV2.Point0075.input,c,d,SourceHeightPointsV2.Point0075.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0076.source_outputs
   exact ⟨SourceHeightPointsV2.Point0076.input,c,d,SourceHeightPointsV2.Point0076.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0077.source_outputs
   exact ⟨SourceHeightPointsV2.Point0077.input,c,d,SourceHeightPointsV2.Point0077.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0078.source_outputs
   exact ⟨SourceHeightPointsV2.Point0078.input,c,d,SourceHeightPointsV2.Point0078.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0079.source_outputs
   exact ⟨SourceHeightPointsV2.Point0079.input,c,d,SourceHeightPointsV2.Point0079.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0080.source_outputs
   exact ⟨SourceHeightPointsV2.Point0080.input,c,d,SourceHeightPointsV2.Point0080.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0081.source_outputs
   exact ⟨SourceHeightPointsV2.Point0081.input,c,d,SourceHeightPointsV2.Point0081.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0082.source_outputs
   exact ⟨SourceHeightPointsV2.Point0082.input,c,d,SourceHeightPointsV2.Point0082.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0083.source_outputs
   exact ⟨SourceHeightPointsV2.Point0083.input,c,d,SourceHeightPointsV2.Point0083.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0084.source_outputs
   exact ⟨SourceHeightPointsV2.Point0084.input,c,d,SourceHeightPointsV2.Point0084.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0085.source_outputs
   exact ⟨SourceHeightPointsV2.Point0085.input,c,d,SourceHeightPointsV2.Point0085.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0086.source_outputs
   exact ⟨SourceHeightPointsV2.Point0086.input,c,d,SourceHeightPointsV2.Point0086.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0087.source_outputs
   exact ⟨SourceHeightPointsV2.Point0087.input,c,d,SourceHeightPointsV2.Point0087.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0088.source_outputs
   exact ⟨SourceHeightPointsV2.Point0088.input,c,d,SourceHeightPointsV2.Point0088.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0089.source_outputs
   exact ⟨SourceHeightPointsV2.Point0089.input,c,d,SourceHeightPointsV2.Point0089.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0090.source_outputs
   exact ⟨SourceHeightPointsV2.Point0090.input,c,d,SourceHeightPointsV2.Point0090.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0091.source_outputs
   exact ⟨SourceHeightPointsV2.Point0091.input,c,d,SourceHeightPointsV2.Point0091.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0092.source_outputs
   exact ⟨SourceHeightPointsV2.Point0092.input,c,d,SourceHeightPointsV2.Point0092.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0093.source_outputs
   exact ⟨SourceHeightPointsV2.Point0093.input,c,d,SourceHeightPointsV2.Point0093.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0094.source_outputs
   exact ⟨SourceHeightPointsV2.Point0094.input,c,d,SourceHeightPointsV2.Point0094.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0095.source_outputs
   exact ⟨SourceHeightPointsV2.Point0095.input,c,d,SourceHeightPointsV2.Point0095.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block02
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block02.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
