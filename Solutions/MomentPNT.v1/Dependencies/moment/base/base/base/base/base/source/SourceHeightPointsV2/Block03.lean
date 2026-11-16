import SourceHeightPointsV2.Point0096
import SourceHeightPointsV2.Point0097
import SourceHeightPointsV2.Point0098
import SourceHeightPointsV2.Point0099
import SourceHeightPointsV2.Point0100
import SourceHeightPointsV2.Point0101
import SourceHeightPointsV2.Point0102
import SourceHeightPointsV2.Point0103
import SourceHeightPointsV2.Point0104
import SourceHeightPointsV2.Point0105
import SourceHeightPointsV2.Point0106
import SourceHeightPointsV2.Point0107
import SourceHeightPointsV2.Point0108
import SourceHeightPointsV2.Point0109
import SourceHeightPointsV2.Point0110
import SourceHeightPointsV2.Point0111
import SourceHeightPointsV2.Point0112
import SourceHeightPointsV2.Point0113
import SourceHeightPointsV2.Point0114
import SourceHeightPointsV2.Point0115
import SourceHeightPointsV2.Point0116
import SourceHeightPointsV2.Point0117
import SourceHeightPointsV2.Point0118
import SourceHeightPointsV2.Point0119
import SourceHeightPointsV2.Point0120
import SourceHeightPointsV2.Point0121
import SourceHeightPointsV2.Point0122
import SourceHeightPointsV2.Point0123
import SourceHeightPointsV2.Point0124
import SourceHeightPointsV2.Point0125
import SourceHeightPointsV2.Point0126
import SourceHeightPointsV2.Point0127
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block03
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 96 ≤ i) (upper : i < 128) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0096.source_outputs
   exact ⟨SourceHeightPointsV2.Point0096.input,c,d,SourceHeightPointsV2.Point0096.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0097.source_outputs
   exact ⟨SourceHeightPointsV2.Point0097.input,c,d,SourceHeightPointsV2.Point0097.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0098.source_outputs
   exact ⟨SourceHeightPointsV2.Point0098.input,c,d,SourceHeightPointsV2.Point0098.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0099.source_outputs
   exact ⟨SourceHeightPointsV2.Point0099.input,c,d,SourceHeightPointsV2.Point0099.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0100.source_outputs
   exact ⟨SourceHeightPointsV2.Point0100.input,c,d,SourceHeightPointsV2.Point0100.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0101.source_outputs
   exact ⟨SourceHeightPointsV2.Point0101.input,c,d,SourceHeightPointsV2.Point0101.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0102.source_outputs
   exact ⟨SourceHeightPointsV2.Point0102.input,c,d,SourceHeightPointsV2.Point0102.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0103.source_outputs
   exact ⟨SourceHeightPointsV2.Point0103.input,c,d,SourceHeightPointsV2.Point0103.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0104.source_outputs
   exact ⟨SourceHeightPointsV2.Point0104.input,c,d,SourceHeightPointsV2.Point0104.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0105.source_outputs
   exact ⟨SourceHeightPointsV2.Point0105.input,c,d,SourceHeightPointsV2.Point0105.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0106.source_outputs
   exact ⟨SourceHeightPointsV2.Point0106.input,c,d,SourceHeightPointsV2.Point0106.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0107.source_outputs
   exact ⟨SourceHeightPointsV2.Point0107.input,c,d,SourceHeightPointsV2.Point0107.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0108.source_outputs
   exact ⟨SourceHeightPointsV2.Point0108.input,c,d,SourceHeightPointsV2.Point0108.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0109.source_outputs
   exact ⟨SourceHeightPointsV2.Point0109.input,c,d,SourceHeightPointsV2.Point0109.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0110.source_outputs
   exact ⟨SourceHeightPointsV2.Point0110.input,c,d,SourceHeightPointsV2.Point0110.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0111.source_outputs
   exact ⟨SourceHeightPointsV2.Point0111.input,c,d,SourceHeightPointsV2.Point0111.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0112.source_outputs
   exact ⟨SourceHeightPointsV2.Point0112.input,c,d,SourceHeightPointsV2.Point0112.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0113.source_outputs
   exact ⟨SourceHeightPointsV2.Point0113.input,c,d,SourceHeightPointsV2.Point0113.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0114.source_outputs
   exact ⟨SourceHeightPointsV2.Point0114.input,c,d,SourceHeightPointsV2.Point0114.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0115.source_outputs
   exact ⟨SourceHeightPointsV2.Point0115.input,c,d,SourceHeightPointsV2.Point0115.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0116.source_outputs
   exact ⟨SourceHeightPointsV2.Point0116.input,c,d,SourceHeightPointsV2.Point0116.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0117.source_outputs
   exact ⟨SourceHeightPointsV2.Point0117.input,c,d,SourceHeightPointsV2.Point0117.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0118.source_outputs
   exact ⟨SourceHeightPointsV2.Point0118.input,c,d,SourceHeightPointsV2.Point0118.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0119.source_outputs
   exact ⟨SourceHeightPointsV2.Point0119.input,c,d,SourceHeightPointsV2.Point0119.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0120.source_outputs
   exact ⟨SourceHeightPointsV2.Point0120.input,c,d,SourceHeightPointsV2.Point0120.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0121.source_outputs
   exact ⟨SourceHeightPointsV2.Point0121.input,c,d,SourceHeightPointsV2.Point0121.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0122.source_outputs
   exact ⟨SourceHeightPointsV2.Point0122.input,c,d,SourceHeightPointsV2.Point0122.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0123.source_outputs
   exact ⟨SourceHeightPointsV2.Point0123.input,c,d,SourceHeightPointsV2.Point0123.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0124.source_outputs
   exact ⟨SourceHeightPointsV2.Point0124.input,c,d,SourceHeightPointsV2.Point0124.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0125.source_outputs
   exact ⟨SourceHeightPointsV2.Point0125.input,c,d,SourceHeightPointsV2.Point0125.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0126.source_outputs
   exact ⟨SourceHeightPointsV2.Point0126.input,c,d,SourceHeightPointsV2.Point0126.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0127.source_outputs
   exact ⟨SourceHeightPointsV2.Point0127.input,c,d,SourceHeightPointsV2.Point0127.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block03
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block03.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
