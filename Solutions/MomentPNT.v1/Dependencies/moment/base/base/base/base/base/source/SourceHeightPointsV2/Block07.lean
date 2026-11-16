import SourceHeightPointsV2.Point0224
import SourceHeightPointsV2.Point0225
import SourceHeightPointsV2.Point0226
import SourceHeightPointsV2.Point0227
import SourceHeightPointsV2.Point0228
import SourceHeightPointsV2.Point0229
import SourceHeightPointsV2.Point0230
import SourceHeightPointsV2.Point0231
import SourceHeightPointsV2.Point0232
import SourceHeightPointsV2.Point0233
import SourceHeightPointsV2.Point0234
import SourceHeightPointsV2.Point0235
import SourceHeightPointsV2.Point0236
import SourceHeightPointsV2.Point0237
import SourceHeightPointsV2.Point0238
import SourceHeightPointsV2.Point0239
import SourceHeightPointsV2.Point0240
import SourceHeightPointsV2.Point0241
import SourceHeightPointsV2.Point0242
import SourceHeightPointsV2.Point0243
import SourceHeightPointsV2.Point0244
import SourceHeightPointsV2.Point0245
import SourceHeightPointsV2.Point0246
import SourceHeightPointsV2.Point0247
import SourceHeightPointsV2.Point0248
import SourceHeightPointsV2.Point0249
import SourceHeightPointsV2.Point0250
import SourceHeightPointsV2.Point0251
import SourceHeightPointsV2.Point0252
import SourceHeightPointsV2.Point0253
import SourceHeightPointsV2.Point0254
import SourceHeightPointsV2.Point0255
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block07
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 224 ≤ i) (upper : i < 256) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0224.source_outputs
   exact ⟨SourceHeightPointsV2.Point0224.input,c,d,SourceHeightPointsV2.Point0224.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0225.source_outputs
   exact ⟨SourceHeightPointsV2.Point0225.input,c,d,SourceHeightPointsV2.Point0225.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0226.source_outputs
   exact ⟨SourceHeightPointsV2.Point0226.input,c,d,SourceHeightPointsV2.Point0226.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0227.source_outputs
   exact ⟨SourceHeightPointsV2.Point0227.input,c,d,SourceHeightPointsV2.Point0227.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0228.source_outputs
   exact ⟨SourceHeightPointsV2.Point0228.input,c,d,SourceHeightPointsV2.Point0228.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0229.source_outputs
   exact ⟨SourceHeightPointsV2.Point0229.input,c,d,SourceHeightPointsV2.Point0229.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0230.source_outputs
   exact ⟨SourceHeightPointsV2.Point0230.input,c,d,SourceHeightPointsV2.Point0230.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0231.source_outputs
   exact ⟨SourceHeightPointsV2.Point0231.input,c,d,SourceHeightPointsV2.Point0231.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0232.source_outputs
   exact ⟨SourceHeightPointsV2.Point0232.input,c,d,SourceHeightPointsV2.Point0232.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0233.source_outputs
   exact ⟨SourceHeightPointsV2.Point0233.input,c,d,SourceHeightPointsV2.Point0233.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0234.source_outputs
   exact ⟨SourceHeightPointsV2.Point0234.input,c,d,SourceHeightPointsV2.Point0234.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0235.source_outputs
   exact ⟨SourceHeightPointsV2.Point0235.input,c,d,SourceHeightPointsV2.Point0235.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0236.source_outputs
   exact ⟨SourceHeightPointsV2.Point0236.input,c,d,SourceHeightPointsV2.Point0236.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0237.source_outputs
   exact ⟨SourceHeightPointsV2.Point0237.input,c,d,SourceHeightPointsV2.Point0237.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0238.source_outputs
   exact ⟨SourceHeightPointsV2.Point0238.input,c,d,SourceHeightPointsV2.Point0238.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0239.source_outputs
   exact ⟨SourceHeightPointsV2.Point0239.input,c,d,SourceHeightPointsV2.Point0239.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0240.source_outputs
   exact ⟨SourceHeightPointsV2.Point0240.input,c,d,SourceHeightPointsV2.Point0240.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0241.source_outputs
   exact ⟨SourceHeightPointsV2.Point0241.input,c,d,SourceHeightPointsV2.Point0241.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0242.source_outputs
   exact ⟨SourceHeightPointsV2.Point0242.input,c,d,SourceHeightPointsV2.Point0242.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0243.source_outputs
   exact ⟨SourceHeightPointsV2.Point0243.input,c,d,SourceHeightPointsV2.Point0243.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0244.source_outputs
   exact ⟨SourceHeightPointsV2.Point0244.input,c,d,SourceHeightPointsV2.Point0244.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0245.source_outputs
   exact ⟨SourceHeightPointsV2.Point0245.input,c,d,SourceHeightPointsV2.Point0245.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0246.source_outputs
   exact ⟨SourceHeightPointsV2.Point0246.input,c,d,SourceHeightPointsV2.Point0246.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0247.source_outputs
   exact ⟨SourceHeightPointsV2.Point0247.input,c,d,SourceHeightPointsV2.Point0247.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0248.source_outputs
   exact ⟨SourceHeightPointsV2.Point0248.input,c,d,SourceHeightPointsV2.Point0248.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0249.source_outputs
   exact ⟨SourceHeightPointsV2.Point0249.input,c,d,SourceHeightPointsV2.Point0249.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0250.source_outputs
   exact ⟨SourceHeightPointsV2.Point0250.input,c,d,SourceHeightPointsV2.Point0250.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0251.source_outputs
   exact ⟨SourceHeightPointsV2.Point0251.input,c,d,SourceHeightPointsV2.Point0251.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0252.source_outputs
   exact ⟨SourceHeightPointsV2.Point0252.input,c,d,SourceHeightPointsV2.Point0252.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0253.source_outputs
   exact ⟨SourceHeightPointsV2.Point0253.input,c,d,SourceHeightPointsV2.Point0253.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0254.source_outputs
   exact ⟨SourceHeightPointsV2.Point0254.input,c,d,SourceHeightPointsV2.Point0254.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0255.source_outputs
   exact ⟨SourceHeightPointsV2.Point0255.input,c,d,SourceHeightPointsV2.Point0255.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block07
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block07.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
