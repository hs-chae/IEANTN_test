import SourceHeightPointsV2.Point0192
import SourceHeightPointsV2.Point0193
import SourceHeightPointsV2.Point0194
import SourceHeightPointsV2.Point0195
import SourceHeightPointsV2.Point0196
import SourceHeightPointsV2.Point0197
import SourceHeightPointsV2.Point0198
import SourceHeightPointsV2.Point0199
import SourceHeightPointsV2.Point0200
import SourceHeightPointsV2.Point0201
import SourceHeightPointsV2.Point0202
import SourceHeightPointsV2.Point0203
import SourceHeightPointsV2.Point0204
import SourceHeightPointsV2.Point0205
import SourceHeightPointsV2.Point0206
import SourceHeightPointsV2.Point0207
import SourceHeightPointsV2.Point0208
import SourceHeightPointsV2.Point0209
import SourceHeightPointsV2.Point0210
import SourceHeightPointsV2.Point0211
import SourceHeightPointsV2.Point0212
import SourceHeightPointsV2.Point0213
import SourceHeightPointsV2.Point0214
import SourceHeightPointsV2.Point0215
import SourceHeightPointsV2.Point0216
import SourceHeightPointsV2.Point0217
import SourceHeightPointsV2.Point0218
import SourceHeightPointsV2.Point0219
import SourceHeightPointsV2.Point0220
import SourceHeightPointsV2.Point0221
import SourceHeightPointsV2.Point0222
import SourceHeightPointsV2.Point0223
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block06
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 192 ≤ i) (upper : i < 224) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0192.source_outputs
   exact ⟨SourceHeightPointsV2.Point0192.input,c,d,SourceHeightPointsV2.Point0192.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0193.source_outputs
   exact ⟨SourceHeightPointsV2.Point0193.input,c,d,SourceHeightPointsV2.Point0193.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0194.source_outputs
   exact ⟨SourceHeightPointsV2.Point0194.input,c,d,SourceHeightPointsV2.Point0194.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0195.source_outputs
   exact ⟨SourceHeightPointsV2.Point0195.input,c,d,SourceHeightPointsV2.Point0195.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0196.source_outputs
   exact ⟨SourceHeightPointsV2.Point0196.input,c,d,SourceHeightPointsV2.Point0196.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0197.source_outputs
   exact ⟨SourceHeightPointsV2.Point0197.input,c,d,SourceHeightPointsV2.Point0197.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0198.source_outputs
   exact ⟨SourceHeightPointsV2.Point0198.input,c,d,SourceHeightPointsV2.Point0198.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0199.source_outputs
   exact ⟨SourceHeightPointsV2.Point0199.input,c,d,SourceHeightPointsV2.Point0199.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0200.source_outputs
   exact ⟨SourceHeightPointsV2.Point0200.input,c,d,SourceHeightPointsV2.Point0200.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0201.source_outputs
   exact ⟨SourceHeightPointsV2.Point0201.input,c,d,SourceHeightPointsV2.Point0201.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0202.source_outputs
   exact ⟨SourceHeightPointsV2.Point0202.input,c,d,SourceHeightPointsV2.Point0202.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0203.source_outputs
   exact ⟨SourceHeightPointsV2.Point0203.input,c,d,SourceHeightPointsV2.Point0203.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0204.source_outputs
   exact ⟨SourceHeightPointsV2.Point0204.input,c,d,SourceHeightPointsV2.Point0204.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0205.source_outputs
   exact ⟨SourceHeightPointsV2.Point0205.input,c,d,SourceHeightPointsV2.Point0205.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0206.source_outputs
   exact ⟨SourceHeightPointsV2.Point0206.input,c,d,SourceHeightPointsV2.Point0206.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0207.source_outputs
   exact ⟨SourceHeightPointsV2.Point0207.input,c,d,SourceHeightPointsV2.Point0207.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0208.source_outputs
   exact ⟨SourceHeightPointsV2.Point0208.input,c,d,SourceHeightPointsV2.Point0208.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0209.source_outputs
   exact ⟨SourceHeightPointsV2.Point0209.input,c,d,SourceHeightPointsV2.Point0209.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0210.source_outputs
   exact ⟨SourceHeightPointsV2.Point0210.input,c,d,SourceHeightPointsV2.Point0210.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0211.source_outputs
   exact ⟨SourceHeightPointsV2.Point0211.input,c,d,SourceHeightPointsV2.Point0211.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0212.source_outputs
   exact ⟨SourceHeightPointsV2.Point0212.input,c,d,SourceHeightPointsV2.Point0212.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0213.source_outputs
   exact ⟨SourceHeightPointsV2.Point0213.input,c,d,SourceHeightPointsV2.Point0213.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0214.source_outputs
   exact ⟨SourceHeightPointsV2.Point0214.input,c,d,SourceHeightPointsV2.Point0214.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0215.source_outputs
   exact ⟨SourceHeightPointsV2.Point0215.input,c,d,SourceHeightPointsV2.Point0215.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0216.source_outputs
   exact ⟨SourceHeightPointsV2.Point0216.input,c,d,SourceHeightPointsV2.Point0216.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0217.source_outputs
   exact ⟨SourceHeightPointsV2.Point0217.input,c,d,SourceHeightPointsV2.Point0217.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0218.source_outputs
   exact ⟨SourceHeightPointsV2.Point0218.input,c,d,SourceHeightPointsV2.Point0218.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0219.source_outputs
   exact ⟨SourceHeightPointsV2.Point0219.input,c,d,SourceHeightPointsV2.Point0219.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0220.source_outputs
   exact ⟨SourceHeightPointsV2.Point0220.input,c,d,SourceHeightPointsV2.Point0220.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0221.source_outputs
   exact ⟨SourceHeightPointsV2.Point0221.input,c,d,SourceHeightPointsV2.Point0221.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0222.source_outputs
   exact ⟨SourceHeightPointsV2.Point0222.input,c,d,SourceHeightPointsV2.Point0222.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0223.source_outputs
   exact ⟨SourceHeightPointsV2.Point0223.input,c,d,SourceHeightPointsV2.Point0223.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block06
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block06.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
