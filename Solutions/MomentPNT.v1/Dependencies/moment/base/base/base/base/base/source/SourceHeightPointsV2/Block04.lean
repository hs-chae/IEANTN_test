import SourceHeightPointsV2.Point0128
import SourceHeightPointsV2.Point0129
import SourceHeightPointsV2.Point0130
import SourceHeightPointsV2.Point0131
import SourceHeightPointsV2.Point0132
import SourceHeightPointsV2.Point0133
import SourceHeightPointsV2.Point0134
import SourceHeightPointsV2.Point0135
import SourceHeightPointsV2.Point0136
import SourceHeightPointsV2.Point0137
import SourceHeightPointsV2.Point0138
import SourceHeightPointsV2.Point0139
import SourceHeightPointsV2.Point0140
import SourceHeightPointsV2.Point0141
import SourceHeightPointsV2.Point0142
import SourceHeightPointsV2.Point0143
import SourceHeightPointsV2.Point0144
import SourceHeightPointsV2.Point0145
import SourceHeightPointsV2.Point0146
import SourceHeightPointsV2.Point0147
import SourceHeightPointsV2.Point0148
import SourceHeightPointsV2.Point0149
import SourceHeightPointsV2.Point0150
import SourceHeightPointsV2.Point0151
import SourceHeightPointsV2.Point0152
import SourceHeightPointsV2.Point0153
import SourceHeightPointsV2.Point0154
import SourceHeightPointsV2.Point0155
import SourceHeightPointsV2.Point0156
import SourceHeightPointsV2.Point0157
import SourceHeightPointsV2.Point0158
import SourceHeightPointsV2.Point0159
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block04
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 128 ≤ i) (upper : i < 160) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0128.source_outputs
   exact ⟨SourceHeightPointsV2.Point0128.input,c,d,SourceHeightPointsV2.Point0128.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0129.source_outputs
   exact ⟨SourceHeightPointsV2.Point0129.input,c,d,SourceHeightPointsV2.Point0129.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0130.source_outputs
   exact ⟨SourceHeightPointsV2.Point0130.input,c,d,SourceHeightPointsV2.Point0130.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0131.source_outputs
   exact ⟨SourceHeightPointsV2.Point0131.input,c,d,SourceHeightPointsV2.Point0131.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0132.source_outputs
   exact ⟨SourceHeightPointsV2.Point0132.input,c,d,SourceHeightPointsV2.Point0132.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0133.source_outputs
   exact ⟨SourceHeightPointsV2.Point0133.input,c,d,SourceHeightPointsV2.Point0133.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0134.source_outputs
   exact ⟨SourceHeightPointsV2.Point0134.input,c,d,SourceHeightPointsV2.Point0134.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0135.source_outputs
   exact ⟨SourceHeightPointsV2.Point0135.input,c,d,SourceHeightPointsV2.Point0135.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0136.source_outputs
   exact ⟨SourceHeightPointsV2.Point0136.input,c,d,SourceHeightPointsV2.Point0136.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0137.source_outputs
   exact ⟨SourceHeightPointsV2.Point0137.input,c,d,SourceHeightPointsV2.Point0137.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0138.source_outputs
   exact ⟨SourceHeightPointsV2.Point0138.input,c,d,SourceHeightPointsV2.Point0138.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0139.source_outputs
   exact ⟨SourceHeightPointsV2.Point0139.input,c,d,SourceHeightPointsV2.Point0139.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0140.source_outputs
   exact ⟨SourceHeightPointsV2.Point0140.input,c,d,SourceHeightPointsV2.Point0140.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0141.source_outputs
   exact ⟨SourceHeightPointsV2.Point0141.input,c,d,SourceHeightPointsV2.Point0141.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0142.source_outputs
   exact ⟨SourceHeightPointsV2.Point0142.input,c,d,SourceHeightPointsV2.Point0142.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0143.source_outputs
   exact ⟨SourceHeightPointsV2.Point0143.input,c,d,SourceHeightPointsV2.Point0143.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0144.source_outputs
   exact ⟨SourceHeightPointsV2.Point0144.input,c,d,SourceHeightPointsV2.Point0144.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0145.source_outputs
   exact ⟨SourceHeightPointsV2.Point0145.input,c,d,SourceHeightPointsV2.Point0145.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0146.source_outputs
   exact ⟨SourceHeightPointsV2.Point0146.input,c,d,SourceHeightPointsV2.Point0146.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0147.source_outputs
   exact ⟨SourceHeightPointsV2.Point0147.input,c,d,SourceHeightPointsV2.Point0147.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0148.source_outputs
   exact ⟨SourceHeightPointsV2.Point0148.input,c,d,SourceHeightPointsV2.Point0148.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0149.source_outputs
   exact ⟨SourceHeightPointsV2.Point0149.input,c,d,SourceHeightPointsV2.Point0149.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0150.source_outputs
   exact ⟨SourceHeightPointsV2.Point0150.input,c,d,SourceHeightPointsV2.Point0150.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0151.source_outputs
   exact ⟨SourceHeightPointsV2.Point0151.input,c,d,SourceHeightPointsV2.Point0151.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0152.source_outputs
   exact ⟨SourceHeightPointsV2.Point0152.input,c,d,SourceHeightPointsV2.Point0152.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0153.source_outputs
   exact ⟨SourceHeightPointsV2.Point0153.input,c,d,SourceHeightPointsV2.Point0153.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0154.source_outputs
   exact ⟨SourceHeightPointsV2.Point0154.input,c,d,SourceHeightPointsV2.Point0154.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0155.source_outputs
   exact ⟨SourceHeightPointsV2.Point0155.input,c,d,SourceHeightPointsV2.Point0155.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0156.source_outputs
   exact ⟨SourceHeightPointsV2.Point0156.input,c,d,SourceHeightPointsV2.Point0156.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0157.source_outputs
   exact ⟨SourceHeightPointsV2.Point0157.input,c,d,SourceHeightPointsV2.Point0157.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0158.source_outputs
   exact ⟨SourceHeightPointsV2.Point0158.input,c,d,SourceHeightPointsV2.Point0158.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0159.source_outputs
   exact ⟨SourceHeightPointsV2.Point0159.input,c,d,SourceHeightPointsV2.Point0159.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block04
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block04.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
