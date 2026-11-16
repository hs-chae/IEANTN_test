import SourceHeightPointsV2.Point0160
import SourceHeightPointsV2.Point0161
import SourceHeightPointsV2.Point0162
import SourceHeightPointsV2.Point0163
import SourceHeightPointsV2.Point0164
import SourceHeightPointsV2.Point0165
import SourceHeightPointsV2.Point0166
import SourceHeightPointsV2.Point0167
import SourceHeightPointsV2.Point0168
import SourceHeightPointsV2.Point0169
import SourceHeightPointsV2.Point0170
import SourceHeightPointsV2.Point0171
import SourceHeightPointsV2.Point0172
import SourceHeightPointsV2.Point0173
import SourceHeightPointsV2.Point0174
import SourceHeightPointsV2.Point0175
import SourceHeightPointsV2.Point0176
import SourceHeightPointsV2.Point0177
import SourceHeightPointsV2.Point0178
import SourceHeightPointsV2.Point0179
import SourceHeightPointsV2.Point0180
import SourceHeightPointsV2.Point0181
import SourceHeightPointsV2.Point0182
import SourceHeightPointsV2.Point0183
import SourceHeightPointsV2.Point0184
import SourceHeightPointsV2.Point0185
import SourceHeightPointsV2.Point0186
import SourceHeightPointsV2.Point0187
import SourceHeightPointsV2.Point0188
import SourceHeightPointsV2.Point0189
import SourceHeightPointsV2.Point0190
import SourceHeightPointsV2.Point0191
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block05
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 160 ≤ i) (upper : i < 192) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0160.source_outputs
   exact ⟨SourceHeightPointsV2.Point0160.input,c,d,SourceHeightPointsV2.Point0160.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0161.source_outputs
   exact ⟨SourceHeightPointsV2.Point0161.input,c,d,SourceHeightPointsV2.Point0161.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0162.source_outputs
   exact ⟨SourceHeightPointsV2.Point0162.input,c,d,SourceHeightPointsV2.Point0162.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0163.source_outputs
   exact ⟨SourceHeightPointsV2.Point0163.input,c,d,SourceHeightPointsV2.Point0163.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0164.source_outputs
   exact ⟨SourceHeightPointsV2.Point0164.input,c,d,SourceHeightPointsV2.Point0164.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0165.source_outputs
   exact ⟨SourceHeightPointsV2.Point0165.input,c,d,SourceHeightPointsV2.Point0165.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0166.source_outputs
   exact ⟨SourceHeightPointsV2.Point0166.input,c,d,SourceHeightPointsV2.Point0166.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0167.source_outputs
   exact ⟨SourceHeightPointsV2.Point0167.input,c,d,SourceHeightPointsV2.Point0167.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0168.source_outputs
   exact ⟨SourceHeightPointsV2.Point0168.input,c,d,SourceHeightPointsV2.Point0168.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0169.source_outputs
   exact ⟨SourceHeightPointsV2.Point0169.input,c,d,SourceHeightPointsV2.Point0169.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0170.source_outputs
   exact ⟨SourceHeightPointsV2.Point0170.input,c,d,SourceHeightPointsV2.Point0170.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0171.source_outputs
   exact ⟨SourceHeightPointsV2.Point0171.input,c,d,SourceHeightPointsV2.Point0171.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0172.source_outputs
   exact ⟨SourceHeightPointsV2.Point0172.input,c,d,SourceHeightPointsV2.Point0172.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0173.source_outputs
   exact ⟨SourceHeightPointsV2.Point0173.input,c,d,SourceHeightPointsV2.Point0173.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0174.source_outputs
   exact ⟨SourceHeightPointsV2.Point0174.input,c,d,SourceHeightPointsV2.Point0174.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0175.source_outputs
   exact ⟨SourceHeightPointsV2.Point0175.input,c,d,SourceHeightPointsV2.Point0175.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0176.source_outputs
   exact ⟨SourceHeightPointsV2.Point0176.input,c,d,SourceHeightPointsV2.Point0176.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0177.source_outputs
   exact ⟨SourceHeightPointsV2.Point0177.input,c,d,SourceHeightPointsV2.Point0177.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0178.source_outputs
   exact ⟨SourceHeightPointsV2.Point0178.input,c,d,SourceHeightPointsV2.Point0178.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0179.source_outputs
   exact ⟨SourceHeightPointsV2.Point0179.input,c,d,SourceHeightPointsV2.Point0179.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0180.source_outputs
   exact ⟨SourceHeightPointsV2.Point0180.input,c,d,SourceHeightPointsV2.Point0180.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0181.source_outputs
   exact ⟨SourceHeightPointsV2.Point0181.input,c,d,SourceHeightPointsV2.Point0181.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0182.source_outputs
   exact ⟨SourceHeightPointsV2.Point0182.input,c,d,SourceHeightPointsV2.Point0182.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0183.source_outputs
   exact ⟨SourceHeightPointsV2.Point0183.input,c,d,SourceHeightPointsV2.Point0183.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0184.source_outputs
   exact ⟨SourceHeightPointsV2.Point0184.input,c,d,SourceHeightPointsV2.Point0184.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0185.source_outputs
   exact ⟨SourceHeightPointsV2.Point0185.input,c,d,SourceHeightPointsV2.Point0185.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0186.source_outputs
   exact ⟨SourceHeightPointsV2.Point0186.input,c,d,SourceHeightPointsV2.Point0186.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0187.source_outputs
   exact ⟨SourceHeightPointsV2.Point0187.input,c,d,SourceHeightPointsV2.Point0187.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0188.source_outputs
   exact ⟨SourceHeightPointsV2.Point0188.input,c,d,SourceHeightPointsV2.Point0188.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0189.source_outputs
   exact ⟨SourceHeightPointsV2.Point0189.input,c,d,SourceHeightPointsV2.Point0189.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0190.source_outputs
   exact ⟨SourceHeightPointsV2.Point0190.input,c,d,SourceHeightPointsV2.Point0190.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0191.source_outputs
   exact ⟨SourceHeightPointsV2.Point0191.input,c,d,SourceHeightPointsV2.Point0191.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block05
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block05.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
