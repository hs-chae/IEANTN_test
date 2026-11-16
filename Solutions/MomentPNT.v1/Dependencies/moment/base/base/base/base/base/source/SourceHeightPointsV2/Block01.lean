import SourceHeightPointsV2.Point0032
import SourceHeightPointsV2.Point0033
import SourceHeightPointsV2.Point0034
import SourceHeightPointsV2.Point0035
import SourceHeightPointsV2.Point0036
import SourceHeightPointsV2.Point0037
import SourceHeightPointsV2.Point0038
import SourceHeightPointsV2.Point0039
import SourceHeightPointsV2.Point0040
import SourceHeightPointsV2.Point0041
import SourceHeightPointsV2.Point0042
import SourceHeightPointsV2.Point0043
import SourceHeightPointsV2.Point0044
import SourceHeightPointsV2.Point0045
import SourceHeightPointsV2.Point0046
import SourceHeightPointsV2.Point0047
import SourceHeightPointsV2.Point0048
import SourceHeightPointsV2.Point0049
import SourceHeightPointsV2.Point0050
import SourceHeightPointsV2.Point0051
import SourceHeightPointsV2.Point0052
import SourceHeightPointsV2.Point0053
import SourceHeightPointsV2.Point0054
import SourceHeightPointsV2.Point0055
import SourceHeightPointsV2.Point0056
import SourceHeightPointsV2.Point0057
import SourceHeightPointsV2.Point0058
import SourceHeightPointsV2.Point0059
import SourceHeightPointsV2.Point0060
import SourceHeightPointsV2.Point0061
import SourceHeightPointsV2.Point0062
import SourceHeightPointsV2.Point0063
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block01
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 32 ≤ i) (upper : i < 64) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0032.source_outputs
   exact ⟨SourceHeightPointsV2.Point0032.input,c,d,SourceHeightPointsV2.Point0032.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0033.source_outputs
   exact ⟨SourceHeightPointsV2.Point0033.input,c,d,SourceHeightPointsV2.Point0033.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0034.source_outputs
   exact ⟨SourceHeightPointsV2.Point0034.input,c,d,SourceHeightPointsV2.Point0034.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0035.source_outputs
   exact ⟨SourceHeightPointsV2.Point0035.input,c,d,SourceHeightPointsV2.Point0035.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0036.source_outputs
   exact ⟨SourceHeightPointsV2.Point0036.input,c,d,SourceHeightPointsV2.Point0036.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0037.source_outputs
   exact ⟨SourceHeightPointsV2.Point0037.input,c,d,SourceHeightPointsV2.Point0037.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0038.source_outputs
   exact ⟨SourceHeightPointsV2.Point0038.input,c,d,SourceHeightPointsV2.Point0038.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0039.source_outputs
   exact ⟨SourceHeightPointsV2.Point0039.input,c,d,SourceHeightPointsV2.Point0039.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0040.source_outputs
   exact ⟨SourceHeightPointsV2.Point0040.input,c,d,SourceHeightPointsV2.Point0040.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0041.source_outputs
   exact ⟨SourceHeightPointsV2.Point0041.input,c,d,SourceHeightPointsV2.Point0041.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0042.source_outputs
   exact ⟨SourceHeightPointsV2.Point0042.input,c,d,SourceHeightPointsV2.Point0042.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0043.source_outputs
   exact ⟨SourceHeightPointsV2.Point0043.input,c,d,SourceHeightPointsV2.Point0043.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0044.source_outputs
   exact ⟨SourceHeightPointsV2.Point0044.input,c,d,SourceHeightPointsV2.Point0044.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0045.source_outputs
   exact ⟨SourceHeightPointsV2.Point0045.input,c,d,SourceHeightPointsV2.Point0045.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0046.source_outputs
   exact ⟨SourceHeightPointsV2.Point0046.input,c,d,SourceHeightPointsV2.Point0046.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0047.source_outputs
   exact ⟨SourceHeightPointsV2.Point0047.input,c,d,SourceHeightPointsV2.Point0047.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0048.source_outputs
   exact ⟨SourceHeightPointsV2.Point0048.input,c,d,SourceHeightPointsV2.Point0048.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0049.source_outputs
   exact ⟨SourceHeightPointsV2.Point0049.input,c,d,SourceHeightPointsV2.Point0049.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0050.source_outputs
   exact ⟨SourceHeightPointsV2.Point0050.input,c,d,SourceHeightPointsV2.Point0050.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0051.source_outputs
   exact ⟨SourceHeightPointsV2.Point0051.input,c,d,SourceHeightPointsV2.Point0051.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0052.source_outputs
   exact ⟨SourceHeightPointsV2.Point0052.input,c,d,SourceHeightPointsV2.Point0052.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0053.source_outputs
   exact ⟨SourceHeightPointsV2.Point0053.input,c,d,SourceHeightPointsV2.Point0053.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0054.source_outputs
   exact ⟨SourceHeightPointsV2.Point0054.input,c,d,SourceHeightPointsV2.Point0054.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0055.source_outputs
   exact ⟨SourceHeightPointsV2.Point0055.input,c,d,SourceHeightPointsV2.Point0055.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0056.source_outputs
   exact ⟨SourceHeightPointsV2.Point0056.input,c,d,SourceHeightPointsV2.Point0056.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0057.source_outputs
   exact ⟨SourceHeightPointsV2.Point0057.input,c,d,SourceHeightPointsV2.Point0057.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0058.source_outputs
   exact ⟨SourceHeightPointsV2.Point0058.input,c,d,SourceHeightPointsV2.Point0058.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0059.source_outputs
   exact ⟨SourceHeightPointsV2.Point0059.input,c,d,SourceHeightPointsV2.Point0059.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0060.source_outputs
   exact ⟨SourceHeightPointsV2.Point0060.input,c,d,SourceHeightPointsV2.Point0060.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0061.source_outputs
   exact ⟨SourceHeightPointsV2.Point0061.input,c,d,SourceHeightPointsV2.Point0061.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0062.source_outputs
   exact ⟨SourceHeightPointsV2.Point0062.input,c,d,SourceHeightPointsV2.Point0062.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0063.source_outputs
   exact ⟨SourceHeightPointsV2.Point0063.input,c,d,SourceHeightPointsV2.Point0063.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block01
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block01.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
