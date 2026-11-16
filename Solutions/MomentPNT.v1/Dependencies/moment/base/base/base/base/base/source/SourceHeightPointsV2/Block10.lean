import SourceHeightPointsV2.Point0320
import SourceHeightPointsV2.Point0321
import SourceHeightPointsV2.Point0322
import SourceHeightPointsV2.Point0323
import SourceHeightPointsV2.Point0324
import SourceHeightPointsV2.Point0325
import SourceHeightPointsV2.Point0326
import SourceHeightPointsV2.Point0327
import SourceHeightPointsV2.Point0328
import SourceHeightPointsV2.Point0329
import SourceHeightPointsV2.Point0330
import SourceHeightPointsV2.Point0331
import SourceHeightPointsV2.Point0332
import SourceHeightPointsV2.Point0333
import SourceHeightPointsV2.Point0334
import SourceHeightPointsV2.Point0335
import SourceHeightPointsV2.Point0336
import SourceHeightPointsV2.Point0337
import SourceHeightPointsV2.Point0338
import SourceHeightPointsV2.Point0339
import SourceHeightPointsV2.Point0340
import SourceHeightPointsV2.Point0341
import SourceHeightPointsV2.Point0342
import SourceHeightPointsV2.Point0343
import SourceHeightPointsV2.Point0344
import SourceHeightPointsV2.Point0345
import SourceHeightPointsV2.Point0346
import SourceHeightPointsV2.Point0347
import SourceHeightPointsV2.Point0348
import SourceHeightPointsV2.Point0349
import SourceHeightPointsV2.Point0350
import SourceHeightPointsV2.Point0351
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block10
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 320 ≤ i) (upper : i < 352) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0320.source_outputs
   exact ⟨SourceHeightPointsV2.Point0320.input,c,d,SourceHeightPointsV2.Point0320.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0321.source_outputs
   exact ⟨SourceHeightPointsV2.Point0321.input,c,d,SourceHeightPointsV2.Point0321.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0322.source_outputs
   exact ⟨SourceHeightPointsV2.Point0322.input,c,d,SourceHeightPointsV2.Point0322.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0323.source_outputs
   exact ⟨SourceHeightPointsV2.Point0323.input,c,d,SourceHeightPointsV2.Point0323.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0324.source_outputs
   exact ⟨SourceHeightPointsV2.Point0324.input,c,d,SourceHeightPointsV2.Point0324.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0325.source_outputs
   exact ⟨SourceHeightPointsV2.Point0325.input,c,d,SourceHeightPointsV2.Point0325.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0326.source_outputs
   exact ⟨SourceHeightPointsV2.Point0326.input,c,d,SourceHeightPointsV2.Point0326.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0327.source_outputs
   exact ⟨SourceHeightPointsV2.Point0327.input,c,d,SourceHeightPointsV2.Point0327.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0328.source_outputs
   exact ⟨SourceHeightPointsV2.Point0328.input,c,d,SourceHeightPointsV2.Point0328.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0329.source_outputs
   exact ⟨SourceHeightPointsV2.Point0329.input,c,d,SourceHeightPointsV2.Point0329.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0330.source_outputs
   exact ⟨SourceHeightPointsV2.Point0330.input,c,d,SourceHeightPointsV2.Point0330.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0331.source_outputs
   exact ⟨SourceHeightPointsV2.Point0331.input,c,d,SourceHeightPointsV2.Point0331.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0332.source_outputs
   exact ⟨SourceHeightPointsV2.Point0332.input,c,d,SourceHeightPointsV2.Point0332.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0333.source_outputs
   exact ⟨SourceHeightPointsV2.Point0333.input,c,d,SourceHeightPointsV2.Point0333.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0334.source_outputs
   exact ⟨SourceHeightPointsV2.Point0334.input,c,d,SourceHeightPointsV2.Point0334.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0335.source_outputs
   exact ⟨SourceHeightPointsV2.Point0335.input,c,d,SourceHeightPointsV2.Point0335.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0336.source_outputs
   exact ⟨SourceHeightPointsV2.Point0336.input,c,d,SourceHeightPointsV2.Point0336.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0337.source_outputs
   exact ⟨SourceHeightPointsV2.Point0337.input,c,d,SourceHeightPointsV2.Point0337.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0338.source_outputs
   exact ⟨SourceHeightPointsV2.Point0338.input,c,d,SourceHeightPointsV2.Point0338.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0339.source_outputs
   exact ⟨SourceHeightPointsV2.Point0339.input,c,d,SourceHeightPointsV2.Point0339.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0340.source_outputs
   exact ⟨SourceHeightPointsV2.Point0340.input,c,d,SourceHeightPointsV2.Point0340.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0341.source_outputs
   exact ⟨SourceHeightPointsV2.Point0341.input,c,d,SourceHeightPointsV2.Point0341.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0342.source_outputs
   exact ⟨SourceHeightPointsV2.Point0342.input,c,d,SourceHeightPointsV2.Point0342.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0343.source_outputs
   exact ⟨SourceHeightPointsV2.Point0343.input,c,d,SourceHeightPointsV2.Point0343.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0344.source_outputs
   exact ⟨SourceHeightPointsV2.Point0344.input,c,d,SourceHeightPointsV2.Point0344.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0345.source_outputs
   exact ⟨SourceHeightPointsV2.Point0345.input,c,d,SourceHeightPointsV2.Point0345.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0346.source_outputs
   exact ⟨SourceHeightPointsV2.Point0346.input,c,d,SourceHeightPointsV2.Point0346.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0347.source_outputs
   exact ⟨SourceHeightPointsV2.Point0347.input,c,d,SourceHeightPointsV2.Point0347.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0348.source_outputs
   exact ⟨SourceHeightPointsV2.Point0348.input,c,d,SourceHeightPointsV2.Point0348.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0349.source_outputs
   exact ⟨SourceHeightPointsV2.Point0349.input,c,d,SourceHeightPointsV2.Point0349.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0350.source_outputs
   exact ⟨SourceHeightPointsV2.Point0350.input,c,d,SourceHeightPointsV2.Point0350.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0351.source_outputs
   exact ⟨SourceHeightPointsV2.Point0351.input,c,d,SourceHeightPointsV2.Point0351.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block10
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block10.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
