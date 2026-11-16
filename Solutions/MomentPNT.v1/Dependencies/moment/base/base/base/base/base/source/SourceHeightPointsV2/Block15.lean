import SourceHeightPointsV2.Point0480
import SourceHeightPointsV2.Point0481
import SourceHeightPointsV2.Point0482
import SourceHeightPointsV2.Point0483
import SourceHeightPointsV2.Point0484
import SourceHeightPointsV2.Point0485
import SourceHeightPointsV2.Point0486
import SourceHeightPointsV2.Point0487
import SourceHeightPointsV2.Point0488
import SourceHeightPointsV2.Point0489
import SourceHeightPointsV2.Point0490
import SourceHeightPointsV2.Point0491
import SourceHeightPointsV2.Point0492
import SourceHeightPointsV2.Point0493
import SourceHeightPointsV2.Point0494
import SourceHeightPointsV2.Point0495
import SourceHeightPointsV2.Point0496
import SourceHeightPointsV2.Point0497
import SourceHeightPointsV2.Point0498
import SourceHeightPointsV2.Point0499
import SourceHeightPointsV2.Point0500
import SourceHeightPointsV2.Point0501
import SourceHeightPointsV2.Point0502
import SourceHeightPointsV2.Point0503
import SourceHeightPointsV2.Point0504
import SourceHeightPointsV2.Point0505
import SourceHeightPointsV2.Point0506
import SourceHeightPointsV2.Point0507
import SourceHeightPointsV2.Point0508
import SourceHeightPointsV2.Point0509
import SourceHeightPointsV2.Point0510
import SourceHeightPointsV2.Point0511
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block15
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 480 ≤ i) (upper : i < 512) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0480.source_outputs
   exact ⟨SourceHeightPointsV2.Point0480.input,c,d,SourceHeightPointsV2.Point0480.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0481.source_outputs
   exact ⟨SourceHeightPointsV2.Point0481.input,c,d,SourceHeightPointsV2.Point0481.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0482.source_outputs
   exact ⟨SourceHeightPointsV2.Point0482.input,c,d,SourceHeightPointsV2.Point0482.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0483.source_outputs
   exact ⟨SourceHeightPointsV2.Point0483.input,c,d,SourceHeightPointsV2.Point0483.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0484.source_outputs
   exact ⟨SourceHeightPointsV2.Point0484.input,c,d,SourceHeightPointsV2.Point0484.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0485.source_outputs
   exact ⟨SourceHeightPointsV2.Point0485.input,c,d,SourceHeightPointsV2.Point0485.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0486.source_outputs
   exact ⟨SourceHeightPointsV2.Point0486.input,c,d,SourceHeightPointsV2.Point0486.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0487.source_outputs
   exact ⟨SourceHeightPointsV2.Point0487.input,c,d,SourceHeightPointsV2.Point0487.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0488.source_outputs
   exact ⟨SourceHeightPointsV2.Point0488.input,c,d,SourceHeightPointsV2.Point0488.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0489.source_outputs
   exact ⟨SourceHeightPointsV2.Point0489.input,c,d,SourceHeightPointsV2.Point0489.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0490.source_outputs
   exact ⟨SourceHeightPointsV2.Point0490.input,c,d,SourceHeightPointsV2.Point0490.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0491.source_outputs
   exact ⟨SourceHeightPointsV2.Point0491.input,c,d,SourceHeightPointsV2.Point0491.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0492.source_outputs
   exact ⟨SourceHeightPointsV2.Point0492.input,c,d,SourceHeightPointsV2.Point0492.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0493.source_outputs
   exact ⟨SourceHeightPointsV2.Point0493.input,c,d,SourceHeightPointsV2.Point0493.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0494.source_outputs
   exact ⟨SourceHeightPointsV2.Point0494.input,c,d,SourceHeightPointsV2.Point0494.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0495.source_outputs
   exact ⟨SourceHeightPointsV2.Point0495.input,c,d,SourceHeightPointsV2.Point0495.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0496.source_outputs
   exact ⟨SourceHeightPointsV2.Point0496.input,c,d,SourceHeightPointsV2.Point0496.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0497.source_outputs
   exact ⟨SourceHeightPointsV2.Point0497.input,c,d,SourceHeightPointsV2.Point0497.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0498.source_outputs
   exact ⟨SourceHeightPointsV2.Point0498.input,c,d,SourceHeightPointsV2.Point0498.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0499.source_outputs
   exact ⟨SourceHeightPointsV2.Point0499.input,c,d,SourceHeightPointsV2.Point0499.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0500.source_outputs
   exact ⟨SourceHeightPointsV2.Point0500.input,c,d,SourceHeightPointsV2.Point0500.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0501.source_outputs
   exact ⟨SourceHeightPointsV2.Point0501.input,c,d,SourceHeightPointsV2.Point0501.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0502.source_outputs
   exact ⟨SourceHeightPointsV2.Point0502.input,c,d,SourceHeightPointsV2.Point0502.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0503.source_outputs
   exact ⟨SourceHeightPointsV2.Point0503.input,c,d,SourceHeightPointsV2.Point0503.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0504.source_outputs
   exact ⟨SourceHeightPointsV2.Point0504.input,c,d,SourceHeightPointsV2.Point0504.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0505.source_outputs
   exact ⟨SourceHeightPointsV2.Point0505.input,c,d,SourceHeightPointsV2.Point0505.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0506.source_outputs
   exact ⟨SourceHeightPointsV2.Point0506.input,c,d,SourceHeightPointsV2.Point0506.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0507.source_outputs
   exact ⟨SourceHeightPointsV2.Point0507.input,c,d,SourceHeightPointsV2.Point0507.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0508.source_outputs
   exact ⟨SourceHeightPointsV2.Point0508.input,c,d,SourceHeightPointsV2.Point0508.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0509.source_outputs
   exact ⟨SourceHeightPointsV2.Point0509.input,c,d,SourceHeightPointsV2.Point0509.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0510.source_outputs
   exact ⟨SourceHeightPointsV2.Point0510.input,c,d,SourceHeightPointsV2.Point0510.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0511.source_outputs
   exact ⟨SourceHeightPointsV2.Point0511.input,c,d,SourceHeightPointsV2.Point0511.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block15
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block15.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
