import SourceHeightPointsV2.Point0672
import SourceHeightPointsV2.Point0673
import SourceHeightPointsV2.Point0674
import SourceHeightPointsV2.Point0675
import SourceHeightPointsV2.Point0676
import SourceHeightPointsV2.Point0677
import SourceHeightPointsV2.Point0678
import SourceHeightPointsV2.Point0679
import SourceHeightPointsV2.Point0680
import SourceHeightPointsV2.Point0681
import SourceHeightPointsV2.Point0682
import SourceHeightPointsV2.Point0683
import SourceHeightPointsV2.Point0684
import SourceHeightPointsV2.Point0685
import SourceHeightPointsV2.Point0686
import SourceHeightPointsV2.Point0687
import SourceHeightPointsV2.Point0688
import SourceHeightPointsV2.Point0689
import SourceHeightPointsV2.Point0690
import SourceHeightPointsV2.Point0691
import SourceHeightPointsV2.Point0692
import SourceHeightPointsV2.Point0693
import SourceHeightPointsV2.Point0694
import SourceHeightPointsV2.Point0695
import SourceHeightPointsV2.Point0696
import SourceHeightPointsV2.Point0697
import SourceHeightPointsV2.Point0698
import SourceHeightPointsV2.Point0699
import SourceHeightPointsV2.Point0700
import SourceHeightPointsV2.Point0701
import SourceHeightPointsV2.Point0702
import SourceHeightPointsV2.Point0703
import Mathlib.Tactic.IntervalCases
namespace SourceHeightPointsV2.Block21
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (i : ℕ) (lower : 672 ≤ i) (upper : i < 704) :
 ∃ input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs (SynergyHeightC.InitCacheProposal.postState NatArena.empty) input c d := by
 interval_cases i
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0672.source_outputs
   exact ⟨SourceHeightPointsV2.Point0672.input,c,d,SourceHeightPointsV2.Point0672.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0673.source_outputs
   exact ⟨SourceHeightPointsV2.Point0673.input,c,d,SourceHeightPointsV2.Point0673.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0674.source_outputs
   exact ⟨SourceHeightPointsV2.Point0674.input,c,d,SourceHeightPointsV2.Point0674.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0675.source_outputs
   exact ⟨SourceHeightPointsV2.Point0675.input,c,d,SourceHeightPointsV2.Point0675.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0676.source_outputs
   exact ⟨SourceHeightPointsV2.Point0676.input,c,d,SourceHeightPointsV2.Point0676.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0677.source_outputs
   exact ⟨SourceHeightPointsV2.Point0677.input,c,d,SourceHeightPointsV2.Point0677.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0678.source_outputs
   exact ⟨SourceHeightPointsV2.Point0678.input,c,d,SourceHeightPointsV2.Point0678.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0679.source_outputs
   exact ⟨SourceHeightPointsV2.Point0679.input,c,d,SourceHeightPointsV2.Point0679.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0680.source_outputs
   exact ⟨SourceHeightPointsV2.Point0680.input,c,d,SourceHeightPointsV2.Point0680.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0681.source_outputs
   exact ⟨SourceHeightPointsV2.Point0681.input,c,d,SourceHeightPointsV2.Point0681.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0682.source_outputs
   exact ⟨SourceHeightPointsV2.Point0682.input,c,d,SourceHeightPointsV2.Point0682.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0683.source_outputs
   exact ⟨SourceHeightPointsV2.Point0683.input,c,d,SourceHeightPointsV2.Point0683.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0684.source_outputs
   exact ⟨SourceHeightPointsV2.Point0684.input,c,d,SourceHeightPointsV2.Point0684.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0685.source_outputs
   exact ⟨SourceHeightPointsV2.Point0685.input,c,d,SourceHeightPointsV2.Point0685.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0686.source_outputs
   exact ⟨SourceHeightPointsV2.Point0686.input,c,d,SourceHeightPointsV2.Point0686.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0687.source_outputs
   exact ⟨SourceHeightPointsV2.Point0687.input,c,d,SourceHeightPointsV2.Point0687.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0688.source_outputs
   exact ⟨SourceHeightPointsV2.Point0688.input,c,d,SourceHeightPointsV2.Point0688.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0689.source_outputs
   exact ⟨SourceHeightPointsV2.Point0689.input,c,d,SourceHeightPointsV2.Point0689.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0690.source_outputs
   exact ⟨SourceHeightPointsV2.Point0690.input,c,d,SourceHeightPointsV2.Point0690.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0691.source_outputs
   exact ⟨SourceHeightPointsV2.Point0691.input,c,d,SourceHeightPointsV2.Point0691.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0692.source_outputs
   exact ⟨SourceHeightPointsV2.Point0692.input,c,d,SourceHeightPointsV2.Point0692.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0693.source_outputs
   exact ⟨SourceHeightPointsV2.Point0693.input,c,d,SourceHeightPointsV2.Point0693.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0694.source_outputs
   exact ⟨SourceHeightPointsV2.Point0694.input,c,d,SourceHeightPointsV2.Point0694.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0695.source_outputs
   exact ⟨SourceHeightPointsV2.Point0695.input,c,d,SourceHeightPointsV2.Point0695.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0696.source_outputs
   exact ⟨SourceHeightPointsV2.Point0696.input,c,d,SourceHeightPointsV2.Point0696.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0697.source_outputs
   exact ⟨SourceHeightPointsV2.Point0697.input,c,d,SourceHeightPointsV2.Point0697.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0698.source_outputs
   exact ⟨SourceHeightPointsV2.Point0698.input,c,d,SourceHeightPointsV2.Point0698.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0699.source_outputs
   exact ⟨SourceHeightPointsV2.Point0699.input,c,d,SourceHeightPointsV2.Point0699.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0700.source_outputs
   exact ⟨SourceHeightPointsV2.Point0700.input,c,d,SourceHeightPointsV2.Point0700.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0701.source_outputs
   exact ⟨SourceHeightPointsV2.Point0701.input,c,d,SourceHeightPointsV2.Point0701.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0702.source_outputs
   exact ⟨SourceHeightPointsV2.Point0702.input,c,d,SourceHeightPointsV2.Point0702.input_defined,hm,hs⟩
 · obtain ⟨c,d,hm,hs⟩ := SourceHeightPointsV2.Point0703.source_outputs
   exact ⟨SourceHeightPointsV2.Point0703.input,c,d,SourceHeightPointsV2.Point0703.input_defined,hm,hs⟩
end SourceHeightPointsV2.Block21
open Lean Elab
run_elab do
 let n := `SourceHeightPointsV2.Block21.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
