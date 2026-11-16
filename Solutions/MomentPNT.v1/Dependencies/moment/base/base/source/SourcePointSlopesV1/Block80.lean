/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0640
import SourceMainFramesV1.Point0641
import SourceMainFramesV1.Point0642
import SourceMainFramesV1.Point0643
import SourceMainFramesV1.Point0644
import SourceMainFramesV1.Point0645
import SourceMainFramesV1.Point0646
import SourceMainFramesV1.Point0647
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block80
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0640.outputs.2.hi,
 SourceMainFramesV1.Point0641.outputs.2.hi,
 SourceMainFramesV1.Point0642.outputs.2.hi,
 SourceMainFramesV1.Point0643.outputs.2.hi,
 SourceMainFramesV1.Point0644.outputs.2.hi,
 SourceMainFramesV1.Point0645.outputs.2.hi,
 SourceMainFramesV1.Point0646.outputs.2.hi,
 SourceMainFramesV1.Point0647.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 640 ≤ i) (high : i < 648)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=640) domain
     SourceMainFramesV1.Point0640.input_defined SourceMainFramesV1.Point0640.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0640.outputs.2.hi (by
         change SourceMainFramesV1.Point0640.outputs.2.hi ∈ [SourceMainFramesV1.Point0640.outputs.2.hi, SourceMainFramesV1.Point0641.outputs.2.hi, SourceMainFramesV1.Point0642.outputs.2.hi, SourceMainFramesV1.Point0643.outputs.2.hi, SourceMainFramesV1.Point0644.outputs.2.hi, SourceMainFramesV1.Point0645.outputs.2.hi, SourceMainFramesV1.Point0646.outputs.2.hi, SourceMainFramesV1.Point0647.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=641) domain
     SourceMainFramesV1.Point0641.input_defined SourceMainFramesV1.Point0641.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0641.outputs.2.hi (by
         change SourceMainFramesV1.Point0641.outputs.2.hi ∈ [SourceMainFramesV1.Point0640.outputs.2.hi, SourceMainFramesV1.Point0641.outputs.2.hi, SourceMainFramesV1.Point0642.outputs.2.hi, SourceMainFramesV1.Point0643.outputs.2.hi, SourceMainFramesV1.Point0644.outputs.2.hi, SourceMainFramesV1.Point0645.outputs.2.hi, SourceMainFramesV1.Point0646.outputs.2.hi, SourceMainFramesV1.Point0647.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=642) domain
     SourceMainFramesV1.Point0642.input_defined SourceMainFramesV1.Point0642.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0642.outputs.2.hi (by
         change SourceMainFramesV1.Point0642.outputs.2.hi ∈ [SourceMainFramesV1.Point0640.outputs.2.hi, SourceMainFramesV1.Point0641.outputs.2.hi, SourceMainFramesV1.Point0642.outputs.2.hi, SourceMainFramesV1.Point0643.outputs.2.hi, SourceMainFramesV1.Point0644.outputs.2.hi, SourceMainFramesV1.Point0645.outputs.2.hi, SourceMainFramesV1.Point0646.outputs.2.hi, SourceMainFramesV1.Point0647.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=643) domain
     SourceMainFramesV1.Point0643.input_defined SourceMainFramesV1.Point0643.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0643.outputs.2.hi (by
         change SourceMainFramesV1.Point0643.outputs.2.hi ∈ [SourceMainFramesV1.Point0640.outputs.2.hi, SourceMainFramesV1.Point0641.outputs.2.hi, SourceMainFramesV1.Point0642.outputs.2.hi, SourceMainFramesV1.Point0643.outputs.2.hi, SourceMainFramesV1.Point0644.outputs.2.hi, SourceMainFramesV1.Point0645.outputs.2.hi, SourceMainFramesV1.Point0646.outputs.2.hi, SourceMainFramesV1.Point0647.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=644) domain
     SourceMainFramesV1.Point0644.input_defined SourceMainFramesV1.Point0644.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0644.outputs.2.hi (by
         change SourceMainFramesV1.Point0644.outputs.2.hi ∈ [SourceMainFramesV1.Point0640.outputs.2.hi, SourceMainFramesV1.Point0641.outputs.2.hi, SourceMainFramesV1.Point0642.outputs.2.hi, SourceMainFramesV1.Point0643.outputs.2.hi, SourceMainFramesV1.Point0644.outputs.2.hi, SourceMainFramesV1.Point0645.outputs.2.hi, SourceMainFramesV1.Point0646.outputs.2.hi, SourceMainFramesV1.Point0647.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=645) domain
     SourceMainFramesV1.Point0645.input_defined SourceMainFramesV1.Point0645.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0645.outputs.2.hi (by
         change SourceMainFramesV1.Point0645.outputs.2.hi ∈ [SourceMainFramesV1.Point0640.outputs.2.hi, SourceMainFramesV1.Point0641.outputs.2.hi, SourceMainFramesV1.Point0642.outputs.2.hi, SourceMainFramesV1.Point0643.outputs.2.hi, SourceMainFramesV1.Point0644.outputs.2.hi, SourceMainFramesV1.Point0645.outputs.2.hi, SourceMainFramesV1.Point0646.outputs.2.hi, SourceMainFramesV1.Point0647.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=646) domain
     SourceMainFramesV1.Point0646.input_defined SourceMainFramesV1.Point0646.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0646.outputs.2.hi (by
         change SourceMainFramesV1.Point0646.outputs.2.hi ∈ [SourceMainFramesV1.Point0640.outputs.2.hi, SourceMainFramesV1.Point0641.outputs.2.hi, SourceMainFramesV1.Point0642.outputs.2.hi, SourceMainFramesV1.Point0643.outputs.2.hi, SourceMainFramesV1.Point0644.outputs.2.hi, SourceMainFramesV1.Point0645.outputs.2.hi, SourceMainFramesV1.Point0646.outputs.2.hi, SourceMainFramesV1.Point0647.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=647) domain
     SourceMainFramesV1.Point0647.input_defined SourceMainFramesV1.Point0647.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0647.outputs.2.hi (by
         change SourceMainFramesV1.Point0647.outputs.2.hi ∈ [SourceMainFramesV1.Point0640.outputs.2.hi, SourceMainFramesV1.Point0641.outputs.2.hi, SourceMainFramesV1.Point0642.outputs.2.hi, SourceMainFramesV1.Point0643.outputs.2.hi, SourceMainFramesV1.Point0644.outputs.2.hi, SourceMainFramesV1.Point0645.outputs.2.hi, SourceMainFramesV1.Point0646.outputs.2.hi, SourceMainFramesV1.Point0647.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block80
