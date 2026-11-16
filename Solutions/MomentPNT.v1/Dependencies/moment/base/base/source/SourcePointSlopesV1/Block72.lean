/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0576
import SourceMainFramesV1.Point0577
import SourceMainFramesV1.Point0578
import SourceMainFramesV1.Point0579
import SourceMainFramesV1.Point0580
import SourceMainFramesV1.Point0581
import SourceMainFramesV1.Point0582
import SourceMainFramesV1.Point0583
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block72
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0576.outputs.2.hi,
 SourceMainFramesV1.Point0577.outputs.2.hi,
 SourceMainFramesV1.Point0578.outputs.2.hi,
 SourceMainFramesV1.Point0579.outputs.2.hi,
 SourceMainFramesV1.Point0580.outputs.2.hi,
 SourceMainFramesV1.Point0581.outputs.2.hi,
 SourceMainFramesV1.Point0582.outputs.2.hi,
 SourceMainFramesV1.Point0583.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 576 ≤ i) (high : i < 584)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=576) domain
     SourceMainFramesV1.Point0576.input_defined SourceMainFramesV1.Point0576.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0576.outputs.2.hi (by
         change SourceMainFramesV1.Point0576.outputs.2.hi ∈ [SourceMainFramesV1.Point0576.outputs.2.hi, SourceMainFramesV1.Point0577.outputs.2.hi, SourceMainFramesV1.Point0578.outputs.2.hi, SourceMainFramesV1.Point0579.outputs.2.hi, SourceMainFramesV1.Point0580.outputs.2.hi, SourceMainFramesV1.Point0581.outputs.2.hi, SourceMainFramesV1.Point0582.outputs.2.hi, SourceMainFramesV1.Point0583.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=577) domain
     SourceMainFramesV1.Point0577.input_defined SourceMainFramesV1.Point0577.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0577.outputs.2.hi (by
         change SourceMainFramesV1.Point0577.outputs.2.hi ∈ [SourceMainFramesV1.Point0576.outputs.2.hi, SourceMainFramesV1.Point0577.outputs.2.hi, SourceMainFramesV1.Point0578.outputs.2.hi, SourceMainFramesV1.Point0579.outputs.2.hi, SourceMainFramesV1.Point0580.outputs.2.hi, SourceMainFramesV1.Point0581.outputs.2.hi, SourceMainFramesV1.Point0582.outputs.2.hi, SourceMainFramesV1.Point0583.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=578) domain
     SourceMainFramesV1.Point0578.input_defined SourceMainFramesV1.Point0578.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0578.outputs.2.hi (by
         change SourceMainFramesV1.Point0578.outputs.2.hi ∈ [SourceMainFramesV1.Point0576.outputs.2.hi, SourceMainFramesV1.Point0577.outputs.2.hi, SourceMainFramesV1.Point0578.outputs.2.hi, SourceMainFramesV1.Point0579.outputs.2.hi, SourceMainFramesV1.Point0580.outputs.2.hi, SourceMainFramesV1.Point0581.outputs.2.hi, SourceMainFramesV1.Point0582.outputs.2.hi, SourceMainFramesV1.Point0583.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=579) domain
     SourceMainFramesV1.Point0579.input_defined SourceMainFramesV1.Point0579.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0579.outputs.2.hi (by
         change SourceMainFramesV1.Point0579.outputs.2.hi ∈ [SourceMainFramesV1.Point0576.outputs.2.hi, SourceMainFramesV1.Point0577.outputs.2.hi, SourceMainFramesV1.Point0578.outputs.2.hi, SourceMainFramesV1.Point0579.outputs.2.hi, SourceMainFramesV1.Point0580.outputs.2.hi, SourceMainFramesV1.Point0581.outputs.2.hi, SourceMainFramesV1.Point0582.outputs.2.hi, SourceMainFramesV1.Point0583.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=580) domain
     SourceMainFramesV1.Point0580.input_defined SourceMainFramesV1.Point0580.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0580.outputs.2.hi (by
         change SourceMainFramesV1.Point0580.outputs.2.hi ∈ [SourceMainFramesV1.Point0576.outputs.2.hi, SourceMainFramesV1.Point0577.outputs.2.hi, SourceMainFramesV1.Point0578.outputs.2.hi, SourceMainFramesV1.Point0579.outputs.2.hi, SourceMainFramesV1.Point0580.outputs.2.hi, SourceMainFramesV1.Point0581.outputs.2.hi, SourceMainFramesV1.Point0582.outputs.2.hi, SourceMainFramesV1.Point0583.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=581) domain
     SourceMainFramesV1.Point0581.input_defined SourceMainFramesV1.Point0581.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0581.outputs.2.hi (by
         change SourceMainFramesV1.Point0581.outputs.2.hi ∈ [SourceMainFramesV1.Point0576.outputs.2.hi, SourceMainFramesV1.Point0577.outputs.2.hi, SourceMainFramesV1.Point0578.outputs.2.hi, SourceMainFramesV1.Point0579.outputs.2.hi, SourceMainFramesV1.Point0580.outputs.2.hi, SourceMainFramesV1.Point0581.outputs.2.hi, SourceMainFramesV1.Point0582.outputs.2.hi, SourceMainFramesV1.Point0583.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=582) domain
     SourceMainFramesV1.Point0582.input_defined SourceMainFramesV1.Point0582.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0582.outputs.2.hi (by
         change SourceMainFramesV1.Point0582.outputs.2.hi ∈ [SourceMainFramesV1.Point0576.outputs.2.hi, SourceMainFramesV1.Point0577.outputs.2.hi, SourceMainFramesV1.Point0578.outputs.2.hi, SourceMainFramesV1.Point0579.outputs.2.hi, SourceMainFramesV1.Point0580.outputs.2.hi, SourceMainFramesV1.Point0581.outputs.2.hi, SourceMainFramesV1.Point0582.outputs.2.hi, SourceMainFramesV1.Point0583.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=583) domain
     SourceMainFramesV1.Point0583.input_defined SourceMainFramesV1.Point0583.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0583.outputs.2.hi (by
         change SourceMainFramesV1.Point0583.outputs.2.hi ∈ [SourceMainFramesV1.Point0576.outputs.2.hi, SourceMainFramesV1.Point0577.outputs.2.hi, SourceMainFramesV1.Point0578.outputs.2.hi, SourceMainFramesV1.Point0579.outputs.2.hi, SourceMainFramesV1.Point0580.outputs.2.hi, SourceMainFramesV1.Point0581.outputs.2.hi, SourceMainFramesV1.Point0582.outputs.2.hi, SourceMainFramesV1.Point0583.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block72
