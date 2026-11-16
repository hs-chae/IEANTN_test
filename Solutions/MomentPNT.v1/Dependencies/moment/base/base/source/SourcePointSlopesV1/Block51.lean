/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0408
import SourceMainFramesV1.Point0409
import SourceMainFramesV1.Point0410
import SourceMainFramesV1.Point0411
import SourceMainFramesV1.Point0412
import SourceMainFramesV1.Point0413
import SourceMainFramesV1.Point0414
import SourceMainFramesV1.Point0415
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block51
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0408.outputs.2.hi,
 SourceMainFramesV1.Point0409.outputs.2.hi,
 SourceMainFramesV1.Point0410.outputs.2.hi,
 SourceMainFramesV1.Point0411.outputs.2.hi,
 SourceMainFramesV1.Point0412.outputs.2.hi,
 SourceMainFramesV1.Point0413.outputs.2.hi,
 SourceMainFramesV1.Point0414.outputs.2.hi,
 SourceMainFramesV1.Point0415.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 408 ≤ i) (high : i < 416)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=408) domain
     SourceMainFramesV1.Point0408.input_defined SourceMainFramesV1.Point0408.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0408.outputs.2.hi (by
         change SourceMainFramesV1.Point0408.outputs.2.hi ∈ [SourceMainFramesV1.Point0408.outputs.2.hi, SourceMainFramesV1.Point0409.outputs.2.hi, SourceMainFramesV1.Point0410.outputs.2.hi, SourceMainFramesV1.Point0411.outputs.2.hi, SourceMainFramesV1.Point0412.outputs.2.hi, SourceMainFramesV1.Point0413.outputs.2.hi, SourceMainFramesV1.Point0414.outputs.2.hi, SourceMainFramesV1.Point0415.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=409) domain
     SourceMainFramesV1.Point0409.input_defined SourceMainFramesV1.Point0409.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0409.outputs.2.hi (by
         change SourceMainFramesV1.Point0409.outputs.2.hi ∈ [SourceMainFramesV1.Point0408.outputs.2.hi, SourceMainFramesV1.Point0409.outputs.2.hi, SourceMainFramesV1.Point0410.outputs.2.hi, SourceMainFramesV1.Point0411.outputs.2.hi, SourceMainFramesV1.Point0412.outputs.2.hi, SourceMainFramesV1.Point0413.outputs.2.hi, SourceMainFramesV1.Point0414.outputs.2.hi, SourceMainFramesV1.Point0415.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=410) domain
     SourceMainFramesV1.Point0410.input_defined SourceMainFramesV1.Point0410.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0410.outputs.2.hi (by
         change SourceMainFramesV1.Point0410.outputs.2.hi ∈ [SourceMainFramesV1.Point0408.outputs.2.hi, SourceMainFramesV1.Point0409.outputs.2.hi, SourceMainFramesV1.Point0410.outputs.2.hi, SourceMainFramesV1.Point0411.outputs.2.hi, SourceMainFramesV1.Point0412.outputs.2.hi, SourceMainFramesV1.Point0413.outputs.2.hi, SourceMainFramesV1.Point0414.outputs.2.hi, SourceMainFramesV1.Point0415.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=411) domain
     SourceMainFramesV1.Point0411.input_defined SourceMainFramesV1.Point0411.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0411.outputs.2.hi (by
         change SourceMainFramesV1.Point0411.outputs.2.hi ∈ [SourceMainFramesV1.Point0408.outputs.2.hi, SourceMainFramesV1.Point0409.outputs.2.hi, SourceMainFramesV1.Point0410.outputs.2.hi, SourceMainFramesV1.Point0411.outputs.2.hi, SourceMainFramesV1.Point0412.outputs.2.hi, SourceMainFramesV1.Point0413.outputs.2.hi, SourceMainFramesV1.Point0414.outputs.2.hi, SourceMainFramesV1.Point0415.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=412) domain
     SourceMainFramesV1.Point0412.input_defined SourceMainFramesV1.Point0412.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0412.outputs.2.hi (by
         change SourceMainFramesV1.Point0412.outputs.2.hi ∈ [SourceMainFramesV1.Point0408.outputs.2.hi, SourceMainFramesV1.Point0409.outputs.2.hi, SourceMainFramesV1.Point0410.outputs.2.hi, SourceMainFramesV1.Point0411.outputs.2.hi, SourceMainFramesV1.Point0412.outputs.2.hi, SourceMainFramesV1.Point0413.outputs.2.hi, SourceMainFramesV1.Point0414.outputs.2.hi, SourceMainFramesV1.Point0415.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=413) domain
     SourceMainFramesV1.Point0413.input_defined SourceMainFramesV1.Point0413.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0413.outputs.2.hi (by
         change SourceMainFramesV1.Point0413.outputs.2.hi ∈ [SourceMainFramesV1.Point0408.outputs.2.hi, SourceMainFramesV1.Point0409.outputs.2.hi, SourceMainFramesV1.Point0410.outputs.2.hi, SourceMainFramesV1.Point0411.outputs.2.hi, SourceMainFramesV1.Point0412.outputs.2.hi, SourceMainFramesV1.Point0413.outputs.2.hi, SourceMainFramesV1.Point0414.outputs.2.hi, SourceMainFramesV1.Point0415.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=414) domain
     SourceMainFramesV1.Point0414.input_defined SourceMainFramesV1.Point0414.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0414.outputs.2.hi (by
         change SourceMainFramesV1.Point0414.outputs.2.hi ∈ [SourceMainFramesV1.Point0408.outputs.2.hi, SourceMainFramesV1.Point0409.outputs.2.hi, SourceMainFramesV1.Point0410.outputs.2.hi, SourceMainFramesV1.Point0411.outputs.2.hi, SourceMainFramesV1.Point0412.outputs.2.hi, SourceMainFramesV1.Point0413.outputs.2.hi, SourceMainFramesV1.Point0414.outputs.2.hi, SourceMainFramesV1.Point0415.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=415) domain
     SourceMainFramesV1.Point0415.input_defined SourceMainFramesV1.Point0415.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0415.outputs.2.hi (by
         change SourceMainFramesV1.Point0415.outputs.2.hi ∈ [SourceMainFramesV1.Point0408.outputs.2.hi, SourceMainFramesV1.Point0409.outputs.2.hi, SourceMainFramesV1.Point0410.outputs.2.hi, SourceMainFramesV1.Point0411.outputs.2.hi, SourceMainFramesV1.Point0412.outputs.2.hi, SourceMainFramesV1.Point0413.outputs.2.hi, SourceMainFramesV1.Point0414.outputs.2.hi, SourceMainFramesV1.Point0415.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block51
