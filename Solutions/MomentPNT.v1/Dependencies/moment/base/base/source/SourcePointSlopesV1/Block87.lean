/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0696
import SourceMainFramesV1.Point0697
import SourceMainFramesV1.Point0698
import SourceMainFramesV1.Point0699
import SourceMainFramesV1.Point0700
import SourceMainFramesV1.Point0701
import SourceMainFramesV1.Point0702
import SourceMainFramesV1.Point0703
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block87
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0696.outputs.2.hi,
 SourceMainFramesV1.Point0697.outputs.2.hi,
 SourceMainFramesV1.Point0698.outputs.2.hi,
 SourceMainFramesV1.Point0699.outputs.2.hi,
 SourceMainFramesV1.Point0700.outputs.2.hi,
 SourceMainFramesV1.Point0701.outputs.2.hi,
 SourceMainFramesV1.Point0702.outputs.2.hi,
 SourceMainFramesV1.Point0703.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 696 ≤ i) (high : i < 704)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=696) domain
     SourceMainFramesV1.Point0696.input_defined SourceMainFramesV1.Point0696.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0696.outputs.2.hi (by
         change SourceMainFramesV1.Point0696.outputs.2.hi ∈ [SourceMainFramesV1.Point0696.outputs.2.hi, SourceMainFramesV1.Point0697.outputs.2.hi, SourceMainFramesV1.Point0698.outputs.2.hi, SourceMainFramesV1.Point0699.outputs.2.hi, SourceMainFramesV1.Point0700.outputs.2.hi, SourceMainFramesV1.Point0701.outputs.2.hi, SourceMainFramesV1.Point0702.outputs.2.hi, SourceMainFramesV1.Point0703.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=697) domain
     SourceMainFramesV1.Point0697.input_defined SourceMainFramesV1.Point0697.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0697.outputs.2.hi (by
         change SourceMainFramesV1.Point0697.outputs.2.hi ∈ [SourceMainFramesV1.Point0696.outputs.2.hi, SourceMainFramesV1.Point0697.outputs.2.hi, SourceMainFramesV1.Point0698.outputs.2.hi, SourceMainFramesV1.Point0699.outputs.2.hi, SourceMainFramesV1.Point0700.outputs.2.hi, SourceMainFramesV1.Point0701.outputs.2.hi, SourceMainFramesV1.Point0702.outputs.2.hi, SourceMainFramesV1.Point0703.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=698) domain
     SourceMainFramesV1.Point0698.input_defined SourceMainFramesV1.Point0698.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0698.outputs.2.hi (by
         change SourceMainFramesV1.Point0698.outputs.2.hi ∈ [SourceMainFramesV1.Point0696.outputs.2.hi, SourceMainFramesV1.Point0697.outputs.2.hi, SourceMainFramesV1.Point0698.outputs.2.hi, SourceMainFramesV1.Point0699.outputs.2.hi, SourceMainFramesV1.Point0700.outputs.2.hi, SourceMainFramesV1.Point0701.outputs.2.hi, SourceMainFramesV1.Point0702.outputs.2.hi, SourceMainFramesV1.Point0703.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=699) domain
     SourceMainFramesV1.Point0699.input_defined SourceMainFramesV1.Point0699.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0699.outputs.2.hi (by
         change SourceMainFramesV1.Point0699.outputs.2.hi ∈ [SourceMainFramesV1.Point0696.outputs.2.hi, SourceMainFramesV1.Point0697.outputs.2.hi, SourceMainFramesV1.Point0698.outputs.2.hi, SourceMainFramesV1.Point0699.outputs.2.hi, SourceMainFramesV1.Point0700.outputs.2.hi, SourceMainFramesV1.Point0701.outputs.2.hi, SourceMainFramesV1.Point0702.outputs.2.hi, SourceMainFramesV1.Point0703.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=700) domain
     SourceMainFramesV1.Point0700.input_defined SourceMainFramesV1.Point0700.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0700.outputs.2.hi (by
         change SourceMainFramesV1.Point0700.outputs.2.hi ∈ [SourceMainFramesV1.Point0696.outputs.2.hi, SourceMainFramesV1.Point0697.outputs.2.hi, SourceMainFramesV1.Point0698.outputs.2.hi, SourceMainFramesV1.Point0699.outputs.2.hi, SourceMainFramesV1.Point0700.outputs.2.hi, SourceMainFramesV1.Point0701.outputs.2.hi, SourceMainFramesV1.Point0702.outputs.2.hi, SourceMainFramesV1.Point0703.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=701) domain
     SourceMainFramesV1.Point0701.input_defined SourceMainFramesV1.Point0701.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0701.outputs.2.hi (by
         change SourceMainFramesV1.Point0701.outputs.2.hi ∈ [SourceMainFramesV1.Point0696.outputs.2.hi, SourceMainFramesV1.Point0697.outputs.2.hi, SourceMainFramesV1.Point0698.outputs.2.hi, SourceMainFramesV1.Point0699.outputs.2.hi, SourceMainFramesV1.Point0700.outputs.2.hi, SourceMainFramesV1.Point0701.outputs.2.hi, SourceMainFramesV1.Point0702.outputs.2.hi, SourceMainFramesV1.Point0703.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=702) domain
     SourceMainFramesV1.Point0702.input_defined SourceMainFramesV1.Point0702.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0702.outputs.2.hi (by
         change SourceMainFramesV1.Point0702.outputs.2.hi ∈ [SourceMainFramesV1.Point0696.outputs.2.hi, SourceMainFramesV1.Point0697.outputs.2.hi, SourceMainFramesV1.Point0698.outputs.2.hi, SourceMainFramesV1.Point0699.outputs.2.hi, SourceMainFramesV1.Point0700.outputs.2.hi, SourceMainFramesV1.Point0701.outputs.2.hi, SourceMainFramesV1.Point0702.outputs.2.hi, SourceMainFramesV1.Point0703.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=703) domain
     SourceMainFramesV1.Point0703.input_defined SourceMainFramesV1.Point0703.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0703.outputs.2.hi (by
         change SourceMainFramesV1.Point0703.outputs.2.hi ∈ [SourceMainFramesV1.Point0696.outputs.2.hi, SourceMainFramesV1.Point0697.outputs.2.hi, SourceMainFramesV1.Point0698.outputs.2.hi, SourceMainFramesV1.Point0699.outputs.2.hi, SourceMainFramesV1.Point0700.outputs.2.hi, SourceMainFramesV1.Point0701.outputs.2.hi, SourceMainFramesV1.Point0702.outputs.2.hi, SourceMainFramesV1.Point0703.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block87
