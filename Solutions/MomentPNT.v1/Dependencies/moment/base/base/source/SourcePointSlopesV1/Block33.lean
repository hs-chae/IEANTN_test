/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0264
import SourceMainFramesV1.Point0265
import SourceMainFramesV1.Point0266
import SourceMainFramesV1.Point0267
import SourceMainFramesV1.Point0268
import SourceMainFramesV1.Point0269
import SourceMainFramesV1.Point0270
import SourceMainFramesV1.Point0271
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block33
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0264.outputs.2.hi,
 SourceMainFramesV1.Point0265.outputs.2.hi,
 SourceMainFramesV1.Point0266.outputs.2.hi,
 SourceMainFramesV1.Point0267.outputs.2.hi,
 SourceMainFramesV1.Point0268.outputs.2.hi,
 SourceMainFramesV1.Point0269.outputs.2.hi,
 SourceMainFramesV1.Point0270.outputs.2.hi,
 SourceMainFramesV1.Point0271.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 264 ≤ i) (high : i < 272)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=264) domain
     SourceMainFramesV1.Point0264.input_defined SourceMainFramesV1.Point0264.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0264.outputs.2.hi (by
         change SourceMainFramesV1.Point0264.outputs.2.hi ∈ [SourceMainFramesV1.Point0264.outputs.2.hi, SourceMainFramesV1.Point0265.outputs.2.hi, SourceMainFramesV1.Point0266.outputs.2.hi, SourceMainFramesV1.Point0267.outputs.2.hi, SourceMainFramesV1.Point0268.outputs.2.hi, SourceMainFramesV1.Point0269.outputs.2.hi, SourceMainFramesV1.Point0270.outputs.2.hi, SourceMainFramesV1.Point0271.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=265) domain
     SourceMainFramesV1.Point0265.input_defined SourceMainFramesV1.Point0265.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0265.outputs.2.hi (by
         change SourceMainFramesV1.Point0265.outputs.2.hi ∈ [SourceMainFramesV1.Point0264.outputs.2.hi, SourceMainFramesV1.Point0265.outputs.2.hi, SourceMainFramesV1.Point0266.outputs.2.hi, SourceMainFramesV1.Point0267.outputs.2.hi, SourceMainFramesV1.Point0268.outputs.2.hi, SourceMainFramesV1.Point0269.outputs.2.hi, SourceMainFramesV1.Point0270.outputs.2.hi, SourceMainFramesV1.Point0271.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=266) domain
     SourceMainFramesV1.Point0266.input_defined SourceMainFramesV1.Point0266.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0266.outputs.2.hi (by
         change SourceMainFramesV1.Point0266.outputs.2.hi ∈ [SourceMainFramesV1.Point0264.outputs.2.hi, SourceMainFramesV1.Point0265.outputs.2.hi, SourceMainFramesV1.Point0266.outputs.2.hi, SourceMainFramesV1.Point0267.outputs.2.hi, SourceMainFramesV1.Point0268.outputs.2.hi, SourceMainFramesV1.Point0269.outputs.2.hi, SourceMainFramesV1.Point0270.outputs.2.hi, SourceMainFramesV1.Point0271.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=267) domain
     SourceMainFramesV1.Point0267.input_defined SourceMainFramesV1.Point0267.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0267.outputs.2.hi (by
         change SourceMainFramesV1.Point0267.outputs.2.hi ∈ [SourceMainFramesV1.Point0264.outputs.2.hi, SourceMainFramesV1.Point0265.outputs.2.hi, SourceMainFramesV1.Point0266.outputs.2.hi, SourceMainFramesV1.Point0267.outputs.2.hi, SourceMainFramesV1.Point0268.outputs.2.hi, SourceMainFramesV1.Point0269.outputs.2.hi, SourceMainFramesV1.Point0270.outputs.2.hi, SourceMainFramesV1.Point0271.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=268) domain
     SourceMainFramesV1.Point0268.input_defined SourceMainFramesV1.Point0268.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0268.outputs.2.hi (by
         change SourceMainFramesV1.Point0268.outputs.2.hi ∈ [SourceMainFramesV1.Point0264.outputs.2.hi, SourceMainFramesV1.Point0265.outputs.2.hi, SourceMainFramesV1.Point0266.outputs.2.hi, SourceMainFramesV1.Point0267.outputs.2.hi, SourceMainFramesV1.Point0268.outputs.2.hi, SourceMainFramesV1.Point0269.outputs.2.hi, SourceMainFramesV1.Point0270.outputs.2.hi, SourceMainFramesV1.Point0271.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=269) domain
     SourceMainFramesV1.Point0269.input_defined SourceMainFramesV1.Point0269.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0269.outputs.2.hi (by
         change SourceMainFramesV1.Point0269.outputs.2.hi ∈ [SourceMainFramesV1.Point0264.outputs.2.hi, SourceMainFramesV1.Point0265.outputs.2.hi, SourceMainFramesV1.Point0266.outputs.2.hi, SourceMainFramesV1.Point0267.outputs.2.hi, SourceMainFramesV1.Point0268.outputs.2.hi, SourceMainFramesV1.Point0269.outputs.2.hi, SourceMainFramesV1.Point0270.outputs.2.hi, SourceMainFramesV1.Point0271.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=270) domain
     SourceMainFramesV1.Point0270.input_defined SourceMainFramesV1.Point0270.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0270.outputs.2.hi (by
         change SourceMainFramesV1.Point0270.outputs.2.hi ∈ [SourceMainFramesV1.Point0264.outputs.2.hi, SourceMainFramesV1.Point0265.outputs.2.hi, SourceMainFramesV1.Point0266.outputs.2.hi, SourceMainFramesV1.Point0267.outputs.2.hi, SourceMainFramesV1.Point0268.outputs.2.hi, SourceMainFramesV1.Point0269.outputs.2.hi, SourceMainFramesV1.Point0270.outputs.2.hi, SourceMainFramesV1.Point0271.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=271) domain
     SourceMainFramesV1.Point0271.input_defined SourceMainFramesV1.Point0271.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0271.outputs.2.hi (by
         change SourceMainFramesV1.Point0271.outputs.2.hi ∈ [SourceMainFramesV1.Point0264.outputs.2.hi, SourceMainFramesV1.Point0265.outputs.2.hi, SourceMainFramesV1.Point0266.outputs.2.hi, SourceMainFramesV1.Point0267.outputs.2.hi, SourceMainFramesV1.Point0268.outputs.2.hi, SourceMainFramesV1.Point0269.outputs.2.hi, SourceMainFramesV1.Point0270.outputs.2.hi, SourceMainFramesV1.Point0271.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block33
