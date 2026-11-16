/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0424
import SourceMainFramesV1.Point0425
import SourceMainFramesV1.Point0426
import SourceMainFramesV1.Point0427
import SourceMainFramesV1.Point0428
import SourceMainFramesV1.Point0429
import SourceMainFramesV1.Point0430
import SourceMainFramesV1.Point0431
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block53
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0424.outputs.2.hi,
 SourceMainFramesV1.Point0425.outputs.2.hi,
 SourceMainFramesV1.Point0426.outputs.2.hi,
 SourceMainFramesV1.Point0427.outputs.2.hi,
 SourceMainFramesV1.Point0428.outputs.2.hi,
 SourceMainFramesV1.Point0429.outputs.2.hi,
 SourceMainFramesV1.Point0430.outputs.2.hi,
 SourceMainFramesV1.Point0431.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 424 ≤ i) (high : i < 432)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=424) domain
     SourceMainFramesV1.Point0424.input_defined SourceMainFramesV1.Point0424.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0424.outputs.2.hi (by
         change SourceMainFramesV1.Point0424.outputs.2.hi ∈ [SourceMainFramesV1.Point0424.outputs.2.hi, SourceMainFramesV1.Point0425.outputs.2.hi, SourceMainFramesV1.Point0426.outputs.2.hi, SourceMainFramesV1.Point0427.outputs.2.hi, SourceMainFramesV1.Point0428.outputs.2.hi, SourceMainFramesV1.Point0429.outputs.2.hi, SourceMainFramesV1.Point0430.outputs.2.hi, SourceMainFramesV1.Point0431.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=425) domain
     SourceMainFramesV1.Point0425.input_defined SourceMainFramesV1.Point0425.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0425.outputs.2.hi (by
         change SourceMainFramesV1.Point0425.outputs.2.hi ∈ [SourceMainFramesV1.Point0424.outputs.2.hi, SourceMainFramesV1.Point0425.outputs.2.hi, SourceMainFramesV1.Point0426.outputs.2.hi, SourceMainFramesV1.Point0427.outputs.2.hi, SourceMainFramesV1.Point0428.outputs.2.hi, SourceMainFramesV1.Point0429.outputs.2.hi, SourceMainFramesV1.Point0430.outputs.2.hi, SourceMainFramesV1.Point0431.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=426) domain
     SourceMainFramesV1.Point0426.input_defined SourceMainFramesV1.Point0426.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0426.outputs.2.hi (by
         change SourceMainFramesV1.Point0426.outputs.2.hi ∈ [SourceMainFramesV1.Point0424.outputs.2.hi, SourceMainFramesV1.Point0425.outputs.2.hi, SourceMainFramesV1.Point0426.outputs.2.hi, SourceMainFramesV1.Point0427.outputs.2.hi, SourceMainFramesV1.Point0428.outputs.2.hi, SourceMainFramesV1.Point0429.outputs.2.hi, SourceMainFramesV1.Point0430.outputs.2.hi, SourceMainFramesV1.Point0431.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=427) domain
     SourceMainFramesV1.Point0427.input_defined SourceMainFramesV1.Point0427.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0427.outputs.2.hi (by
         change SourceMainFramesV1.Point0427.outputs.2.hi ∈ [SourceMainFramesV1.Point0424.outputs.2.hi, SourceMainFramesV1.Point0425.outputs.2.hi, SourceMainFramesV1.Point0426.outputs.2.hi, SourceMainFramesV1.Point0427.outputs.2.hi, SourceMainFramesV1.Point0428.outputs.2.hi, SourceMainFramesV1.Point0429.outputs.2.hi, SourceMainFramesV1.Point0430.outputs.2.hi, SourceMainFramesV1.Point0431.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=428) domain
     SourceMainFramesV1.Point0428.input_defined SourceMainFramesV1.Point0428.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0428.outputs.2.hi (by
         change SourceMainFramesV1.Point0428.outputs.2.hi ∈ [SourceMainFramesV1.Point0424.outputs.2.hi, SourceMainFramesV1.Point0425.outputs.2.hi, SourceMainFramesV1.Point0426.outputs.2.hi, SourceMainFramesV1.Point0427.outputs.2.hi, SourceMainFramesV1.Point0428.outputs.2.hi, SourceMainFramesV1.Point0429.outputs.2.hi, SourceMainFramesV1.Point0430.outputs.2.hi, SourceMainFramesV1.Point0431.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=429) domain
     SourceMainFramesV1.Point0429.input_defined SourceMainFramesV1.Point0429.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0429.outputs.2.hi (by
         change SourceMainFramesV1.Point0429.outputs.2.hi ∈ [SourceMainFramesV1.Point0424.outputs.2.hi, SourceMainFramesV1.Point0425.outputs.2.hi, SourceMainFramesV1.Point0426.outputs.2.hi, SourceMainFramesV1.Point0427.outputs.2.hi, SourceMainFramesV1.Point0428.outputs.2.hi, SourceMainFramesV1.Point0429.outputs.2.hi, SourceMainFramesV1.Point0430.outputs.2.hi, SourceMainFramesV1.Point0431.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=430) domain
     SourceMainFramesV1.Point0430.input_defined SourceMainFramesV1.Point0430.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0430.outputs.2.hi (by
         change SourceMainFramesV1.Point0430.outputs.2.hi ∈ [SourceMainFramesV1.Point0424.outputs.2.hi, SourceMainFramesV1.Point0425.outputs.2.hi, SourceMainFramesV1.Point0426.outputs.2.hi, SourceMainFramesV1.Point0427.outputs.2.hi, SourceMainFramesV1.Point0428.outputs.2.hi, SourceMainFramesV1.Point0429.outputs.2.hi, SourceMainFramesV1.Point0430.outputs.2.hi, SourceMainFramesV1.Point0431.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=431) domain
     SourceMainFramesV1.Point0431.input_defined SourceMainFramesV1.Point0431.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0431.outputs.2.hi (by
         change SourceMainFramesV1.Point0431.outputs.2.hi ∈ [SourceMainFramesV1.Point0424.outputs.2.hi, SourceMainFramesV1.Point0425.outputs.2.hi, SourceMainFramesV1.Point0426.outputs.2.hi, SourceMainFramesV1.Point0427.outputs.2.hi, SourceMainFramesV1.Point0428.outputs.2.hi, SourceMainFramesV1.Point0429.outputs.2.hi, SourceMainFramesV1.Point0430.outputs.2.hi, SourceMainFramesV1.Point0431.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block53
