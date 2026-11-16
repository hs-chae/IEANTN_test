/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0352
import SourceMainFramesV1.Point0353
import SourceMainFramesV1.Point0354
import SourceMainFramesV1.Point0355
import SourceMainFramesV1.Point0356
import SourceMainFramesV1.Point0357
import SourceMainFramesV1.Point0358
import SourceMainFramesV1.Point0359
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block44
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0352.outputs.2.hi,
 SourceMainFramesV1.Point0353.outputs.2.hi,
 SourceMainFramesV1.Point0354.outputs.2.hi,
 SourceMainFramesV1.Point0355.outputs.2.hi,
 SourceMainFramesV1.Point0356.outputs.2.hi,
 SourceMainFramesV1.Point0357.outputs.2.hi,
 SourceMainFramesV1.Point0358.outputs.2.hi,
 SourceMainFramesV1.Point0359.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 352 ≤ i) (high : i < 360)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=352) domain
     SourceMainFramesV1.Point0352.input_defined SourceMainFramesV1.Point0352.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0352.outputs.2.hi (by
         change SourceMainFramesV1.Point0352.outputs.2.hi ∈ [SourceMainFramesV1.Point0352.outputs.2.hi, SourceMainFramesV1.Point0353.outputs.2.hi, SourceMainFramesV1.Point0354.outputs.2.hi, SourceMainFramesV1.Point0355.outputs.2.hi, SourceMainFramesV1.Point0356.outputs.2.hi, SourceMainFramesV1.Point0357.outputs.2.hi, SourceMainFramesV1.Point0358.outputs.2.hi, SourceMainFramesV1.Point0359.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=353) domain
     SourceMainFramesV1.Point0353.input_defined SourceMainFramesV1.Point0353.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0353.outputs.2.hi (by
         change SourceMainFramesV1.Point0353.outputs.2.hi ∈ [SourceMainFramesV1.Point0352.outputs.2.hi, SourceMainFramesV1.Point0353.outputs.2.hi, SourceMainFramesV1.Point0354.outputs.2.hi, SourceMainFramesV1.Point0355.outputs.2.hi, SourceMainFramesV1.Point0356.outputs.2.hi, SourceMainFramesV1.Point0357.outputs.2.hi, SourceMainFramesV1.Point0358.outputs.2.hi, SourceMainFramesV1.Point0359.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=354) domain
     SourceMainFramesV1.Point0354.input_defined SourceMainFramesV1.Point0354.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0354.outputs.2.hi (by
         change SourceMainFramesV1.Point0354.outputs.2.hi ∈ [SourceMainFramesV1.Point0352.outputs.2.hi, SourceMainFramesV1.Point0353.outputs.2.hi, SourceMainFramesV1.Point0354.outputs.2.hi, SourceMainFramesV1.Point0355.outputs.2.hi, SourceMainFramesV1.Point0356.outputs.2.hi, SourceMainFramesV1.Point0357.outputs.2.hi, SourceMainFramesV1.Point0358.outputs.2.hi, SourceMainFramesV1.Point0359.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=355) domain
     SourceMainFramesV1.Point0355.input_defined SourceMainFramesV1.Point0355.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0355.outputs.2.hi (by
         change SourceMainFramesV1.Point0355.outputs.2.hi ∈ [SourceMainFramesV1.Point0352.outputs.2.hi, SourceMainFramesV1.Point0353.outputs.2.hi, SourceMainFramesV1.Point0354.outputs.2.hi, SourceMainFramesV1.Point0355.outputs.2.hi, SourceMainFramesV1.Point0356.outputs.2.hi, SourceMainFramesV1.Point0357.outputs.2.hi, SourceMainFramesV1.Point0358.outputs.2.hi, SourceMainFramesV1.Point0359.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=356) domain
     SourceMainFramesV1.Point0356.input_defined SourceMainFramesV1.Point0356.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0356.outputs.2.hi (by
         change SourceMainFramesV1.Point0356.outputs.2.hi ∈ [SourceMainFramesV1.Point0352.outputs.2.hi, SourceMainFramesV1.Point0353.outputs.2.hi, SourceMainFramesV1.Point0354.outputs.2.hi, SourceMainFramesV1.Point0355.outputs.2.hi, SourceMainFramesV1.Point0356.outputs.2.hi, SourceMainFramesV1.Point0357.outputs.2.hi, SourceMainFramesV1.Point0358.outputs.2.hi, SourceMainFramesV1.Point0359.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=357) domain
     SourceMainFramesV1.Point0357.input_defined SourceMainFramesV1.Point0357.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0357.outputs.2.hi (by
         change SourceMainFramesV1.Point0357.outputs.2.hi ∈ [SourceMainFramesV1.Point0352.outputs.2.hi, SourceMainFramesV1.Point0353.outputs.2.hi, SourceMainFramesV1.Point0354.outputs.2.hi, SourceMainFramesV1.Point0355.outputs.2.hi, SourceMainFramesV1.Point0356.outputs.2.hi, SourceMainFramesV1.Point0357.outputs.2.hi, SourceMainFramesV1.Point0358.outputs.2.hi, SourceMainFramesV1.Point0359.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=358) domain
     SourceMainFramesV1.Point0358.input_defined SourceMainFramesV1.Point0358.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0358.outputs.2.hi (by
         change SourceMainFramesV1.Point0358.outputs.2.hi ∈ [SourceMainFramesV1.Point0352.outputs.2.hi, SourceMainFramesV1.Point0353.outputs.2.hi, SourceMainFramesV1.Point0354.outputs.2.hi, SourceMainFramesV1.Point0355.outputs.2.hi, SourceMainFramesV1.Point0356.outputs.2.hi, SourceMainFramesV1.Point0357.outputs.2.hi, SourceMainFramesV1.Point0358.outputs.2.hi, SourceMainFramesV1.Point0359.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=359) domain
     SourceMainFramesV1.Point0359.input_defined SourceMainFramesV1.Point0359.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0359.outputs.2.hi (by
         change SourceMainFramesV1.Point0359.outputs.2.hi ∈ [SourceMainFramesV1.Point0352.outputs.2.hi, SourceMainFramesV1.Point0353.outputs.2.hi, SourceMainFramesV1.Point0354.outputs.2.hi, SourceMainFramesV1.Point0355.outputs.2.hi, SourceMainFramesV1.Point0356.outputs.2.hi, SourceMainFramesV1.Point0357.outputs.2.hi, SourceMainFramesV1.Point0358.outputs.2.hi, SourceMainFramesV1.Point0359.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block44
