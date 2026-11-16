/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0080
import SourceMainFramesV1.Point0081
import SourceMainFramesV1.Point0082
import SourceMainFramesV1.Point0083
import SourceMainFramesV1.Point0084
import SourceMainFramesV1.Point0085
import SourceMainFramesV1.Point0086
import SourceMainFramesV1.Point0087
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block10
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0080.outputs.2.hi,
 SourceMainFramesV1.Point0081.outputs.2.hi,
 SourceMainFramesV1.Point0082.outputs.2.hi,
 SourceMainFramesV1.Point0083.outputs.2.hi,
 SourceMainFramesV1.Point0084.outputs.2.hi,
 SourceMainFramesV1.Point0085.outputs.2.hi,
 SourceMainFramesV1.Point0086.outputs.2.hi,
 SourceMainFramesV1.Point0087.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 80 ≤ i) (high : i < 88)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=80) domain
     SourceMainFramesV1.Point0080.input_defined SourceMainFramesV1.Point0080.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0080.outputs.2.hi (by
         change SourceMainFramesV1.Point0080.outputs.2.hi ∈ [SourceMainFramesV1.Point0080.outputs.2.hi, SourceMainFramesV1.Point0081.outputs.2.hi, SourceMainFramesV1.Point0082.outputs.2.hi, SourceMainFramesV1.Point0083.outputs.2.hi, SourceMainFramesV1.Point0084.outputs.2.hi, SourceMainFramesV1.Point0085.outputs.2.hi, SourceMainFramesV1.Point0086.outputs.2.hi, SourceMainFramesV1.Point0087.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=81) domain
     SourceMainFramesV1.Point0081.input_defined SourceMainFramesV1.Point0081.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0081.outputs.2.hi (by
         change SourceMainFramesV1.Point0081.outputs.2.hi ∈ [SourceMainFramesV1.Point0080.outputs.2.hi, SourceMainFramesV1.Point0081.outputs.2.hi, SourceMainFramesV1.Point0082.outputs.2.hi, SourceMainFramesV1.Point0083.outputs.2.hi, SourceMainFramesV1.Point0084.outputs.2.hi, SourceMainFramesV1.Point0085.outputs.2.hi, SourceMainFramesV1.Point0086.outputs.2.hi, SourceMainFramesV1.Point0087.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=82) domain
     SourceMainFramesV1.Point0082.input_defined SourceMainFramesV1.Point0082.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0082.outputs.2.hi (by
         change SourceMainFramesV1.Point0082.outputs.2.hi ∈ [SourceMainFramesV1.Point0080.outputs.2.hi, SourceMainFramesV1.Point0081.outputs.2.hi, SourceMainFramesV1.Point0082.outputs.2.hi, SourceMainFramesV1.Point0083.outputs.2.hi, SourceMainFramesV1.Point0084.outputs.2.hi, SourceMainFramesV1.Point0085.outputs.2.hi, SourceMainFramesV1.Point0086.outputs.2.hi, SourceMainFramesV1.Point0087.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=83) domain
     SourceMainFramesV1.Point0083.input_defined SourceMainFramesV1.Point0083.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0083.outputs.2.hi (by
         change SourceMainFramesV1.Point0083.outputs.2.hi ∈ [SourceMainFramesV1.Point0080.outputs.2.hi, SourceMainFramesV1.Point0081.outputs.2.hi, SourceMainFramesV1.Point0082.outputs.2.hi, SourceMainFramesV1.Point0083.outputs.2.hi, SourceMainFramesV1.Point0084.outputs.2.hi, SourceMainFramesV1.Point0085.outputs.2.hi, SourceMainFramesV1.Point0086.outputs.2.hi, SourceMainFramesV1.Point0087.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=84) domain
     SourceMainFramesV1.Point0084.input_defined SourceMainFramesV1.Point0084.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0084.outputs.2.hi (by
         change SourceMainFramesV1.Point0084.outputs.2.hi ∈ [SourceMainFramesV1.Point0080.outputs.2.hi, SourceMainFramesV1.Point0081.outputs.2.hi, SourceMainFramesV1.Point0082.outputs.2.hi, SourceMainFramesV1.Point0083.outputs.2.hi, SourceMainFramesV1.Point0084.outputs.2.hi, SourceMainFramesV1.Point0085.outputs.2.hi, SourceMainFramesV1.Point0086.outputs.2.hi, SourceMainFramesV1.Point0087.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=85) domain
     SourceMainFramesV1.Point0085.input_defined SourceMainFramesV1.Point0085.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0085.outputs.2.hi (by
         change SourceMainFramesV1.Point0085.outputs.2.hi ∈ [SourceMainFramesV1.Point0080.outputs.2.hi, SourceMainFramesV1.Point0081.outputs.2.hi, SourceMainFramesV1.Point0082.outputs.2.hi, SourceMainFramesV1.Point0083.outputs.2.hi, SourceMainFramesV1.Point0084.outputs.2.hi, SourceMainFramesV1.Point0085.outputs.2.hi, SourceMainFramesV1.Point0086.outputs.2.hi, SourceMainFramesV1.Point0087.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=86) domain
     SourceMainFramesV1.Point0086.input_defined SourceMainFramesV1.Point0086.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0086.outputs.2.hi (by
         change SourceMainFramesV1.Point0086.outputs.2.hi ∈ [SourceMainFramesV1.Point0080.outputs.2.hi, SourceMainFramesV1.Point0081.outputs.2.hi, SourceMainFramesV1.Point0082.outputs.2.hi, SourceMainFramesV1.Point0083.outputs.2.hi, SourceMainFramesV1.Point0084.outputs.2.hi, SourceMainFramesV1.Point0085.outputs.2.hi, SourceMainFramesV1.Point0086.outputs.2.hi, SourceMainFramesV1.Point0087.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=87) domain
     SourceMainFramesV1.Point0087.input_defined SourceMainFramesV1.Point0087.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0087.outputs.2.hi (by
         change SourceMainFramesV1.Point0087.outputs.2.hi ∈ [SourceMainFramesV1.Point0080.outputs.2.hi, SourceMainFramesV1.Point0081.outputs.2.hi, SourceMainFramesV1.Point0082.outputs.2.hi, SourceMainFramesV1.Point0083.outputs.2.hi, SourceMainFramesV1.Point0084.outputs.2.hi, SourceMainFramesV1.Point0085.outputs.2.hi, SourceMainFramesV1.Point0086.outputs.2.hi, SourceMainFramesV1.Point0087.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block10
