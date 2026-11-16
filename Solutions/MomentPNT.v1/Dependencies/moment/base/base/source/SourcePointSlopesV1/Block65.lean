/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0520
import SourceMainFramesV1.Point0521
import SourceMainFramesV1.Point0522
import SourceMainFramesV1.Point0523
import SourceMainFramesV1.Point0524
import SourceMainFramesV1.Point0525
import SourceMainFramesV1.Point0526
import SourceMainFramesV1.Point0527
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block65
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0520.outputs.2.hi,
 SourceMainFramesV1.Point0521.outputs.2.hi,
 SourceMainFramesV1.Point0522.outputs.2.hi,
 SourceMainFramesV1.Point0523.outputs.2.hi,
 SourceMainFramesV1.Point0524.outputs.2.hi,
 SourceMainFramesV1.Point0525.outputs.2.hi,
 SourceMainFramesV1.Point0526.outputs.2.hi,
 SourceMainFramesV1.Point0527.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 520 ≤ i) (high : i < 528)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=520) domain
     SourceMainFramesV1.Point0520.input_defined SourceMainFramesV1.Point0520.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0520.outputs.2.hi (by
         change SourceMainFramesV1.Point0520.outputs.2.hi ∈ [SourceMainFramesV1.Point0520.outputs.2.hi, SourceMainFramesV1.Point0521.outputs.2.hi, SourceMainFramesV1.Point0522.outputs.2.hi, SourceMainFramesV1.Point0523.outputs.2.hi, SourceMainFramesV1.Point0524.outputs.2.hi, SourceMainFramesV1.Point0525.outputs.2.hi, SourceMainFramesV1.Point0526.outputs.2.hi, SourceMainFramesV1.Point0527.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=521) domain
     SourceMainFramesV1.Point0521.input_defined SourceMainFramesV1.Point0521.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0521.outputs.2.hi (by
         change SourceMainFramesV1.Point0521.outputs.2.hi ∈ [SourceMainFramesV1.Point0520.outputs.2.hi, SourceMainFramesV1.Point0521.outputs.2.hi, SourceMainFramesV1.Point0522.outputs.2.hi, SourceMainFramesV1.Point0523.outputs.2.hi, SourceMainFramesV1.Point0524.outputs.2.hi, SourceMainFramesV1.Point0525.outputs.2.hi, SourceMainFramesV1.Point0526.outputs.2.hi, SourceMainFramesV1.Point0527.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=522) domain
     SourceMainFramesV1.Point0522.input_defined SourceMainFramesV1.Point0522.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0522.outputs.2.hi (by
         change SourceMainFramesV1.Point0522.outputs.2.hi ∈ [SourceMainFramesV1.Point0520.outputs.2.hi, SourceMainFramesV1.Point0521.outputs.2.hi, SourceMainFramesV1.Point0522.outputs.2.hi, SourceMainFramesV1.Point0523.outputs.2.hi, SourceMainFramesV1.Point0524.outputs.2.hi, SourceMainFramesV1.Point0525.outputs.2.hi, SourceMainFramesV1.Point0526.outputs.2.hi, SourceMainFramesV1.Point0527.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=523) domain
     SourceMainFramesV1.Point0523.input_defined SourceMainFramesV1.Point0523.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0523.outputs.2.hi (by
         change SourceMainFramesV1.Point0523.outputs.2.hi ∈ [SourceMainFramesV1.Point0520.outputs.2.hi, SourceMainFramesV1.Point0521.outputs.2.hi, SourceMainFramesV1.Point0522.outputs.2.hi, SourceMainFramesV1.Point0523.outputs.2.hi, SourceMainFramesV1.Point0524.outputs.2.hi, SourceMainFramesV1.Point0525.outputs.2.hi, SourceMainFramesV1.Point0526.outputs.2.hi, SourceMainFramesV1.Point0527.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=524) domain
     SourceMainFramesV1.Point0524.input_defined SourceMainFramesV1.Point0524.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0524.outputs.2.hi (by
         change SourceMainFramesV1.Point0524.outputs.2.hi ∈ [SourceMainFramesV1.Point0520.outputs.2.hi, SourceMainFramesV1.Point0521.outputs.2.hi, SourceMainFramesV1.Point0522.outputs.2.hi, SourceMainFramesV1.Point0523.outputs.2.hi, SourceMainFramesV1.Point0524.outputs.2.hi, SourceMainFramesV1.Point0525.outputs.2.hi, SourceMainFramesV1.Point0526.outputs.2.hi, SourceMainFramesV1.Point0527.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=525) domain
     SourceMainFramesV1.Point0525.input_defined SourceMainFramesV1.Point0525.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0525.outputs.2.hi (by
         change SourceMainFramesV1.Point0525.outputs.2.hi ∈ [SourceMainFramesV1.Point0520.outputs.2.hi, SourceMainFramesV1.Point0521.outputs.2.hi, SourceMainFramesV1.Point0522.outputs.2.hi, SourceMainFramesV1.Point0523.outputs.2.hi, SourceMainFramesV1.Point0524.outputs.2.hi, SourceMainFramesV1.Point0525.outputs.2.hi, SourceMainFramesV1.Point0526.outputs.2.hi, SourceMainFramesV1.Point0527.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=526) domain
     SourceMainFramesV1.Point0526.input_defined SourceMainFramesV1.Point0526.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0526.outputs.2.hi (by
         change SourceMainFramesV1.Point0526.outputs.2.hi ∈ [SourceMainFramesV1.Point0520.outputs.2.hi, SourceMainFramesV1.Point0521.outputs.2.hi, SourceMainFramesV1.Point0522.outputs.2.hi, SourceMainFramesV1.Point0523.outputs.2.hi, SourceMainFramesV1.Point0524.outputs.2.hi, SourceMainFramesV1.Point0525.outputs.2.hi, SourceMainFramesV1.Point0526.outputs.2.hi, SourceMainFramesV1.Point0527.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=527) domain
     SourceMainFramesV1.Point0527.input_defined SourceMainFramesV1.Point0527.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0527.outputs.2.hi (by
         change SourceMainFramesV1.Point0527.outputs.2.hi ∈ [SourceMainFramesV1.Point0520.outputs.2.hi, SourceMainFramesV1.Point0521.outputs.2.hi, SourceMainFramesV1.Point0522.outputs.2.hi, SourceMainFramesV1.Point0523.outputs.2.hi, SourceMainFramesV1.Point0524.outputs.2.hi, SourceMainFramesV1.Point0525.outputs.2.hi, SourceMainFramesV1.Point0526.outputs.2.hi, SourceMainFramesV1.Point0527.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block65
