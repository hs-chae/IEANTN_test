/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0632
import SourceMainFramesV1.Point0633
import SourceMainFramesV1.Point0634
import SourceMainFramesV1.Point0635
import SourceMainFramesV1.Point0636
import SourceMainFramesV1.Point0637
import SourceMainFramesV1.Point0638
import SourceMainFramesV1.Point0639
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block79
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0632.outputs.2.hi,
 SourceMainFramesV1.Point0633.outputs.2.hi,
 SourceMainFramesV1.Point0634.outputs.2.hi,
 SourceMainFramesV1.Point0635.outputs.2.hi,
 SourceMainFramesV1.Point0636.outputs.2.hi,
 SourceMainFramesV1.Point0637.outputs.2.hi,
 SourceMainFramesV1.Point0638.outputs.2.hi,
 SourceMainFramesV1.Point0639.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 632 ≤ i) (high : i < 640)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=632) domain
     SourceMainFramesV1.Point0632.input_defined SourceMainFramesV1.Point0632.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0632.outputs.2.hi (by
         change SourceMainFramesV1.Point0632.outputs.2.hi ∈ [SourceMainFramesV1.Point0632.outputs.2.hi, SourceMainFramesV1.Point0633.outputs.2.hi, SourceMainFramesV1.Point0634.outputs.2.hi, SourceMainFramesV1.Point0635.outputs.2.hi, SourceMainFramesV1.Point0636.outputs.2.hi, SourceMainFramesV1.Point0637.outputs.2.hi, SourceMainFramesV1.Point0638.outputs.2.hi, SourceMainFramesV1.Point0639.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=633) domain
     SourceMainFramesV1.Point0633.input_defined SourceMainFramesV1.Point0633.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0633.outputs.2.hi (by
         change SourceMainFramesV1.Point0633.outputs.2.hi ∈ [SourceMainFramesV1.Point0632.outputs.2.hi, SourceMainFramesV1.Point0633.outputs.2.hi, SourceMainFramesV1.Point0634.outputs.2.hi, SourceMainFramesV1.Point0635.outputs.2.hi, SourceMainFramesV1.Point0636.outputs.2.hi, SourceMainFramesV1.Point0637.outputs.2.hi, SourceMainFramesV1.Point0638.outputs.2.hi, SourceMainFramesV1.Point0639.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=634) domain
     SourceMainFramesV1.Point0634.input_defined SourceMainFramesV1.Point0634.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0634.outputs.2.hi (by
         change SourceMainFramesV1.Point0634.outputs.2.hi ∈ [SourceMainFramesV1.Point0632.outputs.2.hi, SourceMainFramesV1.Point0633.outputs.2.hi, SourceMainFramesV1.Point0634.outputs.2.hi, SourceMainFramesV1.Point0635.outputs.2.hi, SourceMainFramesV1.Point0636.outputs.2.hi, SourceMainFramesV1.Point0637.outputs.2.hi, SourceMainFramesV1.Point0638.outputs.2.hi, SourceMainFramesV1.Point0639.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=635) domain
     SourceMainFramesV1.Point0635.input_defined SourceMainFramesV1.Point0635.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0635.outputs.2.hi (by
         change SourceMainFramesV1.Point0635.outputs.2.hi ∈ [SourceMainFramesV1.Point0632.outputs.2.hi, SourceMainFramesV1.Point0633.outputs.2.hi, SourceMainFramesV1.Point0634.outputs.2.hi, SourceMainFramesV1.Point0635.outputs.2.hi, SourceMainFramesV1.Point0636.outputs.2.hi, SourceMainFramesV1.Point0637.outputs.2.hi, SourceMainFramesV1.Point0638.outputs.2.hi, SourceMainFramesV1.Point0639.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=636) domain
     SourceMainFramesV1.Point0636.input_defined SourceMainFramesV1.Point0636.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0636.outputs.2.hi (by
         change SourceMainFramesV1.Point0636.outputs.2.hi ∈ [SourceMainFramesV1.Point0632.outputs.2.hi, SourceMainFramesV1.Point0633.outputs.2.hi, SourceMainFramesV1.Point0634.outputs.2.hi, SourceMainFramesV1.Point0635.outputs.2.hi, SourceMainFramesV1.Point0636.outputs.2.hi, SourceMainFramesV1.Point0637.outputs.2.hi, SourceMainFramesV1.Point0638.outputs.2.hi, SourceMainFramesV1.Point0639.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=637) domain
     SourceMainFramesV1.Point0637.input_defined SourceMainFramesV1.Point0637.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0637.outputs.2.hi (by
         change SourceMainFramesV1.Point0637.outputs.2.hi ∈ [SourceMainFramesV1.Point0632.outputs.2.hi, SourceMainFramesV1.Point0633.outputs.2.hi, SourceMainFramesV1.Point0634.outputs.2.hi, SourceMainFramesV1.Point0635.outputs.2.hi, SourceMainFramesV1.Point0636.outputs.2.hi, SourceMainFramesV1.Point0637.outputs.2.hi, SourceMainFramesV1.Point0638.outputs.2.hi, SourceMainFramesV1.Point0639.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=638) domain
     SourceMainFramesV1.Point0638.input_defined SourceMainFramesV1.Point0638.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0638.outputs.2.hi (by
         change SourceMainFramesV1.Point0638.outputs.2.hi ∈ [SourceMainFramesV1.Point0632.outputs.2.hi, SourceMainFramesV1.Point0633.outputs.2.hi, SourceMainFramesV1.Point0634.outputs.2.hi, SourceMainFramesV1.Point0635.outputs.2.hi, SourceMainFramesV1.Point0636.outputs.2.hi, SourceMainFramesV1.Point0637.outputs.2.hi, SourceMainFramesV1.Point0638.outputs.2.hi, SourceMainFramesV1.Point0639.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=639) domain
     SourceMainFramesV1.Point0639.input_defined SourceMainFramesV1.Point0639.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0639.outputs.2.hi (by
         change SourceMainFramesV1.Point0639.outputs.2.hi ∈ [SourceMainFramesV1.Point0632.outputs.2.hi, SourceMainFramesV1.Point0633.outputs.2.hi, SourceMainFramesV1.Point0634.outputs.2.hi, SourceMainFramesV1.Point0635.outputs.2.hi, SourceMainFramesV1.Point0636.outputs.2.hi, SourceMainFramesV1.Point0637.outputs.2.hi, SourceMainFramesV1.Point0638.outputs.2.hi, SourceMainFramesV1.Point0639.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block79
