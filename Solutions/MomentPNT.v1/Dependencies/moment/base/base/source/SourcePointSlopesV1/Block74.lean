/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0592
import SourceMainFramesV1.Point0593
import SourceMainFramesV1.Point0594
import SourceMainFramesV1.Point0595
import SourceMainFramesV1.Point0596
import SourceMainFramesV1.Point0597
import SourceMainFramesV1.Point0598
import SourceMainFramesV1.Point0599
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block74
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0592.outputs.2.hi,
 SourceMainFramesV1.Point0593.outputs.2.hi,
 SourceMainFramesV1.Point0594.outputs.2.hi,
 SourceMainFramesV1.Point0595.outputs.2.hi,
 SourceMainFramesV1.Point0596.outputs.2.hi,
 SourceMainFramesV1.Point0597.outputs.2.hi,
 SourceMainFramesV1.Point0598.outputs.2.hi,
 SourceMainFramesV1.Point0599.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 592 ≤ i) (high : i < 600)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=592) domain
     SourceMainFramesV1.Point0592.input_defined SourceMainFramesV1.Point0592.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0592.outputs.2.hi (by
         change SourceMainFramesV1.Point0592.outputs.2.hi ∈ [SourceMainFramesV1.Point0592.outputs.2.hi, SourceMainFramesV1.Point0593.outputs.2.hi, SourceMainFramesV1.Point0594.outputs.2.hi, SourceMainFramesV1.Point0595.outputs.2.hi, SourceMainFramesV1.Point0596.outputs.2.hi, SourceMainFramesV1.Point0597.outputs.2.hi, SourceMainFramesV1.Point0598.outputs.2.hi, SourceMainFramesV1.Point0599.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=593) domain
     SourceMainFramesV1.Point0593.input_defined SourceMainFramesV1.Point0593.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0593.outputs.2.hi (by
         change SourceMainFramesV1.Point0593.outputs.2.hi ∈ [SourceMainFramesV1.Point0592.outputs.2.hi, SourceMainFramesV1.Point0593.outputs.2.hi, SourceMainFramesV1.Point0594.outputs.2.hi, SourceMainFramesV1.Point0595.outputs.2.hi, SourceMainFramesV1.Point0596.outputs.2.hi, SourceMainFramesV1.Point0597.outputs.2.hi, SourceMainFramesV1.Point0598.outputs.2.hi, SourceMainFramesV1.Point0599.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=594) domain
     SourceMainFramesV1.Point0594.input_defined SourceMainFramesV1.Point0594.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0594.outputs.2.hi (by
         change SourceMainFramesV1.Point0594.outputs.2.hi ∈ [SourceMainFramesV1.Point0592.outputs.2.hi, SourceMainFramesV1.Point0593.outputs.2.hi, SourceMainFramesV1.Point0594.outputs.2.hi, SourceMainFramesV1.Point0595.outputs.2.hi, SourceMainFramesV1.Point0596.outputs.2.hi, SourceMainFramesV1.Point0597.outputs.2.hi, SourceMainFramesV1.Point0598.outputs.2.hi, SourceMainFramesV1.Point0599.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=595) domain
     SourceMainFramesV1.Point0595.input_defined SourceMainFramesV1.Point0595.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0595.outputs.2.hi (by
         change SourceMainFramesV1.Point0595.outputs.2.hi ∈ [SourceMainFramesV1.Point0592.outputs.2.hi, SourceMainFramesV1.Point0593.outputs.2.hi, SourceMainFramesV1.Point0594.outputs.2.hi, SourceMainFramesV1.Point0595.outputs.2.hi, SourceMainFramesV1.Point0596.outputs.2.hi, SourceMainFramesV1.Point0597.outputs.2.hi, SourceMainFramesV1.Point0598.outputs.2.hi, SourceMainFramesV1.Point0599.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=596) domain
     SourceMainFramesV1.Point0596.input_defined SourceMainFramesV1.Point0596.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0596.outputs.2.hi (by
         change SourceMainFramesV1.Point0596.outputs.2.hi ∈ [SourceMainFramesV1.Point0592.outputs.2.hi, SourceMainFramesV1.Point0593.outputs.2.hi, SourceMainFramesV1.Point0594.outputs.2.hi, SourceMainFramesV1.Point0595.outputs.2.hi, SourceMainFramesV1.Point0596.outputs.2.hi, SourceMainFramesV1.Point0597.outputs.2.hi, SourceMainFramesV1.Point0598.outputs.2.hi, SourceMainFramesV1.Point0599.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=597) domain
     SourceMainFramesV1.Point0597.input_defined SourceMainFramesV1.Point0597.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0597.outputs.2.hi (by
         change SourceMainFramesV1.Point0597.outputs.2.hi ∈ [SourceMainFramesV1.Point0592.outputs.2.hi, SourceMainFramesV1.Point0593.outputs.2.hi, SourceMainFramesV1.Point0594.outputs.2.hi, SourceMainFramesV1.Point0595.outputs.2.hi, SourceMainFramesV1.Point0596.outputs.2.hi, SourceMainFramesV1.Point0597.outputs.2.hi, SourceMainFramesV1.Point0598.outputs.2.hi, SourceMainFramesV1.Point0599.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=598) domain
     SourceMainFramesV1.Point0598.input_defined SourceMainFramesV1.Point0598.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0598.outputs.2.hi (by
         change SourceMainFramesV1.Point0598.outputs.2.hi ∈ [SourceMainFramesV1.Point0592.outputs.2.hi, SourceMainFramesV1.Point0593.outputs.2.hi, SourceMainFramesV1.Point0594.outputs.2.hi, SourceMainFramesV1.Point0595.outputs.2.hi, SourceMainFramesV1.Point0596.outputs.2.hi, SourceMainFramesV1.Point0597.outputs.2.hi, SourceMainFramesV1.Point0598.outputs.2.hi, SourceMainFramesV1.Point0599.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=599) domain
     SourceMainFramesV1.Point0599.input_defined SourceMainFramesV1.Point0599.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0599.outputs.2.hi (by
         change SourceMainFramesV1.Point0599.outputs.2.hi ∈ [SourceMainFramesV1.Point0592.outputs.2.hi, SourceMainFramesV1.Point0593.outputs.2.hi, SourceMainFramesV1.Point0594.outputs.2.hi, SourceMainFramesV1.Point0595.outputs.2.hi, SourceMainFramesV1.Point0596.outputs.2.hi, SourceMainFramesV1.Point0597.outputs.2.hi, SourceMainFramesV1.Point0598.outputs.2.hi, SourceMainFramesV1.Point0599.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block74
