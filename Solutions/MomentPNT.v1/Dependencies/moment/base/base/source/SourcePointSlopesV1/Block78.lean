/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0624
import SourceMainFramesV1.Point0625
import SourceMainFramesV1.Point0626
import SourceMainFramesV1.Point0627
import SourceMainFramesV1.Point0628
import SourceMainFramesV1.Point0629
import SourceMainFramesV1.Point0630
import SourceMainFramesV1.Point0631
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block78
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0624.outputs.2.hi,
 SourceMainFramesV1.Point0625.outputs.2.hi,
 SourceMainFramesV1.Point0626.outputs.2.hi,
 SourceMainFramesV1.Point0627.outputs.2.hi,
 SourceMainFramesV1.Point0628.outputs.2.hi,
 SourceMainFramesV1.Point0629.outputs.2.hi,
 SourceMainFramesV1.Point0630.outputs.2.hi,
 SourceMainFramesV1.Point0631.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 624 ≤ i) (high : i < 632)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=624) domain
     SourceMainFramesV1.Point0624.input_defined SourceMainFramesV1.Point0624.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0624.outputs.2.hi (by
         change SourceMainFramesV1.Point0624.outputs.2.hi ∈ [SourceMainFramesV1.Point0624.outputs.2.hi, SourceMainFramesV1.Point0625.outputs.2.hi, SourceMainFramesV1.Point0626.outputs.2.hi, SourceMainFramesV1.Point0627.outputs.2.hi, SourceMainFramesV1.Point0628.outputs.2.hi, SourceMainFramesV1.Point0629.outputs.2.hi, SourceMainFramesV1.Point0630.outputs.2.hi, SourceMainFramesV1.Point0631.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=625) domain
     SourceMainFramesV1.Point0625.input_defined SourceMainFramesV1.Point0625.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0625.outputs.2.hi (by
         change SourceMainFramesV1.Point0625.outputs.2.hi ∈ [SourceMainFramesV1.Point0624.outputs.2.hi, SourceMainFramesV1.Point0625.outputs.2.hi, SourceMainFramesV1.Point0626.outputs.2.hi, SourceMainFramesV1.Point0627.outputs.2.hi, SourceMainFramesV1.Point0628.outputs.2.hi, SourceMainFramesV1.Point0629.outputs.2.hi, SourceMainFramesV1.Point0630.outputs.2.hi, SourceMainFramesV1.Point0631.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=626) domain
     SourceMainFramesV1.Point0626.input_defined SourceMainFramesV1.Point0626.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0626.outputs.2.hi (by
         change SourceMainFramesV1.Point0626.outputs.2.hi ∈ [SourceMainFramesV1.Point0624.outputs.2.hi, SourceMainFramesV1.Point0625.outputs.2.hi, SourceMainFramesV1.Point0626.outputs.2.hi, SourceMainFramesV1.Point0627.outputs.2.hi, SourceMainFramesV1.Point0628.outputs.2.hi, SourceMainFramesV1.Point0629.outputs.2.hi, SourceMainFramesV1.Point0630.outputs.2.hi, SourceMainFramesV1.Point0631.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=627) domain
     SourceMainFramesV1.Point0627.input_defined SourceMainFramesV1.Point0627.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0627.outputs.2.hi (by
         change SourceMainFramesV1.Point0627.outputs.2.hi ∈ [SourceMainFramesV1.Point0624.outputs.2.hi, SourceMainFramesV1.Point0625.outputs.2.hi, SourceMainFramesV1.Point0626.outputs.2.hi, SourceMainFramesV1.Point0627.outputs.2.hi, SourceMainFramesV1.Point0628.outputs.2.hi, SourceMainFramesV1.Point0629.outputs.2.hi, SourceMainFramesV1.Point0630.outputs.2.hi, SourceMainFramesV1.Point0631.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=628) domain
     SourceMainFramesV1.Point0628.input_defined SourceMainFramesV1.Point0628.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0628.outputs.2.hi (by
         change SourceMainFramesV1.Point0628.outputs.2.hi ∈ [SourceMainFramesV1.Point0624.outputs.2.hi, SourceMainFramesV1.Point0625.outputs.2.hi, SourceMainFramesV1.Point0626.outputs.2.hi, SourceMainFramesV1.Point0627.outputs.2.hi, SourceMainFramesV1.Point0628.outputs.2.hi, SourceMainFramesV1.Point0629.outputs.2.hi, SourceMainFramesV1.Point0630.outputs.2.hi, SourceMainFramesV1.Point0631.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=629) domain
     SourceMainFramesV1.Point0629.input_defined SourceMainFramesV1.Point0629.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0629.outputs.2.hi (by
         change SourceMainFramesV1.Point0629.outputs.2.hi ∈ [SourceMainFramesV1.Point0624.outputs.2.hi, SourceMainFramesV1.Point0625.outputs.2.hi, SourceMainFramesV1.Point0626.outputs.2.hi, SourceMainFramesV1.Point0627.outputs.2.hi, SourceMainFramesV1.Point0628.outputs.2.hi, SourceMainFramesV1.Point0629.outputs.2.hi, SourceMainFramesV1.Point0630.outputs.2.hi, SourceMainFramesV1.Point0631.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=630) domain
     SourceMainFramesV1.Point0630.input_defined SourceMainFramesV1.Point0630.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0630.outputs.2.hi (by
         change SourceMainFramesV1.Point0630.outputs.2.hi ∈ [SourceMainFramesV1.Point0624.outputs.2.hi, SourceMainFramesV1.Point0625.outputs.2.hi, SourceMainFramesV1.Point0626.outputs.2.hi, SourceMainFramesV1.Point0627.outputs.2.hi, SourceMainFramesV1.Point0628.outputs.2.hi, SourceMainFramesV1.Point0629.outputs.2.hi, SourceMainFramesV1.Point0630.outputs.2.hi, SourceMainFramesV1.Point0631.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=631) domain
     SourceMainFramesV1.Point0631.input_defined SourceMainFramesV1.Point0631.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0631.outputs.2.hi (by
         change SourceMainFramesV1.Point0631.outputs.2.hi ∈ [SourceMainFramesV1.Point0624.outputs.2.hi, SourceMainFramesV1.Point0625.outputs.2.hi, SourceMainFramesV1.Point0626.outputs.2.hi, SourceMainFramesV1.Point0627.outputs.2.hi, SourceMainFramesV1.Point0628.outputs.2.hi, SourceMainFramesV1.Point0629.outputs.2.hi, SourceMainFramesV1.Point0630.outputs.2.hi, SourceMainFramesV1.Point0631.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block78
