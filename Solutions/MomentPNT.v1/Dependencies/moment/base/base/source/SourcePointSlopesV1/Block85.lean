/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0680
import SourceMainFramesV1.Point0681
import SourceMainFramesV1.Point0682
import SourceMainFramesV1.Point0683
import SourceMainFramesV1.Point0684
import SourceMainFramesV1.Point0685
import SourceMainFramesV1.Point0686
import SourceMainFramesV1.Point0687
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block85
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0680.outputs.2.hi,
 SourceMainFramesV1.Point0681.outputs.2.hi,
 SourceMainFramesV1.Point0682.outputs.2.hi,
 SourceMainFramesV1.Point0683.outputs.2.hi,
 SourceMainFramesV1.Point0684.outputs.2.hi,
 SourceMainFramesV1.Point0685.outputs.2.hi,
 SourceMainFramesV1.Point0686.outputs.2.hi,
 SourceMainFramesV1.Point0687.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 680 ≤ i) (high : i < 688)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=680) domain
     SourceMainFramesV1.Point0680.input_defined SourceMainFramesV1.Point0680.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0680.outputs.2.hi (by
         change SourceMainFramesV1.Point0680.outputs.2.hi ∈ [SourceMainFramesV1.Point0680.outputs.2.hi, SourceMainFramesV1.Point0681.outputs.2.hi, SourceMainFramesV1.Point0682.outputs.2.hi, SourceMainFramesV1.Point0683.outputs.2.hi, SourceMainFramesV1.Point0684.outputs.2.hi, SourceMainFramesV1.Point0685.outputs.2.hi, SourceMainFramesV1.Point0686.outputs.2.hi, SourceMainFramesV1.Point0687.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=681) domain
     SourceMainFramesV1.Point0681.input_defined SourceMainFramesV1.Point0681.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0681.outputs.2.hi (by
         change SourceMainFramesV1.Point0681.outputs.2.hi ∈ [SourceMainFramesV1.Point0680.outputs.2.hi, SourceMainFramesV1.Point0681.outputs.2.hi, SourceMainFramesV1.Point0682.outputs.2.hi, SourceMainFramesV1.Point0683.outputs.2.hi, SourceMainFramesV1.Point0684.outputs.2.hi, SourceMainFramesV1.Point0685.outputs.2.hi, SourceMainFramesV1.Point0686.outputs.2.hi, SourceMainFramesV1.Point0687.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=682) domain
     SourceMainFramesV1.Point0682.input_defined SourceMainFramesV1.Point0682.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0682.outputs.2.hi (by
         change SourceMainFramesV1.Point0682.outputs.2.hi ∈ [SourceMainFramesV1.Point0680.outputs.2.hi, SourceMainFramesV1.Point0681.outputs.2.hi, SourceMainFramesV1.Point0682.outputs.2.hi, SourceMainFramesV1.Point0683.outputs.2.hi, SourceMainFramesV1.Point0684.outputs.2.hi, SourceMainFramesV1.Point0685.outputs.2.hi, SourceMainFramesV1.Point0686.outputs.2.hi, SourceMainFramesV1.Point0687.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=683) domain
     SourceMainFramesV1.Point0683.input_defined SourceMainFramesV1.Point0683.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0683.outputs.2.hi (by
         change SourceMainFramesV1.Point0683.outputs.2.hi ∈ [SourceMainFramesV1.Point0680.outputs.2.hi, SourceMainFramesV1.Point0681.outputs.2.hi, SourceMainFramesV1.Point0682.outputs.2.hi, SourceMainFramesV1.Point0683.outputs.2.hi, SourceMainFramesV1.Point0684.outputs.2.hi, SourceMainFramesV1.Point0685.outputs.2.hi, SourceMainFramesV1.Point0686.outputs.2.hi, SourceMainFramesV1.Point0687.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=684) domain
     SourceMainFramesV1.Point0684.input_defined SourceMainFramesV1.Point0684.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0684.outputs.2.hi (by
         change SourceMainFramesV1.Point0684.outputs.2.hi ∈ [SourceMainFramesV1.Point0680.outputs.2.hi, SourceMainFramesV1.Point0681.outputs.2.hi, SourceMainFramesV1.Point0682.outputs.2.hi, SourceMainFramesV1.Point0683.outputs.2.hi, SourceMainFramesV1.Point0684.outputs.2.hi, SourceMainFramesV1.Point0685.outputs.2.hi, SourceMainFramesV1.Point0686.outputs.2.hi, SourceMainFramesV1.Point0687.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=685) domain
     SourceMainFramesV1.Point0685.input_defined SourceMainFramesV1.Point0685.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0685.outputs.2.hi (by
         change SourceMainFramesV1.Point0685.outputs.2.hi ∈ [SourceMainFramesV1.Point0680.outputs.2.hi, SourceMainFramesV1.Point0681.outputs.2.hi, SourceMainFramesV1.Point0682.outputs.2.hi, SourceMainFramesV1.Point0683.outputs.2.hi, SourceMainFramesV1.Point0684.outputs.2.hi, SourceMainFramesV1.Point0685.outputs.2.hi, SourceMainFramesV1.Point0686.outputs.2.hi, SourceMainFramesV1.Point0687.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=686) domain
     SourceMainFramesV1.Point0686.input_defined SourceMainFramesV1.Point0686.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0686.outputs.2.hi (by
         change SourceMainFramesV1.Point0686.outputs.2.hi ∈ [SourceMainFramesV1.Point0680.outputs.2.hi, SourceMainFramesV1.Point0681.outputs.2.hi, SourceMainFramesV1.Point0682.outputs.2.hi, SourceMainFramesV1.Point0683.outputs.2.hi, SourceMainFramesV1.Point0684.outputs.2.hi, SourceMainFramesV1.Point0685.outputs.2.hi, SourceMainFramesV1.Point0686.outputs.2.hi, SourceMainFramesV1.Point0687.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=687) domain
     SourceMainFramesV1.Point0687.input_defined SourceMainFramesV1.Point0687.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0687.outputs.2.hi (by
         change SourceMainFramesV1.Point0687.outputs.2.hi ∈ [SourceMainFramesV1.Point0680.outputs.2.hi, SourceMainFramesV1.Point0681.outputs.2.hi, SourceMainFramesV1.Point0682.outputs.2.hi, SourceMainFramesV1.Point0683.outputs.2.hi, SourceMainFramesV1.Point0684.outputs.2.hi, SourceMainFramesV1.Point0685.outputs.2.hi, SourceMainFramesV1.Point0686.outputs.2.hi, SourceMainFramesV1.Point0687.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block85
