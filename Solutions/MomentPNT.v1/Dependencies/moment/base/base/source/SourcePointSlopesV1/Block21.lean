/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0168
import SourceMainFramesV1.Point0169
import SourceMainFramesV1.Point0170
import SourceMainFramesV1.Point0171
import SourceMainFramesV1.Point0172
import SourceMainFramesV1.Point0173
import SourceMainFramesV1.Point0174
import SourceMainFramesV1.Point0175
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block21
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0168.outputs.2.hi,
 SourceMainFramesV1.Point0169.outputs.2.hi,
 SourceMainFramesV1.Point0170.outputs.2.hi,
 SourceMainFramesV1.Point0171.outputs.2.hi,
 SourceMainFramesV1.Point0172.outputs.2.hi,
 SourceMainFramesV1.Point0173.outputs.2.hi,
 SourceMainFramesV1.Point0174.outputs.2.hi,
 SourceMainFramesV1.Point0175.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 168 ≤ i) (high : i < 176)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=168) domain
     SourceMainFramesV1.Point0168.input_defined SourceMainFramesV1.Point0168.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0168.outputs.2.hi (by
         change SourceMainFramesV1.Point0168.outputs.2.hi ∈ [SourceMainFramesV1.Point0168.outputs.2.hi, SourceMainFramesV1.Point0169.outputs.2.hi, SourceMainFramesV1.Point0170.outputs.2.hi, SourceMainFramesV1.Point0171.outputs.2.hi, SourceMainFramesV1.Point0172.outputs.2.hi, SourceMainFramesV1.Point0173.outputs.2.hi, SourceMainFramesV1.Point0174.outputs.2.hi, SourceMainFramesV1.Point0175.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=169) domain
     SourceMainFramesV1.Point0169.input_defined SourceMainFramesV1.Point0169.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0169.outputs.2.hi (by
         change SourceMainFramesV1.Point0169.outputs.2.hi ∈ [SourceMainFramesV1.Point0168.outputs.2.hi, SourceMainFramesV1.Point0169.outputs.2.hi, SourceMainFramesV1.Point0170.outputs.2.hi, SourceMainFramesV1.Point0171.outputs.2.hi, SourceMainFramesV1.Point0172.outputs.2.hi, SourceMainFramesV1.Point0173.outputs.2.hi, SourceMainFramesV1.Point0174.outputs.2.hi, SourceMainFramesV1.Point0175.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=170) domain
     SourceMainFramesV1.Point0170.input_defined SourceMainFramesV1.Point0170.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0170.outputs.2.hi (by
         change SourceMainFramesV1.Point0170.outputs.2.hi ∈ [SourceMainFramesV1.Point0168.outputs.2.hi, SourceMainFramesV1.Point0169.outputs.2.hi, SourceMainFramesV1.Point0170.outputs.2.hi, SourceMainFramesV1.Point0171.outputs.2.hi, SourceMainFramesV1.Point0172.outputs.2.hi, SourceMainFramesV1.Point0173.outputs.2.hi, SourceMainFramesV1.Point0174.outputs.2.hi, SourceMainFramesV1.Point0175.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=171) domain
     SourceMainFramesV1.Point0171.input_defined SourceMainFramesV1.Point0171.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0171.outputs.2.hi (by
         change SourceMainFramesV1.Point0171.outputs.2.hi ∈ [SourceMainFramesV1.Point0168.outputs.2.hi, SourceMainFramesV1.Point0169.outputs.2.hi, SourceMainFramesV1.Point0170.outputs.2.hi, SourceMainFramesV1.Point0171.outputs.2.hi, SourceMainFramesV1.Point0172.outputs.2.hi, SourceMainFramesV1.Point0173.outputs.2.hi, SourceMainFramesV1.Point0174.outputs.2.hi, SourceMainFramesV1.Point0175.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=172) domain
     SourceMainFramesV1.Point0172.input_defined SourceMainFramesV1.Point0172.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0172.outputs.2.hi (by
         change SourceMainFramesV1.Point0172.outputs.2.hi ∈ [SourceMainFramesV1.Point0168.outputs.2.hi, SourceMainFramesV1.Point0169.outputs.2.hi, SourceMainFramesV1.Point0170.outputs.2.hi, SourceMainFramesV1.Point0171.outputs.2.hi, SourceMainFramesV1.Point0172.outputs.2.hi, SourceMainFramesV1.Point0173.outputs.2.hi, SourceMainFramesV1.Point0174.outputs.2.hi, SourceMainFramesV1.Point0175.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=173) domain
     SourceMainFramesV1.Point0173.input_defined SourceMainFramesV1.Point0173.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0173.outputs.2.hi (by
         change SourceMainFramesV1.Point0173.outputs.2.hi ∈ [SourceMainFramesV1.Point0168.outputs.2.hi, SourceMainFramesV1.Point0169.outputs.2.hi, SourceMainFramesV1.Point0170.outputs.2.hi, SourceMainFramesV1.Point0171.outputs.2.hi, SourceMainFramesV1.Point0172.outputs.2.hi, SourceMainFramesV1.Point0173.outputs.2.hi, SourceMainFramesV1.Point0174.outputs.2.hi, SourceMainFramesV1.Point0175.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=174) domain
     SourceMainFramesV1.Point0174.input_defined SourceMainFramesV1.Point0174.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0174.outputs.2.hi (by
         change SourceMainFramesV1.Point0174.outputs.2.hi ∈ [SourceMainFramesV1.Point0168.outputs.2.hi, SourceMainFramesV1.Point0169.outputs.2.hi, SourceMainFramesV1.Point0170.outputs.2.hi, SourceMainFramesV1.Point0171.outputs.2.hi, SourceMainFramesV1.Point0172.outputs.2.hi, SourceMainFramesV1.Point0173.outputs.2.hi, SourceMainFramesV1.Point0174.outputs.2.hi, SourceMainFramesV1.Point0175.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=175) domain
     SourceMainFramesV1.Point0175.input_defined SourceMainFramesV1.Point0175.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0175.outputs.2.hi (by
         change SourceMainFramesV1.Point0175.outputs.2.hi ∈ [SourceMainFramesV1.Point0168.outputs.2.hi, SourceMainFramesV1.Point0169.outputs.2.hi, SourceMainFramesV1.Point0170.outputs.2.hi, SourceMainFramesV1.Point0171.outputs.2.hi, SourceMainFramesV1.Point0172.outputs.2.hi, SourceMainFramesV1.Point0173.outputs.2.hi, SourceMainFramesV1.Point0174.outputs.2.hi, SourceMainFramesV1.Point0175.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block21
