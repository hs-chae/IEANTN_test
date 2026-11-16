/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0208
import SourceMainFramesV1.Point0209
import SourceMainFramesV1.Point0210
import SourceMainFramesV1.Point0211
import SourceMainFramesV1.Point0212
import SourceMainFramesV1.Point0213
import SourceMainFramesV1.Point0214
import SourceMainFramesV1.Point0215
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block26
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0208.outputs.2.hi,
 SourceMainFramesV1.Point0209.outputs.2.hi,
 SourceMainFramesV1.Point0210.outputs.2.hi,
 SourceMainFramesV1.Point0211.outputs.2.hi,
 SourceMainFramesV1.Point0212.outputs.2.hi,
 SourceMainFramesV1.Point0213.outputs.2.hi,
 SourceMainFramesV1.Point0214.outputs.2.hi,
 SourceMainFramesV1.Point0215.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 208 ≤ i) (high : i < 216)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=208) domain
     SourceMainFramesV1.Point0208.input_defined SourceMainFramesV1.Point0208.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0208.outputs.2.hi (by
         change SourceMainFramesV1.Point0208.outputs.2.hi ∈ [SourceMainFramesV1.Point0208.outputs.2.hi, SourceMainFramesV1.Point0209.outputs.2.hi, SourceMainFramesV1.Point0210.outputs.2.hi, SourceMainFramesV1.Point0211.outputs.2.hi, SourceMainFramesV1.Point0212.outputs.2.hi, SourceMainFramesV1.Point0213.outputs.2.hi, SourceMainFramesV1.Point0214.outputs.2.hi, SourceMainFramesV1.Point0215.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=209) domain
     SourceMainFramesV1.Point0209.input_defined SourceMainFramesV1.Point0209.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0209.outputs.2.hi (by
         change SourceMainFramesV1.Point0209.outputs.2.hi ∈ [SourceMainFramesV1.Point0208.outputs.2.hi, SourceMainFramesV1.Point0209.outputs.2.hi, SourceMainFramesV1.Point0210.outputs.2.hi, SourceMainFramesV1.Point0211.outputs.2.hi, SourceMainFramesV1.Point0212.outputs.2.hi, SourceMainFramesV1.Point0213.outputs.2.hi, SourceMainFramesV1.Point0214.outputs.2.hi, SourceMainFramesV1.Point0215.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=210) domain
     SourceMainFramesV1.Point0210.input_defined SourceMainFramesV1.Point0210.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0210.outputs.2.hi (by
         change SourceMainFramesV1.Point0210.outputs.2.hi ∈ [SourceMainFramesV1.Point0208.outputs.2.hi, SourceMainFramesV1.Point0209.outputs.2.hi, SourceMainFramesV1.Point0210.outputs.2.hi, SourceMainFramesV1.Point0211.outputs.2.hi, SourceMainFramesV1.Point0212.outputs.2.hi, SourceMainFramesV1.Point0213.outputs.2.hi, SourceMainFramesV1.Point0214.outputs.2.hi, SourceMainFramesV1.Point0215.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=211) domain
     SourceMainFramesV1.Point0211.input_defined SourceMainFramesV1.Point0211.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0211.outputs.2.hi (by
         change SourceMainFramesV1.Point0211.outputs.2.hi ∈ [SourceMainFramesV1.Point0208.outputs.2.hi, SourceMainFramesV1.Point0209.outputs.2.hi, SourceMainFramesV1.Point0210.outputs.2.hi, SourceMainFramesV1.Point0211.outputs.2.hi, SourceMainFramesV1.Point0212.outputs.2.hi, SourceMainFramesV1.Point0213.outputs.2.hi, SourceMainFramesV1.Point0214.outputs.2.hi, SourceMainFramesV1.Point0215.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=212) domain
     SourceMainFramesV1.Point0212.input_defined SourceMainFramesV1.Point0212.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0212.outputs.2.hi (by
         change SourceMainFramesV1.Point0212.outputs.2.hi ∈ [SourceMainFramesV1.Point0208.outputs.2.hi, SourceMainFramesV1.Point0209.outputs.2.hi, SourceMainFramesV1.Point0210.outputs.2.hi, SourceMainFramesV1.Point0211.outputs.2.hi, SourceMainFramesV1.Point0212.outputs.2.hi, SourceMainFramesV1.Point0213.outputs.2.hi, SourceMainFramesV1.Point0214.outputs.2.hi, SourceMainFramesV1.Point0215.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=213) domain
     SourceMainFramesV1.Point0213.input_defined SourceMainFramesV1.Point0213.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0213.outputs.2.hi (by
         change SourceMainFramesV1.Point0213.outputs.2.hi ∈ [SourceMainFramesV1.Point0208.outputs.2.hi, SourceMainFramesV1.Point0209.outputs.2.hi, SourceMainFramesV1.Point0210.outputs.2.hi, SourceMainFramesV1.Point0211.outputs.2.hi, SourceMainFramesV1.Point0212.outputs.2.hi, SourceMainFramesV1.Point0213.outputs.2.hi, SourceMainFramesV1.Point0214.outputs.2.hi, SourceMainFramesV1.Point0215.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=214) domain
     SourceMainFramesV1.Point0214.input_defined SourceMainFramesV1.Point0214.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0214.outputs.2.hi (by
         change SourceMainFramesV1.Point0214.outputs.2.hi ∈ [SourceMainFramesV1.Point0208.outputs.2.hi, SourceMainFramesV1.Point0209.outputs.2.hi, SourceMainFramesV1.Point0210.outputs.2.hi, SourceMainFramesV1.Point0211.outputs.2.hi, SourceMainFramesV1.Point0212.outputs.2.hi, SourceMainFramesV1.Point0213.outputs.2.hi, SourceMainFramesV1.Point0214.outputs.2.hi, SourceMainFramesV1.Point0215.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=215) domain
     SourceMainFramesV1.Point0215.input_defined SourceMainFramesV1.Point0215.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0215.outputs.2.hi (by
         change SourceMainFramesV1.Point0215.outputs.2.hi ∈ [SourceMainFramesV1.Point0208.outputs.2.hi, SourceMainFramesV1.Point0209.outputs.2.hi, SourceMainFramesV1.Point0210.outputs.2.hi, SourceMainFramesV1.Point0211.outputs.2.hi, SourceMainFramesV1.Point0212.outputs.2.hi, SourceMainFramesV1.Point0213.outputs.2.hi, SourceMainFramesV1.Point0214.outputs.2.hi, SourceMainFramesV1.Point0215.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block26
