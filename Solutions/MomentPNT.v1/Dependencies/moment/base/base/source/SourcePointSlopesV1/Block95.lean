/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0760
import SourceMainFramesV1.Point0761
import SourceMainFramesV1.Point0762
import SourceMainFramesV1.Point0763
import SourceMainFramesV1.Point0764
import SourceMainFramesV1.Point0765
import SourceMainFramesV1.Point0766
import SourceMainFramesV1.Point0767
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block95
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0760.outputs.2.hi,
 SourceMainFramesV1.Point0761.outputs.2.hi,
 SourceMainFramesV1.Point0762.outputs.2.hi,
 SourceMainFramesV1.Point0763.outputs.2.hi,
 SourceMainFramesV1.Point0764.outputs.2.hi,
 SourceMainFramesV1.Point0765.outputs.2.hi,
 SourceMainFramesV1.Point0766.outputs.2.hi,
 SourceMainFramesV1.Point0767.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 760 ≤ i) (high : i < 768)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=760) domain
     SourceMainFramesV1.Point0760.input_defined SourceMainFramesV1.Point0760.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0760.outputs.2.hi (by
         change SourceMainFramesV1.Point0760.outputs.2.hi ∈ [SourceMainFramesV1.Point0760.outputs.2.hi, SourceMainFramesV1.Point0761.outputs.2.hi, SourceMainFramesV1.Point0762.outputs.2.hi, SourceMainFramesV1.Point0763.outputs.2.hi, SourceMainFramesV1.Point0764.outputs.2.hi, SourceMainFramesV1.Point0765.outputs.2.hi, SourceMainFramesV1.Point0766.outputs.2.hi, SourceMainFramesV1.Point0767.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=761) domain
     SourceMainFramesV1.Point0761.input_defined SourceMainFramesV1.Point0761.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0761.outputs.2.hi (by
         change SourceMainFramesV1.Point0761.outputs.2.hi ∈ [SourceMainFramesV1.Point0760.outputs.2.hi, SourceMainFramesV1.Point0761.outputs.2.hi, SourceMainFramesV1.Point0762.outputs.2.hi, SourceMainFramesV1.Point0763.outputs.2.hi, SourceMainFramesV1.Point0764.outputs.2.hi, SourceMainFramesV1.Point0765.outputs.2.hi, SourceMainFramesV1.Point0766.outputs.2.hi, SourceMainFramesV1.Point0767.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=762) domain
     SourceMainFramesV1.Point0762.input_defined SourceMainFramesV1.Point0762.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0762.outputs.2.hi (by
         change SourceMainFramesV1.Point0762.outputs.2.hi ∈ [SourceMainFramesV1.Point0760.outputs.2.hi, SourceMainFramesV1.Point0761.outputs.2.hi, SourceMainFramesV1.Point0762.outputs.2.hi, SourceMainFramesV1.Point0763.outputs.2.hi, SourceMainFramesV1.Point0764.outputs.2.hi, SourceMainFramesV1.Point0765.outputs.2.hi, SourceMainFramesV1.Point0766.outputs.2.hi, SourceMainFramesV1.Point0767.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=763) domain
     SourceMainFramesV1.Point0763.input_defined SourceMainFramesV1.Point0763.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0763.outputs.2.hi (by
         change SourceMainFramesV1.Point0763.outputs.2.hi ∈ [SourceMainFramesV1.Point0760.outputs.2.hi, SourceMainFramesV1.Point0761.outputs.2.hi, SourceMainFramesV1.Point0762.outputs.2.hi, SourceMainFramesV1.Point0763.outputs.2.hi, SourceMainFramesV1.Point0764.outputs.2.hi, SourceMainFramesV1.Point0765.outputs.2.hi, SourceMainFramesV1.Point0766.outputs.2.hi, SourceMainFramesV1.Point0767.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=764) domain
     SourceMainFramesV1.Point0764.input_defined SourceMainFramesV1.Point0764.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0764.outputs.2.hi (by
         change SourceMainFramesV1.Point0764.outputs.2.hi ∈ [SourceMainFramesV1.Point0760.outputs.2.hi, SourceMainFramesV1.Point0761.outputs.2.hi, SourceMainFramesV1.Point0762.outputs.2.hi, SourceMainFramesV1.Point0763.outputs.2.hi, SourceMainFramesV1.Point0764.outputs.2.hi, SourceMainFramesV1.Point0765.outputs.2.hi, SourceMainFramesV1.Point0766.outputs.2.hi, SourceMainFramesV1.Point0767.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=765) domain
     SourceMainFramesV1.Point0765.input_defined SourceMainFramesV1.Point0765.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0765.outputs.2.hi (by
         change SourceMainFramesV1.Point0765.outputs.2.hi ∈ [SourceMainFramesV1.Point0760.outputs.2.hi, SourceMainFramesV1.Point0761.outputs.2.hi, SourceMainFramesV1.Point0762.outputs.2.hi, SourceMainFramesV1.Point0763.outputs.2.hi, SourceMainFramesV1.Point0764.outputs.2.hi, SourceMainFramesV1.Point0765.outputs.2.hi, SourceMainFramesV1.Point0766.outputs.2.hi, SourceMainFramesV1.Point0767.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=766) domain
     SourceMainFramesV1.Point0766.input_defined SourceMainFramesV1.Point0766.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0766.outputs.2.hi (by
         change SourceMainFramesV1.Point0766.outputs.2.hi ∈ [SourceMainFramesV1.Point0760.outputs.2.hi, SourceMainFramesV1.Point0761.outputs.2.hi, SourceMainFramesV1.Point0762.outputs.2.hi, SourceMainFramesV1.Point0763.outputs.2.hi, SourceMainFramesV1.Point0764.outputs.2.hi, SourceMainFramesV1.Point0765.outputs.2.hi, SourceMainFramesV1.Point0766.outputs.2.hi, SourceMainFramesV1.Point0767.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=767) domain
     SourceMainFramesV1.Point0767.input_defined SourceMainFramesV1.Point0767.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0767.outputs.2.hi (by
         change SourceMainFramesV1.Point0767.outputs.2.hi ∈ [SourceMainFramesV1.Point0760.outputs.2.hi, SourceMainFramesV1.Point0761.outputs.2.hi, SourceMainFramesV1.Point0762.outputs.2.hi, SourceMainFramesV1.Point0763.outputs.2.hi, SourceMainFramesV1.Point0764.outputs.2.hi, SourceMainFramesV1.Point0765.outputs.2.hi, SourceMainFramesV1.Point0766.outputs.2.hi, SourceMainFramesV1.Point0767.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block95
