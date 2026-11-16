/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0392
import SourceMainFramesV1.Point0393
import SourceMainFramesV1.Point0394
import SourceMainFramesV1.Point0395
import SourceMainFramesV1.Point0396
import SourceMainFramesV1.Point0397
import SourceMainFramesV1.Point0398
import SourceMainFramesV1.Point0399
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block49
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0392.outputs.2.hi,
 SourceMainFramesV1.Point0393.outputs.2.hi,
 SourceMainFramesV1.Point0394.outputs.2.hi,
 SourceMainFramesV1.Point0395.outputs.2.hi,
 SourceMainFramesV1.Point0396.outputs.2.hi,
 SourceMainFramesV1.Point0397.outputs.2.hi,
 SourceMainFramesV1.Point0398.outputs.2.hi,
 SourceMainFramesV1.Point0399.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 392 ≤ i) (high : i < 400)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=392) domain
     SourceMainFramesV1.Point0392.input_defined SourceMainFramesV1.Point0392.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0392.outputs.2.hi (by
         change SourceMainFramesV1.Point0392.outputs.2.hi ∈ [SourceMainFramesV1.Point0392.outputs.2.hi, SourceMainFramesV1.Point0393.outputs.2.hi, SourceMainFramesV1.Point0394.outputs.2.hi, SourceMainFramesV1.Point0395.outputs.2.hi, SourceMainFramesV1.Point0396.outputs.2.hi, SourceMainFramesV1.Point0397.outputs.2.hi, SourceMainFramesV1.Point0398.outputs.2.hi, SourceMainFramesV1.Point0399.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=393) domain
     SourceMainFramesV1.Point0393.input_defined SourceMainFramesV1.Point0393.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0393.outputs.2.hi (by
         change SourceMainFramesV1.Point0393.outputs.2.hi ∈ [SourceMainFramesV1.Point0392.outputs.2.hi, SourceMainFramesV1.Point0393.outputs.2.hi, SourceMainFramesV1.Point0394.outputs.2.hi, SourceMainFramesV1.Point0395.outputs.2.hi, SourceMainFramesV1.Point0396.outputs.2.hi, SourceMainFramesV1.Point0397.outputs.2.hi, SourceMainFramesV1.Point0398.outputs.2.hi, SourceMainFramesV1.Point0399.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=394) domain
     SourceMainFramesV1.Point0394.input_defined SourceMainFramesV1.Point0394.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0394.outputs.2.hi (by
         change SourceMainFramesV1.Point0394.outputs.2.hi ∈ [SourceMainFramesV1.Point0392.outputs.2.hi, SourceMainFramesV1.Point0393.outputs.2.hi, SourceMainFramesV1.Point0394.outputs.2.hi, SourceMainFramesV1.Point0395.outputs.2.hi, SourceMainFramesV1.Point0396.outputs.2.hi, SourceMainFramesV1.Point0397.outputs.2.hi, SourceMainFramesV1.Point0398.outputs.2.hi, SourceMainFramesV1.Point0399.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=395) domain
     SourceMainFramesV1.Point0395.input_defined SourceMainFramesV1.Point0395.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0395.outputs.2.hi (by
         change SourceMainFramesV1.Point0395.outputs.2.hi ∈ [SourceMainFramesV1.Point0392.outputs.2.hi, SourceMainFramesV1.Point0393.outputs.2.hi, SourceMainFramesV1.Point0394.outputs.2.hi, SourceMainFramesV1.Point0395.outputs.2.hi, SourceMainFramesV1.Point0396.outputs.2.hi, SourceMainFramesV1.Point0397.outputs.2.hi, SourceMainFramesV1.Point0398.outputs.2.hi, SourceMainFramesV1.Point0399.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=396) domain
     SourceMainFramesV1.Point0396.input_defined SourceMainFramesV1.Point0396.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0396.outputs.2.hi (by
         change SourceMainFramesV1.Point0396.outputs.2.hi ∈ [SourceMainFramesV1.Point0392.outputs.2.hi, SourceMainFramesV1.Point0393.outputs.2.hi, SourceMainFramesV1.Point0394.outputs.2.hi, SourceMainFramesV1.Point0395.outputs.2.hi, SourceMainFramesV1.Point0396.outputs.2.hi, SourceMainFramesV1.Point0397.outputs.2.hi, SourceMainFramesV1.Point0398.outputs.2.hi, SourceMainFramesV1.Point0399.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=397) domain
     SourceMainFramesV1.Point0397.input_defined SourceMainFramesV1.Point0397.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0397.outputs.2.hi (by
         change SourceMainFramesV1.Point0397.outputs.2.hi ∈ [SourceMainFramesV1.Point0392.outputs.2.hi, SourceMainFramesV1.Point0393.outputs.2.hi, SourceMainFramesV1.Point0394.outputs.2.hi, SourceMainFramesV1.Point0395.outputs.2.hi, SourceMainFramesV1.Point0396.outputs.2.hi, SourceMainFramesV1.Point0397.outputs.2.hi, SourceMainFramesV1.Point0398.outputs.2.hi, SourceMainFramesV1.Point0399.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=398) domain
     SourceMainFramesV1.Point0398.input_defined SourceMainFramesV1.Point0398.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0398.outputs.2.hi (by
         change SourceMainFramesV1.Point0398.outputs.2.hi ∈ [SourceMainFramesV1.Point0392.outputs.2.hi, SourceMainFramesV1.Point0393.outputs.2.hi, SourceMainFramesV1.Point0394.outputs.2.hi, SourceMainFramesV1.Point0395.outputs.2.hi, SourceMainFramesV1.Point0396.outputs.2.hi, SourceMainFramesV1.Point0397.outputs.2.hi, SourceMainFramesV1.Point0398.outputs.2.hi, SourceMainFramesV1.Point0399.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=399) domain
     SourceMainFramesV1.Point0399.input_defined SourceMainFramesV1.Point0399.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0399.outputs.2.hi (by
         change SourceMainFramesV1.Point0399.outputs.2.hi ∈ [SourceMainFramesV1.Point0392.outputs.2.hi, SourceMainFramesV1.Point0393.outputs.2.hi, SourceMainFramesV1.Point0394.outputs.2.hi, SourceMainFramesV1.Point0395.outputs.2.hi, SourceMainFramesV1.Point0396.outputs.2.hi, SourceMainFramesV1.Point0397.outputs.2.hi, SourceMainFramesV1.Point0398.outputs.2.hi, SourceMainFramesV1.Point0399.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block49
