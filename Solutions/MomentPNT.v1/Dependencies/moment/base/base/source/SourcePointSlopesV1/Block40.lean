/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0320
import SourceMainFramesV1.Point0321
import SourceMainFramesV1.Point0322
import SourceMainFramesV1.Point0323
import SourceMainFramesV1.Point0324
import SourceMainFramesV1.Point0325
import SourceMainFramesV1.Point0326
import SourceMainFramesV1.Point0327
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block40
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0320.outputs.2.hi,
 SourceMainFramesV1.Point0321.outputs.2.hi,
 SourceMainFramesV1.Point0322.outputs.2.hi,
 SourceMainFramesV1.Point0323.outputs.2.hi,
 SourceMainFramesV1.Point0324.outputs.2.hi,
 SourceMainFramesV1.Point0325.outputs.2.hi,
 SourceMainFramesV1.Point0326.outputs.2.hi,
 SourceMainFramesV1.Point0327.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 320 ≤ i) (high : i < 328)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=320) domain
     SourceMainFramesV1.Point0320.input_defined SourceMainFramesV1.Point0320.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0320.outputs.2.hi (by
         change SourceMainFramesV1.Point0320.outputs.2.hi ∈ [SourceMainFramesV1.Point0320.outputs.2.hi, SourceMainFramesV1.Point0321.outputs.2.hi, SourceMainFramesV1.Point0322.outputs.2.hi, SourceMainFramesV1.Point0323.outputs.2.hi, SourceMainFramesV1.Point0324.outputs.2.hi, SourceMainFramesV1.Point0325.outputs.2.hi, SourceMainFramesV1.Point0326.outputs.2.hi, SourceMainFramesV1.Point0327.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=321) domain
     SourceMainFramesV1.Point0321.input_defined SourceMainFramesV1.Point0321.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0321.outputs.2.hi (by
         change SourceMainFramesV1.Point0321.outputs.2.hi ∈ [SourceMainFramesV1.Point0320.outputs.2.hi, SourceMainFramesV1.Point0321.outputs.2.hi, SourceMainFramesV1.Point0322.outputs.2.hi, SourceMainFramesV1.Point0323.outputs.2.hi, SourceMainFramesV1.Point0324.outputs.2.hi, SourceMainFramesV1.Point0325.outputs.2.hi, SourceMainFramesV1.Point0326.outputs.2.hi, SourceMainFramesV1.Point0327.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=322) domain
     SourceMainFramesV1.Point0322.input_defined SourceMainFramesV1.Point0322.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0322.outputs.2.hi (by
         change SourceMainFramesV1.Point0322.outputs.2.hi ∈ [SourceMainFramesV1.Point0320.outputs.2.hi, SourceMainFramesV1.Point0321.outputs.2.hi, SourceMainFramesV1.Point0322.outputs.2.hi, SourceMainFramesV1.Point0323.outputs.2.hi, SourceMainFramesV1.Point0324.outputs.2.hi, SourceMainFramesV1.Point0325.outputs.2.hi, SourceMainFramesV1.Point0326.outputs.2.hi, SourceMainFramesV1.Point0327.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=323) domain
     SourceMainFramesV1.Point0323.input_defined SourceMainFramesV1.Point0323.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0323.outputs.2.hi (by
         change SourceMainFramesV1.Point0323.outputs.2.hi ∈ [SourceMainFramesV1.Point0320.outputs.2.hi, SourceMainFramesV1.Point0321.outputs.2.hi, SourceMainFramesV1.Point0322.outputs.2.hi, SourceMainFramesV1.Point0323.outputs.2.hi, SourceMainFramesV1.Point0324.outputs.2.hi, SourceMainFramesV1.Point0325.outputs.2.hi, SourceMainFramesV1.Point0326.outputs.2.hi, SourceMainFramesV1.Point0327.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=324) domain
     SourceMainFramesV1.Point0324.input_defined SourceMainFramesV1.Point0324.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0324.outputs.2.hi (by
         change SourceMainFramesV1.Point0324.outputs.2.hi ∈ [SourceMainFramesV1.Point0320.outputs.2.hi, SourceMainFramesV1.Point0321.outputs.2.hi, SourceMainFramesV1.Point0322.outputs.2.hi, SourceMainFramesV1.Point0323.outputs.2.hi, SourceMainFramesV1.Point0324.outputs.2.hi, SourceMainFramesV1.Point0325.outputs.2.hi, SourceMainFramesV1.Point0326.outputs.2.hi, SourceMainFramesV1.Point0327.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=325) domain
     SourceMainFramesV1.Point0325.input_defined SourceMainFramesV1.Point0325.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0325.outputs.2.hi (by
         change SourceMainFramesV1.Point0325.outputs.2.hi ∈ [SourceMainFramesV1.Point0320.outputs.2.hi, SourceMainFramesV1.Point0321.outputs.2.hi, SourceMainFramesV1.Point0322.outputs.2.hi, SourceMainFramesV1.Point0323.outputs.2.hi, SourceMainFramesV1.Point0324.outputs.2.hi, SourceMainFramesV1.Point0325.outputs.2.hi, SourceMainFramesV1.Point0326.outputs.2.hi, SourceMainFramesV1.Point0327.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=326) domain
     SourceMainFramesV1.Point0326.input_defined SourceMainFramesV1.Point0326.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0326.outputs.2.hi (by
         change SourceMainFramesV1.Point0326.outputs.2.hi ∈ [SourceMainFramesV1.Point0320.outputs.2.hi, SourceMainFramesV1.Point0321.outputs.2.hi, SourceMainFramesV1.Point0322.outputs.2.hi, SourceMainFramesV1.Point0323.outputs.2.hi, SourceMainFramesV1.Point0324.outputs.2.hi, SourceMainFramesV1.Point0325.outputs.2.hi, SourceMainFramesV1.Point0326.outputs.2.hi, SourceMainFramesV1.Point0327.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=327) domain
     SourceMainFramesV1.Point0327.input_defined SourceMainFramesV1.Point0327.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0327.outputs.2.hi (by
         change SourceMainFramesV1.Point0327.outputs.2.hi ∈ [SourceMainFramesV1.Point0320.outputs.2.hi, SourceMainFramesV1.Point0321.outputs.2.hi, SourceMainFramesV1.Point0322.outputs.2.hi, SourceMainFramesV1.Point0323.outputs.2.hi, SourceMainFramesV1.Point0324.outputs.2.hi, SourceMainFramesV1.Point0325.outputs.2.hi, SourceMainFramesV1.Point0326.outputs.2.hi, SourceMainFramesV1.Point0327.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block40
