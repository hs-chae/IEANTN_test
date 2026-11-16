/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0488
import SourceMainFramesV1.Point0489
import SourceMainFramesV1.Point0490
import SourceMainFramesV1.Point0491
import SourceMainFramesV1.Point0492
import SourceMainFramesV1.Point0493
import SourceMainFramesV1.Point0494
import SourceMainFramesV1.Point0495
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block61
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0488.outputs.2.hi,
 SourceMainFramesV1.Point0489.outputs.2.hi,
 SourceMainFramesV1.Point0490.outputs.2.hi,
 SourceMainFramesV1.Point0491.outputs.2.hi,
 SourceMainFramesV1.Point0492.outputs.2.hi,
 SourceMainFramesV1.Point0493.outputs.2.hi,
 SourceMainFramesV1.Point0494.outputs.2.hi,
 SourceMainFramesV1.Point0495.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 488 ≤ i) (high : i < 496)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=488) domain
     SourceMainFramesV1.Point0488.input_defined SourceMainFramesV1.Point0488.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0488.outputs.2.hi (by
         change SourceMainFramesV1.Point0488.outputs.2.hi ∈ [SourceMainFramesV1.Point0488.outputs.2.hi, SourceMainFramesV1.Point0489.outputs.2.hi, SourceMainFramesV1.Point0490.outputs.2.hi, SourceMainFramesV1.Point0491.outputs.2.hi, SourceMainFramesV1.Point0492.outputs.2.hi, SourceMainFramesV1.Point0493.outputs.2.hi, SourceMainFramesV1.Point0494.outputs.2.hi, SourceMainFramesV1.Point0495.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=489) domain
     SourceMainFramesV1.Point0489.input_defined SourceMainFramesV1.Point0489.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0489.outputs.2.hi (by
         change SourceMainFramesV1.Point0489.outputs.2.hi ∈ [SourceMainFramesV1.Point0488.outputs.2.hi, SourceMainFramesV1.Point0489.outputs.2.hi, SourceMainFramesV1.Point0490.outputs.2.hi, SourceMainFramesV1.Point0491.outputs.2.hi, SourceMainFramesV1.Point0492.outputs.2.hi, SourceMainFramesV1.Point0493.outputs.2.hi, SourceMainFramesV1.Point0494.outputs.2.hi, SourceMainFramesV1.Point0495.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=490) domain
     SourceMainFramesV1.Point0490.input_defined SourceMainFramesV1.Point0490.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0490.outputs.2.hi (by
         change SourceMainFramesV1.Point0490.outputs.2.hi ∈ [SourceMainFramesV1.Point0488.outputs.2.hi, SourceMainFramesV1.Point0489.outputs.2.hi, SourceMainFramesV1.Point0490.outputs.2.hi, SourceMainFramesV1.Point0491.outputs.2.hi, SourceMainFramesV1.Point0492.outputs.2.hi, SourceMainFramesV1.Point0493.outputs.2.hi, SourceMainFramesV1.Point0494.outputs.2.hi, SourceMainFramesV1.Point0495.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=491) domain
     SourceMainFramesV1.Point0491.input_defined SourceMainFramesV1.Point0491.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0491.outputs.2.hi (by
         change SourceMainFramesV1.Point0491.outputs.2.hi ∈ [SourceMainFramesV1.Point0488.outputs.2.hi, SourceMainFramesV1.Point0489.outputs.2.hi, SourceMainFramesV1.Point0490.outputs.2.hi, SourceMainFramesV1.Point0491.outputs.2.hi, SourceMainFramesV1.Point0492.outputs.2.hi, SourceMainFramesV1.Point0493.outputs.2.hi, SourceMainFramesV1.Point0494.outputs.2.hi, SourceMainFramesV1.Point0495.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=492) domain
     SourceMainFramesV1.Point0492.input_defined SourceMainFramesV1.Point0492.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0492.outputs.2.hi (by
         change SourceMainFramesV1.Point0492.outputs.2.hi ∈ [SourceMainFramesV1.Point0488.outputs.2.hi, SourceMainFramesV1.Point0489.outputs.2.hi, SourceMainFramesV1.Point0490.outputs.2.hi, SourceMainFramesV1.Point0491.outputs.2.hi, SourceMainFramesV1.Point0492.outputs.2.hi, SourceMainFramesV1.Point0493.outputs.2.hi, SourceMainFramesV1.Point0494.outputs.2.hi, SourceMainFramesV1.Point0495.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=493) domain
     SourceMainFramesV1.Point0493.input_defined SourceMainFramesV1.Point0493.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0493.outputs.2.hi (by
         change SourceMainFramesV1.Point0493.outputs.2.hi ∈ [SourceMainFramesV1.Point0488.outputs.2.hi, SourceMainFramesV1.Point0489.outputs.2.hi, SourceMainFramesV1.Point0490.outputs.2.hi, SourceMainFramesV1.Point0491.outputs.2.hi, SourceMainFramesV1.Point0492.outputs.2.hi, SourceMainFramesV1.Point0493.outputs.2.hi, SourceMainFramesV1.Point0494.outputs.2.hi, SourceMainFramesV1.Point0495.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=494) domain
     SourceMainFramesV1.Point0494.input_defined SourceMainFramesV1.Point0494.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0494.outputs.2.hi (by
         change SourceMainFramesV1.Point0494.outputs.2.hi ∈ [SourceMainFramesV1.Point0488.outputs.2.hi, SourceMainFramesV1.Point0489.outputs.2.hi, SourceMainFramesV1.Point0490.outputs.2.hi, SourceMainFramesV1.Point0491.outputs.2.hi, SourceMainFramesV1.Point0492.outputs.2.hi, SourceMainFramesV1.Point0493.outputs.2.hi, SourceMainFramesV1.Point0494.outputs.2.hi, SourceMainFramesV1.Point0495.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=495) domain
     SourceMainFramesV1.Point0495.input_defined SourceMainFramesV1.Point0495.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0495.outputs.2.hi (by
         change SourceMainFramesV1.Point0495.outputs.2.hi ∈ [SourceMainFramesV1.Point0488.outputs.2.hi, SourceMainFramesV1.Point0489.outputs.2.hi, SourceMainFramesV1.Point0490.outputs.2.hi, SourceMainFramesV1.Point0491.outputs.2.hi, SourceMainFramesV1.Point0492.outputs.2.hi, SourceMainFramesV1.Point0493.outputs.2.hi, SourceMainFramesV1.Point0494.outputs.2.hi, SourceMainFramesV1.Point0495.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block61
