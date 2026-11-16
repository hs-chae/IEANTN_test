/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0336
import SourceMainFramesV1.Point0337
import SourceMainFramesV1.Point0338
import SourceMainFramesV1.Point0339
import SourceMainFramesV1.Point0340
import SourceMainFramesV1.Point0341
import SourceMainFramesV1.Point0342
import SourceMainFramesV1.Point0343
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block42
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0336.outputs.2.hi,
 SourceMainFramesV1.Point0337.outputs.2.hi,
 SourceMainFramesV1.Point0338.outputs.2.hi,
 SourceMainFramesV1.Point0339.outputs.2.hi,
 SourceMainFramesV1.Point0340.outputs.2.hi,
 SourceMainFramesV1.Point0341.outputs.2.hi,
 SourceMainFramesV1.Point0342.outputs.2.hi,
 SourceMainFramesV1.Point0343.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 336 ≤ i) (high : i < 344)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=336) domain
     SourceMainFramesV1.Point0336.input_defined SourceMainFramesV1.Point0336.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0336.outputs.2.hi (by
         change SourceMainFramesV1.Point0336.outputs.2.hi ∈ [SourceMainFramesV1.Point0336.outputs.2.hi, SourceMainFramesV1.Point0337.outputs.2.hi, SourceMainFramesV1.Point0338.outputs.2.hi, SourceMainFramesV1.Point0339.outputs.2.hi, SourceMainFramesV1.Point0340.outputs.2.hi, SourceMainFramesV1.Point0341.outputs.2.hi, SourceMainFramesV1.Point0342.outputs.2.hi, SourceMainFramesV1.Point0343.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=337) domain
     SourceMainFramesV1.Point0337.input_defined SourceMainFramesV1.Point0337.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0337.outputs.2.hi (by
         change SourceMainFramesV1.Point0337.outputs.2.hi ∈ [SourceMainFramesV1.Point0336.outputs.2.hi, SourceMainFramesV1.Point0337.outputs.2.hi, SourceMainFramesV1.Point0338.outputs.2.hi, SourceMainFramesV1.Point0339.outputs.2.hi, SourceMainFramesV1.Point0340.outputs.2.hi, SourceMainFramesV1.Point0341.outputs.2.hi, SourceMainFramesV1.Point0342.outputs.2.hi, SourceMainFramesV1.Point0343.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=338) domain
     SourceMainFramesV1.Point0338.input_defined SourceMainFramesV1.Point0338.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0338.outputs.2.hi (by
         change SourceMainFramesV1.Point0338.outputs.2.hi ∈ [SourceMainFramesV1.Point0336.outputs.2.hi, SourceMainFramesV1.Point0337.outputs.2.hi, SourceMainFramesV1.Point0338.outputs.2.hi, SourceMainFramesV1.Point0339.outputs.2.hi, SourceMainFramesV1.Point0340.outputs.2.hi, SourceMainFramesV1.Point0341.outputs.2.hi, SourceMainFramesV1.Point0342.outputs.2.hi, SourceMainFramesV1.Point0343.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=339) domain
     SourceMainFramesV1.Point0339.input_defined SourceMainFramesV1.Point0339.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0339.outputs.2.hi (by
         change SourceMainFramesV1.Point0339.outputs.2.hi ∈ [SourceMainFramesV1.Point0336.outputs.2.hi, SourceMainFramesV1.Point0337.outputs.2.hi, SourceMainFramesV1.Point0338.outputs.2.hi, SourceMainFramesV1.Point0339.outputs.2.hi, SourceMainFramesV1.Point0340.outputs.2.hi, SourceMainFramesV1.Point0341.outputs.2.hi, SourceMainFramesV1.Point0342.outputs.2.hi, SourceMainFramesV1.Point0343.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=340) domain
     SourceMainFramesV1.Point0340.input_defined SourceMainFramesV1.Point0340.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0340.outputs.2.hi (by
         change SourceMainFramesV1.Point0340.outputs.2.hi ∈ [SourceMainFramesV1.Point0336.outputs.2.hi, SourceMainFramesV1.Point0337.outputs.2.hi, SourceMainFramesV1.Point0338.outputs.2.hi, SourceMainFramesV1.Point0339.outputs.2.hi, SourceMainFramesV1.Point0340.outputs.2.hi, SourceMainFramesV1.Point0341.outputs.2.hi, SourceMainFramesV1.Point0342.outputs.2.hi, SourceMainFramesV1.Point0343.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=341) domain
     SourceMainFramesV1.Point0341.input_defined SourceMainFramesV1.Point0341.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0341.outputs.2.hi (by
         change SourceMainFramesV1.Point0341.outputs.2.hi ∈ [SourceMainFramesV1.Point0336.outputs.2.hi, SourceMainFramesV1.Point0337.outputs.2.hi, SourceMainFramesV1.Point0338.outputs.2.hi, SourceMainFramesV1.Point0339.outputs.2.hi, SourceMainFramesV1.Point0340.outputs.2.hi, SourceMainFramesV1.Point0341.outputs.2.hi, SourceMainFramesV1.Point0342.outputs.2.hi, SourceMainFramesV1.Point0343.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=342) domain
     SourceMainFramesV1.Point0342.input_defined SourceMainFramesV1.Point0342.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0342.outputs.2.hi (by
         change SourceMainFramesV1.Point0342.outputs.2.hi ∈ [SourceMainFramesV1.Point0336.outputs.2.hi, SourceMainFramesV1.Point0337.outputs.2.hi, SourceMainFramesV1.Point0338.outputs.2.hi, SourceMainFramesV1.Point0339.outputs.2.hi, SourceMainFramesV1.Point0340.outputs.2.hi, SourceMainFramesV1.Point0341.outputs.2.hi, SourceMainFramesV1.Point0342.outputs.2.hi, SourceMainFramesV1.Point0343.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=343) domain
     SourceMainFramesV1.Point0343.input_defined SourceMainFramesV1.Point0343.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0343.outputs.2.hi (by
         change SourceMainFramesV1.Point0343.outputs.2.hi ∈ [SourceMainFramesV1.Point0336.outputs.2.hi, SourceMainFramesV1.Point0337.outputs.2.hi, SourceMainFramesV1.Point0338.outputs.2.hi, SourceMainFramesV1.Point0339.outputs.2.hi, SourceMainFramesV1.Point0340.outputs.2.hi, SourceMainFramesV1.Point0341.outputs.2.hi, SourceMainFramesV1.Point0342.outputs.2.hi, SourceMainFramesV1.Point0343.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block42
