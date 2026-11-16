/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0472
import SourceMainFramesV1.Point0473
import SourceMainFramesV1.Point0474
import SourceMainFramesV1.Point0475
import SourceMainFramesV1.Point0476
import SourceMainFramesV1.Point0477
import SourceMainFramesV1.Point0478
import SourceMainFramesV1.Point0479
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block59
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0472.outputs.2.hi,
 SourceMainFramesV1.Point0473.outputs.2.hi,
 SourceMainFramesV1.Point0474.outputs.2.hi,
 SourceMainFramesV1.Point0475.outputs.2.hi,
 SourceMainFramesV1.Point0476.outputs.2.hi,
 SourceMainFramesV1.Point0477.outputs.2.hi,
 SourceMainFramesV1.Point0478.outputs.2.hi,
 SourceMainFramesV1.Point0479.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 472 ≤ i) (high : i < 480)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=472) domain
     SourceMainFramesV1.Point0472.input_defined SourceMainFramesV1.Point0472.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0472.outputs.2.hi (by
         change SourceMainFramesV1.Point0472.outputs.2.hi ∈ [SourceMainFramesV1.Point0472.outputs.2.hi, SourceMainFramesV1.Point0473.outputs.2.hi, SourceMainFramesV1.Point0474.outputs.2.hi, SourceMainFramesV1.Point0475.outputs.2.hi, SourceMainFramesV1.Point0476.outputs.2.hi, SourceMainFramesV1.Point0477.outputs.2.hi, SourceMainFramesV1.Point0478.outputs.2.hi, SourceMainFramesV1.Point0479.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=473) domain
     SourceMainFramesV1.Point0473.input_defined SourceMainFramesV1.Point0473.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0473.outputs.2.hi (by
         change SourceMainFramesV1.Point0473.outputs.2.hi ∈ [SourceMainFramesV1.Point0472.outputs.2.hi, SourceMainFramesV1.Point0473.outputs.2.hi, SourceMainFramesV1.Point0474.outputs.2.hi, SourceMainFramesV1.Point0475.outputs.2.hi, SourceMainFramesV1.Point0476.outputs.2.hi, SourceMainFramesV1.Point0477.outputs.2.hi, SourceMainFramesV1.Point0478.outputs.2.hi, SourceMainFramesV1.Point0479.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=474) domain
     SourceMainFramesV1.Point0474.input_defined SourceMainFramesV1.Point0474.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0474.outputs.2.hi (by
         change SourceMainFramesV1.Point0474.outputs.2.hi ∈ [SourceMainFramesV1.Point0472.outputs.2.hi, SourceMainFramesV1.Point0473.outputs.2.hi, SourceMainFramesV1.Point0474.outputs.2.hi, SourceMainFramesV1.Point0475.outputs.2.hi, SourceMainFramesV1.Point0476.outputs.2.hi, SourceMainFramesV1.Point0477.outputs.2.hi, SourceMainFramesV1.Point0478.outputs.2.hi, SourceMainFramesV1.Point0479.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=475) domain
     SourceMainFramesV1.Point0475.input_defined SourceMainFramesV1.Point0475.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0475.outputs.2.hi (by
         change SourceMainFramesV1.Point0475.outputs.2.hi ∈ [SourceMainFramesV1.Point0472.outputs.2.hi, SourceMainFramesV1.Point0473.outputs.2.hi, SourceMainFramesV1.Point0474.outputs.2.hi, SourceMainFramesV1.Point0475.outputs.2.hi, SourceMainFramesV1.Point0476.outputs.2.hi, SourceMainFramesV1.Point0477.outputs.2.hi, SourceMainFramesV1.Point0478.outputs.2.hi, SourceMainFramesV1.Point0479.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=476) domain
     SourceMainFramesV1.Point0476.input_defined SourceMainFramesV1.Point0476.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0476.outputs.2.hi (by
         change SourceMainFramesV1.Point0476.outputs.2.hi ∈ [SourceMainFramesV1.Point0472.outputs.2.hi, SourceMainFramesV1.Point0473.outputs.2.hi, SourceMainFramesV1.Point0474.outputs.2.hi, SourceMainFramesV1.Point0475.outputs.2.hi, SourceMainFramesV1.Point0476.outputs.2.hi, SourceMainFramesV1.Point0477.outputs.2.hi, SourceMainFramesV1.Point0478.outputs.2.hi, SourceMainFramesV1.Point0479.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=477) domain
     SourceMainFramesV1.Point0477.input_defined SourceMainFramesV1.Point0477.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0477.outputs.2.hi (by
         change SourceMainFramesV1.Point0477.outputs.2.hi ∈ [SourceMainFramesV1.Point0472.outputs.2.hi, SourceMainFramesV1.Point0473.outputs.2.hi, SourceMainFramesV1.Point0474.outputs.2.hi, SourceMainFramesV1.Point0475.outputs.2.hi, SourceMainFramesV1.Point0476.outputs.2.hi, SourceMainFramesV1.Point0477.outputs.2.hi, SourceMainFramesV1.Point0478.outputs.2.hi, SourceMainFramesV1.Point0479.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=478) domain
     SourceMainFramesV1.Point0478.input_defined SourceMainFramesV1.Point0478.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0478.outputs.2.hi (by
         change SourceMainFramesV1.Point0478.outputs.2.hi ∈ [SourceMainFramesV1.Point0472.outputs.2.hi, SourceMainFramesV1.Point0473.outputs.2.hi, SourceMainFramesV1.Point0474.outputs.2.hi, SourceMainFramesV1.Point0475.outputs.2.hi, SourceMainFramesV1.Point0476.outputs.2.hi, SourceMainFramesV1.Point0477.outputs.2.hi, SourceMainFramesV1.Point0478.outputs.2.hi, SourceMainFramesV1.Point0479.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=479) domain
     SourceMainFramesV1.Point0479.input_defined SourceMainFramesV1.Point0479.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0479.outputs.2.hi (by
         change SourceMainFramesV1.Point0479.outputs.2.hi ∈ [SourceMainFramesV1.Point0472.outputs.2.hi, SourceMainFramesV1.Point0473.outputs.2.hi, SourceMainFramesV1.Point0474.outputs.2.hi, SourceMainFramesV1.Point0475.outputs.2.hi, SourceMainFramesV1.Point0476.outputs.2.hi, SourceMainFramesV1.Point0477.outputs.2.hi, SourceMainFramesV1.Point0478.outputs.2.hi, SourceMainFramesV1.Point0479.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block59
