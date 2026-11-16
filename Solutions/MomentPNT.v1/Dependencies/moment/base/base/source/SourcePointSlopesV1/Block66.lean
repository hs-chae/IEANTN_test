/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0528
import SourceMainFramesV1.Point0529
import SourceMainFramesV1.Point0530
import SourceMainFramesV1.Point0531
import SourceMainFramesV1.Point0532
import SourceMainFramesV1.Point0533
import SourceMainFramesV1.Point0534
import SourceMainFramesV1.Point0535
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block66
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0528.outputs.2.hi,
 SourceMainFramesV1.Point0529.outputs.2.hi,
 SourceMainFramesV1.Point0530.outputs.2.hi,
 SourceMainFramesV1.Point0531.outputs.2.hi,
 SourceMainFramesV1.Point0532.outputs.2.hi,
 SourceMainFramesV1.Point0533.outputs.2.hi,
 SourceMainFramesV1.Point0534.outputs.2.hi,
 SourceMainFramesV1.Point0535.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 528 ≤ i) (high : i < 536)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=528) domain
     SourceMainFramesV1.Point0528.input_defined SourceMainFramesV1.Point0528.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0528.outputs.2.hi (by
         change SourceMainFramesV1.Point0528.outputs.2.hi ∈ [SourceMainFramesV1.Point0528.outputs.2.hi, SourceMainFramesV1.Point0529.outputs.2.hi, SourceMainFramesV1.Point0530.outputs.2.hi, SourceMainFramesV1.Point0531.outputs.2.hi, SourceMainFramesV1.Point0532.outputs.2.hi, SourceMainFramesV1.Point0533.outputs.2.hi, SourceMainFramesV1.Point0534.outputs.2.hi, SourceMainFramesV1.Point0535.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=529) domain
     SourceMainFramesV1.Point0529.input_defined SourceMainFramesV1.Point0529.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0529.outputs.2.hi (by
         change SourceMainFramesV1.Point0529.outputs.2.hi ∈ [SourceMainFramesV1.Point0528.outputs.2.hi, SourceMainFramesV1.Point0529.outputs.2.hi, SourceMainFramesV1.Point0530.outputs.2.hi, SourceMainFramesV1.Point0531.outputs.2.hi, SourceMainFramesV1.Point0532.outputs.2.hi, SourceMainFramesV1.Point0533.outputs.2.hi, SourceMainFramesV1.Point0534.outputs.2.hi, SourceMainFramesV1.Point0535.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=530) domain
     SourceMainFramesV1.Point0530.input_defined SourceMainFramesV1.Point0530.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0530.outputs.2.hi (by
         change SourceMainFramesV1.Point0530.outputs.2.hi ∈ [SourceMainFramesV1.Point0528.outputs.2.hi, SourceMainFramesV1.Point0529.outputs.2.hi, SourceMainFramesV1.Point0530.outputs.2.hi, SourceMainFramesV1.Point0531.outputs.2.hi, SourceMainFramesV1.Point0532.outputs.2.hi, SourceMainFramesV1.Point0533.outputs.2.hi, SourceMainFramesV1.Point0534.outputs.2.hi, SourceMainFramesV1.Point0535.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=531) domain
     SourceMainFramesV1.Point0531.input_defined SourceMainFramesV1.Point0531.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0531.outputs.2.hi (by
         change SourceMainFramesV1.Point0531.outputs.2.hi ∈ [SourceMainFramesV1.Point0528.outputs.2.hi, SourceMainFramesV1.Point0529.outputs.2.hi, SourceMainFramesV1.Point0530.outputs.2.hi, SourceMainFramesV1.Point0531.outputs.2.hi, SourceMainFramesV1.Point0532.outputs.2.hi, SourceMainFramesV1.Point0533.outputs.2.hi, SourceMainFramesV1.Point0534.outputs.2.hi, SourceMainFramesV1.Point0535.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=532) domain
     SourceMainFramesV1.Point0532.input_defined SourceMainFramesV1.Point0532.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0532.outputs.2.hi (by
         change SourceMainFramesV1.Point0532.outputs.2.hi ∈ [SourceMainFramesV1.Point0528.outputs.2.hi, SourceMainFramesV1.Point0529.outputs.2.hi, SourceMainFramesV1.Point0530.outputs.2.hi, SourceMainFramesV1.Point0531.outputs.2.hi, SourceMainFramesV1.Point0532.outputs.2.hi, SourceMainFramesV1.Point0533.outputs.2.hi, SourceMainFramesV1.Point0534.outputs.2.hi, SourceMainFramesV1.Point0535.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=533) domain
     SourceMainFramesV1.Point0533.input_defined SourceMainFramesV1.Point0533.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0533.outputs.2.hi (by
         change SourceMainFramesV1.Point0533.outputs.2.hi ∈ [SourceMainFramesV1.Point0528.outputs.2.hi, SourceMainFramesV1.Point0529.outputs.2.hi, SourceMainFramesV1.Point0530.outputs.2.hi, SourceMainFramesV1.Point0531.outputs.2.hi, SourceMainFramesV1.Point0532.outputs.2.hi, SourceMainFramesV1.Point0533.outputs.2.hi, SourceMainFramesV1.Point0534.outputs.2.hi, SourceMainFramesV1.Point0535.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=534) domain
     SourceMainFramesV1.Point0534.input_defined SourceMainFramesV1.Point0534.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0534.outputs.2.hi (by
         change SourceMainFramesV1.Point0534.outputs.2.hi ∈ [SourceMainFramesV1.Point0528.outputs.2.hi, SourceMainFramesV1.Point0529.outputs.2.hi, SourceMainFramesV1.Point0530.outputs.2.hi, SourceMainFramesV1.Point0531.outputs.2.hi, SourceMainFramesV1.Point0532.outputs.2.hi, SourceMainFramesV1.Point0533.outputs.2.hi, SourceMainFramesV1.Point0534.outputs.2.hi, SourceMainFramesV1.Point0535.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=535) domain
     SourceMainFramesV1.Point0535.input_defined SourceMainFramesV1.Point0535.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0535.outputs.2.hi (by
         change SourceMainFramesV1.Point0535.outputs.2.hi ∈ [SourceMainFramesV1.Point0528.outputs.2.hi, SourceMainFramesV1.Point0529.outputs.2.hi, SourceMainFramesV1.Point0530.outputs.2.hi, SourceMainFramesV1.Point0531.outputs.2.hi, SourceMainFramesV1.Point0532.outputs.2.hi, SourceMainFramesV1.Point0533.outputs.2.hi, SourceMainFramesV1.Point0534.outputs.2.hi, SourceMainFramesV1.Point0535.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block66
