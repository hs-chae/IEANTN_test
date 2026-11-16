/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0240
import SourceMainFramesV1.Point0241
import SourceMainFramesV1.Point0242
import SourceMainFramesV1.Point0243
import SourceMainFramesV1.Point0244
import SourceMainFramesV1.Point0245
import SourceMainFramesV1.Point0246
import SourceMainFramesV1.Point0247
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block30
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0240.outputs.2.hi,
 SourceMainFramesV1.Point0241.outputs.2.hi,
 SourceMainFramesV1.Point0242.outputs.2.hi,
 SourceMainFramesV1.Point0243.outputs.2.hi,
 SourceMainFramesV1.Point0244.outputs.2.hi,
 SourceMainFramesV1.Point0245.outputs.2.hi,
 SourceMainFramesV1.Point0246.outputs.2.hi,
 SourceMainFramesV1.Point0247.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 240 ≤ i) (high : i < 248)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=240) domain
     SourceMainFramesV1.Point0240.input_defined SourceMainFramesV1.Point0240.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0240.outputs.2.hi (by
         change SourceMainFramesV1.Point0240.outputs.2.hi ∈ [SourceMainFramesV1.Point0240.outputs.2.hi, SourceMainFramesV1.Point0241.outputs.2.hi, SourceMainFramesV1.Point0242.outputs.2.hi, SourceMainFramesV1.Point0243.outputs.2.hi, SourceMainFramesV1.Point0244.outputs.2.hi, SourceMainFramesV1.Point0245.outputs.2.hi, SourceMainFramesV1.Point0246.outputs.2.hi, SourceMainFramesV1.Point0247.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=241) domain
     SourceMainFramesV1.Point0241.input_defined SourceMainFramesV1.Point0241.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0241.outputs.2.hi (by
         change SourceMainFramesV1.Point0241.outputs.2.hi ∈ [SourceMainFramesV1.Point0240.outputs.2.hi, SourceMainFramesV1.Point0241.outputs.2.hi, SourceMainFramesV1.Point0242.outputs.2.hi, SourceMainFramesV1.Point0243.outputs.2.hi, SourceMainFramesV1.Point0244.outputs.2.hi, SourceMainFramesV1.Point0245.outputs.2.hi, SourceMainFramesV1.Point0246.outputs.2.hi, SourceMainFramesV1.Point0247.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=242) domain
     SourceMainFramesV1.Point0242.input_defined SourceMainFramesV1.Point0242.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0242.outputs.2.hi (by
         change SourceMainFramesV1.Point0242.outputs.2.hi ∈ [SourceMainFramesV1.Point0240.outputs.2.hi, SourceMainFramesV1.Point0241.outputs.2.hi, SourceMainFramesV1.Point0242.outputs.2.hi, SourceMainFramesV1.Point0243.outputs.2.hi, SourceMainFramesV1.Point0244.outputs.2.hi, SourceMainFramesV1.Point0245.outputs.2.hi, SourceMainFramesV1.Point0246.outputs.2.hi, SourceMainFramesV1.Point0247.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=243) domain
     SourceMainFramesV1.Point0243.input_defined SourceMainFramesV1.Point0243.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0243.outputs.2.hi (by
         change SourceMainFramesV1.Point0243.outputs.2.hi ∈ [SourceMainFramesV1.Point0240.outputs.2.hi, SourceMainFramesV1.Point0241.outputs.2.hi, SourceMainFramesV1.Point0242.outputs.2.hi, SourceMainFramesV1.Point0243.outputs.2.hi, SourceMainFramesV1.Point0244.outputs.2.hi, SourceMainFramesV1.Point0245.outputs.2.hi, SourceMainFramesV1.Point0246.outputs.2.hi, SourceMainFramesV1.Point0247.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=244) domain
     SourceMainFramesV1.Point0244.input_defined SourceMainFramesV1.Point0244.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0244.outputs.2.hi (by
         change SourceMainFramesV1.Point0244.outputs.2.hi ∈ [SourceMainFramesV1.Point0240.outputs.2.hi, SourceMainFramesV1.Point0241.outputs.2.hi, SourceMainFramesV1.Point0242.outputs.2.hi, SourceMainFramesV1.Point0243.outputs.2.hi, SourceMainFramesV1.Point0244.outputs.2.hi, SourceMainFramesV1.Point0245.outputs.2.hi, SourceMainFramesV1.Point0246.outputs.2.hi, SourceMainFramesV1.Point0247.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=245) domain
     SourceMainFramesV1.Point0245.input_defined SourceMainFramesV1.Point0245.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0245.outputs.2.hi (by
         change SourceMainFramesV1.Point0245.outputs.2.hi ∈ [SourceMainFramesV1.Point0240.outputs.2.hi, SourceMainFramesV1.Point0241.outputs.2.hi, SourceMainFramesV1.Point0242.outputs.2.hi, SourceMainFramesV1.Point0243.outputs.2.hi, SourceMainFramesV1.Point0244.outputs.2.hi, SourceMainFramesV1.Point0245.outputs.2.hi, SourceMainFramesV1.Point0246.outputs.2.hi, SourceMainFramesV1.Point0247.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=246) domain
     SourceMainFramesV1.Point0246.input_defined SourceMainFramesV1.Point0246.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0246.outputs.2.hi (by
         change SourceMainFramesV1.Point0246.outputs.2.hi ∈ [SourceMainFramesV1.Point0240.outputs.2.hi, SourceMainFramesV1.Point0241.outputs.2.hi, SourceMainFramesV1.Point0242.outputs.2.hi, SourceMainFramesV1.Point0243.outputs.2.hi, SourceMainFramesV1.Point0244.outputs.2.hi, SourceMainFramesV1.Point0245.outputs.2.hi, SourceMainFramesV1.Point0246.outputs.2.hi, SourceMainFramesV1.Point0247.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=247) domain
     SourceMainFramesV1.Point0247.input_defined SourceMainFramesV1.Point0247.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0247.outputs.2.hi (by
         change SourceMainFramesV1.Point0247.outputs.2.hi ∈ [SourceMainFramesV1.Point0240.outputs.2.hi, SourceMainFramesV1.Point0241.outputs.2.hi, SourceMainFramesV1.Point0242.outputs.2.hi, SourceMainFramesV1.Point0243.outputs.2.hi, SourceMainFramesV1.Point0244.outputs.2.hi, SourceMainFramesV1.Point0245.outputs.2.hi, SourceMainFramesV1.Point0246.outputs.2.hi, SourceMainFramesV1.Point0247.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block30
