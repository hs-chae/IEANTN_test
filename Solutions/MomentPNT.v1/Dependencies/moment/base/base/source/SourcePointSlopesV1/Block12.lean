/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0096
import SourceMainFramesV1.Point0097
import SourceMainFramesV1.Point0098
import SourceMainFramesV1.Point0099
import SourceMainFramesV1.Point0100
import SourceMainFramesV1.Point0101
import SourceMainFramesV1.Point0102
import SourceMainFramesV1.Point0103
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block12
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0096.outputs.2.hi,
 SourceMainFramesV1.Point0097.outputs.2.hi,
 SourceMainFramesV1.Point0098.outputs.2.hi,
 SourceMainFramesV1.Point0099.outputs.2.hi,
 SourceMainFramesV1.Point0100.outputs.2.hi,
 SourceMainFramesV1.Point0101.outputs.2.hi,
 SourceMainFramesV1.Point0102.outputs.2.hi,
 SourceMainFramesV1.Point0103.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 96 ≤ i) (high : i < 104)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=96) domain
     SourceMainFramesV1.Point0096.input_defined SourceMainFramesV1.Point0096.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0096.outputs.2.hi (by
         change SourceMainFramesV1.Point0096.outputs.2.hi ∈ [SourceMainFramesV1.Point0096.outputs.2.hi, SourceMainFramesV1.Point0097.outputs.2.hi, SourceMainFramesV1.Point0098.outputs.2.hi, SourceMainFramesV1.Point0099.outputs.2.hi, SourceMainFramesV1.Point0100.outputs.2.hi, SourceMainFramesV1.Point0101.outputs.2.hi, SourceMainFramesV1.Point0102.outputs.2.hi, SourceMainFramesV1.Point0103.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=97) domain
     SourceMainFramesV1.Point0097.input_defined SourceMainFramesV1.Point0097.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0097.outputs.2.hi (by
         change SourceMainFramesV1.Point0097.outputs.2.hi ∈ [SourceMainFramesV1.Point0096.outputs.2.hi, SourceMainFramesV1.Point0097.outputs.2.hi, SourceMainFramesV1.Point0098.outputs.2.hi, SourceMainFramesV1.Point0099.outputs.2.hi, SourceMainFramesV1.Point0100.outputs.2.hi, SourceMainFramesV1.Point0101.outputs.2.hi, SourceMainFramesV1.Point0102.outputs.2.hi, SourceMainFramesV1.Point0103.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=98) domain
     SourceMainFramesV1.Point0098.input_defined SourceMainFramesV1.Point0098.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0098.outputs.2.hi (by
         change SourceMainFramesV1.Point0098.outputs.2.hi ∈ [SourceMainFramesV1.Point0096.outputs.2.hi, SourceMainFramesV1.Point0097.outputs.2.hi, SourceMainFramesV1.Point0098.outputs.2.hi, SourceMainFramesV1.Point0099.outputs.2.hi, SourceMainFramesV1.Point0100.outputs.2.hi, SourceMainFramesV1.Point0101.outputs.2.hi, SourceMainFramesV1.Point0102.outputs.2.hi, SourceMainFramesV1.Point0103.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=99) domain
     SourceMainFramesV1.Point0099.input_defined SourceMainFramesV1.Point0099.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0099.outputs.2.hi (by
         change SourceMainFramesV1.Point0099.outputs.2.hi ∈ [SourceMainFramesV1.Point0096.outputs.2.hi, SourceMainFramesV1.Point0097.outputs.2.hi, SourceMainFramesV1.Point0098.outputs.2.hi, SourceMainFramesV1.Point0099.outputs.2.hi, SourceMainFramesV1.Point0100.outputs.2.hi, SourceMainFramesV1.Point0101.outputs.2.hi, SourceMainFramesV1.Point0102.outputs.2.hi, SourceMainFramesV1.Point0103.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=100) domain
     SourceMainFramesV1.Point0100.input_defined SourceMainFramesV1.Point0100.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0100.outputs.2.hi (by
         change SourceMainFramesV1.Point0100.outputs.2.hi ∈ [SourceMainFramesV1.Point0096.outputs.2.hi, SourceMainFramesV1.Point0097.outputs.2.hi, SourceMainFramesV1.Point0098.outputs.2.hi, SourceMainFramesV1.Point0099.outputs.2.hi, SourceMainFramesV1.Point0100.outputs.2.hi, SourceMainFramesV1.Point0101.outputs.2.hi, SourceMainFramesV1.Point0102.outputs.2.hi, SourceMainFramesV1.Point0103.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=101) domain
     SourceMainFramesV1.Point0101.input_defined SourceMainFramesV1.Point0101.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0101.outputs.2.hi (by
         change SourceMainFramesV1.Point0101.outputs.2.hi ∈ [SourceMainFramesV1.Point0096.outputs.2.hi, SourceMainFramesV1.Point0097.outputs.2.hi, SourceMainFramesV1.Point0098.outputs.2.hi, SourceMainFramesV1.Point0099.outputs.2.hi, SourceMainFramesV1.Point0100.outputs.2.hi, SourceMainFramesV1.Point0101.outputs.2.hi, SourceMainFramesV1.Point0102.outputs.2.hi, SourceMainFramesV1.Point0103.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=102) domain
     SourceMainFramesV1.Point0102.input_defined SourceMainFramesV1.Point0102.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0102.outputs.2.hi (by
         change SourceMainFramesV1.Point0102.outputs.2.hi ∈ [SourceMainFramesV1.Point0096.outputs.2.hi, SourceMainFramesV1.Point0097.outputs.2.hi, SourceMainFramesV1.Point0098.outputs.2.hi, SourceMainFramesV1.Point0099.outputs.2.hi, SourceMainFramesV1.Point0100.outputs.2.hi, SourceMainFramesV1.Point0101.outputs.2.hi, SourceMainFramesV1.Point0102.outputs.2.hi, SourceMainFramesV1.Point0103.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=103) domain
     SourceMainFramesV1.Point0103.input_defined SourceMainFramesV1.Point0103.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0103.outputs.2.hi (by
         change SourceMainFramesV1.Point0103.outputs.2.hi ∈ [SourceMainFramesV1.Point0096.outputs.2.hi, SourceMainFramesV1.Point0097.outputs.2.hi, SourceMainFramesV1.Point0098.outputs.2.hi, SourceMainFramesV1.Point0099.outputs.2.hi, SourceMainFramesV1.Point0100.outputs.2.hi, SourceMainFramesV1.Point0101.outputs.2.hi, SourceMainFramesV1.Point0102.outputs.2.hi, SourceMainFramesV1.Point0103.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block12
