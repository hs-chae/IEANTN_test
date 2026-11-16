/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0136
import SourceMainFramesV1.Point0137
import SourceMainFramesV1.Point0138
import SourceMainFramesV1.Point0139
import SourceMainFramesV1.Point0140
import SourceMainFramesV1.Point0141
import SourceMainFramesV1.Point0142
import SourceMainFramesV1.Point0143
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block17
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0136.outputs.2.hi,
 SourceMainFramesV1.Point0137.outputs.2.hi,
 SourceMainFramesV1.Point0138.outputs.2.hi,
 SourceMainFramesV1.Point0139.outputs.2.hi,
 SourceMainFramesV1.Point0140.outputs.2.hi,
 SourceMainFramesV1.Point0141.outputs.2.hi,
 SourceMainFramesV1.Point0142.outputs.2.hi,
 SourceMainFramesV1.Point0143.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 136 ≤ i) (high : i < 144)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=136) domain
     SourceMainFramesV1.Point0136.input_defined SourceMainFramesV1.Point0136.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0136.outputs.2.hi (by
         change SourceMainFramesV1.Point0136.outputs.2.hi ∈ [SourceMainFramesV1.Point0136.outputs.2.hi, SourceMainFramesV1.Point0137.outputs.2.hi, SourceMainFramesV1.Point0138.outputs.2.hi, SourceMainFramesV1.Point0139.outputs.2.hi, SourceMainFramesV1.Point0140.outputs.2.hi, SourceMainFramesV1.Point0141.outputs.2.hi, SourceMainFramesV1.Point0142.outputs.2.hi, SourceMainFramesV1.Point0143.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=137) domain
     SourceMainFramesV1.Point0137.input_defined SourceMainFramesV1.Point0137.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0137.outputs.2.hi (by
         change SourceMainFramesV1.Point0137.outputs.2.hi ∈ [SourceMainFramesV1.Point0136.outputs.2.hi, SourceMainFramesV1.Point0137.outputs.2.hi, SourceMainFramesV1.Point0138.outputs.2.hi, SourceMainFramesV1.Point0139.outputs.2.hi, SourceMainFramesV1.Point0140.outputs.2.hi, SourceMainFramesV1.Point0141.outputs.2.hi, SourceMainFramesV1.Point0142.outputs.2.hi, SourceMainFramesV1.Point0143.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=138) domain
     SourceMainFramesV1.Point0138.input_defined SourceMainFramesV1.Point0138.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0138.outputs.2.hi (by
         change SourceMainFramesV1.Point0138.outputs.2.hi ∈ [SourceMainFramesV1.Point0136.outputs.2.hi, SourceMainFramesV1.Point0137.outputs.2.hi, SourceMainFramesV1.Point0138.outputs.2.hi, SourceMainFramesV1.Point0139.outputs.2.hi, SourceMainFramesV1.Point0140.outputs.2.hi, SourceMainFramesV1.Point0141.outputs.2.hi, SourceMainFramesV1.Point0142.outputs.2.hi, SourceMainFramesV1.Point0143.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=139) domain
     SourceMainFramesV1.Point0139.input_defined SourceMainFramesV1.Point0139.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0139.outputs.2.hi (by
         change SourceMainFramesV1.Point0139.outputs.2.hi ∈ [SourceMainFramesV1.Point0136.outputs.2.hi, SourceMainFramesV1.Point0137.outputs.2.hi, SourceMainFramesV1.Point0138.outputs.2.hi, SourceMainFramesV1.Point0139.outputs.2.hi, SourceMainFramesV1.Point0140.outputs.2.hi, SourceMainFramesV1.Point0141.outputs.2.hi, SourceMainFramesV1.Point0142.outputs.2.hi, SourceMainFramesV1.Point0143.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=140) domain
     SourceMainFramesV1.Point0140.input_defined SourceMainFramesV1.Point0140.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0140.outputs.2.hi (by
         change SourceMainFramesV1.Point0140.outputs.2.hi ∈ [SourceMainFramesV1.Point0136.outputs.2.hi, SourceMainFramesV1.Point0137.outputs.2.hi, SourceMainFramesV1.Point0138.outputs.2.hi, SourceMainFramesV1.Point0139.outputs.2.hi, SourceMainFramesV1.Point0140.outputs.2.hi, SourceMainFramesV1.Point0141.outputs.2.hi, SourceMainFramesV1.Point0142.outputs.2.hi, SourceMainFramesV1.Point0143.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=141) domain
     SourceMainFramesV1.Point0141.input_defined SourceMainFramesV1.Point0141.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0141.outputs.2.hi (by
         change SourceMainFramesV1.Point0141.outputs.2.hi ∈ [SourceMainFramesV1.Point0136.outputs.2.hi, SourceMainFramesV1.Point0137.outputs.2.hi, SourceMainFramesV1.Point0138.outputs.2.hi, SourceMainFramesV1.Point0139.outputs.2.hi, SourceMainFramesV1.Point0140.outputs.2.hi, SourceMainFramesV1.Point0141.outputs.2.hi, SourceMainFramesV1.Point0142.outputs.2.hi, SourceMainFramesV1.Point0143.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=142) domain
     SourceMainFramesV1.Point0142.input_defined SourceMainFramesV1.Point0142.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0142.outputs.2.hi (by
         change SourceMainFramesV1.Point0142.outputs.2.hi ∈ [SourceMainFramesV1.Point0136.outputs.2.hi, SourceMainFramesV1.Point0137.outputs.2.hi, SourceMainFramesV1.Point0138.outputs.2.hi, SourceMainFramesV1.Point0139.outputs.2.hi, SourceMainFramesV1.Point0140.outputs.2.hi, SourceMainFramesV1.Point0141.outputs.2.hi, SourceMainFramesV1.Point0142.outputs.2.hi, SourceMainFramesV1.Point0143.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=143) domain
     SourceMainFramesV1.Point0143.input_defined SourceMainFramesV1.Point0143.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0143.outputs.2.hi (by
         change SourceMainFramesV1.Point0143.outputs.2.hi ∈ [SourceMainFramesV1.Point0136.outputs.2.hi, SourceMainFramesV1.Point0137.outputs.2.hi, SourceMainFramesV1.Point0138.outputs.2.hi, SourceMainFramesV1.Point0139.outputs.2.hi, SourceMainFramesV1.Point0140.outputs.2.hi, SourceMainFramesV1.Point0141.outputs.2.hi, SourceMainFramesV1.Point0142.outputs.2.hi, SourceMainFramesV1.Point0143.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block17
