/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0192
import SourceMainFramesV1.Point0193
import SourceMainFramesV1.Point0194
import SourceMainFramesV1.Point0195
import SourceMainFramesV1.Point0196
import SourceMainFramesV1.Point0197
import SourceMainFramesV1.Point0198
import SourceMainFramesV1.Point0199
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block24
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0192.outputs.2.hi,
 SourceMainFramesV1.Point0193.outputs.2.hi,
 SourceMainFramesV1.Point0194.outputs.2.hi,
 SourceMainFramesV1.Point0195.outputs.2.hi,
 SourceMainFramesV1.Point0196.outputs.2.hi,
 SourceMainFramesV1.Point0197.outputs.2.hi,
 SourceMainFramesV1.Point0198.outputs.2.hi,
 SourceMainFramesV1.Point0199.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 192 ≤ i) (high : i < 200)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=192) domain
     SourceMainFramesV1.Point0192.input_defined SourceMainFramesV1.Point0192.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0192.outputs.2.hi (by
         change SourceMainFramesV1.Point0192.outputs.2.hi ∈ [SourceMainFramesV1.Point0192.outputs.2.hi, SourceMainFramesV1.Point0193.outputs.2.hi, SourceMainFramesV1.Point0194.outputs.2.hi, SourceMainFramesV1.Point0195.outputs.2.hi, SourceMainFramesV1.Point0196.outputs.2.hi, SourceMainFramesV1.Point0197.outputs.2.hi, SourceMainFramesV1.Point0198.outputs.2.hi, SourceMainFramesV1.Point0199.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=193) domain
     SourceMainFramesV1.Point0193.input_defined SourceMainFramesV1.Point0193.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0193.outputs.2.hi (by
         change SourceMainFramesV1.Point0193.outputs.2.hi ∈ [SourceMainFramesV1.Point0192.outputs.2.hi, SourceMainFramesV1.Point0193.outputs.2.hi, SourceMainFramesV1.Point0194.outputs.2.hi, SourceMainFramesV1.Point0195.outputs.2.hi, SourceMainFramesV1.Point0196.outputs.2.hi, SourceMainFramesV1.Point0197.outputs.2.hi, SourceMainFramesV1.Point0198.outputs.2.hi, SourceMainFramesV1.Point0199.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=194) domain
     SourceMainFramesV1.Point0194.input_defined SourceMainFramesV1.Point0194.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0194.outputs.2.hi (by
         change SourceMainFramesV1.Point0194.outputs.2.hi ∈ [SourceMainFramesV1.Point0192.outputs.2.hi, SourceMainFramesV1.Point0193.outputs.2.hi, SourceMainFramesV1.Point0194.outputs.2.hi, SourceMainFramesV1.Point0195.outputs.2.hi, SourceMainFramesV1.Point0196.outputs.2.hi, SourceMainFramesV1.Point0197.outputs.2.hi, SourceMainFramesV1.Point0198.outputs.2.hi, SourceMainFramesV1.Point0199.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=195) domain
     SourceMainFramesV1.Point0195.input_defined SourceMainFramesV1.Point0195.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0195.outputs.2.hi (by
         change SourceMainFramesV1.Point0195.outputs.2.hi ∈ [SourceMainFramesV1.Point0192.outputs.2.hi, SourceMainFramesV1.Point0193.outputs.2.hi, SourceMainFramesV1.Point0194.outputs.2.hi, SourceMainFramesV1.Point0195.outputs.2.hi, SourceMainFramesV1.Point0196.outputs.2.hi, SourceMainFramesV1.Point0197.outputs.2.hi, SourceMainFramesV1.Point0198.outputs.2.hi, SourceMainFramesV1.Point0199.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=196) domain
     SourceMainFramesV1.Point0196.input_defined SourceMainFramesV1.Point0196.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0196.outputs.2.hi (by
         change SourceMainFramesV1.Point0196.outputs.2.hi ∈ [SourceMainFramesV1.Point0192.outputs.2.hi, SourceMainFramesV1.Point0193.outputs.2.hi, SourceMainFramesV1.Point0194.outputs.2.hi, SourceMainFramesV1.Point0195.outputs.2.hi, SourceMainFramesV1.Point0196.outputs.2.hi, SourceMainFramesV1.Point0197.outputs.2.hi, SourceMainFramesV1.Point0198.outputs.2.hi, SourceMainFramesV1.Point0199.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=197) domain
     SourceMainFramesV1.Point0197.input_defined SourceMainFramesV1.Point0197.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0197.outputs.2.hi (by
         change SourceMainFramesV1.Point0197.outputs.2.hi ∈ [SourceMainFramesV1.Point0192.outputs.2.hi, SourceMainFramesV1.Point0193.outputs.2.hi, SourceMainFramesV1.Point0194.outputs.2.hi, SourceMainFramesV1.Point0195.outputs.2.hi, SourceMainFramesV1.Point0196.outputs.2.hi, SourceMainFramesV1.Point0197.outputs.2.hi, SourceMainFramesV1.Point0198.outputs.2.hi, SourceMainFramesV1.Point0199.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=198) domain
     SourceMainFramesV1.Point0198.input_defined SourceMainFramesV1.Point0198.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0198.outputs.2.hi (by
         change SourceMainFramesV1.Point0198.outputs.2.hi ∈ [SourceMainFramesV1.Point0192.outputs.2.hi, SourceMainFramesV1.Point0193.outputs.2.hi, SourceMainFramesV1.Point0194.outputs.2.hi, SourceMainFramesV1.Point0195.outputs.2.hi, SourceMainFramesV1.Point0196.outputs.2.hi, SourceMainFramesV1.Point0197.outputs.2.hi, SourceMainFramesV1.Point0198.outputs.2.hi, SourceMainFramesV1.Point0199.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=199) domain
     SourceMainFramesV1.Point0199.input_defined SourceMainFramesV1.Point0199.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0199.outputs.2.hi (by
         change SourceMainFramesV1.Point0199.outputs.2.hi ∈ [SourceMainFramesV1.Point0192.outputs.2.hi, SourceMainFramesV1.Point0193.outputs.2.hi, SourceMainFramesV1.Point0194.outputs.2.hi, SourceMainFramesV1.Point0195.outputs.2.hi, SourceMainFramesV1.Point0196.outputs.2.hi, SourceMainFramesV1.Point0197.outputs.2.hi, SourceMainFramesV1.Point0198.outputs.2.hi, SourceMainFramesV1.Point0199.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block24
