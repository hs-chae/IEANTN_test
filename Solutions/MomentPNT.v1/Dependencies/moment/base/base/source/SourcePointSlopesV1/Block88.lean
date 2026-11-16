/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0704
import SourceMainFramesV1.Point0705
import SourceMainFramesV1.Point0706
import SourceMainFramesV1.Point0707
import SourceMainFramesV1.Point0708
import SourceMainFramesV1.Point0709
import SourceMainFramesV1.Point0710
import SourceMainFramesV1.Point0711
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block88
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0704.outputs.2.hi,
 SourceMainFramesV1.Point0705.outputs.2.hi,
 SourceMainFramesV1.Point0706.outputs.2.hi,
 SourceMainFramesV1.Point0707.outputs.2.hi,
 SourceMainFramesV1.Point0708.outputs.2.hi,
 SourceMainFramesV1.Point0709.outputs.2.hi,
 SourceMainFramesV1.Point0710.outputs.2.hi,
 SourceMainFramesV1.Point0711.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 704 ≤ i) (high : i < 712)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=704) domain
     SourceMainFramesV1.Point0704.input_defined SourceMainFramesV1.Point0704.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0704.outputs.2.hi (by
         change SourceMainFramesV1.Point0704.outputs.2.hi ∈ [SourceMainFramesV1.Point0704.outputs.2.hi, SourceMainFramesV1.Point0705.outputs.2.hi, SourceMainFramesV1.Point0706.outputs.2.hi, SourceMainFramesV1.Point0707.outputs.2.hi, SourceMainFramesV1.Point0708.outputs.2.hi, SourceMainFramesV1.Point0709.outputs.2.hi, SourceMainFramesV1.Point0710.outputs.2.hi, SourceMainFramesV1.Point0711.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=705) domain
     SourceMainFramesV1.Point0705.input_defined SourceMainFramesV1.Point0705.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0705.outputs.2.hi (by
         change SourceMainFramesV1.Point0705.outputs.2.hi ∈ [SourceMainFramesV1.Point0704.outputs.2.hi, SourceMainFramesV1.Point0705.outputs.2.hi, SourceMainFramesV1.Point0706.outputs.2.hi, SourceMainFramesV1.Point0707.outputs.2.hi, SourceMainFramesV1.Point0708.outputs.2.hi, SourceMainFramesV1.Point0709.outputs.2.hi, SourceMainFramesV1.Point0710.outputs.2.hi, SourceMainFramesV1.Point0711.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=706) domain
     SourceMainFramesV1.Point0706.input_defined SourceMainFramesV1.Point0706.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0706.outputs.2.hi (by
         change SourceMainFramesV1.Point0706.outputs.2.hi ∈ [SourceMainFramesV1.Point0704.outputs.2.hi, SourceMainFramesV1.Point0705.outputs.2.hi, SourceMainFramesV1.Point0706.outputs.2.hi, SourceMainFramesV1.Point0707.outputs.2.hi, SourceMainFramesV1.Point0708.outputs.2.hi, SourceMainFramesV1.Point0709.outputs.2.hi, SourceMainFramesV1.Point0710.outputs.2.hi, SourceMainFramesV1.Point0711.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=707) domain
     SourceMainFramesV1.Point0707.input_defined SourceMainFramesV1.Point0707.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0707.outputs.2.hi (by
         change SourceMainFramesV1.Point0707.outputs.2.hi ∈ [SourceMainFramesV1.Point0704.outputs.2.hi, SourceMainFramesV1.Point0705.outputs.2.hi, SourceMainFramesV1.Point0706.outputs.2.hi, SourceMainFramesV1.Point0707.outputs.2.hi, SourceMainFramesV1.Point0708.outputs.2.hi, SourceMainFramesV1.Point0709.outputs.2.hi, SourceMainFramesV1.Point0710.outputs.2.hi, SourceMainFramesV1.Point0711.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=708) domain
     SourceMainFramesV1.Point0708.input_defined SourceMainFramesV1.Point0708.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0708.outputs.2.hi (by
         change SourceMainFramesV1.Point0708.outputs.2.hi ∈ [SourceMainFramesV1.Point0704.outputs.2.hi, SourceMainFramesV1.Point0705.outputs.2.hi, SourceMainFramesV1.Point0706.outputs.2.hi, SourceMainFramesV1.Point0707.outputs.2.hi, SourceMainFramesV1.Point0708.outputs.2.hi, SourceMainFramesV1.Point0709.outputs.2.hi, SourceMainFramesV1.Point0710.outputs.2.hi, SourceMainFramesV1.Point0711.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=709) domain
     SourceMainFramesV1.Point0709.input_defined SourceMainFramesV1.Point0709.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0709.outputs.2.hi (by
         change SourceMainFramesV1.Point0709.outputs.2.hi ∈ [SourceMainFramesV1.Point0704.outputs.2.hi, SourceMainFramesV1.Point0705.outputs.2.hi, SourceMainFramesV1.Point0706.outputs.2.hi, SourceMainFramesV1.Point0707.outputs.2.hi, SourceMainFramesV1.Point0708.outputs.2.hi, SourceMainFramesV1.Point0709.outputs.2.hi, SourceMainFramesV1.Point0710.outputs.2.hi, SourceMainFramesV1.Point0711.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=710) domain
     SourceMainFramesV1.Point0710.input_defined SourceMainFramesV1.Point0710.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0710.outputs.2.hi (by
         change SourceMainFramesV1.Point0710.outputs.2.hi ∈ [SourceMainFramesV1.Point0704.outputs.2.hi, SourceMainFramesV1.Point0705.outputs.2.hi, SourceMainFramesV1.Point0706.outputs.2.hi, SourceMainFramesV1.Point0707.outputs.2.hi, SourceMainFramesV1.Point0708.outputs.2.hi, SourceMainFramesV1.Point0709.outputs.2.hi, SourceMainFramesV1.Point0710.outputs.2.hi, SourceMainFramesV1.Point0711.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=711) domain
     SourceMainFramesV1.Point0711.input_defined SourceMainFramesV1.Point0711.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0711.outputs.2.hi (by
         change SourceMainFramesV1.Point0711.outputs.2.hi ∈ [SourceMainFramesV1.Point0704.outputs.2.hi, SourceMainFramesV1.Point0705.outputs.2.hi, SourceMainFramesV1.Point0706.outputs.2.hi, SourceMainFramesV1.Point0707.outputs.2.hi, SourceMainFramesV1.Point0708.outputs.2.hi, SourceMainFramesV1.Point0709.outputs.2.hi, SourceMainFramesV1.Point0710.outputs.2.hi, SourceMainFramesV1.Point0711.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block88
