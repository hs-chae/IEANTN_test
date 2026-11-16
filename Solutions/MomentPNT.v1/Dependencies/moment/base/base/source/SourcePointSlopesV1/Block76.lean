/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0608
import SourceMainFramesV1.Point0609
import SourceMainFramesV1.Point0610
import SourceMainFramesV1.Point0611
import SourceMainFramesV1.Point0612
import SourceMainFramesV1.Point0613
import SourceMainFramesV1.Point0614
import SourceMainFramesV1.Point0615
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block76
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0608.outputs.2.hi,
 SourceMainFramesV1.Point0609.outputs.2.hi,
 SourceMainFramesV1.Point0610.outputs.2.hi,
 SourceMainFramesV1.Point0611.outputs.2.hi,
 SourceMainFramesV1.Point0612.outputs.2.hi,
 SourceMainFramesV1.Point0613.outputs.2.hi,
 SourceMainFramesV1.Point0614.outputs.2.hi,
 SourceMainFramesV1.Point0615.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 608 ≤ i) (high : i < 616)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=608) domain
     SourceMainFramesV1.Point0608.input_defined SourceMainFramesV1.Point0608.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0608.outputs.2.hi (by
         change SourceMainFramesV1.Point0608.outputs.2.hi ∈ [SourceMainFramesV1.Point0608.outputs.2.hi, SourceMainFramesV1.Point0609.outputs.2.hi, SourceMainFramesV1.Point0610.outputs.2.hi, SourceMainFramesV1.Point0611.outputs.2.hi, SourceMainFramesV1.Point0612.outputs.2.hi, SourceMainFramesV1.Point0613.outputs.2.hi, SourceMainFramesV1.Point0614.outputs.2.hi, SourceMainFramesV1.Point0615.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=609) domain
     SourceMainFramesV1.Point0609.input_defined SourceMainFramesV1.Point0609.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0609.outputs.2.hi (by
         change SourceMainFramesV1.Point0609.outputs.2.hi ∈ [SourceMainFramesV1.Point0608.outputs.2.hi, SourceMainFramesV1.Point0609.outputs.2.hi, SourceMainFramesV1.Point0610.outputs.2.hi, SourceMainFramesV1.Point0611.outputs.2.hi, SourceMainFramesV1.Point0612.outputs.2.hi, SourceMainFramesV1.Point0613.outputs.2.hi, SourceMainFramesV1.Point0614.outputs.2.hi, SourceMainFramesV1.Point0615.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=610) domain
     SourceMainFramesV1.Point0610.input_defined SourceMainFramesV1.Point0610.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0610.outputs.2.hi (by
         change SourceMainFramesV1.Point0610.outputs.2.hi ∈ [SourceMainFramesV1.Point0608.outputs.2.hi, SourceMainFramesV1.Point0609.outputs.2.hi, SourceMainFramesV1.Point0610.outputs.2.hi, SourceMainFramesV1.Point0611.outputs.2.hi, SourceMainFramesV1.Point0612.outputs.2.hi, SourceMainFramesV1.Point0613.outputs.2.hi, SourceMainFramesV1.Point0614.outputs.2.hi, SourceMainFramesV1.Point0615.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=611) domain
     SourceMainFramesV1.Point0611.input_defined SourceMainFramesV1.Point0611.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0611.outputs.2.hi (by
         change SourceMainFramesV1.Point0611.outputs.2.hi ∈ [SourceMainFramesV1.Point0608.outputs.2.hi, SourceMainFramesV1.Point0609.outputs.2.hi, SourceMainFramesV1.Point0610.outputs.2.hi, SourceMainFramesV1.Point0611.outputs.2.hi, SourceMainFramesV1.Point0612.outputs.2.hi, SourceMainFramesV1.Point0613.outputs.2.hi, SourceMainFramesV1.Point0614.outputs.2.hi, SourceMainFramesV1.Point0615.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=612) domain
     SourceMainFramesV1.Point0612.input_defined SourceMainFramesV1.Point0612.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0612.outputs.2.hi (by
         change SourceMainFramesV1.Point0612.outputs.2.hi ∈ [SourceMainFramesV1.Point0608.outputs.2.hi, SourceMainFramesV1.Point0609.outputs.2.hi, SourceMainFramesV1.Point0610.outputs.2.hi, SourceMainFramesV1.Point0611.outputs.2.hi, SourceMainFramesV1.Point0612.outputs.2.hi, SourceMainFramesV1.Point0613.outputs.2.hi, SourceMainFramesV1.Point0614.outputs.2.hi, SourceMainFramesV1.Point0615.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=613) domain
     SourceMainFramesV1.Point0613.input_defined SourceMainFramesV1.Point0613.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0613.outputs.2.hi (by
         change SourceMainFramesV1.Point0613.outputs.2.hi ∈ [SourceMainFramesV1.Point0608.outputs.2.hi, SourceMainFramesV1.Point0609.outputs.2.hi, SourceMainFramesV1.Point0610.outputs.2.hi, SourceMainFramesV1.Point0611.outputs.2.hi, SourceMainFramesV1.Point0612.outputs.2.hi, SourceMainFramesV1.Point0613.outputs.2.hi, SourceMainFramesV1.Point0614.outputs.2.hi, SourceMainFramesV1.Point0615.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=614) domain
     SourceMainFramesV1.Point0614.input_defined SourceMainFramesV1.Point0614.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0614.outputs.2.hi (by
         change SourceMainFramesV1.Point0614.outputs.2.hi ∈ [SourceMainFramesV1.Point0608.outputs.2.hi, SourceMainFramesV1.Point0609.outputs.2.hi, SourceMainFramesV1.Point0610.outputs.2.hi, SourceMainFramesV1.Point0611.outputs.2.hi, SourceMainFramesV1.Point0612.outputs.2.hi, SourceMainFramesV1.Point0613.outputs.2.hi, SourceMainFramesV1.Point0614.outputs.2.hi, SourceMainFramesV1.Point0615.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=615) domain
     SourceMainFramesV1.Point0615.input_defined SourceMainFramesV1.Point0615.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0615.outputs.2.hi (by
         change SourceMainFramesV1.Point0615.outputs.2.hi ∈ [SourceMainFramesV1.Point0608.outputs.2.hi, SourceMainFramesV1.Point0609.outputs.2.hi, SourceMainFramesV1.Point0610.outputs.2.hi, SourceMainFramesV1.Point0611.outputs.2.hi, SourceMainFramesV1.Point0612.outputs.2.hi, SourceMainFramesV1.Point0613.outputs.2.hi, SourceMainFramesV1.Point0614.outputs.2.hi, SourceMainFramesV1.Point0615.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block76
