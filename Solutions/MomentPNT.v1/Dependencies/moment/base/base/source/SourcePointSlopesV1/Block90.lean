/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0720
import SourceMainFramesV1.Point0721
import SourceMainFramesV1.Point0722
import SourceMainFramesV1.Point0723
import SourceMainFramesV1.Point0724
import SourceMainFramesV1.Point0725
import SourceMainFramesV1.Point0726
import SourceMainFramesV1.Point0727
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block90
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0720.outputs.2.hi,
 SourceMainFramesV1.Point0721.outputs.2.hi,
 SourceMainFramesV1.Point0722.outputs.2.hi,
 SourceMainFramesV1.Point0723.outputs.2.hi,
 SourceMainFramesV1.Point0724.outputs.2.hi,
 SourceMainFramesV1.Point0725.outputs.2.hi,
 SourceMainFramesV1.Point0726.outputs.2.hi,
 SourceMainFramesV1.Point0727.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 720 ≤ i) (high : i < 728)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=720) domain
     SourceMainFramesV1.Point0720.input_defined SourceMainFramesV1.Point0720.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0720.outputs.2.hi (by
         change SourceMainFramesV1.Point0720.outputs.2.hi ∈ [SourceMainFramesV1.Point0720.outputs.2.hi, SourceMainFramesV1.Point0721.outputs.2.hi, SourceMainFramesV1.Point0722.outputs.2.hi, SourceMainFramesV1.Point0723.outputs.2.hi, SourceMainFramesV1.Point0724.outputs.2.hi, SourceMainFramesV1.Point0725.outputs.2.hi, SourceMainFramesV1.Point0726.outputs.2.hi, SourceMainFramesV1.Point0727.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=721) domain
     SourceMainFramesV1.Point0721.input_defined SourceMainFramesV1.Point0721.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0721.outputs.2.hi (by
         change SourceMainFramesV1.Point0721.outputs.2.hi ∈ [SourceMainFramesV1.Point0720.outputs.2.hi, SourceMainFramesV1.Point0721.outputs.2.hi, SourceMainFramesV1.Point0722.outputs.2.hi, SourceMainFramesV1.Point0723.outputs.2.hi, SourceMainFramesV1.Point0724.outputs.2.hi, SourceMainFramesV1.Point0725.outputs.2.hi, SourceMainFramesV1.Point0726.outputs.2.hi, SourceMainFramesV1.Point0727.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=722) domain
     SourceMainFramesV1.Point0722.input_defined SourceMainFramesV1.Point0722.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0722.outputs.2.hi (by
         change SourceMainFramesV1.Point0722.outputs.2.hi ∈ [SourceMainFramesV1.Point0720.outputs.2.hi, SourceMainFramesV1.Point0721.outputs.2.hi, SourceMainFramesV1.Point0722.outputs.2.hi, SourceMainFramesV1.Point0723.outputs.2.hi, SourceMainFramesV1.Point0724.outputs.2.hi, SourceMainFramesV1.Point0725.outputs.2.hi, SourceMainFramesV1.Point0726.outputs.2.hi, SourceMainFramesV1.Point0727.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=723) domain
     SourceMainFramesV1.Point0723.input_defined SourceMainFramesV1.Point0723.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0723.outputs.2.hi (by
         change SourceMainFramesV1.Point0723.outputs.2.hi ∈ [SourceMainFramesV1.Point0720.outputs.2.hi, SourceMainFramesV1.Point0721.outputs.2.hi, SourceMainFramesV1.Point0722.outputs.2.hi, SourceMainFramesV1.Point0723.outputs.2.hi, SourceMainFramesV1.Point0724.outputs.2.hi, SourceMainFramesV1.Point0725.outputs.2.hi, SourceMainFramesV1.Point0726.outputs.2.hi, SourceMainFramesV1.Point0727.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=724) domain
     SourceMainFramesV1.Point0724.input_defined SourceMainFramesV1.Point0724.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0724.outputs.2.hi (by
         change SourceMainFramesV1.Point0724.outputs.2.hi ∈ [SourceMainFramesV1.Point0720.outputs.2.hi, SourceMainFramesV1.Point0721.outputs.2.hi, SourceMainFramesV1.Point0722.outputs.2.hi, SourceMainFramesV1.Point0723.outputs.2.hi, SourceMainFramesV1.Point0724.outputs.2.hi, SourceMainFramesV1.Point0725.outputs.2.hi, SourceMainFramesV1.Point0726.outputs.2.hi, SourceMainFramesV1.Point0727.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=725) domain
     SourceMainFramesV1.Point0725.input_defined SourceMainFramesV1.Point0725.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0725.outputs.2.hi (by
         change SourceMainFramesV1.Point0725.outputs.2.hi ∈ [SourceMainFramesV1.Point0720.outputs.2.hi, SourceMainFramesV1.Point0721.outputs.2.hi, SourceMainFramesV1.Point0722.outputs.2.hi, SourceMainFramesV1.Point0723.outputs.2.hi, SourceMainFramesV1.Point0724.outputs.2.hi, SourceMainFramesV1.Point0725.outputs.2.hi, SourceMainFramesV1.Point0726.outputs.2.hi, SourceMainFramesV1.Point0727.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=726) domain
     SourceMainFramesV1.Point0726.input_defined SourceMainFramesV1.Point0726.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0726.outputs.2.hi (by
         change SourceMainFramesV1.Point0726.outputs.2.hi ∈ [SourceMainFramesV1.Point0720.outputs.2.hi, SourceMainFramesV1.Point0721.outputs.2.hi, SourceMainFramesV1.Point0722.outputs.2.hi, SourceMainFramesV1.Point0723.outputs.2.hi, SourceMainFramesV1.Point0724.outputs.2.hi, SourceMainFramesV1.Point0725.outputs.2.hi, SourceMainFramesV1.Point0726.outputs.2.hi, SourceMainFramesV1.Point0727.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=727) domain
     SourceMainFramesV1.Point0727.input_defined SourceMainFramesV1.Point0727.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0727.outputs.2.hi (by
         change SourceMainFramesV1.Point0727.outputs.2.hi ∈ [SourceMainFramesV1.Point0720.outputs.2.hi, SourceMainFramesV1.Point0721.outputs.2.hi, SourceMainFramesV1.Point0722.outputs.2.hi, SourceMainFramesV1.Point0723.outputs.2.hi, SourceMainFramesV1.Point0724.outputs.2.hi, SourceMainFramesV1.Point0725.outputs.2.hi, SourceMainFramesV1.Point0726.outputs.2.hi, SourceMainFramesV1.Point0727.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block90
