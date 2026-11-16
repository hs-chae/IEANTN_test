/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0648
import SourceMainFramesV1.Point0649
import SourceMainFramesV1.Point0650
import SourceMainFramesV1.Point0651
import SourceMainFramesV1.Point0652
import SourceMainFramesV1.Point0653
import SourceMainFramesV1.Point0654
import SourceMainFramesV1.Point0655
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block81
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0648.outputs.2.hi,
 SourceMainFramesV1.Point0649.outputs.2.hi,
 SourceMainFramesV1.Point0650.outputs.2.hi,
 SourceMainFramesV1.Point0651.outputs.2.hi,
 SourceMainFramesV1.Point0652.outputs.2.hi,
 SourceMainFramesV1.Point0653.outputs.2.hi,
 SourceMainFramesV1.Point0654.outputs.2.hi,
 SourceMainFramesV1.Point0655.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 648 ≤ i) (high : i < 656)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=648) domain
     SourceMainFramesV1.Point0648.input_defined SourceMainFramesV1.Point0648.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0648.outputs.2.hi (by
         change SourceMainFramesV1.Point0648.outputs.2.hi ∈ [SourceMainFramesV1.Point0648.outputs.2.hi, SourceMainFramesV1.Point0649.outputs.2.hi, SourceMainFramesV1.Point0650.outputs.2.hi, SourceMainFramesV1.Point0651.outputs.2.hi, SourceMainFramesV1.Point0652.outputs.2.hi, SourceMainFramesV1.Point0653.outputs.2.hi, SourceMainFramesV1.Point0654.outputs.2.hi, SourceMainFramesV1.Point0655.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=649) domain
     SourceMainFramesV1.Point0649.input_defined SourceMainFramesV1.Point0649.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0649.outputs.2.hi (by
         change SourceMainFramesV1.Point0649.outputs.2.hi ∈ [SourceMainFramesV1.Point0648.outputs.2.hi, SourceMainFramesV1.Point0649.outputs.2.hi, SourceMainFramesV1.Point0650.outputs.2.hi, SourceMainFramesV1.Point0651.outputs.2.hi, SourceMainFramesV1.Point0652.outputs.2.hi, SourceMainFramesV1.Point0653.outputs.2.hi, SourceMainFramesV1.Point0654.outputs.2.hi, SourceMainFramesV1.Point0655.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=650) domain
     SourceMainFramesV1.Point0650.input_defined SourceMainFramesV1.Point0650.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0650.outputs.2.hi (by
         change SourceMainFramesV1.Point0650.outputs.2.hi ∈ [SourceMainFramesV1.Point0648.outputs.2.hi, SourceMainFramesV1.Point0649.outputs.2.hi, SourceMainFramesV1.Point0650.outputs.2.hi, SourceMainFramesV1.Point0651.outputs.2.hi, SourceMainFramesV1.Point0652.outputs.2.hi, SourceMainFramesV1.Point0653.outputs.2.hi, SourceMainFramesV1.Point0654.outputs.2.hi, SourceMainFramesV1.Point0655.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=651) domain
     SourceMainFramesV1.Point0651.input_defined SourceMainFramesV1.Point0651.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0651.outputs.2.hi (by
         change SourceMainFramesV1.Point0651.outputs.2.hi ∈ [SourceMainFramesV1.Point0648.outputs.2.hi, SourceMainFramesV1.Point0649.outputs.2.hi, SourceMainFramesV1.Point0650.outputs.2.hi, SourceMainFramesV1.Point0651.outputs.2.hi, SourceMainFramesV1.Point0652.outputs.2.hi, SourceMainFramesV1.Point0653.outputs.2.hi, SourceMainFramesV1.Point0654.outputs.2.hi, SourceMainFramesV1.Point0655.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=652) domain
     SourceMainFramesV1.Point0652.input_defined SourceMainFramesV1.Point0652.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0652.outputs.2.hi (by
         change SourceMainFramesV1.Point0652.outputs.2.hi ∈ [SourceMainFramesV1.Point0648.outputs.2.hi, SourceMainFramesV1.Point0649.outputs.2.hi, SourceMainFramesV1.Point0650.outputs.2.hi, SourceMainFramesV1.Point0651.outputs.2.hi, SourceMainFramesV1.Point0652.outputs.2.hi, SourceMainFramesV1.Point0653.outputs.2.hi, SourceMainFramesV1.Point0654.outputs.2.hi, SourceMainFramesV1.Point0655.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=653) domain
     SourceMainFramesV1.Point0653.input_defined SourceMainFramesV1.Point0653.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0653.outputs.2.hi (by
         change SourceMainFramesV1.Point0653.outputs.2.hi ∈ [SourceMainFramesV1.Point0648.outputs.2.hi, SourceMainFramesV1.Point0649.outputs.2.hi, SourceMainFramesV1.Point0650.outputs.2.hi, SourceMainFramesV1.Point0651.outputs.2.hi, SourceMainFramesV1.Point0652.outputs.2.hi, SourceMainFramesV1.Point0653.outputs.2.hi, SourceMainFramesV1.Point0654.outputs.2.hi, SourceMainFramesV1.Point0655.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=654) domain
     SourceMainFramesV1.Point0654.input_defined SourceMainFramesV1.Point0654.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0654.outputs.2.hi (by
         change SourceMainFramesV1.Point0654.outputs.2.hi ∈ [SourceMainFramesV1.Point0648.outputs.2.hi, SourceMainFramesV1.Point0649.outputs.2.hi, SourceMainFramesV1.Point0650.outputs.2.hi, SourceMainFramesV1.Point0651.outputs.2.hi, SourceMainFramesV1.Point0652.outputs.2.hi, SourceMainFramesV1.Point0653.outputs.2.hi, SourceMainFramesV1.Point0654.outputs.2.hi, SourceMainFramesV1.Point0655.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=655) domain
     SourceMainFramesV1.Point0655.input_defined SourceMainFramesV1.Point0655.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0655.outputs.2.hi (by
         change SourceMainFramesV1.Point0655.outputs.2.hi ∈ [SourceMainFramesV1.Point0648.outputs.2.hi, SourceMainFramesV1.Point0649.outputs.2.hi, SourceMainFramesV1.Point0650.outputs.2.hi, SourceMainFramesV1.Point0651.outputs.2.hi, SourceMainFramesV1.Point0652.outputs.2.hi, SourceMainFramesV1.Point0653.outputs.2.hi, SourceMainFramesV1.Point0654.outputs.2.hi, SourceMainFramesV1.Point0655.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block81
