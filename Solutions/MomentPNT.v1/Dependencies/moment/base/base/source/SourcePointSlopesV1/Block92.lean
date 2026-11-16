/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0736
import SourceMainFramesV1.Point0737
import SourceMainFramesV1.Point0738
import SourceMainFramesV1.Point0739
import SourceMainFramesV1.Point0740
import SourceMainFramesV1.Point0741
import SourceMainFramesV1.Point0742
import SourceMainFramesV1.Point0743
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block92
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0736.outputs.2.hi,
 SourceMainFramesV1.Point0737.outputs.2.hi,
 SourceMainFramesV1.Point0738.outputs.2.hi,
 SourceMainFramesV1.Point0739.outputs.2.hi,
 SourceMainFramesV1.Point0740.outputs.2.hi,
 SourceMainFramesV1.Point0741.outputs.2.hi,
 SourceMainFramesV1.Point0742.outputs.2.hi,
 SourceMainFramesV1.Point0743.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 736 ≤ i) (high : i < 744)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=736) domain
     SourceMainFramesV1.Point0736.input_defined SourceMainFramesV1.Point0736.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0736.outputs.2.hi (by
         change SourceMainFramesV1.Point0736.outputs.2.hi ∈ [SourceMainFramesV1.Point0736.outputs.2.hi, SourceMainFramesV1.Point0737.outputs.2.hi, SourceMainFramesV1.Point0738.outputs.2.hi, SourceMainFramesV1.Point0739.outputs.2.hi, SourceMainFramesV1.Point0740.outputs.2.hi, SourceMainFramesV1.Point0741.outputs.2.hi, SourceMainFramesV1.Point0742.outputs.2.hi, SourceMainFramesV1.Point0743.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=737) domain
     SourceMainFramesV1.Point0737.input_defined SourceMainFramesV1.Point0737.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0737.outputs.2.hi (by
         change SourceMainFramesV1.Point0737.outputs.2.hi ∈ [SourceMainFramesV1.Point0736.outputs.2.hi, SourceMainFramesV1.Point0737.outputs.2.hi, SourceMainFramesV1.Point0738.outputs.2.hi, SourceMainFramesV1.Point0739.outputs.2.hi, SourceMainFramesV1.Point0740.outputs.2.hi, SourceMainFramesV1.Point0741.outputs.2.hi, SourceMainFramesV1.Point0742.outputs.2.hi, SourceMainFramesV1.Point0743.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=738) domain
     SourceMainFramesV1.Point0738.input_defined SourceMainFramesV1.Point0738.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0738.outputs.2.hi (by
         change SourceMainFramesV1.Point0738.outputs.2.hi ∈ [SourceMainFramesV1.Point0736.outputs.2.hi, SourceMainFramesV1.Point0737.outputs.2.hi, SourceMainFramesV1.Point0738.outputs.2.hi, SourceMainFramesV1.Point0739.outputs.2.hi, SourceMainFramesV1.Point0740.outputs.2.hi, SourceMainFramesV1.Point0741.outputs.2.hi, SourceMainFramesV1.Point0742.outputs.2.hi, SourceMainFramesV1.Point0743.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=739) domain
     SourceMainFramesV1.Point0739.input_defined SourceMainFramesV1.Point0739.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0739.outputs.2.hi (by
         change SourceMainFramesV1.Point0739.outputs.2.hi ∈ [SourceMainFramesV1.Point0736.outputs.2.hi, SourceMainFramesV1.Point0737.outputs.2.hi, SourceMainFramesV1.Point0738.outputs.2.hi, SourceMainFramesV1.Point0739.outputs.2.hi, SourceMainFramesV1.Point0740.outputs.2.hi, SourceMainFramesV1.Point0741.outputs.2.hi, SourceMainFramesV1.Point0742.outputs.2.hi, SourceMainFramesV1.Point0743.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=740) domain
     SourceMainFramesV1.Point0740.input_defined SourceMainFramesV1.Point0740.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0740.outputs.2.hi (by
         change SourceMainFramesV1.Point0740.outputs.2.hi ∈ [SourceMainFramesV1.Point0736.outputs.2.hi, SourceMainFramesV1.Point0737.outputs.2.hi, SourceMainFramesV1.Point0738.outputs.2.hi, SourceMainFramesV1.Point0739.outputs.2.hi, SourceMainFramesV1.Point0740.outputs.2.hi, SourceMainFramesV1.Point0741.outputs.2.hi, SourceMainFramesV1.Point0742.outputs.2.hi, SourceMainFramesV1.Point0743.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=741) domain
     SourceMainFramesV1.Point0741.input_defined SourceMainFramesV1.Point0741.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0741.outputs.2.hi (by
         change SourceMainFramesV1.Point0741.outputs.2.hi ∈ [SourceMainFramesV1.Point0736.outputs.2.hi, SourceMainFramesV1.Point0737.outputs.2.hi, SourceMainFramesV1.Point0738.outputs.2.hi, SourceMainFramesV1.Point0739.outputs.2.hi, SourceMainFramesV1.Point0740.outputs.2.hi, SourceMainFramesV1.Point0741.outputs.2.hi, SourceMainFramesV1.Point0742.outputs.2.hi, SourceMainFramesV1.Point0743.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=742) domain
     SourceMainFramesV1.Point0742.input_defined SourceMainFramesV1.Point0742.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0742.outputs.2.hi (by
         change SourceMainFramesV1.Point0742.outputs.2.hi ∈ [SourceMainFramesV1.Point0736.outputs.2.hi, SourceMainFramesV1.Point0737.outputs.2.hi, SourceMainFramesV1.Point0738.outputs.2.hi, SourceMainFramesV1.Point0739.outputs.2.hi, SourceMainFramesV1.Point0740.outputs.2.hi, SourceMainFramesV1.Point0741.outputs.2.hi, SourceMainFramesV1.Point0742.outputs.2.hi, SourceMainFramesV1.Point0743.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=743) domain
     SourceMainFramesV1.Point0743.input_defined SourceMainFramesV1.Point0743.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0743.outputs.2.hi (by
         change SourceMainFramesV1.Point0743.outputs.2.hi ∈ [SourceMainFramesV1.Point0736.outputs.2.hi, SourceMainFramesV1.Point0737.outputs.2.hi, SourceMainFramesV1.Point0738.outputs.2.hi, SourceMainFramesV1.Point0739.outputs.2.hi, SourceMainFramesV1.Point0740.outputs.2.hi, SourceMainFramesV1.Point0741.outputs.2.hi, SourceMainFramesV1.Point0742.outputs.2.hi, SourceMainFramesV1.Point0743.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block92
