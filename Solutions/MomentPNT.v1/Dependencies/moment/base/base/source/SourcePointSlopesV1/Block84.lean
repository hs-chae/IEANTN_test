/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0672
import SourceMainFramesV1.Point0673
import SourceMainFramesV1.Point0674
import SourceMainFramesV1.Point0675
import SourceMainFramesV1.Point0676
import SourceMainFramesV1.Point0677
import SourceMainFramesV1.Point0678
import SourceMainFramesV1.Point0679
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block84
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0672.outputs.2.hi,
 SourceMainFramesV1.Point0673.outputs.2.hi,
 SourceMainFramesV1.Point0674.outputs.2.hi,
 SourceMainFramesV1.Point0675.outputs.2.hi,
 SourceMainFramesV1.Point0676.outputs.2.hi,
 SourceMainFramesV1.Point0677.outputs.2.hi,
 SourceMainFramesV1.Point0678.outputs.2.hi,
 SourceMainFramesV1.Point0679.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 672 ≤ i) (high : i < 680)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=672) domain
     SourceMainFramesV1.Point0672.input_defined SourceMainFramesV1.Point0672.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0672.outputs.2.hi (by
         change SourceMainFramesV1.Point0672.outputs.2.hi ∈ [SourceMainFramesV1.Point0672.outputs.2.hi, SourceMainFramesV1.Point0673.outputs.2.hi, SourceMainFramesV1.Point0674.outputs.2.hi, SourceMainFramesV1.Point0675.outputs.2.hi, SourceMainFramesV1.Point0676.outputs.2.hi, SourceMainFramesV1.Point0677.outputs.2.hi, SourceMainFramesV1.Point0678.outputs.2.hi, SourceMainFramesV1.Point0679.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=673) domain
     SourceMainFramesV1.Point0673.input_defined SourceMainFramesV1.Point0673.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0673.outputs.2.hi (by
         change SourceMainFramesV1.Point0673.outputs.2.hi ∈ [SourceMainFramesV1.Point0672.outputs.2.hi, SourceMainFramesV1.Point0673.outputs.2.hi, SourceMainFramesV1.Point0674.outputs.2.hi, SourceMainFramesV1.Point0675.outputs.2.hi, SourceMainFramesV1.Point0676.outputs.2.hi, SourceMainFramesV1.Point0677.outputs.2.hi, SourceMainFramesV1.Point0678.outputs.2.hi, SourceMainFramesV1.Point0679.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=674) domain
     SourceMainFramesV1.Point0674.input_defined SourceMainFramesV1.Point0674.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0674.outputs.2.hi (by
         change SourceMainFramesV1.Point0674.outputs.2.hi ∈ [SourceMainFramesV1.Point0672.outputs.2.hi, SourceMainFramesV1.Point0673.outputs.2.hi, SourceMainFramesV1.Point0674.outputs.2.hi, SourceMainFramesV1.Point0675.outputs.2.hi, SourceMainFramesV1.Point0676.outputs.2.hi, SourceMainFramesV1.Point0677.outputs.2.hi, SourceMainFramesV1.Point0678.outputs.2.hi, SourceMainFramesV1.Point0679.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=675) domain
     SourceMainFramesV1.Point0675.input_defined SourceMainFramesV1.Point0675.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0675.outputs.2.hi (by
         change SourceMainFramesV1.Point0675.outputs.2.hi ∈ [SourceMainFramesV1.Point0672.outputs.2.hi, SourceMainFramesV1.Point0673.outputs.2.hi, SourceMainFramesV1.Point0674.outputs.2.hi, SourceMainFramesV1.Point0675.outputs.2.hi, SourceMainFramesV1.Point0676.outputs.2.hi, SourceMainFramesV1.Point0677.outputs.2.hi, SourceMainFramesV1.Point0678.outputs.2.hi, SourceMainFramesV1.Point0679.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=676) domain
     SourceMainFramesV1.Point0676.input_defined SourceMainFramesV1.Point0676.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0676.outputs.2.hi (by
         change SourceMainFramesV1.Point0676.outputs.2.hi ∈ [SourceMainFramesV1.Point0672.outputs.2.hi, SourceMainFramesV1.Point0673.outputs.2.hi, SourceMainFramesV1.Point0674.outputs.2.hi, SourceMainFramesV1.Point0675.outputs.2.hi, SourceMainFramesV1.Point0676.outputs.2.hi, SourceMainFramesV1.Point0677.outputs.2.hi, SourceMainFramesV1.Point0678.outputs.2.hi, SourceMainFramesV1.Point0679.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=677) domain
     SourceMainFramesV1.Point0677.input_defined SourceMainFramesV1.Point0677.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0677.outputs.2.hi (by
         change SourceMainFramesV1.Point0677.outputs.2.hi ∈ [SourceMainFramesV1.Point0672.outputs.2.hi, SourceMainFramesV1.Point0673.outputs.2.hi, SourceMainFramesV1.Point0674.outputs.2.hi, SourceMainFramesV1.Point0675.outputs.2.hi, SourceMainFramesV1.Point0676.outputs.2.hi, SourceMainFramesV1.Point0677.outputs.2.hi, SourceMainFramesV1.Point0678.outputs.2.hi, SourceMainFramesV1.Point0679.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=678) domain
     SourceMainFramesV1.Point0678.input_defined SourceMainFramesV1.Point0678.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0678.outputs.2.hi (by
         change SourceMainFramesV1.Point0678.outputs.2.hi ∈ [SourceMainFramesV1.Point0672.outputs.2.hi, SourceMainFramesV1.Point0673.outputs.2.hi, SourceMainFramesV1.Point0674.outputs.2.hi, SourceMainFramesV1.Point0675.outputs.2.hi, SourceMainFramesV1.Point0676.outputs.2.hi, SourceMainFramesV1.Point0677.outputs.2.hi, SourceMainFramesV1.Point0678.outputs.2.hi, SourceMainFramesV1.Point0679.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=679) domain
     SourceMainFramesV1.Point0679.input_defined SourceMainFramesV1.Point0679.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0679.outputs.2.hi (by
         change SourceMainFramesV1.Point0679.outputs.2.hi ∈ [SourceMainFramesV1.Point0672.outputs.2.hi, SourceMainFramesV1.Point0673.outputs.2.hi, SourceMainFramesV1.Point0674.outputs.2.hi, SourceMainFramesV1.Point0675.outputs.2.hi, SourceMainFramesV1.Point0676.outputs.2.hi, SourceMainFramesV1.Point0677.outputs.2.hi, SourceMainFramesV1.Point0678.outputs.2.hi, SourceMainFramesV1.Point0679.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block84
