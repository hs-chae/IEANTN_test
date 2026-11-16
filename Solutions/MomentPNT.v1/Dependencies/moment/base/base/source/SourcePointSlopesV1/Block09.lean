/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0072
import SourceMainFramesV1.Point0073
import SourceMainFramesV1.Point0074
import SourceMainFramesV1.Point0075
import SourceMainFramesV1.Point0076
import SourceMainFramesV1.Point0077
import SourceMainFramesV1.Point0078
import SourceMainFramesV1.Point0079
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block09
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0072.outputs.2.hi,
 SourceMainFramesV1.Point0073.outputs.2.hi,
 SourceMainFramesV1.Point0074.outputs.2.hi,
 SourceMainFramesV1.Point0075.outputs.2.hi,
 SourceMainFramesV1.Point0076.outputs.2.hi,
 SourceMainFramesV1.Point0077.outputs.2.hi,
 SourceMainFramesV1.Point0078.outputs.2.hi,
 SourceMainFramesV1.Point0079.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 72 ≤ i) (high : i < 80)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=72) domain
     SourceMainFramesV1.Point0072.input_defined SourceMainFramesV1.Point0072.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0072.outputs.2.hi (by
         change SourceMainFramesV1.Point0072.outputs.2.hi ∈ [SourceMainFramesV1.Point0072.outputs.2.hi, SourceMainFramesV1.Point0073.outputs.2.hi, SourceMainFramesV1.Point0074.outputs.2.hi, SourceMainFramesV1.Point0075.outputs.2.hi, SourceMainFramesV1.Point0076.outputs.2.hi, SourceMainFramesV1.Point0077.outputs.2.hi, SourceMainFramesV1.Point0078.outputs.2.hi, SourceMainFramesV1.Point0079.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=73) domain
     SourceMainFramesV1.Point0073.input_defined SourceMainFramesV1.Point0073.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0073.outputs.2.hi (by
         change SourceMainFramesV1.Point0073.outputs.2.hi ∈ [SourceMainFramesV1.Point0072.outputs.2.hi, SourceMainFramesV1.Point0073.outputs.2.hi, SourceMainFramesV1.Point0074.outputs.2.hi, SourceMainFramesV1.Point0075.outputs.2.hi, SourceMainFramesV1.Point0076.outputs.2.hi, SourceMainFramesV1.Point0077.outputs.2.hi, SourceMainFramesV1.Point0078.outputs.2.hi, SourceMainFramesV1.Point0079.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=74) domain
     SourceMainFramesV1.Point0074.input_defined SourceMainFramesV1.Point0074.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0074.outputs.2.hi (by
         change SourceMainFramesV1.Point0074.outputs.2.hi ∈ [SourceMainFramesV1.Point0072.outputs.2.hi, SourceMainFramesV1.Point0073.outputs.2.hi, SourceMainFramesV1.Point0074.outputs.2.hi, SourceMainFramesV1.Point0075.outputs.2.hi, SourceMainFramesV1.Point0076.outputs.2.hi, SourceMainFramesV1.Point0077.outputs.2.hi, SourceMainFramesV1.Point0078.outputs.2.hi, SourceMainFramesV1.Point0079.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=75) domain
     SourceMainFramesV1.Point0075.input_defined SourceMainFramesV1.Point0075.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0075.outputs.2.hi (by
         change SourceMainFramesV1.Point0075.outputs.2.hi ∈ [SourceMainFramesV1.Point0072.outputs.2.hi, SourceMainFramesV1.Point0073.outputs.2.hi, SourceMainFramesV1.Point0074.outputs.2.hi, SourceMainFramesV1.Point0075.outputs.2.hi, SourceMainFramesV1.Point0076.outputs.2.hi, SourceMainFramesV1.Point0077.outputs.2.hi, SourceMainFramesV1.Point0078.outputs.2.hi, SourceMainFramesV1.Point0079.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=76) domain
     SourceMainFramesV1.Point0076.input_defined SourceMainFramesV1.Point0076.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0076.outputs.2.hi (by
         change SourceMainFramesV1.Point0076.outputs.2.hi ∈ [SourceMainFramesV1.Point0072.outputs.2.hi, SourceMainFramesV1.Point0073.outputs.2.hi, SourceMainFramesV1.Point0074.outputs.2.hi, SourceMainFramesV1.Point0075.outputs.2.hi, SourceMainFramesV1.Point0076.outputs.2.hi, SourceMainFramesV1.Point0077.outputs.2.hi, SourceMainFramesV1.Point0078.outputs.2.hi, SourceMainFramesV1.Point0079.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=77) domain
     SourceMainFramesV1.Point0077.input_defined SourceMainFramesV1.Point0077.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0077.outputs.2.hi (by
         change SourceMainFramesV1.Point0077.outputs.2.hi ∈ [SourceMainFramesV1.Point0072.outputs.2.hi, SourceMainFramesV1.Point0073.outputs.2.hi, SourceMainFramesV1.Point0074.outputs.2.hi, SourceMainFramesV1.Point0075.outputs.2.hi, SourceMainFramesV1.Point0076.outputs.2.hi, SourceMainFramesV1.Point0077.outputs.2.hi, SourceMainFramesV1.Point0078.outputs.2.hi, SourceMainFramesV1.Point0079.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=78) domain
     SourceMainFramesV1.Point0078.input_defined SourceMainFramesV1.Point0078.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0078.outputs.2.hi (by
         change SourceMainFramesV1.Point0078.outputs.2.hi ∈ [SourceMainFramesV1.Point0072.outputs.2.hi, SourceMainFramesV1.Point0073.outputs.2.hi, SourceMainFramesV1.Point0074.outputs.2.hi, SourceMainFramesV1.Point0075.outputs.2.hi, SourceMainFramesV1.Point0076.outputs.2.hi, SourceMainFramesV1.Point0077.outputs.2.hi, SourceMainFramesV1.Point0078.outputs.2.hi, SourceMainFramesV1.Point0079.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=79) domain
     SourceMainFramesV1.Point0079.input_defined SourceMainFramesV1.Point0079.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0079.outputs.2.hi (by
         change SourceMainFramesV1.Point0079.outputs.2.hi ∈ [SourceMainFramesV1.Point0072.outputs.2.hi, SourceMainFramesV1.Point0073.outputs.2.hi, SourceMainFramesV1.Point0074.outputs.2.hi, SourceMainFramesV1.Point0075.outputs.2.hi, SourceMainFramesV1.Point0076.outputs.2.hi, SourceMainFramesV1.Point0077.outputs.2.hi, SourceMainFramesV1.Point0078.outputs.2.hi, SourceMainFramesV1.Point0079.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block09
