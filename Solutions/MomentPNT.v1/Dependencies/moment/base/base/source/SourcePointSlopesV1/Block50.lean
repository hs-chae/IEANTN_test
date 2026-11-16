/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0400
import SourceMainFramesV1.Point0401
import SourceMainFramesV1.Point0402
import SourceMainFramesV1.Point0403
import SourceMainFramesV1.Point0404
import SourceMainFramesV1.Point0405
import SourceMainFramesV1.Point0406
import SourceMainFramesV1.Point0407
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block50
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0400.outputs.2.hi,
 SourceMainFramesV1.Point0401.outputs.2.hi,
 SourceMainFramesV1.Point0402.outputs.2.hi,
 SourceMainFramesV1.Point0403.outputs.2.hi,
 SourceMainFramesV1.Point0404.outputs.2.hi,
 SourceMainFramesV1.Point0405.outputs.2.hi,
 SourceMainFramesV1.Point0406.outputs.2.hi,
 SourceMainFramesV1.Point0407.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 400 ≤ i) (high : i < 408)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=400) domain
     SourceMainFramesV1.Point0400.input_defined SourceMainFramesV1.Point0400.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0400.outputs.2.hi (by
         change SourceMainFramesV1.Point0400.outputs.2.hi ∈ [SourceMainFramesV1.Point0400.outputs.2.hi, SourceMainFramesV1.Point0401.outputs.2.hi, SourceMainFramesV1.Point0402.outputs.2.hi, SourceMainFramesV1.Point0403.outputs.2.hi, SourceMainFramesV1.Point0404.outputs.2.hi, SourceMainFramesV1.Point0405.outputs.2.hi, SourceMainFramesV1.Point0406.outputs.2.hi, SourceMainFramesV1.Point0407.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=401) domain
     SourceMainFramesV1.Point0401.input_defined SourceMainFramesV1.Point0401.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0401.outputs.2.hi (by
         change SourceMainFramesV1.Point0401.outputs.2.hi ∈ [SourceMainFramesV1.Point0400.outputs.2.hi, SourceMainFramesV1.Point0401.outputs.2.hi, SourceMainFramesV1.Point0402.outputs.2.hi, SourceMainFramesV1.Point0403.outputs.2.hi, SourceMainFramesV1.Point0404.outputs.2.hi, SourceMainFramesV1.Point0405.outputs.2.hi, SourceMainFramesV1.Point0406.outputs.2.hi, SourceMainFramesV1.Point0407.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=402) domain
     SourceMainFramesV1.Point0402.input_defined SourceMainFramesV1.Point0402.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0402.outputs.2.hi (by
         change SourceMainFramesV1.Point0402.outputs.2.hi ∈ [SourceMainFramesV1.Point0400.outputs.2.hi, SourceMainFramesV1.Point0401.outputs.2.hi, SourceMainFramesV1.Point0402.outputs.2.hi, SourceMainFramesV1.Point0403.outputs.2.hi, SourceMainFramesV1.Point0404.outputs.2.hi, SourceMainFramesV1.Point0405.outputs.2.hi, SourceMainFramesV1.Point0406.outputs.2.hi, SourceMainFramesV1.Point0407.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=403) domain
     SourceMainFramesV1.Point0403.input_defined SourceMainFramesV1.Point0403.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0403.outputs.2.hi (by
         change SourceMainFramesV1.Point0403.outputs.2.hi ∈ [SourceMainFramesV1.Point0400.outputs.2.hi, SourceMainFramesV1.Point0401.outputs.2.hi, SourceMainFramesV1.Point0402.outputs.2.hi, SourceMainFramesV1.Point0403.outputs.2.hi, SourceMainFramesV1.Point0404.outputs.2.hi, SourceMainFramesV1.Point0405.outputs.2.hi, SourceMainFramesV1.Point0406.outputs.2.hi, SourceMainFramesV1.Point0407.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=404) domain
     SourceMainFramesV1.Point0404.input_defined SourceMainFramesV1.Point0404.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0404.outputs.2.hi (by
         change SourceMainFramesV1.Point0404.outputs.2.hi ∈ [SourceMainFramesV1.Point0400.outputs.2.hi, SourceMainFramesV1.Point0401.outputs.2.hi, SourceMainFramesV1.Point0402.outputs.2.hi, SourceMainFramesV1.Point0403.outputs.2.hi, SourceMainFramesV1.Point0404.outputs.2.hi, SourceMainFramesV1.Point0405.outputs.2.hi, SourceMainFramesV1.Point0406.outputs.2.hi, SourceMainFramesV1.Point0407.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=405) domain
     SourceMainFramesV1.Point0405.input_defined SourceMainFramesV1.Point0405.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0405.outputs.2.hi (by
         change SourceMainFramesV1.Point0405.outputs.2.hi ∈ [SourceMainFramesV1.Point0400.outputs.2.hi, SourceMainFramesV1.Point0401.outputs.2.hi, SourceMainFramesV1.Point0402.outputs.2.hi, SourceMainFramesV1.Point0403.outputs.2.hi, SourceMainFramesV1.Point0404.outputs.2.hi, SourceMainFramesV1.Point0405.outputs.2.hi, SourceMainFramesV1.Point0406.outputs.2.hi, SourceMainFramesV1.Point0407.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=406) domain
     SourceMainFramesV1.Point0406.input_defined SourceMainFramesV1.Point0406.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0406.outputs.2.hi (by
         change SourceMainFramesV1.Point0406.outputs.2.hi ∈ [SourceMainFramesV1.Point0400.outputs.2.hi, SourceMainFramesV1.Point0401.outputs.2.hi, SourceMainFramesV1.Point0402.outputs.2.hi, SourceMainFramesV1.Point0403.outputs.2.hi, SourceMainFramesV1.Point0404.outputs.2.hi, SourceMainFramesV1.Point0405.outputs.2.hi, SourceMainFramesV1.Point0406.outputs.2.hi, SourceMainFramesV1.Point0407.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=407) domain
     SourceMainFramesV1.Point0407.input_defined SourceMainFramesV1.Point0407.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0407.outputs.2.hi (by
         change SourceMainFramesV1.Point0407.outputs.2.hi ∈ [SourceMainFramesV1.Point0400.outputs.2.hi, SourceMainFramesV1.Point0401.outputs.2.hi, SourceMainFramesV1.Point0402.outputs.2.hi, SourceMainFramesV1.Point0403.outputs.2.hi, SourceMainFramesV1.Point0404.outputs.2.hi, SourceMainFramesV1.Point0405.outputs.2.hi, SourceMainFramesV1.Point0406.outputs.2.hi, SourceMainFramesV1.Point0407.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block50
