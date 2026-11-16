/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0560
import SourceMainFramesV1.Point0561
import SourceMainFramesV1.Point0562
import SourceMainFramesV1.Point0563
import SourceMainFramesV1.Point0564
import SourceMainFramesV1.Point0565
import SourceMainFramesV1.Point0566
import SourceMainFramesV1.Point0567
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block70
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0560.outputs.2.hi,
 SourceMainFramesV1.Point0561.outputs.2.hi,
 SourceMainFramesV1.Point0562.outputs.2.hi,
 SourceMainFramesV1.Point0563.outputs.2.hi,
 SourceMainFramesV1.Point0564.outputs.2.hi,
 SourceMainFramesV1.Point0565.outputs.2.hi,
 SourceMainFramesV1.Point0566.outputs.2.hi,
 SourceMainFramesV1.Point0567.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 560 ≤ i) (high : i < 568)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=560) domain
     SourceMainFramesV1.Point0560.input_defined SourceMainFramesV1.Point0560.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0560.outputs.2.hi (by
         change SourceMainFramesV1.Point0560.outputs.2.hi ∈ [SourceMainFramesV1.Point0560.outputs.2.hi, SourceMainFramesV1.Point0561.outputs.2.hi, SourceMainFramesV1.Point0562.outputs.2.hi, SourceMainFramesV1.Point0563.outputs.2.hi, SourceMainFramesV1.Point0564.outputs.2.hi, SourceMainFramesV1.Point0565.outputs.2.hi, SourceMainFramesV1.Point0566.outputs.2.hi, SourceMainFramesV1.Point0567.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=561) domain
     SourceMainFramesV1.Point0561.input_defined SourceMainFramesV1.Point0561.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0561.outputs.2.hi (by
         change SourceMainFramesV1.Point0561.outputs.2.hi ∈ [SourceMainFramesV1.Point0560.outputs.2.hi, SourceMainFramesV1.Point0561.outputs.2.hi, SourceMainFramesV1.Point0562.outputs.2.hi, SourceMainFramesV1.Point0563.outputs.2.hi, SourceMainFramesV1.Point0564.outputs.2.hi, SourceMainFramesV1.Point0565.outputs.2.hi, SourceMainFramesV1.Point0566.outputs.2.hi, SourceMainFramesV1.Point0567.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=562) domain
     SourceMainFramesV1.Point0562.input_defined SourceMainFramesV1.Point0562.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0562.outputs.2.hi (by
         change SourceMainFramesV1.Point0562.outputs.2.hi ∈ [SourceMainFramesV1.Point0560.outputs.2.hi, SourceMainFramesV1.Point0561.outputs.2.hi, SourceMainFramesV1.Point0562.outputs.2.hi, SourceMainFramesV1.Point0563.outputs.2.hi, SourceMainFramesV1.Point0564.outputs.2.hi, SourceMainFramesV1.Point0565.outputs.2.hi, SourceMainFramesV1.Point0566.outputs.2.hi, SourceMainFramesV1.Point0567.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=563) domain
     SourceMainFramesV1.Point0563.input_defined SourceMainFramesV1.Point0563.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0563.outputs.2.hi (by
         change SourceMainFramesV1.Point0563.outputs.2.hi ∈ [SourceMainFramesV1.Point0560.outputs.2.hi, SourceMainFramesV1.Point0561.outputs.2.hi, SourceMainFramesV1.Point0562.outputs.2.hi, SourceMainFramesV1.Point0563.outputs.2.hi, SourceMainFramesV1.Point0564.outputs.2.hi, SourceMainFramesV1.Point0565.outputs.2.hi, SourceMainFramesV1.Point0566.outputs.2.hi, SourceMainFramesV1.Point0567.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=564) domain
     SourceMainFramesV1.Point0564.input_defined SourceMainFramesV1.Point0564.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0564.outputs.2.hi (by
         change SourceMainFramesV1.Point0564.outputs.2.hi ∈ [SourceMainFramesV1.Point0560.outputs.2.hi, SourceMainFramesV1.Point0561.outputs.2.hi, SourceMainFramesV1.Point0562.outputs.2.hi, SourceMainFramesV1.Point0563.outputs.2.hi, SourceMainFramesV1.Point0564.outputs.2.hi, SourceMainFramesV1.Point0565.outputs.2.hi, SourceMainFramesV1.Point0566.outputs.2.hi, SourceMainFramesV1.Point0567.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=565) domain
     SourceMainFramesV1.Point0565.input_defined SourceMainFramesV1.Point0565.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0565.outputs.2.hi (by
         change SourceMainFramesV1.Point0565.outputs.2.hi ∈ [SourceMainFramesV1.Point0560.outputs.2.hi, SourceMainFramesV1.Point0561.outputs.2.hi, SourceMainFramesV1.Point0562.outputs.2.hi, SourceMainFramesV1.Point0563.outputs.2.hi, SourceMainFramesV1.Point0564.outputs.2.hi, SourceMainFramesV1.Point0565.outputs.2.hi, SourceMainFramesV1.Point0566.outputs.2.hi, SourceMainFramesV1.Point0567.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=566) domain
     SourceMainFramesV1.Point0566.input_defined SourceMainFramesV1.Point0566.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0566.outputs.2.hi (by
         change SourceMainFramesV1.Point0566.outputs.2.hi ∈ [SourceMainFramesV1.Point0560.outputs.2.hi, SourceMainFramesV1.Point0561.outputs.2.hi, SourceMainFramesV1.Point0562.outputs.2.hi, SourceMainFramesV1.Point0563.outputs.2.hi, SourceMainFramesV1.Point0564.outputs.2.hi, SourceMainFramesV1.Point0565.outputs.2.hi, SourceMainFramesV1.Point0566.outputs.2.hi, SourceMainFramesV1.Point0567.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=567) domain
     SourceMainFramesV1.Point0567.input_defined SourceMainFramesV1.Point0567.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0567.outputs.2.hi (by
         change SourceMainFramesV1.Point0567.outputs.2.hi ∈ [SourceMainFramesV1.Point0560.outputs.2.hi, SourceMainFramesV1.Point0561.outputs.2.hi, SourceMainFramesV1.Point0562.outputs.2.hi, SourceMainFramesV1.Point0563.outputs.2.hi, SourceMainFramesV1.Point0564.outputs.2.hi, SourceMainFramesV1.Point0565.outputs.2.hi, SourceMainFramesV1.Point0566.outputs.2.hi, SourceMainFramesV1.Point0567.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block70
