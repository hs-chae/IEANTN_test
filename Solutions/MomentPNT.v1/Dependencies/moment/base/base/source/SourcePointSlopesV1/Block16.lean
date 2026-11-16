/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0128
import SourceMainFramesV1.Point0129
import SourceMainFramesV1.Point0130
import SourceMainFramesV1.Point0131
import SourceMainFramesV1.Point0132
import SourceMainFramesV1.Point0133
import SourceMainFramesV1.Point0134
import SourceMainFramesV1.Point0135
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block16
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0128.outputs.2.hi,
 SourceMainFramesV1.Point0129.outputs.2.hi,
 SourceMainFramesV1.Point0130.outputs.2.hi,
 SourceMainFramesV1.Point0131.outputs.2.hi,
 SourceMainFramesV1.Point0132.outputs.2.hi,
 SourceMainFramesV1.Point0133.outputs.2.hi,
 SourceMainFramesV1.Point0134.outputs.2.hi,
 SourceMainFramesV1.Point0135.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 128 ≤ i) (high : i < 136)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=128) domain
     SourceMainFramesV1.Point0128.input_defined SourceMainFramesV1.Point0128.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0128.outputs.2.hi (by
         change SourceMainFramesV1.Point0128.outputs.2.hi ∈ [SourceMainFramesV1.Point0128.outputs.2.hi, SourceMainFramesV1.Point0129.outputs.2.hi, SourceMainFramesV1.Point0130.outputs.2.hi, SourceMainFramesV1.Point0131.outputs.2.hi, SourceMainFramesV1.Point0132.outputs.2.hi, SourceMainFramesV1.Point0133.outputs.2.hi, SourceMainFramesV1.Point0134.outputs.2.hi, SourceMainFramesV1.Point0135.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=129) domain
     SourceMainFramesV1.Point0129.input_defined SourceMainFramesV1.Point0129.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0129.outputs.2.hi (by
         change SourceMainFramesV1.Point0129.outputs.2.hi ∈ [SourceMainFramesV1.Point0128.outputs.2.hi, SourceMainFramesV1.Point0129.outputs.2.hi, SourceMainFramesV1.Point0130.outputs.2.hi, SourceMainFramesV1.Point0131.outputs.2.hi, SourceMainFramesV1.Point0132.outputs.2.hi, SourceMainFramesV1.Point0133.outputs.2.hi, SourceMainFramesV1.Point0134.outputs.2.hi, SourceMainFramesV1.Point0135.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=130) domain
     SourceMainFramesV1.Point0130.input_defined SourceMainFramesV1.Point0130.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0130.outputs.2.hi (by
         change SourceMainFramesV1.Point0130.outputs.2.hi ∈ [SourceMainFramesV1.Point0128.outputs.2.hi, SourceMainFramesV1.Point0129.outputs.2.hi, SourceMainFramesV1.Point0130.outputs.2.hi, SourceMainFramesV1.Point0131.outputs.2.hi, SourceMainFramesV1.Point0132.outputs.2.hi, SourceMainFramesV1.Point0133.outputs.2.hi, SourceMainFramesV1.Point0134.outputs.2.hi, SourceMainFramesV1.Point0135.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=131) domain
     SourceMainFramesV1.Point0131.input_defined SourceMainFramesV1.Point0131.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0131.outputs.2.hi (by
         change SourceMainFramesV1.Point0131.outputs.2.hi ∈ [SourceMainFramesV1.Point0128.outputs.2.hi, SourceMainFramesV1.Point0129.outputs.2.hi, SourceMainFramesV1.Point0130.outputs.2.hi, SourceMainFramesV1.Point0131.outputs.2.hi, SourceMainFramesV1.Point0132.outputs.2.hi, SourceMainFramesV1.Point0133.outputs.2.hi, SourceMainFramesV1.Point0134.outputs.2.hi, SourceMainFramesV1.Point0135.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=132) domain
     SourceMainFramesV1.Point0132.input_defined SourceMainFramesV1.Point0132.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0132.outputs.2.hi (by
         change SourceMainFramesV1.Point0132.outputs.2.hi ∈ [SourceMainFramesV1.Point0128.outputs.2.hi, SourceMainFramesV1.Point0129.outputs.2.hi, SourceMainFramesV1.Point0130.outputs.2.hi, SourceMainFramesV1.Point0131.outputs.2.hi, SourceMainFramesV1.Point0132.outputs.2.hi, SourceMainFramesV1.Point0133.outputs.2.hi, SourceMainFramesV1.Point0134.outputs.2.hi, SourceMainFramesV1.Point0135.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=133) domain
     SourceMainFramesV1.Point0133.input_defined SourceMainFramesV1.Point0133.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0133.outputs.2.hi (by
         change SourceMainFramesV1.Point0133.outputs.2.hi ∈ [SourceMainFramesV1.Point0128.outputs.2.hi, SourceMainFramesV1.Point0129.outputs.2.hi, SourceMainFramesV1.Point0130.outputs.2.hi, SourceMainFramesV1.Point0131.outputs.2.hi, SourceMainFramesV1.Point0132.outputs.2.hi, SourceMainFramesV1.Point0133.outputs.2.hi, SourceMainFramesV1.Point0134.outputs.2.hi, SourceMainFramesV1.Point0135.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=134) domain
     SourceMainFramesV1.Point0134.input_defined SourceMainFramesV1.Point0134.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0134.outputs.2.hi (by
         change SourceMainFramesV1.Point0134.outputs.2.hi ∈ [SourceMainFramesV1.Point0128.outputs.2.hi, SourceMainFramesV1.Point0129.outputs.2.hi, SourceMainFramesV1.Point0130.outputs.2.hi, SourceMainFramesV1.Point0131.outputs.2.hi, SourceMainFramesV1.Point0132.outputs.2.hi, SourceMainFramesV1.Point0133.outputs.2.hi, SourceMainFramesV1.Point0134.outputs.2.hi, SourceMainFramesV1.Point0135.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=135) domain
     SourceMainFramesV1.Point0135.input_defined SourceMainFramesV1.Point0135.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0135.outputs.2.hi (by
         change SourceMainFramesV1.Point0135.outputs.2.hi ∈ [SourceMainFramesV1.Point0128.outputs.2.hi, SourceMainFramesV1.Point0129.outputs.2.hi, SourceMainFramesV1.Point0130.outputs.2.hi, SourceMainFramesV1.Point0131.outputs.2.hi, SourceMainFramesV1.Point0132.outputs.2.hi, SourceMainFramesV1.Point0133.outputs.2.hi, SourceMainFramesV1.Point0134.outputs.2.hi, SourceMainFramesV1.Point0135.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block16
