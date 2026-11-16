/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0440
import SourceMainFramesV1.Point0441
import SourceMainFramesV1.Point0442
import SourceMainFramesV1.Point0443
import SourceMainFramesV1.Point0444
import SourceMainFramesV1.Point0445
import SourceMainFramesV1.Point0446
import SourceMainFramesV1.Point0447
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block55
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0440.outputs.2.hi,
 SourceMainFramesV1.Point0441.outputs.2.hi,
 SourceMainFramesV1.Point0442.outputs.2.hi,
 SourceMainFramesV1.Point0443.outputs.2.hi,
 SourceMainFramesV1.Point0444.outputs.2.hi,
 SourceMainFramesV1.Point0445.outputs.2.hi,
 SourceMainFramesV1.Point0446.outputs.2.hi,
 SourceMainFramesV1.Point0447.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 440 ≤ i) (high : i < 448)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=440) domain
     SourceMainFramesV1.Point0440.input_defined SourceMainFramesV1.Point0440.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0440.outputs.2.hi (by
         change SourceMainFramesV1.Point0440.outputs.2.hi ∈ [SourceMainFramesV1.Point0440.outputs.2.hi, SourceMainFramesV1.Point0441.outputs.2.hi, SourceMainFramesV1.Point0442.outputs.2.hi, SourceMainFramesV1.Point0443.outputs.2.hi, SourceMainFramesV1.Point0444.outputs.2.hi, SourceMainFramesV1.Point0445.outputs.2.hi, SourceMainFramesV1.Point0446.outputs.2.hi, SourceMainFramesV1.Point0447.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=441) domain
     SourceMainFramesV1.Point0441.input_defined SourceMainFramesV1.Point0441.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0441.outputs.2.hi (by
         change SourceMainFramesV1.Point0441.outputs.2.hi ∈ [SourceMainFramesV1.Point0440.outputs.2.hi, SourceMainFramesV1.Point0441.outputs.2.hi, SourceMainFramesV1.Point0442.outputs.2.hi, SourceMainFramesV1.Point0443.outputs.2.hi, SourceMainFramesV1.Point0444.outputs.2.hi, SourceMainFramesV1.Point0445.outputs.2.hi, SourceMainFramesV1.Point0446.outputs.2.hi, SourceMainFramesV1.Point0447.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=442) domain
     SourceMainFramesV1.Point0442.input_defined SourceMainFramesV1.Point0442.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0442.outputs.2.hi (by
         change SourceMainFramesV1.Point0442.outputs.2.hi ∈ [SourceMainFramesV1.Point0440.outputs.2.hi, SourceMainFramesV1.Point0441.outputs.2.hi, SourceMainFramesV1.Point0442.outputs.2.hi, SourceMainFramesV1.Point0443.outputs.2.hi, SourceMainFramesV1.Point0444.outputs.2.hi, SourceMainFramesV1.Point0445.outputs.2.hi, SourceMainFramesV1.Point0446.outputs.2.hi, SourceMainFramesV1.Point0447.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=443) domain
     SourceMainFramesV1.Point0443.input_defined SourceMainFramesV1.Point0443.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0443.outputs.2.hi (by
         change SourceMainFramesV1.Point0443.outputs.2.hi ∈ [SourceMainFramesV1.Point0440.outputs.2.hi, SourceMainFramesV1.Point0441.outputs.2.hi, SourceMainFramesV1.Point0442.outputs.2.hi, SourceMainFramesV1.Point0443.outputs.2.hi, SourceMainFramesV1.Point0444.outputs.2.hi, SourceMainFramesV1.Point0445.outputs.2.hi, SourceMainFramesV1.Point0446.outputs.2.hi, SourceMainFramesV1.Point0447.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=444) domain
     SourceMainFramesV1.Point0444.input_defined SourceMainFramesV1.Point0444.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0444.outputs.2.hi (by
         change SourceMainFramesV1.Point0444.outputs.2.hi ∈ [SourceMainFramesV1.Point0440.outputs.2.hi, SourceMainFramesV1.Point0441.outputs.2.hi, SourceMainFramesV1.Point0442.outputs.2.hi, SourceMainFramesV1.Point0443.outputs.2.hi, SourceMainFramesV1.Point0444.outputs.2.hi, SourceMainFramesV1.Point0445.outputs.2.hi, SourceMainFramesV1.Point0446.outputs.2.hi, SourceMainFramesV1.Point0447.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=445) domain
     SourceMainFramesV1.Point0445.input_defined SourceMainFramesV1.Point0445.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0445.outputs.2.hi (by
         change SourceMainFramesV1.Point0445.outputs.2.hi ∈ [SourceMainFramesV1.Point0440.outputs.2.hi, SourceMainFramesV1.Point0441.outputs.2.hi, SourceMainFramesV1.Point0442.outputs.2.hi, SourceMainFramesV1.Point0443.outputs.2.hi, SourceMainFramesV1.Point0444.outputs.2.hi, SourceMainFramesV1.Point0445.outputs.2.hi, SourceMainFramesV1.Point0446.outputs.2.hi, SourceMainFramesV1.Point0447.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=446) domain
     SourceMainFramesV1.Point0446.input_defined SourceMainFramesV1.Point0446.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0446.outputs.2.hi (by
         change SourceMainFramesV1.Point0446.outputs.2.hi ∈ [SourceMainFramesV1.Point0440.outputs.2.hi, SourceMainFramesV1.Point0441.outputs.2.hi, SourceMainFramesV1.Point0442.outputs.2.hi, SourceMainFramesV1.Point0443.outputs.2.hi, SourceMainFramesV1.Point0444.outputs.2.hi, SourceMainFramesV1.Point0445.outputs.2.hi, SourceMainFramesV1.Point0446.outputs.2.hi, SourceMainFramesV1.Point0447.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=447) domain
     SourceMainFramesV1.Point0447.input_defined SourceMainFramesV1.Point0447.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0447.outputs.2.hi (by
         change SourceMainFramesV1.Point0447.outputs.2.hi ∈ [SourceMainFramesV1.Point0440.outputs.2.hi, SourceMainFramesV1.Point0441.outputs.2.hi, SourceMainFramesV1.Point0442.outputs.2.hi, SourceMainFramesV1.Point0443.outputs.2.hi, SourceMainFramesV1.Point0444.outputs.2.hi, SourceMainFramesV1.Point0445.outputs.2.hi, SourceMainFramesV1.Point0446.outputs.2.hi, SourceMainFramesV1.Point0447.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block55
