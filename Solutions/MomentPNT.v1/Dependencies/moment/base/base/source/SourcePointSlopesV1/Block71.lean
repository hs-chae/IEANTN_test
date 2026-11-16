/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0568
import SourceMainFramesV1.Point0569
import SourceMainFramesV1.Point0570
import SourceMainFramesV1.Point0571
import SourceMainFramesV1.Point0572
import SourceMainFramesV1.Point0573
import SourceMainFramesV1.Point0574
import SourceMainFramesV1.Point0575
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block71
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0568.outputs.2.hi,
 SourceMainFramesV1.Point0569.outputs.2.hi,
 SourceMainFramesV1.Point0570.outputs.2.hi,
 SourceMainFramesV1.Point0571.outputs.2.hi,
 SourceMainFramesV1.Point0572.outputs.2.hi,
 SourceMainFramesV1.Point0573.outputs.2.hi,
 SourceMainFramesV1.Point0574.outputs.2.hi,
 SourceMainFramesV1.Point0575.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 568 ≤ i) (high : i < 576)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=568) domain
     SourceMainFramesV1.Point0568.input_defined SourceMainFramesV1.Point0568.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0568.outputs.2.hi (by
         change SourceMainFramesV1.Point0568.outputs.2.hi ∈ [SourceMainFramesV1.Point0568.outputs.2.hi, SourceMainFramesV1.Point0569.outputs.2.hi, SourceMainFramesV1.Point0570.outputs.2.hi, SourceMainFramesV1.Point0571.outputs.2.hi, SourceMainFramesV1.Point0572.outputs.2.hi, SourceMainFramesV1.Point0573.outputs.2.hi, SourceMainFramesV1.Point0574.outputs.2.hi, SourceMainFramesV1.Point0575.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=569) domain
     SourceMainFramesV1.Point0569.input_defined SourceMainFramesV1.Point0569.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0569.outputs.2.hi (by
         change SourceMainFramesV1.Point0569.outputs.2.hi ∈ [SourceMainFramesV1.Point0568.outputs.2.hi, SourceMainFramesV1.Point0569.outputs.2.hi, SourceMainFramesV1.Point0570.outputs.2.hi, SourceMainFramesV1.Point0571.outputs.2.hi, SourceMainFramesV1.Point0572.outputs.2.hi, SourceMainFramesV1.Point0573.outputs.2.hi, SourceMainFramesV1.Point0574.outputs.2.hi, SourceMainFramesV1.Point0575.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=570) domain
     SourceMainFramesV1.Point0570.input_defined SourceMainFramesV1.Point0570.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0570.outputs.2.hi (by
         change SourceMainFramesV1.Point0570.outputs.2.hi ∈ [SourceMainFramesV1.Point0568.outputs.2.hi, SourceMainFramesV1.Point0569.outputs.2.hi, SourceMainFramesV1.Point0570.outputs.2.hi, SourceMainFramesV1.Point0571.outputs.2.hi, SourceMainFramesV1.Point0572.outputs.2.hi, SourceMainFramesV1.Point0573.outputs.2.hi, SourceMainFramesV1.Point0574.outputs.2.hi, SourceMainFramesV1.Point0575.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=571) domain
     SourceMainFramesV1.Point0571.input_defined SourceMainFramesV1.Point0571.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0571.outputs.2.hi (by
         change SourceMainFramesV1.Point0571.outputs.2.hi ∈ [SourceMainFramesV1.Point0568.outputs.2.hi, SourceMainFramesV1.Point0569.outputs.2.hi, SourceMainFramesV1.Point0570.outputs.2.hi, SourceMainFramesV1.Point0571.outputs.2.hi, SourceMainFramesV1.Point0572.outputs.2.hi, SourceMainFramesV1.Point0573.outputs.2.hi, SourceMainFramesV1.Point0574.outputs.2.hi, SourceMainFramesV1.Point0575.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=572) domain
     SourceMainFramesV1.Point0572.input_defined SourceMainFramesV1.Point0572.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0572.outputs.2.hi (by
         change SourceMainFramesV1.Point0572.outputs.2.hi ∈ [SourceMainFramesV1.Point0568.outputs.2.hi, SourceMainFramesV1.Point0569.outputs.2.hi, SourceMainFramesV1.Point0570.outputs.2.hi, SourceMainFramesV1.Point0571.outputs.2.hi, SourceMainFramesV1.Point0572.outputs.2.hi, SourceMainFramesV1.Point0573.outputs.2.hi, SourceMainFramesV1.Point0574.outputs.2.hi, SourceMainFramesV1.Point0575.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=573) domain
     SourceMainFramesV1.Point0573.input_defined SourceMainFramesV1.Point0573.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0573.outputs.2.hi (by
         change SourceMainFramesV1.Point0573.outputs.2.hi ∈ [SourceMainFramesV1.Point0568.outputs.2.hi, SourceMainFramesV1.Point0569.outputs.2.hi, SourceMainFramesV1.Point0570.outputs.2.hi, SourceMainFramesV1.Point0571.outputs.2.hi, SourceMainFramesV1.Point0572.outputs.2.hi, SourceMainFramesV1.Point0573.outputs.2.hi, SourceMainFramesV1.Point0574.outputs.2.hi, SourceMainFramesV1.Point0575.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=574) domain
     SourceMainFramesV1.Point0574.input_defined SourceMainFramesV1.Point0574.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0574.outputs.2.hi (by
         change SourceMainFramesV1.Point0574.outputs.2.hi ∈ [SourceMainFramesV1.Point0568.outputs.2.hi, SourceMainFramesV1.Point0569.outputs.2.hi, SourceMainFramesV1.Point0570.outputs.2.hi, SourceMainFramesV1.Point0571.outputs.2.hi, SourceMainFramesV1.Point0572.outputs.2.hi, SourceMainFramesV1.Point0573.outputs.2.hi, SourceMainFramesV1.Point0574.outputs.2.hi, SourceMainFramesV1.Point0575.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=575) domain
     SourceMainFramesV1.Point0575.input_defined SourceMainFramesV1.Point0575.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0575.outputs.2.hi (by
         change SourceMainFramesV1.Point0575.outputs.2.hi ∈ [SourceMainFramesV1.Point0568.outputs.2.hi, SourceMainFramesV1.Point0569.outputs.2.hi, SourceMainFramesV1.Point0570.outputs.2.hi, SourceMainFramesV1.Point0571.outputs.2.hi, SourceMainFramesV1.Point0572.outputs.2.hi, SourceMainFramesV1.Point0573.outputs.2.hi, SourceMainFramesV1.Point0574.outputs.2.hi, SourceMainFramesV1.Point0575.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block71
