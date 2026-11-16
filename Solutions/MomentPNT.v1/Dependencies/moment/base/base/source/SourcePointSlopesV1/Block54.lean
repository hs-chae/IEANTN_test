/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0432
import SourceMainFramesV1.Point0433
import SourceMainFramesV1.Point0434
import SourceMainFramesV1.Point0435
import SourceMainFramesV1.Point0436
import SourceMainFramesV1.Point0437
import SourceMainFramesV1.Point0438
import SourceMainFramesV1.Point0439
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block54
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0432.outputs.2.hi,
 SourceMainFramesV1.Point0433.outputs.2.hi,
 SourceMainFramesV1.Point0434.outputs.2.hi,
 SourceMainFramesV1.Point0435.outputs.2.hi,
 SourceMainFramesV1.Point0436.outputs.2.hi,
 SourceMainFramesV1.Point0437.outputs.2.hi,
 SourceMainFramesV1.Point0438.outputs.2.hi,
 SourceMainFramesV1.Point0439.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 432 ≤ i) (high : i < 440)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=432) domain
     SourceMainFramesV1.Point0432.input_defined SourceMainFramesV1.Point0432.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0432.outputs.2.hi (by
         change SourceMainFramesV1.Point0432.outputs.2.hi ∈ [SourceMainFramesV1.Point0432.outputs.2.hi, SourceMainFramesV1.Point0433.outputs.2.hi, SourceMainFramesV1.Point0434.outputs.2.hi, SourceMainFramesV1.Point0435.outputs.2.hi, SourceMainFramesV1.Point0436.outputs.2.hi, SourceMainFramesV1.Point0437.outputs.2.hi, SourceMainFramesV1.Point0438.outputs.2.hi, SourceMainFramesV1.Point0439.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=433) domain
     SourceMainFramesV1.Point0433.input_defined SourceMainFramesV1.Point0433.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0433.outputs.2.hi (by
         change SourceMainFramesV1.Point0433.outputs.2.hi ∈ [SourceMainFramesV1.Point0432.outputs.2.hi, SourceMainFramesV1.Point0433.outputs.2.hi, SourceMainFramesV1.Point0434.outputs.2.hi, SourceMainFramesV1.Point0435.outputs.2.hi, SourceMainFramesV1.Point0436.outputs.2.hi, SourceMainFramesV1.Point0437.outputs.2.hi, SourceMainFramesV1.Point0438.outputs.2.hi, SourceMainFramesV1.Point0439.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=434) domain
     SourceMainFramesV1.Point0434.input_defined SourceMainFramesV1.Point0434.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0434.outputs.2.hi (by
         change SourceMainFramesV1.Point0434.outputs.2.hi ∈ [SourceMainFramesV1.Point0432.outputs.2.hi, SourceMainFramesV1.Point0433.outputs.2.hi, SourceMainFramesV1.Point0434.outputs.2.hi, SourceMainFramesV1.Point0435.outputs.2.hi, SourceMainFramesV1.Point0436.outputs.2.hi, SourceMainFramesV1.Point0437.outputs.2.hi, SourceMainFramesV1.Point0438.outputs.2.hi, SourceMainFramesV1.Point0439.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=435) domain
     SourceMainFramesV1.Point0435.input_defined SourceMainFramesV1.Point0435.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0435.outputs.2.hi (by
         change SourceMainFramesV1.Point0435.outputs.2.hi ∈ [SourceMainFramesV1.Point0432.outputs.2.hi, SourceMainFramesV1.Point0433.outputs.2.hi, SourceMainFramesV1.Point0434.outputs.2.hi, SourceMainFramesV1.Point0435.outputs.2.hi, SourceMainFramesV1.Point0436.outputs.2.hi, SourceMainFramesV1.Point0437.outputs.2.hi, SourceMainFramesV1.Point0438.outputs.2.hi, SourceMainFramesV1.Point0439.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=436) domain
     SourceMainFramesV1.Point0436.input_defined SourceMainFramesV1.Point0436.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0436.outputs.2.hi (by
         change SourceMainFramesV1.Point0436.outputs.2.hi ∈ [SourceMainFramesV1.Point0432.outputs.2.hi, SourceMainFramesV1.Point0433.outputs.2.hi, SourceMainFramesV1.Point0434.outputs.2.hi, SourceMainFramesV1.Point0435.outputs.2.hi, SourceMainFramesV1.Point0436.outputs.2.hi, SourceMainFramesV1.Point0437.outputs.2.hi, SourceMainFramesV1.Point0438.outputs.2.hi, SourceMainFramesV1.Point0439.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=437) domain
     SourceMainFramesV1.Point0437.input_defined SourceMainFramesV1.Point0437.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0437.outputs.2.hi (by
         change SourceMainFramesV1.Point0437.outputs.2.hi ∈ [SourceMainFramesV1.Point0432.outputs.2.hi, SourceMainFramesV1.Point0433.outputs.2.hi, SourceMainFramesV1.Point0434.outputs.2.hi, SourceMainFramesV1.Point0435.outputs.2.hi, SourceMainFramesV1.Point0436.outputs.2.hi, SourceMainFramesV1.Point0437.outputs.2.hi, SourceMainFramesV1.Point0438.outputs.2.hi, SourceMainFramesV1.Point0439.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=438) domain
     SourceMainFramesV1.Point0438.input_defined SourceMainFramesV1.Point0438.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0438.outputs.2.hi (by
         change SourceMainFramesV1.Point0438.outputs.2.hi ∈ [SourceMainFramesV1.Point0432.outputs.2.hi, SourceMainFramesV1.Point0433.outputs.2.hi, SourceMainFramesV1.Point0434.outputs.2.hi, SourceMainFramesV1.Point0435.outputs.2.hi, SourceMainFramesV1.Point0436.outputs.2.hi, SourceMainFramesV1.Point0437.outputs.2.hi, SourceMainFramesV1.Point0438.outputs.2.hi, SourceMainFramesV1.Point0439.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=439) domain
     SourceMainFramesV1.Point0439.input_defined SourceMainFramesV1.Point0439.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0439.outputs.2.hi (by
         change SourceMainFramesV1.Point0439.outputs.2.hi ∈ [SourceMainFramesV1.Point0432.outputs.2.hi, SourceMainFramesV1.Point0433.outputs.2.hi, SourceMainFramesV1.Point0434.outputs.2.hi, SourceMainFramesV1.Point0435.outputs.2.hi, SourceMainFramesV1.Point0436.outputs.2.hi, SourceMainFramesV1.Point0437.outputs.2.hi, SourceMainFramesV1.Point0438.outputs.2.hi, SourceMainFramesV1.Point0439.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block54
