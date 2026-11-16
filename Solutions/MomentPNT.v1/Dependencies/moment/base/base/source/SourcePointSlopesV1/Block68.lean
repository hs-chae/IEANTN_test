/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0544
import SourceMainFramesV1.Point0545
import SourceMainFramesV1.Point0546
import SourceMainFramesV1.Point0547
import SourceMainFramesV1.Point0548
import SourceMainFramesV1.Point0549
import SourceMainFramesV1.Point0550
import SourceMainFramesV1.Point0551
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block68
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0544.outputs.2.hi,
 SourceMainFramesV1.Point0545.outputs.2.hi,
 SourceMainFramesV1.Point0546.outputs.2.hi,
 SourceMainFramesV1.Point0547.outputs.2.hi,
 SourceMainFramesV1.Point0548.outputs.2.hi,
 SourceMainFramesV1.Point0549.outputs.2.hi,
 SourceMainFramesV1.Point0550.outputs.2.hi,
 SourceMainFramesV1.Point0551.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 544 ≤ i) (high : i < 552)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=544) domain
     SourceMainFramesV1.Point0544.input_defined SourceMainFramesV1.Point0544.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0544.outputs.2.hi (by
         change SourceMainFramesV1.Point0544.outputs.2.hi ∈ [SourceMainFramesV1.Point0544.outputs.2.hi, SourceMainFramesV1.Point0545.outputs.2.hi, SourceMainFramesV1.Point0546.outputs.2.hi, SourceMainFramesV1.Point0547.outputs.2.hi, SourceMainFramesV1.Point0548.outputs.2.hi, SourceMainFramesV1.Point0549.outputs.2.hi, SourceMainFramesV1.Point0550.outputs.2.hi, SourceMainFramesV1.Point0551.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=545) domain
     SourceMainFramesV1.Point0545.input_defined SourceMainFramesV1.Point0545.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0545.outputs.2.hi (by
         change SourceMainFramesV1.Point0545.outputs.2.hi ∈ [SourceMainFramesV1.Point0544.outputs.2.hi, SourceMainFramesV1.Point0545.outputs.2.hi, SourceMainFramesV1.Point0546.outputs.2.hi, SourceMainFramesV1.Point0547.outputs.2.hi, SourceMainFramesV1.Point0548.outputs.2.hi, SourceMainFramesV1.Point0549.outputs.2.hi, SourceMainFramesV1.Point0550.outputs.2.hi, SourceMainFramesV1.Point0551.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=546) domain
     SourceMainFramesV1.Point0546.input_defined SourceMainFramesV1.Point0546.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0546.outputs.2.hi (by
         change SourceMainFramesV1.Point0546.outputs.2.hi ∈ [SourceMainFramesV1.Point0544.outputs.2.hi, SourceMainFramesV1.Point0545.outputs.2.hi, SourceMainFramesV1.Point0546.outputs.2.hi, SourceMainFramesV1.Point0547.outputs.2.hi, SourceMainFramesV1.Point0548.outputs.2.hi, SourceMainFramesV1.Point0549.outputs.2.hi, SourceMainFramesV1.Point0550.outputs.2.hi, SourceMainFramesV1.Point0551.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=547) domain
     SourceMainFramesV1.Point0547.input_defined SourceMainFramesV1.Point0547.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0547.outputs.2.hi (by
         change SourceMainFramesV1.Point0547.outputs.2.hi ∈ [SourceMainFramesV1.Point0544.outputs.2.hi, SourceMainFramesV1.Point0545.outputs.2.hi, SourceMainFramesV1.Point0546.outputs.2.hi, SourceMainFramesV1.Point0547.outputs.2.hi, SourceMainFramesV1.Point0548.outputs.2.hi, SourceMainFramesV1.Point0549.outputs.2.hi, SourceMainFramesV1.Point0550.outputs.2.hi, SourceMainFramesV1.Point0551.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=548) domain
     SourceMainFramesV1.Point0548.input_defined SourceMainFramesV1.Point0548.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0548.outputs.2.hi (by
         change SourceMainFramesV1.Point0548.outputs.2.hi ∈ [SourceMainFramesV1.Point0544.outputs.2.hi, SourceMainFramesV1.Point0545.outputs.2.hi, SourceMainFramesV1.Point0546.outputs.2.hi, SourceMainFramesV1.Point0547.outputs.2.hi, SourceMainFramesV1.Point0548.outputs.2.hi, SourceMainFramesV1.Point0549.outputs.2.hi, SourceMainFramesV1.Point0550.outputs.2.hi, SourceMainFramesV1.Point0551.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=549) domain
     SourceMainFramesV1.Point0549.input_defined SourceMainFramesV1.Point0549.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0549.outputs.2.hi (by
         change SourceMainFramesV1.Point0549.outputs.2.hi ∈ [SourceMainFramesV1.Point0544.outputs.2.hi, SourceMainFramesV1.Point0545.outputs.2.hi, SourceMainFramesV1.Point0546.outputs.2.hi, SourceMainFramesV1.Point0547.outputs.2.hi, SourceMainFramesV1.Point0548.outputs.2.hi, SourceMainFramesV1.Point0549.outputs.2.hi, SourceMainFramesV1.Point0550.outputs.2.hi, SourceMainFramesV1.Point0551.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=550) domain
     SourceMainFramesV1.Point0550.input_defined SourceMainFramesV1.Point0550.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0550.outputs.2.hi (by
         change SourceMainFramesV1.Point0550.outputs.2.hi ∈ [SourceMainFramesV1.Point0544.outputs.2.hi, SourceMainFramesV1.Point0545.outputs.2.hi, SourceMainFramesV1.Point0546.outputs.2.hi, SourceMainFramesV1.Point0547.outputs.2.hi, SourceMainFramesV1.Point0548.outputs.2.hi, SourceMainFramesV1.Point0549.outputs.2.hi, SourceMainFramesV1.Point0550.outputs.2.hi, SourceMainFramesV1.Point0551.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=551) domain
     SourceMainFramesV1.Point0551.input_defined SourceMainFramesV1.Point0551.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0551.outputs.2.hi (by
         change SourceMainFramesV1.Point0551.outputs.2.hi ∈ [SourceMainFramesV1.Point0544.outputs.2.hi, SourceMainFramesV1.Point0545.outputs.2.hi, SourceMainFramesV1.Point0546.outputs.2.hi, SourceMainFramesV1.Point0547.outputs.2.hi, SourceMainFramesV1.Point0548.outputs.2.hi, SourceMainFramesV1.Point0549.outputs.2.hi, SourceMainFramesV1.Point0550.outputs.2.hi, SourceMainFramesV1.Point0551.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block68
