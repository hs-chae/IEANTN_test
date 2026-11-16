/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0688
import SourceMainFramesV1.Point0689
import SourceMainFramesV1.Point0690
import SourceMainFramesV1.Point0691
import SourceMainFramesV1.Point0692
import SourceMainFramesV1.Point0693
import SourceMainFramesV1.Point0694
import SourceMainFramesV1.Point0695
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block86
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0688.outputs.2.hi,
 SourceMainFramesV1.Point0689.outputs.2.hi,
 SourceMainFramesV1.Point0690.outputs.2.hi,
 SourceMainFramesV1.Point0691.outputs.2.hi,
 SourceMainFramesV1.Point0692.outputs.2.hi,
 SourceMainFramesV1.Point0693.outputs.2.hi,
 SourceMainFramesV1.Point0694.outputs.2.hi,
 SourceMainFramesV1.Point0695.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 688 ≤ i) (high : i < 696)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=688) domain
     SourceMainFramesV1.Point0688.input_defined SourceMainFramesV1.Point0688.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0688.outputs.2.hi (by
         change SourceMainFramesV1.Point0688.outputs.2.hi ∈ [SourceMainFramesV1.Point0688.outputs.2.hi, SourceMainFramesV1.Point0689.outputs.2.hi, SourceMainFramesV1.Point0690.outputs.2.hi, SourceMainFramesV1.Point0691.outputs.2.hi, SourceMainFramesV1.Point0692.outputs.2.hi, SourceMainFramesV1.Point0693.outputs.2.hi, SourceMainFramesV1.Point0694.outputs.2.hi, SourceMainFramesV1.Point0695.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=689) domain
     SourceMainFramesV1.Point0689.input_defined SourceMainFramesV1.Point0689.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0689.outputs.2.hi (by
         change SourceMainFramesV1.Point0689.outputs.2.hi ∈ [SourceMainFramesV1.Point0688.outputs.2.hi, SourceMainFramesV1.Point0689.outputs.2.hi, SourceMainFramesV1.Point0690.outputs.2.hi, SourceMainFramesV1.Point0691.outputs.2.hi, SourceMainFramesV1.Point0692.outputs.2.hi, SourceMainFramesV1.Point0693.outputs.2.hi, SourceMainFramesV1.Point0694.outputs.2.hi, SourceMainFramesV1.Point0695.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=690) domain
     SourceMainFramesV1.Point0690.input_defined SourceMainFramesV1.Point0690.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0690.outputs.2.hi (by
         change SourceMainFramesV1.Point0690.outputs.2.hi ∈ [SourceMainFramesV1.Point0688.outputs.2.hi, SourceMainFramesV1.Point0689.outputs.2.hi, SourceMainFramesV1.Point0690.outputs.2.hi, SourceMainFramesV1.Point0691.outputs.2.hi, SourceMainFramesV1.Point0692.outputs.2.hi, SourceMainFramesV1.Point0693.outputs.2.hi, SourceMainFramesV1.Point0694.outputs.2.hi, SourceMainFramesV1.Point0695.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=691) domain
     SourceMainFramesV1.Point0691.input_defined SourceMainFramesV1.Point0691.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0691.outputs.2.hi (by
         change SourceMainFramesV1.Point0691.outputs.2.hi ∈ [SourceMainFramesV1.Point0688.outputs.2.hi, SourceMainFramesV1.Point0689.outputs.2.hi, SourceMainFramesV1.Point0690.outputs.2.hi, SourceMainFramesV1.Point0691.outputs.2.hi, SourceMainFramesV1.Point0692.outputs.2.hi, SourceMainFramesV1.Point0693.outputs.2.hi, SourceMainFramesV1.Point0694.outputs.2.hi, SourceMainFramesV1.Point0695.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=692) domain
     SourceMainFramesV1.Point0692.input_defined SourceMainFramesV1.Point0692.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0692.outputs.2.hi (by
         change SourceMainFramesV1.Point0692.outputs.2.hi ∈ [SourceMainFramesV1.Point0688.outputs.2.hi, SourceMainFramesV1.Point0689.outputs.2.hi, SourceMainFramesV1.Point0690.outputs.2.hi, SourceMainFramesV1.Point0691.outputs.2.hi, SourceMainFramesV1.Point0692.outputs.2.hi, SourceMainFramesV1.Point0693.outputs.2.hi, SourceMainFramesV1.Point0694.outputs.2.hi, SourceMainFramesV1.Point0695.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=693) domain
     SourceMainFramesV1.Point0693.input_defined SourceMainFramesV1.Point0693.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0693.outputs.2.hi (by
         change SourceMainFramesV1.Point0693.outputs.2.hi ∈ [SourceMainFramesV1.Point0688.outputs.2.hi, SourceMainFramesV1.Point0689.outputs.2.hi, SourceMainFramesV1.Point0690.outputs.2.hi, SourceMainFramesV1.Point0691.outputs.2.hi, SourceMainFramesV1.Point0692.outputs.2.hi, SourceMainFramesV1.Point0693.outputs.2.hi, SourceMainFramesV1.Point0694.outputs.2.hi, SourceMainFramesV1.Point0695.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=694) domain
     SourceMainFramesV1.Point0694.input_defined SourceMainFramesV1.Point0694.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0694.outputs.2.hi (by
         change SourceMainFramesV1.Point0694.outputs.2.hi ∈ [SourceMainFramesV1.Point0688.outputs.2.hi, SourceMainFramesV1.Point0689.outputs.2.hi, SourceMainFramesV1.Point0690.outputs.2.hi, SourceMainFramesV1.Point0691.outputs.2.hi, SourceMainFramesV1.Point0692.outputs.2.hi, SourceMainFramesV1.Point0693.outputs.2.hi, SourceMainFramesV1.Point0694.outputs.2.hi, SourceMainFramesV1.Point0695.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=695) domain
     SourceMainFramesV1.Point0695.input_defined SourceMainFramesV1.Point0695.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0695.outputs.2.hi (by
         change SourceMainFramesV1.Point0695.outputs.2.hi ∈ [SourceMainFramesV1.Point0688.outputs.2.hi, SourceMainFramesV1.Point0689.outputs.2.hi, SourceMainFramesV1.Point0690.outputs.2.hi, SourceMainFramesV1.Point0691.outputs.2.hi, SourceMainFramesV1.Point0692.outputs.2.hi, SourceMainFramesV1.Point0693.outputs.2.hi, SourceMainFramesV1.Point0694.outputs.2.hi, SourceMainFramesV1.Point0695.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block86
