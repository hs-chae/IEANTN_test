/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0504
import SourceMainFramesV1.Point0505
import SourceMainFramesV1.Point0506
import SourceMainFramesV1.Point0507
import SourceMainFramesV1.Point0508
import SourceMainFramesV1.Point0509
import SourceMainFramesV1.Point0510
import SourceMainFramesV1.Point0511
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block63
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0504.outputs.2.hi,
 SourceMainFramesV1.Point0505.outputs.2.hi,
 SourceMainFramesV1.Point0506.outputs.2.hi,
 SourceMainFramesV1.Point0507.outputs.2.hi,
 SourceMainFramesV1.Point0508.outputs.2.hi,
 SourceMainFramesV1.Point0509.outputs.2.hi,
 SourceMainFramesV1.Point0510.outputs.2.hi,
 SourceMainFramesV1.Point0511.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 504 ≤ i) (high : i < 512)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=504) domain
     SourceMainFramesV1.Point0504.input_defined SourceMainFramesV1.Point0504.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0504.outputs.2.hi (by
         change SourceMainFramesV1.Point0504.outputs.2.hi ∈ [SourceMainFramesV1.Point0504.outputs.2.hi, SourceMainFramesV1.Point0505.outputs.2.hi, SourceMainFramesV1.Point0506.outputs.2.hi, SourceMainFramesV1.Point0507.outputs.2.hi, SourceMainFramesV1.Point0508.outputs.2.hi, SourceMainFramesV1.Point0509.outputs.2.hi, SourceMainFramesV1.Point0510.outputs.2.hi, SourceMainFramesV1.Point0511.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=505) domain
     SourceMainFramesV1.Point0505.input_defined SourceMainFramesV1.Point0505.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0505.outputs.2.hi (by
         change SourceMainFramesV1.Point0505.outputs.2.hi ∈ [SourceMainFramesV1.Point0504.outputs.2.hi, SourceMainFramesV1.Point0505.outputs.2.hi, SourceMainFramesV1.Point0506.outputs.2.hi, SourceMainFramesV1.Point0507.outputs.2.hi, SourceMainFramesV1.Point0508.outputs.2.hi, SourceMainFramesV1.Point0509.outputs.2.hi, SourceMainFramesV1.Point0510.outputs.2.hi, SourceMainFramesV1.Point0511.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=506) domain
     SourceMainFramesV1.Point0506.input_defined SourceMainFramesV1.Point0506.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0506.outputs.2.hi (by
         change SourceMainFramesV1.Point0506.outputs.2.hi ∈ [SourceMainFramesV1.Point0504.outputs.2.hi, SourceMainFramesV1.Point0505.outputs.2.hi, SourceMainFramesV1.Point0506.outputs.2.hi, SourceMainFramesV1.Point0507.outputs.2.hi, SourceMainFramesV1.Point0508.outputs.2.hi, SourceMainFramesV1.Point0509.outputs.2.hi, SourceMainFramesV1.Point0510.outputs.2.hi, SourceMainFramesV1.Point0511.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=507) domain
     SourceMainFramesV1.Point0507.input_defined SourceMainFramesV1.Point0507.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0507.outputs.2.hi (by
         change SourceMainFramesV1.Point0507.outputs.2.hi ∈ [SourceMainFramesV1.Point0504.outputs.2.hi, SourceMainFramesV1.Point0505.outputs.2.hi, SourceMainFramesV1.Point0506.outputs.2.hi, SourceMainFramesV1.Point0507.outputs.2.hi, SourceMainFramesV1.Point0508.outputs.2.hi, SourceMainFramesV1.Point0509.outputs.2.hi, SourceMainFramesV1.Point0510.outputs.2.hi, SourceMainFramesV1.Point0511.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=508) domain
     SourceMainFramesV1.Point0508.input_defined SourceMainFramesV1.Point0508.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0508.outputs.2.hi (by
         change SourceMainFramesV1.Point0508.outputs.2.hi ∈ [SourceMainFramesV1.Point0504.outputs.2.hi, SourceMainFramesV1.Point0505.outputs.2.hi, SourceMainFramesV1.Point0506.outputs.2.hi, SourceMainFramesV1.Point0507.outputs.2.hi, SourceMainFramesV1.Point0508.outputs.2.hi, SourceMainFramesV1.Point0509.outputs.2.hi, SourceMainFramesV1.Point0510.outputs.2.hi, SourceMainFramesV1.Point0511.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=509) domain
     SourceMainFramesV1.Point0509.input_defined SourceMainFramesV1.Point0509.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0509.outputs.2.hi (by
         change SourceMainFramesV1.Point0509.outputs.2.hi ∈ [SourceMainFramesV1.Point0504.outputs.2.hi, SourceMainFramesV1.Point0505.outputs.2.hi, SourceMainFramesV1.Point0506.outputs.2.hi, SourceMainFramesV1.Point0507.outputs.2.hi, SourceMainFramesV1.Point0508.outputs.2.hi, SourceMainFramesV1.Point0509.outputs.2.hi, SourceMainFramesV1.Point0510.outputs.2.hi, SourceMainFramesV1.Point0511.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=510) domain
     SourceMainFramesV1.Point0510.input_defined SourceMainFramesV1.Point0510.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0510.outputs.2.hi (by
         change SourceMainFramesV1.Point0510.outputs.2.hi ∈ [SourceMainFramesV1.Point0504.outputs.2.hi, SourceMainFramesV1.Point0505.outputs.2.hi, SourceMainFramesV1.Point0506.outputs.2.hi, SourceMainFramesV1.Point0507.outputs.2.hi, SourceMainFramesV1.Point0508.outputs.2.hi, SourceMainFramesV1.Point0509.outputs.2.hi, SourceMainFramesV1.Point0510.outputs.2.hi, SourceMainFramesV1.Point0511.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=511) domain
     SourceMainFramesV1.Point0511.input_defined SourceMainFramesV1.Point0511.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0511.outputs.2.hi (by
         change SourceMainFramesV1.Point0511.outputs.2.hi ∈ [SourceMainFramesV1.Point0504.outputs.2.hi, SourceMainFramesV1.Point0505.outputs.2.hi, SourceMainFramesV1.Point0506.outputs.2.hi, SourceMainFramesV1.Point0507.outputs.2.hi, SourceMainFramesV1.Point0508.outputs.2.hi, SourceMainFramesV1.Point0509.outputs.2.hi, SourceMainFramesV1.Point0510.outputs.2.hi, SourceMainFramesV1.Point0511.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block63
