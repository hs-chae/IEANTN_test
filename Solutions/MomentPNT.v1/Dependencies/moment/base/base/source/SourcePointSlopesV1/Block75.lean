/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0600
import SourceMainFramesV1.Point0601
import SourceMainFramesV1.Point0602
import SourceMainFramesV1.Point0603
import SourceMainFramesV1.Point0604
import SourceMainFramesV1.Point0605
import SourceMainFramesV1.Point0606
import SourceMainFramesV1.Point0607
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block75
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0600.outputs.2.hi,
 SourceMainFramesV1.Point0601.outputs.2.hi,
 SourceMainFramesV1.Point0602.outputs.2.hi,
 SourceMainFramesV1.Point0603.outputs.2.hi,
 SourceMainFramesV1.Point0604.outputs.2.hi,
 SourceMainFramesV1.Point0605.outputs.2.hi,
 SourceMainFramesV1.Point0606.outputs.2.hi,
 SourceMainFramesV1.Point0607.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 600 ≤ i) (high : i < 608)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=600) domain
     SourceMainFramesV1.Point0600.input_defined SourceMainFramesV1.Point0600.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0600.outputs.2.hi (by
         change SourceMainFramesV1.Point0600.outputs.2.hi ∈ [SourceMainFramesV1.Point0600.outputs.2.hi, SourceMainFramesV1.Point0601.outputs.2.hi, SourceMainFramesV1.Point0602.outputs.2.hi, SourceMainFramesV1.Point0603.outputs.2.hi, SourceMainFramesV1.Point0604.outputs.2.hi, SourceMainFramesV1.Point0605.outputs.2.hi, SourceMainFramesV1.Point0606.outputs.2.hi, SourceMainFramesV1.Point0607.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=601) domain
     SourceMainFramesV1.Point0601.input_defined SourceMainFramesV1.Point0601.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0601.outputs.2.hi (by
         change SourceMainFramesV1.Point0601.outputs.2.hi ∈ [SourceMainFramesV1.Point0600.outputs.2.hi, SourceMainFramesV1.Point0601.outputs.2.hi, SourceMainFramesV1.Point0602.outputs.2.hi, SourceMainFramesV1.Point0603.outputs.2.hi, SourceMainFramesV1.Point0604.outputs.2.hi, SourceMainFramesV1.Point0605.outputs.2.hi, SourceMainFramesV1.Point0606.outputs.2.hi, SourceMainFramesV1.Point0607.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=602) domain
     SourceMainFramesV1.Point0602.input_defined SourceMainFramesV1.Point0602.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0602.outputs.2.hi (by
         change SourceMainFramesV1.Point0602.outputs.2.hi ∈ [SourceMainFramesV1.Point0600.outputs.2.hi, SourceMainFramesV1.Point0601.outputs.2.hi, SourceMainFramesV1.Point0602.outputs.2.hi, SourceMainFramesV1.Point0603.outputs.2.hi, SourceMainFramesV1.Point0604.outputs.2.hi, SourceMainFramesV1.Point0605.outputs.2.hi, SourceMainFramesV1.Point0606.outputs.2.hi, SourceMainFramesV1.Point0607.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=603) domain
     SourceMainFramesV1.Point0603.input_defined SourceMainFramesV1.Point0603.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0603.outputs.2.hi (by
         change SourceMainFramesV1.Point0603.outputs.2.hi ∈ [SourceMainFramesV1.Point0600.outputs.2.hi, SourceMainFramesV1.Point0601.outputs.2.hi, SourceMainFramesV1.Point0602.outputs.2.hi, SourceMainFramesV1.Point0603.outputs.2.hi, SourceMainFramesV1.Point0604.outputs.2.hi, SourceMainFramesV1.Point0605.outputs.2.hi, SourceMainFramesV1.Point0606.outputs.2.hi, SourceMainFramesV1.Point0607.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=604) domain
     SourceMainFramesV1.Point0604.input_defined SourceMainFramesV1.Point0604.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0604.outputs.2.hi (by
         change SourceMainFramesV1.Point0604.outputs.2.hi ∈ [SourceMainFramesV1.Point0600.outputs.2.hi, SourceMainFramesV1.Point0601.outputs.2.hi, SourceMainFramesV1.Point0602.outputs.2.hi, SourceMainFramesV1.Point0603.outputs.2.hi, SourceMainFramesV1.Point0604.outputs.2.hi, SourceMainFramesV1.Point0605.outputs.2.hi, SourceMainFramesV1.Point0606.outputs.2.hi, SourceMainFramesV1.Point0607.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=605) domain
     SourceMainFramesV1.Point0605.input_defined SourceMainFramesV1.Point0605.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0605.outputs.2.hi (by
         change SourceMainFramesV1.Point0605.outputs.2.hi ∈ [SourceMainFramesV1.Point0600.outputs.2.hi, SourceMainFramesV1.Point0601.outputs.2.hi, SourceMainFramesV1.Point0602.outputs.2.hi, SourceMainFramesV1.Point0603.outputs.2.hi, SourceMainFramesV1.Point0604.outputs.2.hi, SourceMainFramesV1.Point0605.outputs.2.hi, SourceMainFramesV1.Point0606.outputs.2.hi, SourceMainFramesV1.Point0607.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=606) domain
     SourceMainFramesV1.Point0606.input_defined SourceMainFramesV1.Point0606.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0606.outputs.2.hi (by
         change SourceMainFramesV1.Point0606.outputs.2.hi ∈ [SourceMainFramesV1.Point0600.outputs.2.hi, SourceMainFramesV1.Point0601.outputs.2.hi, SourceMainFramesV1.Point0602.outputs.2.hi, SourceMainFramesV1.Point0603.outputs.2.hi, SourceMainFramesV1.Point0604.outputs.2.hi, SourceMainFramesV1.Point0605.outputs.2.hi, SourceMainFramesV1.Point0606.outputs.2.hi, SourceMainFramesV1.Point0607.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=607) domain
     SourceMainFramesV1.Point0607.input_defined SourceMainFramesV1.Point0607.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0607.outputs.2.hi (by
         change SourceMainFramesV1.Point0607.outputs.2.hi ∈ [SourceMainFramesV1.Point0600.outputs.2.hi, SourceMainFramesV1.Point0601.outputs.2.hi, SourceMainFramesV1.Point0602.outputs.2.hi, SourceMainFramesV1.Point0603.outputs.2.hi, SourceMainFramesV1.Point0604.outputs.2.hi, SourceMainFramesV1.Point0605.outputs.2.hi, SourceMainFramesV1.Point0606.outputs.2.hi, SourceMainFramesV1.Point0607.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block75
