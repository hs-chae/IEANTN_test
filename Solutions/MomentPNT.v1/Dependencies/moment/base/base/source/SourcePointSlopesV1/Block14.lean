/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0112
import SourceMainFramesV1.Point0113
import SourceMainFramesV1.Point0114
import SourceMainFramesV1.Point0115
import SourceMainFramesV1.Point0116
import SourceMainFramesV1.Point0117
import SourceMainFramesV1.Point0118
import SourceMainFramesV1.Point0119
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block14
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0112.outputs.2.hi,
 SourceMainFramesV1.Point0113.outputs.2.hi,
 SourceMainFramesV1.Point0114.outputs.2.hi,
 SourceMainFramesV1.Point0115.outputs.2.hi,
 SourceMainFramesV1.Point0116.outputs.2.hi,
 SourceMainFramesV1.Point0117.outputs.2.hi,
 SourceMainFramesV1.Point0118.outputs.2.hi,
 SourceMainFramesV1.Point0119.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 112 ≤ i) (high : i < 120)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=112) domain
     SourceMainFramesV1.Point0112.input_defined SourceMainFramesV1.Point0112.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0112.outputs.2.hi (by
         change SourceMainFramesV1.Point0112.outputs.2.hi ∈ [SourceMainFramesV1.Point0112.outputs.2.hi, SourceMainFramesV1.Point0113.outputs.2.hi, SourceMainFramesV1.Point0114.outputs.2.hi, SourceMainFramesV1.Point0115.outputs.2.hi, SourceMainFramesV1.Point0116.outputs.2.hi, SourceMainFramesV1.Point0117.outputs.2.hi, SourceMainFramesV1.Point0118.outputs.2.hi, SourceMainFramesV1.Point0119.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=113) domain
     SourceMainFramesV1.Point0113.input_defined SourceMainFramesV1.Point0113.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0113.outputs.2.hi (by
         change SourceMainFramesV1.Point0113.outputs.2.hi ∈ [SourceMainFramesV1.Point0112.outputs.2.hi, SourceMainFramesV1.Point0113.outputs.2.hi, SourceMainFramesV1.Point0114.outputs.2.hi, SourceMainFramesV1.Point0115.outputs.2.hi, SourceMainFramesV1.Point0116.outputs.2.hi, SourceMainFramesV1.Point0117.outputs.2.hi, SourceMainFramesV1.Point0118.outputs.2.hi, SourceMainFramesV1.Point0119.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=114) domain
     SourceMainFramesV1.Point0114.input_defined SourceMainFramesV1.Point0114.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0114.outputs.2.hi (by
         change SourceMainFramesV1.Point0114.outputs.2.hi ∈ [SourceMainFramesV1.Point0112.outputs.2.hi, SourceMainFramesV1.Point0113.outputs.2.hi, SourceMainFramesV1.Point0114.outputs.2.hi, SourceMainFramesV1.Point0115.outputs.2.hi, SourceMainFramesV1.Point0116.outputs.2.hi, SourceMainFramesV1.Point0117.outputs.2.hi, SourceMainFramesV1.Point0118.outputs.2.hi, SourceMainFramesV1.Point0119.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=115) domain
     SourceMainFramesV1.Point0115.input_defined SourceMainFramesV1.Point0115.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0115.outputs.2.hi (by
         change SourceMainFramesV1.Point0115.outputs.2.hi ∈ [SourceMainFramesV1.Point0112.outputs.2.hi, SourceMainFramesV1.Point0113.outputs.2.hi, SourceMainFramesV1.Point0114.outputs.2.hi, SourceMainFramesV1.Point0115.outputs.2.hi, SourceMainFramesV1.Point0116.outputs.2.hi, SourceMainFramesV1.Point0117.outputs.2.hi, SourceMainFramesV1.Point0118.outputs.2.hi, SourceMainFramesV1.Point0119.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=116) domain
     SourceMainFramesV1.Point0116.input_defined SourceMainFramesV1.Point0116.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0116.outputs.2.hi (by
         change SourceMainFramesV1.Point0116.outputs.2.hi ∈ [SourceMainFramesV1.Point0112.outputs.2.hi, SourceMainFramesV1.Point0113.outputs.2.hi, SourceMainFramesV1.Point0114.outputs.2.hi, SourceMainFramesV1.Point0115.outputs.2.hi, SourceMainFramesV1.Point0116.outputs.2.hi, SourceMainFramesV1.Point0117.outputs.2.hi, SourceMainFramesV1.Point0118.outputs.2.hi, SourceMainFramesV1.Point0119.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=117) domain
     SourceMainFramesV1.Point0117.input_defined SourceMainFramesV1.Point0117.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0117.outputs.2.hi (by
         change SourceMainFramesV1.Point0117.outputs.2.hi ∈ [SourceMainFramesV1.Point0112.outputs.2.hi, SourceMainFramesV1.Point0113.outputs.2.hi, SourceMainFramesV1.Point0114.outputs.2.hi, SourceMainFramesV1.Point0115.outputs.2.hi, SourceMainFramesV1.Point0116.outputs.2.hi, SourceMainFramesV1.Point0117.outputs.2.hi, SourceMainFramesV1.Point0118.outputs.2.hi, SourceMainFramesV1.Point0119.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=118) domain
     SourceMainFramesV1.Point0118.input_defined SourceMainFramesV1.Point0118.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0118.outputs.2.hi (by
         change SourceMainFramesV1.Point0118.outputs.2.hi ∈ [SourceMainFramesV1.Point0112.outputs.2.hi, SourceMainFramesV1.Point0113.outputs.2.hi, SourceMainFramesV1.Point0114.outputs.2.hi, SourceMainFramesV1.Point0115.outputs.2.hi, SourceMainFramesV1.Point0116.outputs.2.hi, SourceMainFramesV1.Point0117.outputs.2.hi, SourceMainFramesV1.Point0118.outputs.2.hi, SourceMainFramesV1.Point0119.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=119) domain
     SourceMainFramesV1.Point0119.input_defined SourceMainFramesV1.Point0119.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0119.outputs.2.hi (by
         change SourceMainFramesV1.Point0119.outputs.2.hi ∈ [SourceMainFramesV1.Point0112.outputs.2.hi, SourceMainFramesV1.Point0113.outputs.2.hi, SourceMainFramesV1.Point0114.outputs.2.hi, SourceMainFramesV1.Point0115.outputs.2.hi, SourceMainFramesV1.Point0116.outputs.2.hi, SourceMainFramesV1.Point0117.outputs.2.hi, SourceMainFramesV1.Point0118.outputs.2.hi, SourceMainFramesV1.Point0119.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block14
