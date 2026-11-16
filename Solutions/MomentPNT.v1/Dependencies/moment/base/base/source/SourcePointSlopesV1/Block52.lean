/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0416
import SourceMainFramesV1.Point0417
import SourceMainFramesV1.Point0418
import SourceMainFramesV1.Point0419
import SourceMainFramesV1.Point0420
import SourceMainFramesV1.Point0421
import SourceMainFramesV1.Point0422
import SourceMainFramesV1.Point0423
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block52
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0416.outputs.2.hi,
 SourceMainFramesV1.Point0417.outputs.2.hi,
 SourceMainFramesV1.Point0418.outputs.2.hi,
 SourceMainFramesV1.Point0419.outputs.2.hi,
 SourceMainFramesV1.Point0420.outputs.2.hi,
 SourceMainFramesV1.Point0421.outputs.2.hi,
 SourceMainFramesV1.Point0422.outputs.2.hi,
 SourceMainFramesV1.Point0423.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 416 ≤ i) (high : i < 424)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=416) domain
     SourceMainFramesV1.Point0416.input_defined SourceMainFramesV1.Point0416.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0416.outputs.2.hi (by
         change SourceMainFramesV1.Point0416.outputs.2.hi ∈ [SourceMainFramesV1.Point0416.outputs.2.hi, SourceMainFramesV1.Point0417.outputs.2.hi, SourceMainFramesV1.Point0418.outputs.2.hi, SourceMainFramesV1.Point0419.outputs.2.hi, SourceMainFramesV1.Point0420.outputs.2.hi, SourceMainFramesV1.Point0421.outputs.2.hi, SourceMainFramesV1.Point0422.outputs.2.hi, SourceMainFramesV1.Point0423.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=417) domain
     SourceMainFramesV1.Point0417.input_defined SourceMainFramesV1.Point0417.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0417.outputs.2.hi (by
         change SourceMainFramesV1.Point0417.outputs.2.hi ∈ [SourceMainFramesV1.Point0416.outputs.2.hi, SourceMainFramesV1.Point0417.outputs.2.hi, SourceMainFramesV1.Point0418.outputs.2.hi, SourceMainFramesV1.Point0419.outputs.2.hi, SourceMainFramesV1.Point0420.outputs.2.hi, SourceMainFramesV1.Point0421.outputs.2.hi, SourceMainFramesV1.Point0422.outputs.2.hi, SourceMainFramesV1.Point0423.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=418) domain
     SourceMainFramesV1.Point0418.input_defined SourceMainFramesV1.Point0418.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0418.outputs.2.hi (by
         change SourceMainFramesV1.Point0418.outputs.2.hi ∈ [SourceMainFramesV1.Point0416.outputs.2.hi, SourceMainFramesV1.Point0417.outputs.2.hi, SourceMainFramesV1.Point0418.outputs.2.hi, SourceMainFramesV1.Point0419.outputs.2.hi, SourceMainFramesV1.Point0420.outputs.2.hi, SourceMainFramesV1.Point0421.outputs.2.hi, SourceMainFramesV1.Point0422.outputs.2.hi, SourceMainFramesV1.Point0423.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=419) domain
     SourceMainFramesV1.Point0419.input_defined SourceMainFramesV1.Point0419.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0419.outputs.2.hi (by
         change SourceMainFramesV1.Point0419.outputs.2.hi ∈ [SourceMainFramesV1.Point0416.outputs.2.hi, SourceMainFramesV1.Point0417.outputs.2.hi, SourceMainFramesV1.Point0418.outputs.2.hi, SourceMainFramesV1.Point0419.outputs.2.hi, SourceMainFramesV1.Point0420.outputs.2.hi, SourceMainFramesV1.Point0421.outputs.2.hi, SourceMainFramesV1.Point0422.outputs.2.hi, SourceMainFramesV1.Point0423.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=420) domain
     SourceMainFramesV1.Point0420.input_defined SourceMainFramesV1.Point0420.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0420.outputs.2.hi (by
         change SourceMainFramesV1.Point0420.outputs.2.hi ∈ [SourceMainFramesV1.Point0416.outputs.2.hi, SourceMainFramesV1.Point0417.outputs.2.hi, SourceMainFramesV1.Point0418.outputs.2.hi, SourceMainFramesV1.Point0419.outputs.2.hi, SourceMainFramesV1.Point0420.outputs.2.hi, SourceMainFramesV1.Point0421.outputs.2.hi, SourceMainFramesV1.Point0422.outputs.2.hi, SourceMainFramesV1.Point0423.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=421) domain
     SourceMainFramesV1.Point0421.input_defined SourceMainFramesV1.Point0421.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0421.outputs.2.hi (by
         change SourceMainFramesV1.Point0421.outputs.2.hi ∈ [SourceMainFramesV1.Point0416.outputs.2.hi, SourceMainFramesV1.Point0417.outputs.2.hi, SourceMainFramesV1.Point0418.outputs.2.hi, SourceMainFramesV1.Point0419.outputs.2.hi, SourceMainFramesV1.Point0420.outputs.2.hi, SourceMainFramesV1.Point0421.outputs.2.hi, SourceMainFramesV1.Point0422.outputs.2.hi, SourceMainFramesV1.Point0423.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=422) domain
     SourceMainFramesV1.Point0422.input_defined SourceMainFramesV1.Point0422.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0422.outputs.2.hi (by
         change SourceMainFramesV1.Point0422.outputs.2.hi ∈ [SourceMainFramesV1.Point0416.outputs.2.hi, SourceMainFramesV1.Point0417.outputs.2.hi, SourceMainFramesV1.Point0418.outputs.2.hi, SourceMainFramesV1.Point0419.outputs.2.hi, SourceMainFramesV1.Point0420.outputs.2.hi, SourceMainFramesV1.Point0421.outputs.2.hi, SourceMainFramesV1.Point0422.outputs.2.hi, SourceMainFramesV1.Point0423.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=423) domain
     SourceMainFramesV1.Point0423.input_defined SourceMainFramesV1.Point0423.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0423.outputs.2.hi (by
         change SourceMainFramesV1.Point0423.outputs.2.hi ∈ [SourceMainFramesV1.Point0416.outputs.2.hi, SourceMainFramesV1.Point0417.outputs.2.hi, SourceMainFramesV1.Point0418.outputs.2.hi, SourceMainFramesV1.Point0419.outputs.2.hi, SourceMainFramesV1.Point0420.outputs.2.hi, SourceMainFramesV1.Point0421.outputs.2.hi, SourceMainFramesV1.Point0422.outputs.2.hi, SourceMainFramesV1.Point0423.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block52
