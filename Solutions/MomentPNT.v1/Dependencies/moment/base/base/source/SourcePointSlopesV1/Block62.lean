/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0496
import SourceMainFramesV1.Point0497
import SourceMainFramesV1.Point0498
import SourceMainFramesV1.Point0499
import SourceMainFramesV1.Point0500
import SourceMainFramesV1.Point0501
import SourceMainFramesV1.Point0502
import SourceMainFramesV1.Point0503
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block62
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0496.outputs.2.hi,
 SourceMainFramesV1.Point0497.outputs.2.hi,
 SourceMainFramesV1.Point0498.outputs.2.hi,
 SourceMainFramesV1.Point0499.outputs.2.hi,
 SourceMainFramesV1.Point0500.outputs.2.hi,
 SourceMainFramesV1.Point0501.outputs.2.hi,
 SourceMainFramesV1.Point0502.outputs.2.hi,
 SourceMainFramesV1.Point0503.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 496 ≤ i) (high : i < 504)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=496) domain
     SourceMainFramesV1.Point0496.input_defined SourceMainFramesV1.Point0496.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0496.outputs.2.hi (by
         change SourceMainFramesV1.Point0496.outputs.2.hi ∈ [SourceMainFramesV1.Point0496.outputs.2.hi, SourceMainFramesV1.Point0497.outputs.2.hi, SourceMainFramesV1.Point0498.outputs.2.hi, SourceMainFramesV1.Point0499.outputs.2.hi, SourceMainFramesV1.Point0500.outputs.2.hi, SourceMainFramesV1.Point0501.outputs.2.hi, SourceMainFramesV1.Point0502.outputs.2.hi, SourceMainFramesV1.Point0503.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=497) domain
     SourceMainFramesV1.Point0497.input_defined SourceMainFramesV1.Point0497.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0497.outputs.2.hi (by
         change SourceMainFramesV1.Point0497.outputs.2.hi ∈ [SourceMainFramesV1.Point0496.outputs.2.hi, SourceMainFramesV1.Point0497.outputs.2.hi, SourceMainFramesV1.Point0498.outputs.2.hi, SourceMainFramesV1.Point0499.outputs.2.hi, SourceMainFramesV1.Point0500.outputs.2.hi, SourceMainFramesV1.Point0501.outputs.2.hi, SourceMainFramesV1.Point0502.outputs.2.hi, SourceMainFramesV1.Point0503.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=498) domain
     SourceMainFramesV1.Point0498.input_defined SourceMainFramesV1.Point0498.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0498.outputs.2.hi (by
         change SourceMainFramesV1.Point0498.outputs.2.hi ∈ [SourceMainFramesV1.Point0496.outputs.2.hi, SourceMainFramesV1.Point0497.outputs.2.hi, SourceMainFramesV1.Point0498.outputs.2.hi, SourceMainFramesV1.Point0499.outputs.2.hi, SourceMainFramesV1.Point0500.outputs.2.hi, SourceMainFramesV1.Point0501.outputs.2.hi, SourceMainFramesV1.Point0502.outputs.2.hi, SourceMainFramesV1.Point0503.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=499) domain
     SourceMainFramesV1.Point0499.input_defined SourceMainFramesV1.Point0499.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0499.outputs.2.hi (by
         change SourceMainFramesV1.Point0499.outputs.2.hi ∈ [SourceMainFramesV1.Point0496.outputs.2.hi, SourceMainFramesV1.Point0497.outputs.2.hi, SourceMainFramesV1.Point0498.outputs.2.hi, SourceMainFramesV1.Point0499.outputs.2.hi, SourceMainFramesV1.Point0500.outputs.2.hi, SourceMainFramesV1.Point0501.outputs.2.hi, SourceMainFramesV1.Point0502.outputs.2.hi, SourceMainFramesV1.Point0503.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=500) domain
     SourceMainFramesV1.Point0500.input_defined SourceMainFramesV1.Point0500.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0500.outputs.2.hi (by
         change SourceMainFramesV1.Point0500.outputs.2.hi ∈ [SourceMainFramesV1.Point0496.outputs.2.hi, SourceMainFramesV1.Point0497.outputs.2.hi, SourceMainFramesV1.Point0498.outputs.2.hi, SourceMainFramesV1.Point0499.outputs.2.hi, SourceMainFramesV1.Point0500.outputs.2.hi, SourceMainFramesV1.Point0501.outputs.2.hi, SourceMainFramesV1.Point0502.outputs.2.hi, SourceMainFramesV1.Point0503.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=501) domain
     SourceMainFramesV1.Point0501.input_defined SourceMainFramesV1.Point0501.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0501.outputs.2.hi (by
         change SourceMainFramesV1.Point0501.outputs.2.hi ∈ [SourceMainFramesV1.Point0496.outputs.2.hi, SourceMainFramesV1.Point0497.outputs.2.hi, SourceMainFramesV1.Point0498.outputs.2.hi, SourceMainFramesV1.Point0499.outputs.2.hi, SourceMainFramesV1.Point0500.outputs.2.hi, SourceMainFramesV1.Point0501.outputs.2.hi, SourceMainFramesV1.Point0502.outputs.2.hi, SourceMainFramesV1.Point0503.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=502) domain
     SourceMainFramesV1.Point0502.input_defined SourceMainFramesV1.Point0502.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0502.outputs.2.hi (by
         change SourceMainFramesV1.Point0502.outputs.2.hi ∈ [SourceMainFramesV1.Point0496.outputs.2.hi, SourceMainFramesV1.Point0497.outputs.2.hi, SourceMainFramesV1.Point0498.outputs.2.hi, SourceMainFramesV1.Point0499.outputs.2.hi, SourceMainFramesV1.Point0500.outputs.2.hi, SourceMainFramesV1.Point0501.outputs.2.hi, SourceMainFramesV1.Point0502.outputs.2.hi, SourceMainFramesV1.Point0503.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=503) domain
     SourceMainFramesV1.Point0503.input_defined SourceMainFramesV1.Point0503.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0503.outputs.2.hi (by
         change SourceMainFramesV1.Point0503.outputs.2.hi ∈ [SourceMainFramesV1.Point0496.outputs.2.hi, SourceMainFramesV1.Point0497.outputs.2.hi, SourceMainFramesV1.Point0498.outputs.2.hi, SourceMainFramesV1.Point0499.outputs.2.hi, SourceMainFramesV1.Point0500.outputs.2.hi, SourceMainFramesV1.Point0501.outputs.2.hi, SourceMainFramesV1.Point0502.outputs.2.hi, SourceMainFramesV1.Point0503.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block62
