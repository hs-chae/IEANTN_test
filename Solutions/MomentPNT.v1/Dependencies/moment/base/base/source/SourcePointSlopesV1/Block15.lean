/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0120
import SourceMainFramesV1.Point0121
import SourceMainFramesV1.Point0122
import SourceMainFramesV1.Point0123
import SourceMainFramesV1.Point0124
import SourceMainFramesV1.Point0125
import SourceMainFramesV1.Point0126
import SourceMainFramesV1.Point0127
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block15
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0120.outputs.2.hi,
 SourceMainFramesV1.Point0121.outputs.2.hi,
 SourceMainFramesV1.Point0122.outputs.2.hi,
 SourceMainFramesV1.Point0123.outputs.2.hi,
 SourceMainFramesV1.Point0124.outputs.2.hi,
 SourceMainFramesV1.Point0125.outputs.2.hi,
 SourceMainFramesV1.Point0126.outputs.2.hi,
 SourceMainFramesV1.Point0127.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 120 ≤ i) (high : i < 128)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=120) domain
     SourceMainFramesV1.Point0120.input_defined SourceMainFramesV1.Point0120.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0120.outputs.2.hi (by
         change SourceMainFramesV1.Point0120.outputs.2.hi ∈ [SourceMainFramesV1.Point0120.outputs.2.hi, SourceMainFramesV1.Point0121.outputs.2.hi, SourceMainFramesV1.Point0122.outputs.2.hi, SourceMainFramesV1.Point0123.outputs.2.hi, SourceMainFramesV1.Point0124.outputs.2.hi, SourceMainFramesV1.Point0125.outputs.2.hi, SourceMainFramesV1.Point0126.outputs.2.hi, SourceMainFramesV1.Point0127.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=121) domain
     SourceMainFramesV1.Point0121.input_defined SourceMainFramesV1.Point0121.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0121.outputs.2.hi (by
         change SourceMainFramesV1.Point0121.outputs.2.hi ∈ [SourceMainFramesV1.Point0120.outputs.2.hi, SourceMainFramesV1.Point0121.outputs.2.hi, SourceMainFramesV1.Point0122.outputs.2.hi, SourceMainFramesV1.Point0123.outputs.2.hi, SourceMainFramesV1.Point0124.outputs.2.hi, SourceMainFramesV1.Point0125.outputs.2.hi, SourceMainFramesV1.Point0126.outputs.2.hi, SourceMainFramesV1.Point0127.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=122) domain
     SourceMainFramesV1.Point0122.input_defined SourceMainFramesV1.Point0122.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0122.outputs.2.hi (by
         change SourceMainFramesV1.Point0122.outputs.2.hi ∈ [SourceMainFramesV1.Point0120.outputs.2.hi, SourceMainFramesV1.Point0121.outputs.2.hi, SourceMainFramesV1.Point0122.outputs.2.hi, SourceMainFramesV1.Point0123.outputs.2.hi, SourceMainFramesV1.Point0124.outputs.2.hi, SourceMainFramesV1.Point0125.outputs.2.hi, SourceMainFramesV1.Point0126.outputs.2.hi, SourceMainFramesV1.Point0127.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=123) domain
     SourceMainFramesV1.Point0123.input_defined SourceMainFramesV1.Point0123.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0123.outputs.2.hi (by
         change SourceMainFramesV1.Point0123.outputs.2.hi ∈ [SourceMainFramesV1.Point0120.outputs.2.hi, SourceMainFramesV1.Point0121.outputs.2.hi, SourceMainFramesV1.Point0122.outputs.2.hi, SourceMainFramesV1.Point0123.outputs.2.hi, SourceMainFramesV1.Point0124.outputs.2.hi, SourceMainFramesV1.Point0125.outputs.2.hi, SourceMainFramesV1.Point0126.outputs.2.hi, SourceMainFramesV1.Point0127.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=124) domain
     SourceMainFramesV1.Point0124.input_defined SourceMainFramesV1.Point0124.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0124.outputs.2.hi (by
         change SourceMainFramesV1.Point0124.outputs.2.hi ∈ [SourceMainFramesV1.Point0120.outputs.2.hi, SourceMainFramesV1.Point0121.outputs.2.hi, SourceMainFramesV1.Point0122.outputs.2.hi, SourceMainFramesV1.Point0123.outputs.2.hi, SourceMainFramesV1.Point0124.outputs.2.hi, SourceMainFramesV1.Point0125.outputs.2.hi, SourceMainFramesV1.Point0126.outputs.2.hi, SourceMainFramesV1.Point0127.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=125) domain
     SourceMainFramesV1.Point0125.input_defined SourceMainFramesV1.Point0125.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0125.outputs.2.hi (by
         change SourceMainFramesV1.Point0125.outputs.2.hi ∈ [SourceMainFramesV1.Point0120.outputs.2.hi, SourceMainFramesV1.Point0121.outputs.2.hi, SourceMainFramesV1.Point0122.outputs.2.hi, SourceMainFramesV1.Point0123.outputs.2.hi, SourceMainFramesV1.Point0124.outputs.2.hi, SourceMainFramesV1.Point0125.outputs.2.hi, SourceMainFramesV1.Point0126.outputs.2.hi, SourceMainFramesV1.Point0127.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=126) domain
     SourceMainFramesV1.Point0126.input_defined SourceMainFramesV1.Point0126.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0126.outputs.2.hi (by
         change SourceMainFramesV1.Point0126.outputs.2.hi ∈ [SourceMainFramesV1.Point0120.outputs.2.hi, SourceMainFramesV1.Point0121.outputs.2.hi, SourceMainFramesV1.Point0122.outputs.2.hi, SourceMainFramesV1.Point0123.outputs.2.hi, SourceMainFramesV1.Point0124.outputs.2.hi, SourceMainFramesV1.Point0125.outputs.2.hi, SourceMainFramesV1.Point0126.outputs.2.hi, SourceMainFramesV1.Point0127.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=127) domain
     SourceMainFramesV1.Point0127.input_defined SourceMainFramesV1.Point0127.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0127.outputs.2.hi (by
         change SourceMainFramesV1.Point0127.outputs.2.hi ∈ [SourceMainFramesV1.Point0120.outputs.2.hi, SourceMainFramesV1.Point0121.outputs.2.hi, SourceMainFramesV1.Point0122.outputs.2.hi, SourceMainFramesV1.Point0123.outputs.2.hi, SourceMainFramesV1.Point0124.outputs.2.hi, SourceMainFramesV1.Point0125.outputs.2.hi, SourceMainFramesV1.Point0126.outputs.2.hi, SourceMainFramesV1.Point0127.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block15
