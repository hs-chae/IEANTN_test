/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0296
import SourceMainFramesV1.Point0297
import SourceMainFramesV1.Point0298
import SourceMainFramesV1.Point0299
import SourceMainFramesV1.Point0300
import SourceMainFramesV1.Point0301
import SourceMainFramesV1.Point0302
import SourceMainFramesV1.Point0303
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block37
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0296.outputs.2.hi,
 SourceMainFramesV1.Point0297.outputs.2.hi,
 SourceMainFramesV1.Point0298.outputs.2.hi,
 SourceMainFramesV1.Point0299.outputs.2.hi,
 SourceMainFramesV1.Point0300.outputs.2.hi,
 SourceMainFramesV1.Point0301.outputs.2.hi,
 SourceMainFramesV1.Point0302.outputs.2.hi,
 SourceMainFramesV1.Point0303.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 296 ≤ i) (high : i < 304)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=296) domain
     SourceMainFramesV1.Point0296.input_defined SourceMainFramesV1.Point0296.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0296.outputs.2.hi (by
         change SourceMainFramesV1.Point0296.outputs.2.hi ∈ [SourceMainFramesV1.Point0296.outputs.2.hi, SourceMainFramesV1.Point0297.outputs.2.hi, SourceMainFramesV1.Point0298.outputs.2.hi, SourceMainFramesV1.Point0299.outputs.2.hi, SourceMainFramesV1.Point0300.outputs.2.hi, SourceMainFramesV1.Point0301.outputs.2.hi, SourceMainFramesV1.Point0302.outputs.2.hi, SourceMainFramesV1.Point0303.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=297) domain
     SourceMainFramesV1.Point0297.input_defined SourceMainFramesV1.Point0297.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0297.outputs.2.hi (by
         change SourceMainFramesV1.Point0297.outputs.2.hi ∈ [SourceMainFramesV1.Point0296.outputs.2.hi, SourceMainFramesV1.Point0297.outputs.2.hi, SourceMainFramesV1.Point0298.outputs.2.hi, SourceMainFramesV1.Point0299.outputs.2.hi, SourceMainFramesV1.Point0300.outputs.2.hi, SourceMainFramesV1.Point0301.outputs.2.hi, SourceMainFramesV1.Point0302.outputs.2.hi, SourceMainFramesV1.Point0303.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=298) domain
     SourceMainFramesV1.Point0298.input_defined SourceMainFramesV1.Point0298.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0298.outputs.2.hi (by
         change SourceMainFramesV1.Point0298.outputs.2.hi ∈ [SourceMainFramesV1.Point0296.outputs.2.hi, SourceMainFramesV1.Point0297.outputs.2.hi, SourceMainFramesV1.Point0298.outputs.2.hi, SourceMainFramesV1.Point0299.outputs.2.hi, SourceMainFramesV1.Point0300.outputs.2.hi, SourceMainFramesV1.Point0301.outputs.2.hi, SourceMainFramesV1.Point0302.outputs.2.hi, SourceMainFramesV1.Point0303.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=299) domain
     SourceMainFramesV1.Point0299.input_defined SourceMainFramesV1.Point0299.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0299.outputs.2.hi (by
         change SourceMainFramesV1.Point0299.outputs.2.hi ∈ [SourceMainFramesV1.Point0296.outputs.2.hi, SourceMainFramesV1.Point0297.outputs.2.hi, SourceMainFramesV1.Point0298.outputs.2.hi, SourceMainFramesV1.Point0299.outputs.2.hi, SourceMainFramesV1.Point0300.outputs.2.hi, SourceMainFramesV1.Point0301.outputs.2.hi, SourceMainFramesV1.Point0302.outputs.2.hi, SourceMainFramesV1.Point0303.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=300) domain
     SourceMainFramesV1.Point0300.input_defined SourceMainFramesV1.Point0300.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0300.outputs.2.hi (by
         change SourceMainFramesV1.Point0300.outputs.2.hi ∈ [SourceMainFramesV1.Point0296.outputs.2.hi, SourceMainFramesV1.Point0297.outputs.2.hi, SourceMainFramesV1.Point0298.outputs.2.hi, SourceMainFramesV1.Point0299.outputs.2.hi, SourceMainFramesV1.Point0300.outputs.2.hi, SourceMainFramesV1.Point0301.outputs.2.hi, SourceMainFramesV1.Point0302.outputs.2.hi, SourceMainFramesV1.Point0303.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=301) domain
     SourceMainFramesV1.Point0301.input_defined SourceMainFramesV1.Point0301.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0301.outputs.2.hi (by
         change SourceMainFramesV1.Point0301.outputs.2.hi ∈ [SourceMainFramesV1.Point0296.outputs.2.hi, SourceMainFramesV1.Point0297.outputs.2.hi, SourceMainFramesV1.Point0298.outputs.2.hi, SourceMainFramesV1.Point0299.outputs.2.hi, SourceMainFramesV1.Point0300.outputs.2.hi, SourceMainFramesV1.Point0301.outputs.2.hi, SourceMainFramesV1.Point0302.outputs.2.hi, SourceMainFramesV1.Point0303.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=302) domain
     SourceMainFramesV1.Point0302.input_defined SourceMainFramesV1.Point0302.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0302.outputs.2.hi (by
         change SourceMainFramesV1.Point0302.outputs.2.hi ∈ [SourceMainFramesV1.Point0296.outputs.2.hi, SourceMainFramesV1.Point0297.outputs.2.hi, SourceMainFramesV1.Point0298.outputs.2.hi, SourceMainFramesV1.Point0299.outputs.2.hi, SourceMainFramesV1.Point0300.outputs.2.hi, SourceMainFramesV1.Point0301.outputs.2.hi, SourceMainFramesV1.Point0302.outputs.2.hi, SourceMainFramesV1.Point0303.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=303) domain
     SourceMainFramesV1.Point0303.input_defined SourceMainFramesV1.Point0303.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0303.outputs.2.hi (by
         change SourceMainFramesV1.Point0303.outputs.2.hi ∈ [SourceMainFramesV1.Point0296.outputs.2.hi, SourceMainFramesV1.Point0297.outputs.2.hi, SourceMainFramesV1.Point0298.outputs.2.hi, SourceMainFramesV1.Point0299.outputs.2.hi, SourceMainFramesV1.Point0300.outputs.2.hi, SourceMainFramesV1.Point0301.outputs.2.hi, SourceMainFramesV1.Point0302.outputs.2.hi, SourceMainFramesV1.Point0303.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block37
