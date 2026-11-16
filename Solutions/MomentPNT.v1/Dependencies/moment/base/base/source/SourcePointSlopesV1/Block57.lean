/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0456
import SourceMainFramesV1.Point0457
import SourceMainFramesV1.Point0458
import SourceMainFramesV1.Point0459
import SourceMainFramesV1.Point0460
import SourceMainFramesV1.Point0461
import SourceMainFramesV1.Point0462
import SourceMainFramesV1.Point0463
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block57
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0456.outputs.2.hi,
 SourceMainFramesV1.Point0457.outputs.2.hi,
 SourceMainFramesV1.Point0458.outputs.2.hi,
 SourceMainFramesV1.Point0459.outputs.2.hi,
 SourceMainFramesV1.Point0460.outputs.2.hi,
 SourceMainFramesV1.Point0461.outputs.2.hi,
 SourceMainFramesV1.Point0462.outputs.2.hi,
 SourceMainFramesV1.Point0463.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 456 ≤ i) (high : i < 464)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=456) domain
     SourceMainFramesV1.Point0456.input_defined SourceMainFramesV1.Point0456.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0456.outputs.2.hi (by
         change SourceMainFramesV1.Point0456.outputs.2.hi ∈ [SourceMainFramesV1.Point0456.outputs.2.hi, SourceMainFramesV1.Point0457.outputs.2.hi, SourceMainFramesV1.Point0458.outputs.2.hi, SourceMainFramesV1.Point0459.outputs.2.hi, SourceMainFramesV1.Point0460.outputs.2.hi, SourceMainFramesV1.Point0461.outputs.2.hi, SourceMainFramesV1.Point0462.outputs.2.hi, SourceMainFramesV1.Point0463.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=457) domain
     SourceMainFramesV1.Point0457.input_defined SourceMainFramesV1.Point0457.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0457.outputs.2.hi (by
         change SourceMainFramesV1.Point0457.outputs.2.hi ∈ [SourceMainFramesV1.Point0456.outputs.2.hi, SourceMainFramesV1.Point0457.outputs.2.hi, SourceMainFramesV1.Point0458.outputs.2.hi, SourceMainFramesV1.Point0459.outputs.2.hi, SourceMainFramesV1.Point0460.outputs.2.hi, SourceMainFramesV1.Point0461.outputs.2.hi, SourceMainFramesV1.Point0462.outputs.2.hi, SourceMainFramesV1.Point0463.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=458) domain
     SourceMainFramesV1.Point0458.input_defined SourceMainFramesV1.Point0458.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0458.outputs.2.hi (by
         change SourceMainFramesV1.Point0458.outputs.2.hi ∈ [SourceMainFramesV1.Point0456.outputs.2.hi, SourceMainFramesV1.Point0457.outputs.2.hi, SourceMainFramesV1.Point0458.outputs.2.hi, SourceMainFramesV1.Point0459.outputs.2.hi, SourceMainFramesV1.Point0460.outputs.2.hi, SourceMainFramesV1.Point0461.outputs.2.hi, SourceMainFramesV1.Point0462.outputs.2.hi, SourceMainFramesV1.Point0463.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=459) domain
     SourceMainFramesV1.Point0459.input_defined SourceMainFramesV1.Point0459.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0459.outputs.2.hi (by
         change SourceMainFramesV1.Point0459.outputs.2.hi ∈ [SourceMainFramesV1.Point0456.outputs.2.hi, SourceMainFramesV1.Point0457.outputs.2.hi, SourceMainFramesV1.Point0458.outputs.2.hi, SourceMainFramesV1.Point0459.outputs.2.hi, SourceMainFramesV1.Point0460.outputs.2.hi, SourceMainFramesV1.Point0461.outputs.2.hi, SourceMainFramesV1.Point0462.outputs.2.hi, SourceMainFramesV1.Point0463.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=460) domain
     SourceMainFramesV1.Point0460.input_defined SourceMainFramesV1.Point0460.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0460.outputs.2.hi (by
         change SourceMainFramesV1.Point0460.outputs.2.hi ∈ [SourceMainFramesV1.Point0456.outputs.2.hi, SourceMainFramesV1.Point0457.outputs.2.hi, SourceMainFramesV1.Point0458.outputs.2.hi, SourceMainFramesV1.Point0459.outputs.2.hi, SourceMainFramesV1.Point0460.outputs.2.hi, SourceMainFramesV1.Point0461.outputs.2.hi, SourceMainFramesV1.Point0462.outputs.2.hi, SourceMainFramesV1.Point0463.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=461) domain
     SourceMainFramesV1.Point0461.input_defined SourceMainFramesV1.Point0461.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0461.outputs.2.hi (by
         change SourceMainFramesV1.Point0461.outputs.2.hi ∈ [SourceMainFramesV1.Point0456.outputs.2.hi, SourceMainFramesV1.Point0457.outputs.2.hi, SourceMainFramesV1.Point0458.outputs.2.hi, SourceMainFramesV1.Point0459.outputs.2.hi, SourceMainFramesV1.Point0460.outputs.2.hi, SourceMainFramesV1.Point0461.outputs.2.hi, SourceMainFramesV1.Point0462.outputs.2.hi, SourceMainFramesV1.Point0463.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=462) domain
     SourceMainFramesV1.Point0462.input_defined SourceMainFramesV1.Point0462.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0462.outputs.2.hi (by
         change SourceMainFramesV1.Point0462.outputs.2.hi ∈ [SourceMainFramesV1.Point0456.outputs.2.hi, SourceMainFramesV1.Point0457.outputs.2.hi, SourceMainFramesV1.Point0458.outputs.2.hi, SourceMainFramesV1.Point0459.outputs.2.hi, SourceMainFramesV1.Point0460.outputs.2.hi, SourceMainFramesV1.Point0461.outputs.2.hi, SourceMainFramesV1.Point0462.outputs.2.hi, SourceMainFramesV1.Point0463.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=463) domain
     SourceMainFramesV1.Point0463.input_defined SourceMainFramesV1.Point0463.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0463.outputs.2.hi (by
         change SourceMainFramesV1.Point0463.outputs.2.hi ∈ [SourceMainFramesV1.Point0456.outputs.2.hi, SourceMainFramesV1.Point0457.outputs.2.hi, SourceMainFramesV1.Point0458.outputs.2.hi, SourceMainFramesV1.Point0459.outputs.2.hi, SourceMainFramesV1.Point0460.outputs.2.hi, SourceMainFramesV1.Point0461.outputs.2.hi, SourceMainFramesV1.Point0462.outputs.2.hi, SourceMainFramesV1.Point0463.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block57
