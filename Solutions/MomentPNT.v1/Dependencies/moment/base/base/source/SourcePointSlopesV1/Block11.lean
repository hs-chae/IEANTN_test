/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0088
import SourceMainFramesV1.Point0089
import SourceMainFramesV1.Point0090
import SourceMainFramesV1.Point0091
import SourceMainFramesV1.Point0092
import SourceMainFramesV1.Point0093
import SourceMainFramesV1.Point0094
import SourceMainFramesV1.Point0095
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block11
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0088.outputs.2.hi,
 SourceMainFramesV1.Point0089.outputs.2.hi,
 SourceMainFramesV1.Point0090.outputs.2.hi,
 SourceMainFramesV1.Point0091.outputs.2.hi,
 SourceMainFramesV1.Point0092.outputs.2.hi,
 SourceMainFramesV1.Point0093.outputs.2.hi,
 SourceMainFramesV1.Point0094.outputs.2.hi,
 SourceMainFramesV1.Point0095.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 88 ≤ i) (high : i < 96)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=88) domain
     SourceMainFramesV1.Point0088.input_defined SourceMainFramesV1.Point0088.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0088.outputs.2.hi (by
         change SourceMainFramesV1.Point0088.outputs.2.hi ∈ [SourceMainFramesV1.Point0088.outputs.2.hi, SourceMainFramesV1.Point0089.outputs.2.hi, SourceMainFramesV1.Point0090.outputs.2.hi, SourceMainFramesV1.Point0091.outputs.2.hi, SourceMainFramesV1.Point0092.outputs.2.hi, SourceMainFramesV1.Point0093.outputs.2.hi, SourceMainFramesV1.Point0094.outputs.2.hi, SourceMainFramesV1.Point0095.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=89) domain
     SourceMainFramesV1.Point0089.input_defined SourceMainFramesV1.Point0089.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0089.outputs.2.hi (by
         change SourceMainFramesV1.Point0089.outputs.2.hi ∈ [SourceMainFramesV1.Point0088.outputs.2.hi, SourceMainFramesV1.Point0089.outputs.2.hi, SourceMainFramesV1.Point0090.outputs.2.hi, SourceMainFramesV1.Point0091.outputs.2.hi, SourceMainFramesV1.Point0092.outputs.2.hi, SourceMainFramesV1.Point0093.outputs.2.hi, SourceMainFramesV1.Point0094.outputs.2.hi, SourceMainFramesV1.Point0095.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=90) domain
     SourceMainFramesV1.Point0090.input_defined SourceMainFramesV1.Point0090.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0090.outputs.2.hi (by
         change SourceMainFramesV1.Point0090.outputs.2.hi ∈ [SourceMainFramesV1.Point0088.outputs.2.hi, SourceMainFramesV1.Point0089.outputs.2.hi, SourceMainFramesV1.Point0090.outputs.2.hi, SourceMainFramesV1.Point0091.outputs.2.hi, SourceMainFramesV1.Point0092.outputs.2.hi, SourceMainFramesV1.Point0093.outputs.2.hi, SourceMainFramesV1.Point0094.outputs.2.hi, SourceMainFramesV1.Point0095.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=91) domain
     SourceMainFramesV1.Point0091.input_defined SourceMainFramesV1.Point0091.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0091.outputs.2.hi (by
         change SourceMainFramesV1.Point0091.outputs.2.hi ∈ [SourceMainFramesV1.Point0088.outputs.2.hi, SourceMainFramesV1.Point0089.outputs.2.hi, SourceMainFramesV1.Point0090.outputs.2.hi, SourceMainFramesV1.Point0091.outputs.2.hi, SourceMainFramesV1.Point0092.outputs.2.hi, SourceMainFramesV1.Point0093.outputs.2.hi, SourceMainFramesV1.Point0094.outputs.2.hi, SourceMainFramesV1.Point0095.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=92) domain
     SourceMainFramesV1.Point0092.input_defined SourceMainFramesV1.Point0092.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0092.outputs.2.hi (by
         change SourceMainFramesV1.Point0092.outputs.2.hi ∈ [SourceMainFramesV1.Point0088.outputs.2.hi, SourceMainFramesV1.Point0089.outputs.2.hi, SourceMainFramesV1.Point0090.outputs.2.hi, SourceMainFramesV1.Point0091.outputs.2.hi, SourceMainFramesV1.Point0092.outputs.2.hi, SourceMainFramesV1.Point0093.outputs.2.hi, SourceMainFramesV1.Point0094.outputs.2.hi, SourceMainFramesV1.Point0095.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=93) domain
     SourceMainFramesV1.Point0093.input_defined SourceMainFramesV1.Point0093.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0093.outputs.2.hi (by
         change SourceMainFramesV1.Point0093.outputs.2.hi ∈ [SourceMainFramesV1.Point0088.outputs.2.hi, SourceMainFramesV1.Point0089.outputs.2.hi, SourceMainFramesV1.Point0090.outputs.2.hi, SourceMainFramesV1.Point0091.outputs.2.hi, SourceMainFramesV1.Point0092.outputs.2.hi, SourceMainFramesV1.Point0093.outputs.2.hi, SourceMainFramesV1.Point0094.outputs.2.hi, SourceMainFramesV1.Point0095.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=94) domain
     SourceMainFramesV1.Point0094.input_defined SourceMainFramesV1.Point0094.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0094.outputs.2.hi (by
         change SourceMainFramesV1.Point0094.outputs.2.hi ∈ [SourceMainFramesV1.Point0088.outputs.2.hi, SourceMainFramesV1.Point0089.outputs.2.hi, SourceMainFramesV1.Point0090.outputs.2.hi, SourceMainFramesV1.Point0091.outputs.2.hi, SourceMainFramesV1.Point0092.outputs.2.hi, SourceMainFramesV1.Point0093.outputs.2.hi, SourceMainFramesV1.Point0094.outputs.2.hi, SourceMainFramesV1.Point0095.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=95) domain
     SourceMainFramesV1.Point0095.input_defined SourceMainFramesV1.Point0095.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0095.outputs.2.hi (by
         change SourceMainFramesV1.Point0095.outputs.2.hi ∈ [SourceMainFramesV1.Point0088.outputs.2.hi, SourceMainFramesV1.Point0089.outputs.2.hi, SourceMainFramesV1.Point0090.outputs.2.hi, SourceMainFramesV1.Point0091.outputs.2.hi, SourceMainFramesV1.Point0092.outputs.2.hi, SourceMainFramesV1.Point0093.outputs.2.hi, SourceMainFramesV1.Point0094.outputs.2.hi, SourceMainFramesV1.Point0095.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block11
