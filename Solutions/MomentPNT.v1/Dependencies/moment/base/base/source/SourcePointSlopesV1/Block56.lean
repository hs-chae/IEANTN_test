/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0448
import SourceMainFramesV1.Point0449
import SourceMainFramesV1.Point0450
import SourceMainFramesV1.Point0451
import SourceMainFramesV1.Point0452
import SourceMainFramesV1.Point0453
import SourceMainFramesV1.Point0454
import SourceMainFramesV1.Point0455
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block56
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0448.outputs.2.hi,
 SourceMainFramesV1.Point0449.outputs.2.hi,
 SourceMainFramesV1.Point0450.outputs.2.hi,
 SourceMainFramesV1.Point0451.outputs.2.hi,
 SourceMainFramesV1.Point0452.outputs.2.hi,
 SourceMainFramesV1.Point0453.outputs.2.hi,
 SourceMainFramesV1.Point0454.outputs.2.hi,
 SourceMainFramesV1.Point0455.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 448 ≤ i) (high : i < 456)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=448) domain
     SourceMainFramesV1.Point0448.input_defined SourceMainFramesV1.Point0448.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0448.outputs.2.hi (by
         change SourceMainFramesV1.Point0448.outputs.2.hi ∈ [SourceMainFramesV1.Point0448.outputs.2.hi, SourceMainFramesV1.Point0449.outputs.2.hi, SourceMainFramesV1.Point0450.outputs.2.hi, SourceMainFramesV1.Point0451.outputs.2.hi, SourceMainFramesV1.Point0452.outputs.2.hi, SourceMainFramesV1.Point0453.outputs.2.hi, SourceMainFramesV1.Point0454.outputs.2.hi, SourceMainFramesV1.Point0455.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=449) domain
     SourceMainFramesV1.Point0449.input_defined SourceMainFramesV1.Point0449.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0449.outputs.2.hi (by
         change SourceMainFramesV1.Point0449.outputs.2.hi ∈ [SourceMainFramesV1.Point0448.outputs.2.hi, SourceMainFramesV1.Point0449.outputs.2.hi, SourceMainFramesV1.Point0450.outputs.2.hi, SourceMainFramesV1.Point0451.outputs.2.hi, SourceMainFramesV1.Point0452.outputs.2.hi, SourceMainFramesV1.Point0453.outputs.2.hi, SourceMainFramesV1.Point0454.outputs.2.hi, SourceMainFramesV1.Point0455.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=450) domain
     SourceMainFramesV1.Point0450.input_defined SourceMainFramesV1.Point0450.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0450.outputs.2.hi (by
         change SourceMainFramesV1.Point0450.outputs.2.hi ∈ [SourceMainFramesV1.Point0448.outputs.2.hi, SourceMainFramesV1.Point0449.outputs.2.hi, SourceMainFramesV1.Point0450.outputs.2.hi, SourceMainFramesV1.Point0451.outputs.2.hi, SourceMainFramesV1.Point0452.outputs.2.hi, SourceMainFramesV1.Point0453.outputs.2.hi, SourceMainFramesV1.Point0454.outputs.2.hi, SourceMainFramesV1.Point0455.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=451) domain
     SourceMainFramesV1.Point0451.input_defined SourceMainFramesV1.Point0451.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0451.outputs.2.hi (by
         change SourceMainFramesV1.Point0451.outputs.2.hi ∈ [SourceMainFramesV1.Point0448.outputs.2.hi, SourceMainFramesV1.Point0449.outputs.2.hi, SourceMainFramesV1.Point0450.outputs.2.hi, SourceMainFramesV1.Point0451.outputs.2.hi, SourceMainFramesV1.Point0452.outputs.2.hi, SourceMainFramesV1.Point0453.outputs.2.hi, SourceMainFramesV1.Point0454.outputs.2.hi, SourceMainFramesV1.Point0455.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=452) domain
     SourceMainFramesV1.Point0452.input_defined SourceMainFramesV1.Point0452.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0452.outputs.2.hi (by
         change SourceMainFramesV1.Point0452.outputs.2.hi ∈ [SourceMainFramesV1.Point0448.outputs.2.hi, SourceMainFramesV1.Point0449.outputs.2.hi, SourceMainFramesV1.Point0450.outputs.2.hi, SourceMainFramesV1.Point0451.outputs.2.hi, SourceMainFramesV1.Point0452.outputs.2.hi, SourceMainFramesV1.Point0453.outputs.2.hi, SourceMainFramesV1.Point0454.outputs.2.hi, SourceMainFramesV1.Point0455.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=453) domain
     SourceMainFramesV1.Point0453.input_defined SourceMainFramesV1.Point0453.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0453.outputs.2.hi (by
         change SourceMainFramesV1.Point0453.outputs.2.hi ∈ [SourceMainFramesV1.Point0448.outputs.2.hi, SourceMainFramesV1.Point0449.outputs.2.hi, SourceMainFramesV1.Point0450.outputs.2.hi, SourceMainFramesV1.Point0451.outputs.2.hi, SourceMainFramesV1.Point0452.outputs.2.hi, SourceMainFramesV1.Point0453.outputs.2.hi, SourceMainFramesV1.Point0454.outputs.2.hi, SourceMainFramesV1.Point0455.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=454) domain
     SourceMainFramesV1.Point0454.input_defined SourceMainFramesV1.Point0454.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0454.outputs.2.hi (by
         change SourceMainFramesV1.Point0454.outputs.2.hi ∈ [SourceMainFramesV1.Point0448.outputs.2.hi, SourceMainFramesV1.Point0449.outputs.2.hi, SourceMainFramesV1.Point0450.outputs.2.hi, SourceMainFramesV1.Point0451.outputs.2.hi, SourceMainFramesV1.Point0452.outputs.2.hi, SourceMainFramesV1.Point0453.outputs.2.hi, SourceMainFramesV1.Point0454.outputs.2.hi, SourceMainFramesV1.Point0455.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=455) domain
     SourceMainFramesV1.Point0455.input_defined SourceMainFramesV1.Point0455.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0455.outputs.2.hi (by
         change SourceMainFramesV1.Point0455.outputs.2.hi ∈ [SourceMainFramesV1.Point0448.outputs.2.hi, SourceMainFramesV1.Point0449.outputs.2.hi, SourceMainFramesV1.Point0450.outputs.2.hi, SourceMainFramesV1.Point0451.outputs.2.hi, SourceMainFramesV1.Point0452.outputs.2.hi, SourceMainFramesV1.Point0453.outputs.2.hi, SourceMainFramesV1.Point0454.outputs.2.hi, SourceMainFramesV1.Point0455.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block56
