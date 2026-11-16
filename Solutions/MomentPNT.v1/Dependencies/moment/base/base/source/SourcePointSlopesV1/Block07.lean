/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0056
import SourceMainFramesV1.Point0057
import SourceMainFramesV1.Point0058
import SourceMainFramesV1.Point0059
import SourceMainFramesV1.Point0060
import SourceMainFramesV1.Point0061
import SourceMainFramesV1.Point0062
import SourceMainFramesV1.Point0063
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block07
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0056.outputs.2.hi,
 SourceMainFramesV1.Point0057.outputs.2.hi,
 SourceMainFramesV1.Point0058.outputs.2.hi,
 SourceMainFramesV1.Point0059.outputs.2.hi,
 SourceMainFramesV1.Point0060.outputs.2.hi,
 SourceMainFramesV1.Point0061.outputs.2.hi,
 SourceMainFramesV1.Point0062.outputs.2.hi,
 SourceMainFramesV1.Point0063.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 56 ≤ i) (high : i < 64)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=56) domain
     SourceMainFramesV1.Point0056.input_defined SourceMainFramesV1.Point0056.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0056.outputs.2.hi (by
         change SourceMainFramesV1.Point0056.outputs.2.hi ∈ [SourceMainFramesV1.Point0056.outputs.2.hi, SourceMainFramesV1.Point0057.outputs.2.hi, SourceMainFramesV1.Point0058.outputs.2.hi, SourceMainFramesV1.Point0059.outputs.2.hi, SourceMainFramesV1.Point0060.outputs.2.hi, SourceMainFramesV1.Point0061.outputs.2.hi, SourceMainFramesV1.Point0062.outputs.2.hi, SourceMainFramesV1.Point0063.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=57) domain
     SourceMainFramesV1.Point0057.input_defined SourceMainFramesV1.Point0057.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0057.outputs.2.hi (by
         change SourceMainFramesV1.Point0057.outputs.2.hi ∈ [SourceMainFramesV1.Point0056.outputs.2.hi, SourceMainFramesV1.Point0057.outputs.2.hi, SourceMainFramesV1.Point0058.outputs.2.hi, SourceMainFramesV1.Point0059.outputs.2.hi, SourceMainFramesV1.Point0060.outputs.2.hi, SourceMainFramesV1.Point0061.outputs.2.hi, SourceMainFramesV1.Point0062.outputs.2.hi, SourceMainFramesV1.Point0063.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=58) domain
     SourceMainFramesV1.Point0058.input_defined SourceMainFramesV1.Point0058.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0058.outputs.2.hi (by
         change SourceMainFramesV1.Point0058.outputs.2.hi ∈ [SourceMainFramesV1.Point0056.outputs.2.hi, SourceMainFramesV1.Point0057.outputs.2.hi, SourceMainFramesV1.Point0058.outputs.2.hi, SourceMainFramesV1.Point0059.outputs.2.hi, SourceMainFramesV1.Point0060.outputs.2.hi, SourceMainFramesV1.Point0061.outputs.2.hi, SourceMainFramesV1.Point0062.outputs.2.hi, SourceMainFramesV1.Point0063.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=59) domain
     SourceMainFramesV1.Point0059.input_defined SourceMainFramesV1.Point0059.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0059.outputs.2.hi (by
         change SourceMainFramesV1.Point0059.outputs.2.hi ∈ [SourceMainFramesV1.Point0056.outputs.2.hi, SourceMainFramesV1.Point0057.outputs.2.hi, SourceMainFramesV1.Point0058.outputs.2.hi, SourceMainFramesV1.Point0059.outputs.2.hi, SourceMainFramesV1.Point0060.outputs.2.hi, SourceMainFramesV1.Point0061.outputs.2.hi, SourceMainFramesV1.Point0062.outputs.2.hi, SourceMainFramesV1.Point0063.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=60) domain
     SourceMainFramesV1.Point0060.input_defined SourceMainFramesV1.Point0060.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0060.outputs.2.hi (by
         change SourceMainFramesV1.Point0060.outputs.2.hi ∈ [SourceMainFramesV1.Point0056.outputs.2.hi, SourceMainFramesV1.Point0057.outputs.2.hi, SourceMainFramesV1.Point0058.outputs.2.hi, SourceMainFramesV1.Point0059.outputs.2.hi, SourceMainFramesV1.Point0060.outputs.2.hi, SourceMainFramesV1.Point0061.outputs.2.hi, SourceMainFramesV1.Point0062.outputs.2.hi, SourceMainFramesV1.Point0063.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=61) domain
     SourceMainFramesV1.Point0061.input_defined SourceMainFramesV1.Point0061.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0061.outputs.2.hi (by
         change SourceMainFramesV1.Point0061.outputs.2.hi ∈ [SourceMainFramesV1.Point0056.outputs.2.hi, SourceMainFramesV1.Point0057.outputs.2.hi, SourceMainFramesV1.Point0058.outputs.2.hi, SourceMainFramesV1.Point0059.outputs.2.hi, SourceMainFramesV1.Point0060.outputs.2.hi, SourceMainFramesV1.Point0061.outputs.2.hi, SourceMainFramesV1.Point0062.outputs.2.hi, SourceMainFramesV1.Point0063.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=62) domain
     SourceMainFramesV1.Point0062.input_defined SourceMainFramesV1.Point0062.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0062.outputs.2.hi (by
         change SourceMainFramesV1.Point0062.outputs.2.hi ∈ [SourceMainFramesV1.Point0056.outputs.2.hi, SourceMainFramesV1.Point0057.outputs.2.hi, SourceMainFramesV1.Point0058.outputs.2.hi, SourceMainFramesV1.Point0059.outputs.2.hi, SourceMainFramesV1.Point0060.outputs.2.hi, SourceMainFramesV1.Point0061.outputs.2.hi, SourceMainFramesV1.Point0062.outputs.2.hi, SourceMainFramesV1.Point0063.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=63) domain
     SourceMainFramesV1.Point0063.input_defined SourceMainFramesV1.Point0063.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0063.outputs.2.hi (by
         change SourceMainFramesV1.Point0063.outputs.2.hi ∈ [SourceMainFramesV1.Point0056.outputs.2.hi, SourceMainFramesV1.Point0057.outputs.2.hi, SourceMainFramesV1.Point0058.outputs.2.hi, SourceMainFramesV1.Point0059.outputs.2.hi, SourceMainFramesV1.Point0060.outputs.2.hi, SourceMainFramesV1.Point0061.outputs.2.hi, SourceMainFramesV1.Point0062.outputs.2.hi, SourceMainFramesV1.Point0063.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block07
