/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0200
import SourceMainFramesV1.Point0201
import SourceMainFramesV1.Point0202
import SourceMainFramesV1.Point0203
import SourceMainFramesV1.Point0204
import SourceMainFramesV1.Point0205
import SourceMainFramesV1.Point0206
import SourceMainFramesV1.Point0207
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block25
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0200.outputs.2.hi,
 SourceMainFramesV1.Point0201.outputs.2.hi,
 SourceMainFramesV1.Point0202.outputs.2.hi,
 SourceMainFramesV1.Point0203.outputs.2.hi,
 SourceMainFramesV1.Point0204.outputs.2.hi,
 SourceMainFramesV1.Point0205.outputs.2.hi,
 SourceMainFramesV1.Point0206.outputs.2.hi,
 SourceMainFramesV1.Point0207.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 200 ≤ i) (high : i < 208)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=200) domain
     SourceMainFramesV1.Point0200.input_defined SourceMainFramesV1.Point0200.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0200.outputs.2.hi (by
         change SourceMainFramesV1.Point0200.outputs.2.hi ∈ [SourceMainFramesV1.Point0200.outputs.2.hi, SourceMainFramesV1.Point0201.outputs.2.hi, SourceMainFramesV1.Point0202.outputs.2.hi, SourceMainFramesV1.Point0203.outputs.2.hi, SourceMainFramesV1.Point0204.outputs.2.hi, SourceMainFramesV1.Point0205.outputs.2.hi, SourceMainFramesV1.Point0206.outputs.2.hi, SourceMainFramesV1.Point0207.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=201) domain
     SourceMainFramesV1.Point0201.input_defined SourceMainFramesV1.Point0201.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0201.outputs.2.hi (by
         change SourceMainFramesV1.Point0201.outputs.2.hi ∈ [SourceMainFramesV1.Point0200.outputs.2.hi, SourceMainFramesV1.Point0201.outputs.2.hi, SourceMainFramesV1.Point0202.outputs.2.hi, SourceMainFramesV1.Point0203.outputs.2.hi, SourceMainFramesV1.Point0204.outputs.2.hi, SourceMainFramesV1.Point0205.outputs.2.hi, SourceMainFramesV1.Point0206.outputs.2.hi, SourceMainFramesV1.Point0207.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=202) domain
     SourceMainFramesV1.Point0202.input_defined SourceMainFramesV1.Point0202.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0202.outputs.2.hi (by
         change SourceMainFramesV1.Point0202.outputs.2.hi ∈ [SourceMainFramesV1.Point0200.outputs.2.hi, SourceMainFramesV1.Point0201.outputs.2.hi, SourceMainFramesV1.Point0202.outputs.2.hi, SourceMainFramesV1.Point0203.outputs.2.hi, SourceMainFramesV1.Point0204.outputs.2.hi, SourceMainFramesV1.Point0205.outputs.2.hi, SourceMainFramesV1.Point0206.outputs.2.hi, SourceMainFramesV1.Point0207.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=203) domain
     SourceMainFramesV1.Point0203.input_defined SourceMainFramesV1.Point0203.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0203.outputs.2.hi (by
         change SourceMainFramesV1.Point0203.outputs.2.hi ∈ [SourceMainFramesV1.Point0200.outputs.2.hi, SourceMainFramesV1.Point0201.outputs.2.hi, SourceMainFramesV1.Point0202.outputs.2.hi, SourceMainFramesV1.Point0203.outputs.2.hi, SourceMainFramesV1.Point0204.outputs.2.hi, SourceMainFramesV1.Point0205.outputs.2.hi, SourceMainFramesV1.Point0206.outputs.2.hi, SourceMainFramesV1.Point0207.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=204) domain
     SourceMainFramesV1.Point0204.input_defined SourceMainFramesV1.Point0204.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0204.outputs.2.hi (by
         change SourceMainFramesV1.Point0204.outputs.2.hi ∈ [SourceMainFramesV1.Point0200.outputs.2.hi, SourceMainFramesV1.Point0201.outputs.2.hi, SourceMainFramesV1.Point0202.outputs.2.hi, SourceMainFramesV1.Point0203.outputs.2.hi, SourceMainFramesV1.Point0204.outputs.2.hi, SourceMainFramesV1.Point0205.outputs.2.hi, SourceMainFramesV1.Point0206.outputs.2.hi, SourceMainFramesV1.Point0207.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=205) domain
     SourceMainFramesV1.Point0205.input_defined SourceMainFramesV1.Point0205.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0205.outputs.2.hi (by
         change SourceMainFramesV1.Point0205.outputs.2.hi ∈ [SourceMainFramesV1.Point0200.outputs.2.hi, SourceMainFramesV1.Point0201.outputs.2.hi, SourceMainFramesV1.Point0202.outputs.2.hi, SourceMainFramesV1.Point0203.outputs.2.hi, SourceMainFramesV1.Point0204.outputs.2.hi, SourceMainFramesV1.Point0205.outputs.2.hi, SourceMainFramesV1.Point0206.outputs.2.hi, SourceMainFramesV1.Point0207.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=206) domain
     SourceMainFramesV1.Point0206.input_defined SourceMainFramesV1.Point0206.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0206.outputs.2.hi (by
         change SourceMainFramesV1.Point0206.outputs.2.hi ∈ [SourceMainFramesV1.Point0200.outputs.2.hi, SourceMainFramesV1.Point0201.outputs.2.hi, SourceMainFramesV1.Point0202.outputs.2.hi, SourceMainFramesV1.Point0203.outputs.2.hi, SourceMainFramesV1.Point0204.outputs.2.hi, SourceMainFramesV1.Point0205.outputs.2.hi, SourceMainFramesV1.Point0206.outputs.2.hi, SourceMainFramesV1.Point0207.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=207) domain
     SourceMainFramesV1.Point0207.input_defined SourceMainFramesV1.Point0207.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0207.outputs.2.hi (by
         change SourceMainFramesV1.Point0207.outputs.2.hi ∈ [SourceMainFramesV1.Point0200.outputs.2.hi, SourceMainFramesV1.Point0201.outputs.2.hi, SourceMainFramesV1.Point0202.outputs.2.hi, SourceMainFramesV1.Point0203.outputs.2.hi, SourceMainFramesV1.Point0204.outputs.2.hi, SourceMainFramesV1.Point0205.outputs.2.hi, SourceMainFramesV1.Point0206.outputs.2.hi, SourceMainFramesV1.Point0207.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block25
