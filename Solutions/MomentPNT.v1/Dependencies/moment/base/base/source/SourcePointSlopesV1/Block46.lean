/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0368
import SourceMainFramesV1.Point0369
import SourceMainFramesV1.Point0370
import SourceMainFramesV1.Point0371
import SourceMainFramesV1.Point0372
import SourceMainFramesV1.Point0373
import SourceMainFramesV1.Point0374
import SourceMainFramesV1.Point0375
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block46
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0368.outputs.2.hi,
 SourceMainFramesV1.Point0369.outputs.2.hi,
 SourceMainFramesV1.Point0370.outputs.2.hi,
 SourceMainFramesV1.Point0371.outputs.2.hi,
 SourceMainFramesV1.Point0372.outputs.2.hi,
 SourceMainFramesV1.Point0373.outputs.2.hi,
 SourceMainFramesV1.Point0374.outputs.2.hi,
 SourceMainFramesV1.Point0375.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 368 ≤ i) (high : i < 376)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=368) domain
     SourceMainFramesV1.Point0368.input_defined SourceMainFramesV1.Point0368.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0368.outputs.2.hi (by
         change SourceMainFramesV1.Point0368.outputs.2.hi ∈ [SourceMainFramesV1.Point0368.outputs.2.hi, SourceMainFramesV1.Point0369.outputs.2.hi, SourceMainFramesV1.Point0370.outputs.2.hi, SourceMainFramesV1.Point0371.outputs.2.hi, SourceMainFramesV1.Point0372.outputs.2.hi, SourceMainFramesV1.Point0373.outputs.2.hi, SourceMainFramesV1.Point0374.outputs.2.hi, SourceMainFramesV1.Point0375.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=369) domain
     SourceMainFramesV1.Point0369.input_defined SourceMainFramesV1.Point0369.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0369.outputs.2.hi (by
         change SourceMainFramesV1.Point0369.outputs.2.hi ∈ [SourceMainFramesV1.Point0368.outputs.2.hi, SourceMainFramesV1.Point0369.outputs.2.hi, SourceMainFramesV1.Point0370.outputs.2.hi, SourceMainFramesV1.Point0371.outputs.2.hi, SourceMainFramesV1.Point0372.outputs.2.hi, SourceMainFramesV1.Point0373.outputs.2.hi, SourceMainFramesV1.Point0374.outputs.2.hi, SourceMainFramesV1.Point0375.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=370) domain
     SourceMainFramesV1.Point0370.input_defined SourceMainFramesV1.Point0370.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0370.outputs.2.hi (by
         change SourceMainFramesV1.Point0370.outputs.2.hi ∈ [SourceMainFramesV1.Point0368.outputs.2.hi, SourceMainFramesV1.Point0369.outputs.2.hi, SourceMainFramesV1.Point0370.outputs.2.hi, SourceMainFramesV1.Point0371.outputs.2.hi, SourceMainFramesV1.Point0372.outputs.2.hi, SourceMainFramesV1.Point0373.outputs.2.hi, SourceMainFramesV1.Point0374.outputs.2.hi, SourceMainFramesV1.Point0375.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=371) domain
     SourceMainFramesV1.Point0371.input_defined SourceMainFramesV1.Point0371.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0371.outputs.2.hi (by
         change SourceMainFramesV1.Point0371.outputs.2.hi ∈ [SourceMainFramesV1.Point0368.outputs.2.hi, SourceMainFramesV1.Point0369.outputs.2.hi, SourceMainFramesV1.Point0370.outputs.2.hi, SourceMainFramesV1.Point0371.outputs.2.hi, SourceMainFramesV1.Point0372.outputs.2.hi, SourceMainFramesV1.Point0373.outputs.2.hi, SourceMainFramesV1.Point0374.outputs.2.hi, SourceMainFramesV1.Point0375.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=372) domain
     SourceMainFramesV1.Point0372.input_defined SourceMainFramesV1.Point0372.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0372.outputs.2.hi (by
         change SourceMainFramesV1.Point0372.outputs.2.hi ∈ [SourceMainFramesV1.Point0368.outputs.2.hi, SourceMainFramesV1.Point0369.outputs.2.hi, SourceMainFramesV1.Point0370.outputs.2.hi, SourceMainFramesV1.Point0371.outputs.2.hi, SourceMainFramesV1.Point0372.outputs.2.hi, SourceMainFramesV1.Point0373.outputs.2.hi, SourceMainFramesV1.Point0374.outputs.2.hi, SourceMainFramesV1.Point0375.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=373) domain
     SourceMainFramesV1.Point0373.input_defined SourceMainFramesV1.Point0373.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0373.outputs.2.hi (by
         change SourceMainFramesV1.Point0373.outputs.2.hi ∈ [SourceMainFramesV1.Point0368.outputs.2.hi, SourceMainFramesV1.Point0369.outputs.2.hi, SourceMainFramesV1.Point0370.outputs.2.hi, SourceMainFramesV1.Point0371.outputs.2.hi, SourceMainFramesV1.Point0372.outputs.2.hi, SourceMainFramesV1.Point0373.outputs.2.hi, SourceMainFramesV1.Point0374.outputs.2.hi, SourceMainFramesV1.Point0375.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=374) domain
     SourceMainFramesV1.Point0374.input_defined SourceMainFramesV1.Point0374.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0374.outputs.2.hi (by
         change SourceMainFramesV1.Point0374.outputs.2.hi ∈ [SourceMainFramesV1.Point0368.outputs.2.hi, SourceMainFramesV1.Point0369.outputs.2.hi, SourceMainFramesV1.Point0370.outputs.2.hi, SourceMainFramesV1.Point0371.outputs.2.hi, SourceMainFramesV1.Point0372.outputs.2.hi, SourceMainFramesV1.Point0373.outputs.2.hi, SourceMainFramesV1.Point0374.outputs.2.hi, SourceMainFramesV1.Point0375.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=375) domain
     SourceMainFramesV1.Point0375.input_defined SourceMainFramesV1.Point0375.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0375.outputs.2.hi (by
         change SourceMainFramesV1.Point0375.outputs.2.hi ∈ [SourceMainFramesV1.Point0368.outputs.2.hi, SourceMainFramesV1.Point0369.outputs.2.hi, SourceMainFramesV1.Point0370.outputs.2.hi, SourceMainFramesV1.Point0371.outputs.2.hi, SourceMainFramesV1.Point0372.outputs.2.hi, SourceMainFramesV1.Point0373.outputs.2.hi, SourceMainFramesV1.Point0374.outputs.2.hi, SourceMainFramesV1.Point0375.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block46
