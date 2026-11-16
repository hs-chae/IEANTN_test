/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0360
import SourceMainFramesV1.Point0361
import SourceMainFramesV1.Point0362
import SourceMainFramesV1.Point0363
import SourceMainFramesV1.Point0364
import SourceMainFramesV1.Point0365
import SourceMainFramesV1.Point0366
import SourceMainFramesV1.Point0367
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block45
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0360.outputs.2.hi,
 SourceMainFramesV1.Point0361.outputs.2.hi,
 SourceMainFramesV1.Point0362.outputs.2.hi,
 SourceMainFramesV1.Point0363.outputs.2.hi,
 SourceMainFramesV1.Point0364.outputs.2.hi,
 SourceMainFramesV1.Point0365.outputs.2.hi,
 SourceMainFramesV1.Point0366.outputs.2.hi,
 SourceMainFramesV1.Point0367.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 360 ≤ i) (high : i < 368)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=360) domain
     SourceMainFramesV1.Point0360.input_defined SourceMainFramesV1.Point0360.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0360.outputs.2.hi (by
         change SourceMainFramesV1.Point0360.outputs.2.hi ∈ [SourceMainFramesV1.Point0360.outputs.2.hi, SourceMainFramesV1.Point0361.outputs.2.hi, SourceMainFramesV1.Point0362.outputs.2.hi, SourceMainFramesV1.Point0363.outputs.2.hi, SourceMainFramesV1.Point0364.outputs.2.hi, SourceMainFramesV1.Point0365.outputs.2.hi, SourceMainFramesV1.Point0366.outputs.2.hi, SourceMainFramesV1.Point0367.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=361) domain
     SourceMainFramesV1.Point0361.input_defined SourceMainFramesV1.Point0361.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0361.outputs.2.hi (by
         change SourceMainFramesV1.Point0361.outputs.2.hi ∈ [SourceMainFramesV1.Point0360.outputs.2.hi, SourceMainFramesV1.Point0361.outputs.2.hi, SourceMainFramesV1.Point0362.outputs.2.hi, SourceMainFramesV1.Point0363.outputs.2.hi, SourceMainFramesV1.Point0364.outputs.2.hi, SourceMainFramesV1.Point0365.outputs.2.hi, SourceMainFramesV1.Point0366.outputs.2.hi, SourceMainFramesV1.Point0367.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=362) domain
     SourceMainFramesV1.Point0362.input_defined SourceMainFramesV1.Point0362.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0362.outputs.2.hi (by
         change SourceMainFramesV1.Point0362.outputs.2.hi ∈ [SourceMainFramesV1.Point0360.outputs.2.hi, SourceMainFramesV1.Point0361.outputs.2.hi, SourceMainFramesV1.Point0362.outputs.2.hi, SourceMainFramesV1.Point0363.outputs.2.hi, SourceMainFramesV1.Point0364.outputs.2.hi, SourceMainFramesV1.Point0365.outputs.2.hi, SourceMainFramesV1.Point0366.outputs.2.hi, SourceMainFramesV1.Point0367.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=363) domain
     SourceMainFramesV1.Point0363.input_defined SourceMainFramesV1.Point0363.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0363.outputs.2.hi (by
         change SourceMainFramesV1.Point0363.outputs.2.hi ∈ [SourceMainFramesV1.Point0360.outputs.2.hi, SourceMainFramesV1.Point0361.outputs.2.hi, SourceMainFramesV1.Point0362.outputs.2.hi, SourceMainFramesV1.Point0363.outputs.2.hi, SourceMainFramesV1.Point0364.outputs.2.hi, SourceMainFramesV1.Point0365.outputs.2.hi, SourceMainFramesV1.Point0366.outputs.2.hi, SourceMainFramesV1.Point0367.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=364) domain
     SourceMainFramesV1.Point0364.input_defined SourceMainFramesV1.Point0364.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0364.outputs.2.hi (by
         change SourceMainFramesV1.Point0364.outputs.2.hi ∈ [SourceMainFramesV1.Point0360.outputs.2.hi, SourceMainFramesV1.Point0361.outputs.2.hi, SourceMainFramesV1.Point0362.outputs.2.hi, SourceMainFramesV1.Point0363.outputs.2.hi, SourceMainFramesV1.Point0364.outputs.2.hi, SourceMainFramesV1.Point0365.outputs.2.hi, SourceMainFramesV1.Point0366.outputs.2.hi, SourceMainFramesV1.Point0367.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=365) domain
     SourceMainFramesV1.Point0365.input_defined SourceMainFramesV1.Point0365.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0365.outputs.2.hi (by
         change SourceMainFramesV1.Point0365.outputs.2.hi ∈ [SourceMainFramesV1.Point0360.outputs.2.hi, SourceMainFramesV1.Point0361.outputs.2.hi, SourceMainFramesV1.Point0362.outputs.2.hi, SourceMainFramesV1.Point0363.outputs.2.hi, SourceMainFramesV1.Point0364.outputs.2.hi, SourceMainFramesV1.Point0365.outputs.2.hi, SourceMainFramesV1.Point0366.outputs.2.hi, SourceMainFramesV1.Point0367.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=366) domain
     SourceMainFramesV1.Point0366.input_defined SourceMainFramesV1.Point0366.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0366.outputs.2.hi (by
         change SourceMainFramesV1.Point0366.outputs.2.hi ∈ [SourceMainFramesV1.Point0360.outputs.2.hi, SourceMainFramesV1.Point0361.outputs.2.hi, SourceMainFramesV1.Point0362.outputs.2.hi, SourceMainFramesV1.Point0363.outputs.2.hi, SourceMainFramesV1.Point0364.outputs.2.hi, SourceMainFramesV1.Point0365.outputs.2.hi, SourceMainFramesV1.Point0366.outputs.2.hi, SourceMainFramesV1.Point0367.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=367) domain
     SourceMainFramesV1.Point0367.input_defined SourceMainFramesV1.Point0367.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0367.outputs.2.hi (by
         change SourceMainFramesV1.Point0367.outputs.2.hi ∈ [SourceMainFramesV1.Point0360.outputs.2.hi, SourceMainFramesV1.Point0361.outputs.2.hi, SourceMainFramesV1.Point0362.outputs.2.hi, SourceMainFramesV1.Point0363.outputs.2.hi, SourceMainFramesV1.Point0364.outputs.2.hi, SourceMainFramesV1.Point0365.outputs.2.hi, SourceMainFramesV1.Point0366.outputs.2.hi, SourceMainFramesV1.Point0367.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block45
