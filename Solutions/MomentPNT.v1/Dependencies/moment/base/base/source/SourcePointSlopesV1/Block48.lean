/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0384
import SourceMainFramesV1.Point0385
import SourceMainFramesV1.Point0386
import SourceMainFramesV1.Point0387
import SourceMainFramesV1.Point0388
import SourceMainFramesV1.Point0389
import SourceMainFramesV1.Point0390
import SourceMainFramesV1.Point0391
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block48
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0384.outputs.2.hi,
 SourceMainFramesV1.Point0385.outputs.2.hi,
 SourceMainFramesV1.Point0386.outputs.2.hi,
 SourceMainFramesV1.Point0387.outputs.2.hi,
 SourceMainFramesV1.Point0388.outputs.2.hi,
 SourceMainFramesV1.Point0389.outputs.2.hi,
 SourceMainFramesV1.Point0390.outputs.2.hi,
 SourceMainFramesV1.Point0391.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 384 ≤ i) (high : i < 392)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=384) domain
     SourceMainFramesV1.Point0384.input_defined SourceMainFramesV1.Point0384.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0384.outputs.2.hi (by
         change SourceMainFramesV1.Point0384.outputs.2.hi ∈ [SourceMainFramesV1.Point0384.outputs.2.hi, SourceMainFramesV1.Point0385.outputs.2.hi, SourceMainFramesV1.Point0386.outputs.2.hi, SourceMainFramesV1.Point0387.outputs.2.hi, SourceMainFramesV1.Point0388.outputs.2.hi, SourceMainFramesV1.Point0389.outputs.2.hi, SourceMainFramesV1.Point0390.outputs.2.hi, SourceMainFramesV1.Point0391.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=385) domain
     SourceMainFramesV1.Point0385.input_defined SourceMainFramesV1.Point0385.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0385.outputs.2.hi (by
         change SourceMainFramesV1.Point0385.outputs.2.hi ∈ [SourceMainFramesV1.Point0384.outputs.2.hi, SourceMainFramesV1.Point0385.outputs.2.hi, SourceMainFramesV1.Point0386.outputs.2.hi, SourceMainFramesV1.Point0387.outputs.2.hi, SourceMainFramesV1.Point0388.outputs.2.hi, SourceMainFramesV1.Point0389.outputs.2.hi, SourceMainFramesV1.Point0390.outputs.2.hi, SourceMainFramesV1.Point0391.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=386) domain
     SourceMainFramesV1.Point0386.input_defined SourceMainFramesV1.Point0386.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0386.outputs.2.hi (by
         change SourceMainFramesV1.Point0386.outputs.2.hi ∈ [SourceMainFramesV1.Point0384.outputs.2.hi, SourceMainFramesV1.Point0385.outputs.2.hi, SourceMainFramesV1.Point0386.outputs.2.hi, SourceMainFramesV1.Point0387.outputs.2.hi, SourceMainFramesV1.Point0388.outputs.2.hi, SourceMainFramesV1.Point0389.outputs.2.hi, SourceMainFramesV1.Point0390.outputs.2.hi, SourceMainFramesV1.Point0391.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=387) domain
     SourceMainFramesV1.Point0387.input_defined SourceMainFramesV1.Point0387.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0387.outputs.2.hi (by
         change SourceMainFramesV1.Point0387.outputs.2.hi ∈ [SourceMainFramesV1.Point0384.outputs.2.hi, SourceMainFramesV1.Point0385.outputs.2.hi, SourceMainFramesV1.Point0386.outputs.2.hi, SourceMainFramesV1.Point0387.outputs.2.hi, SourceMainFramesV1.Point0388.outputs.2.hi, SourceMainFramesV1.Point0389.outputs.2.hi, SourceMainFramesV1.Point0390.outputs.2.hi, SourceMainFramesV1.Point0391.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=388) domain
     SourceMainFramesV1.Point0388.input_defined SourceMainFramesV1.Point0388.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0388.outputs.2.hi (by
         change SourceMainFramesV1.Point0388.outputs.2.hi ∈ [SourceMainFramesV1.Point0384.outputs.2.hi, SourceMainFramesV1.Point0385.outputs.2.hi, SourceMainFramesV1.Point0386.outputs.2.hi, SourceMainFramesV1.Point0387.outputs.2.hi, SourceMainFramesV1.Point0388.outputs.2.hi, SourceMainFramesV1.Point0389.outputs.2.hi, SourceMainFramesV1.Point0390.outputs.2.hi, SourceMainFramesV1.Point0391.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=389) domain
     SourceMainFramesV1.Point0389.input_defined SourceMainFramesV1.Point0389.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0389.outputs.2.hi (by
         change SourceMainFramesV1.Point0389.outputs.2.hi ∈ [SourceMainFramesV1.Point0384.outputs.2.hi, SourceMainFramesV1.Point0385.outputs.2.hi, SourceMainFramesV1.Point0386.outputs.2.hi, SourceMainFramesV1.Point0387.outputs.2.hi, SourceMainFramesV1.Point0388.outputs.2.hi, SourceMainFramesV1.Point0389.outputs.2.hi, SourceMainFramesV1.Point0390.outputs.2.hi, SourceMainFramesV1.Point0391.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=390) domain
     SourceMainFramesV1.Point0390.input_defined SourceMainFramesV1.Point0390.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0390.outputs.2.hi (by
         change SourceMainFramesV1.Point0390.outputs.2.hi ∈ [SourceMainFramesV1.Point0384.outputs.2.hi, SourceMainFramesV1.Point0385.outputs.2.hi, SourceMainFramesV1.Point0386.outputs.2.hi, SourceMainFramesV1.Point0387.outputs.2.hi, SourceMainFramesV1.Point0388.outputs.2.hi, SourceMainFramesV1.Point0389.outputs.2.hi, SourceMainFramesV1.Point0390.outputs.2.hi, SourceMainFramesV1.Point0391.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=391) domain
     SourceMainFramesV1.Point0391.input_defined SourceMainFramesV1.Point0391.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0391.outputs.2.hi (by
         change SourceMainFramesV1.Point0391.outputs.2.hi ∈ [SourceMainFramesV1.Point0384.outputs.2.hi, SourceMainFramesV1.Point0385.outputs.2.hi, SourceMainFramesV1.Point0386.outputs.2.hi, SourceMainFramesV1.Point0387.outputs.2.hi, SourceMainFramesV1.Point0388.outputs.2.hi, SourceMainFramesV1.Point0389.outputs.2.hi, SourceMainFramesV1.Point0390.outputs.2.hi, SourceMainFramesV1.Point0391.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block48
