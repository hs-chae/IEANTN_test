/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0216
import SourceMainFramesV1.Point0217
import SourceMainFramesV1.Point0218
import SourceMainFramesV1.Point0219
import SourceMainFramesV1.Point0220
import SourceMainFramesV1.Point0221
import SourceMainFramesV1.Point0222
import SourceMainFramesV1.Point0223
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block27
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0216.outputs.2.hi,
 SourceMainFramesV1.Point0217.outputs.2.hi,
 SourceMainFramesV1.Point0218.outputs.2.hi,
 SourceMainFramesV1.Point0219.outputs.2.hi,
 SourceMainFramesV1.Point0220.outputs.2.hi,
 SourceMainFramesV1.Point0221.outputs.2.hi,
 SourceMainFramesV1.Point0222.outputs.2.hi,
 SourceMainFramesV1.Point0223.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 216 ≤ i) (high : i < 224)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=216) domain
     SourceMainFramesV1.Point0216.input_defined SourceMainFramesV1.Point0216.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0216.outputs.2.hi (by
         change SourceMainFramesV1.Point0216.outputs.2.hi ∈ [SourceMainFramesV1.Point0216.outputs.2.hi, SourceMainFramesV1.Point0217.outputs.2.hi, SourceMainFramesV1.Point0218.outputs.2.hi, SourceMainFramesV1.Point0219.outputs.2.hi, SourceMainFramesV1.Point0220.outputs.2.hi, SourceMainFramesV1.Point0221.outputs.2.hi, SourceMainFramesV1.Point0222.outputs.2.hi, SourceMainFramesV1.Point0223.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=217) domain
     SourceMainFramesV1.Point0217.input_defined SourceMainFramesV1.Point0217.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0217.outputs.2.hi (by
         change SourceMainFramesV1.Point0217.outputs.2.hi ∈ [SourceMainFramesV1.Point0216.outputs.2.hi, SourceMainFramesV1.Point0217.outputs.2.hi, SourceMainFramesV1.Point0218.outputs.2.hi, SourceMainFramesV1.Point0219.outputs.2.hi, SourceMainFramesV1.Point0220.outputs.2.hi, SourceMainFramesV1.Point0221.outputs.2.hi, SourceMainFramesV1.Point0222.outputs.2.hi, SourceMainFramesV1.Point0223.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=218) domain
     SourceMainFramesV1.Point0218.input_defined SourceMainFramesV1.Point0218.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0218.outputs.2.hi (by
         change SourceMainFramesV1.Point0218.outputs.2.hi ∈ [SourceMainFramesV1.Point0216.outputs.2.hi, SourceMainFramesV1.Point0217.outputs.2.hi, SourceMainFramesV1.Point0218.outputs.2.hi, SourceMainFramesV1.Point0219.outputs.2.hi, SourceMainFramesV1.Point0220.outputs.2.hi, SourceMainFramesV1.Point0221.outputs.2.hi, SourceMainFramesV1.Point0222.outputs.2.hi, SourceMainFramesV1.Point0223.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=219) domain
     SourceMainFramesV1.Point0219.input_defined SourceMainFramesV1.Point0219.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0219.outputs.2.hi (by
         change SourceMainFramesV1.Point0219.outputs.2.hi ∈ [SourceMainFramesV1.Point0216.outputs.2.hi, SourceMainFramesV1.Point0217.outputs.2.hi, SourceMainFramesV1.Point0218.outputs.2.hi, SourceMainFramesV1.Point0219.outputs.2.hi, SourceMainFramesV1.Point0220.outputs.2.hi, SourceMainFramesV1.Point0221.outputs.2.hi, SourceMainFramesV1.Point0222.outputs.2.hi, SourceMainFramesV1.Point0223.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=220) domain
     SourceMainFramesV1.Point0220.input_defined SourceMainFramesV1.Point0220.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0220.outputs.2.hi (by
         change SourceMainFramesV1.Point0220.outputs.2.hi ∈ [SourceMainFramesV1.Point0216.outputs.2.hi, SourceMainFramesV1.Point0217.outputs.2.hi, SourceMainFramesV1.Point0218.outputs.2.hi, SourceMainFramesV1.Point0219.outputs.2.hi, SourceMainFramesV1.Point0220.outputs.2.hi, SourceMainFramesV1.Point0221.outputs.2.hi, SourceMainFramesV1.Point0222.outputs.2.hi, SourceMainFramesV1.Point0223.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=221) domain
     SourceMainFramesV1.Point0221.input_defined SourceMainFramesV1.Point0221.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0221.outputs.2.hi (by
         change SourceMainFramesV1.Point0221.outputs.2.hi ∈ [SourceMainFramesV1.Point0216.outputs.2.hi, SourceMainFramesV1.Point0217.outputs.2.hi, SourceMainFramesV1.Point0218.outputs.2.hi, SourceMainFramesV1.Point0219.outputs.2.hi, SourceMainFramesV1.Point0220.outputs.2.hi, SourceMainFramesV1.Point0221.outputs.2.hi, SourceMainFramesV1.Point0222.outputs.2.hi, SourceMainFramesV1.Point0223.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=222) domain
     SourceMainFramesV1.Point0222.input_defined SourceMainFramesV1.Point0222.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0222.outputs.2.hi (by
         change SourceMainFramesV1.Point0222.outputs.2.hi ∈ [SourceMainFramesV1.Point0216.outputs.2.hi, SourceMainFramesV1.Point0217.outputs.2.hi, SourceMainFramesV1.Point0218.outputs.2.hi, SourceMainFramesV1.Point0219.outputs.2.hi, SourceMainFramesV1.Point0220.outputs.2.hi, SourceMainFramesV1.Point0221.outputs.2.hi, SourceMainFramesV1.Point0222.outputs.2.hi, SourceMainFramesV1.Point0223.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=223) domain
     SourceMainFramesV1.Point0223.input_defined SourceMainFramesV1.Point0223.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0223.outputs.2.hi (by
         change SourceMainFramesV1.Point0223.outputs.2.hi ∈ [SourceMainFramesV1.Point0216.outputs.2.hi, SourceMainFramesV1.Point0217.outputs.2.hi, SourceMainFramesV1.Point0218.outputs.2.hi, SourceMainFramesV1.Point0219.outputs.2.hi, SourceMainFramesV1.Point0220.outputs.2.hi, SourceMainFramesV1.Point0221.outputs.2.hi, SourceMainFramesV1.Point0222.outputs.2.hi, SourceMainFramesV1.Point0223.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block27
