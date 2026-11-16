/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0000
import SourceMainFramesV1.Point0001
import SourceMainFramesV1.Point0002
import SourceMainFramesV1.Point0003
import SourceMainFramesV1.Point0004
import SourceMainFramesV1.Point0005
import SourceMainFramesV1.Point0006
import SourceMainFramesV1.Point0007
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block00
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0000.outputs.2.hi,
 SourceMainFramesV1.Point0001.outputs.2.hi,
 SourceMainFramesV1.Point0002.outputs.2.hi,
 SourceMainFramesV1.Point0003.outputs.2.hi,
 SourceMainFramesV1.Point0004.outputs.2.hi,
 SourceMainFramesV1.Point0005.outputs.2.hi,
 SourceMainFramesV1.Point0006.outputs.2.hi,
 SourceMainFramesV1.Point0007.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 0 ≤ i) (high : i < 8)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=0) domain
     SourceMainFramesV1.Point0000.input_defined SourceMainFramesV1.Point0000.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0000.outputs.2.hi (by
         change SourceMainFramesV1.Point0000.outputs.2.hi ∈ [SourceMainFramesV1.Point0000.outputs.2.hi, SourceMainFramesV1.Point0001.outputs.2.hi, SourceMainFramesV1.Point0002.outputs.2.hi, SourceMainFramesV1.Point0003.outputs.2.hi, SourceMainFramesV1.Point0004.outputs.2.hi, SourceMainFramesV1.Point0005.outputs.2.hi, SourceMainFramesV1.Point0006.outputs.2.hi, SourceMainFramesV1.Point0007.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=1) domain
     SourceMainFramesV1.Point0001.input_defined SourceMainFramesV1.Point0001.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0001.outputs.2.hi (by
         change SourceMainFramesV1.Point0001.outputs.2.hi ∈ [SourceMainFramesV1.Point0000.outputs.2.hi, SourceMainFramesV1.Point0001.outputs.2.hi, SourceMainFramesV1.Point0002.outputs.2.hi, SourceMainFramesV1.Point0003.outputs.2.hi, SourceMainFramesV1.Point0004.outputs.2.hi, SourceMainFramesV1.Point0005.outputs.2.hi, SourceMainFramesV1.Point0006.outputs.2.hi, SourceMainFramesV1.Point0007.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=2) domain
     SourceMainFramesV1.Point0002.input_defined SourceMainFramesV1.Point0002.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0002.outputs.2.hi (by
         change SourceMainFramesV1.Point0002.outputs.2.hi ∈ [SourceMainFramesV1.Point0000.outputs.2.hi, SourceMainFramesV1.Point0001.outputs.2.hi, SourceMainFramesV1.Point0002.outputs.2.hi, SourceMainFramesV1.Point0003.outputs.2.hi, SourceMainFramesV1.Point0004.outputs.2.hi, SourceMainFramesV1.Point0005.outputs.2.hi, SourceMainFramesV1.Point0006.outputs.2.hi, SourceMainFramesV1.Point0007.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=3) domain
     SourceMainFramesV1.Point0003.input_defined SourceMainFramesV1.Point0003.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0003.outputs.2.hi (by
         change SourceMainFramesV1.Point0003.outputs.2.hi ∈ [SourceMainFramesV1.Point0000.outputs.2.hi, SourceMainFramesV1.Point0001.outputs.2.hi, SourceMainFramesV1.Point0002.outputs.2.hi, SourceMainFramesV1.Point0003.outputs.2.hi, SourceMainFramesV1.Point0004.outputs.2.hi, SourceMainFramesV1.Point0005.outputs.2.hi, SourceMainFramesV1.Point0006.outputs.2.hi, SourceMainFramesV1.Point0007.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=4) domain
     SourceMainFramesV1.Point0004.input_defined SourceMainFramesV1.Point0004.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0004.outputs.2.hi (by
         change SourceMainFramesV1.Point0004.outputs.2.hi ∈ [SourceMainFramesV1.Point0000.outputs.2.hi, SourceMainFramesV1.Point0001.outputs.2.hi, SourceMainFramesV1.Point0002.outputs.2.hi, SourceMainFramesV1.Point0003.outputs.2.hi, SourceMainFramesV1.Point0004.outputs.2.hi, SourceMainFramesV1.Point0005.outputs.2.hi, SourceMainFramesV1.Point0006.outputs.2.hi, SourceMainFramesV1.Point0007.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=5) domain
     SourceMainFramesV1.Point0005.input_defined SourceMainFramesV1.Point0005.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0005.outputs.2.hi (by
         change SourceMainFramesV1.Point0005.outputs.2.hi ∈ [SourceMainFramesV1.Point0000.outputs.2.hi, SourceMainFramesV1.Point0001.outputs.2.hi, SourceMainFramesV1.Point0002.outputs.2.hi, SourceMainFramesV1.Point0003.outputs.2.hi, SourceMainFramesV1.Point0004.outputs.2.hi, SourceMainFramesV1.Point0005.outputs.2.hi, SourceMainFramesV1.Point0006.outputs.2.hi, SourceMainFramesV1.Point0007.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=6) domain
     SourceMainFramesV1.Point0006.input_defined SourceMainFramesV1.Point0006.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0006.outputs.2.hi (by
         change SourceMainFramesV1.Point0006.outputs.2.hi ∈ [SourceMainFramesV1.Point0000.outputs.2.hi, SourceMainFramesV1.Point0001.outputs.2.hi, SourceMainFramesV1.Point0002.outputs.2.hi, SourceMainFramesV1.Point0003.outputs.2.hi, SourceMainFramesV1.Point0004.outputs.2.hi, SourceMainFramesV1.Point0005.outputs.2.hi, SourceMainFramesV1.Point0006.outputs.2.hi, SourceMainFramesV1.Point0007.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=7) domain
     SourceMainFramesV1.Point0007.input_defined SourceMainFramesV1.Point0007.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0007.outputs.2.hi (by
         change SourceMainFramesV1.Point0007.outputs.2.hi ∈ [SourceMainFramesV1.Point0000.outputs.2.hi, SourceMainFramesV1.Point0001.outputs.2.hi, SourceMainFramesV1.Point0002.outputs.2.hi, SourceMainFramesV1.Point0003.outputs.2.hi, SourceMainFramesV1.Point0004.outputs.2.hi, SourceMainFramesV1.Point0005.outputs.2.hi, SourceMainFramesV1.Point0006.outputs.2.hi, SourceMainFramesV1.Point0007.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block00
