/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0008
import SourceMainFramesV1.Point0009
import SourceMainFramesV1.Point0010
import SourceMainFramesV1.Point0011
import SourceMainFramesV1.Point0012
import SourceMainFramesV1.Point0013
import SourceMainFramesV1.Point0014
import SourceMainFramesV1.Point0015
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block01
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0008.outputs.2.hi,
 SourceMainFramesV1.Point0009.outputs.2.hi,
 SourceMainFramesV1.Point0010.outputs.2.hi,
 SourceMainFramesV1.Point0011.outputs.2.hi,
 SourceMainFramesV1.Point0012.outputs.2.hi,
 SourceMainFramesV1.Point0013.outputs.2.hi,
 SourceMainFramesV1.Point0014.outputs.2.hi,
 SourceMainFramesV1.Point0015.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 8 ≤ i) (high : i < 16)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=8) domain
     SourceMainFramesV1.Point0008.input_defined SourceMainFramesV1.Point0008.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0008.outputs.2.hi (by
         change SourceMainFramesV1.Point0008.outputs.2.hi ∈ [SourceMainFramesV1.Point0008.outputs.2.hi, SourceMainFramesV1.Point0009.outputs.2.hi, SourceMainFramesV1.Point0010.outputs.2.hi, SourceMainFramesV1.Point0011.outputs.2.hi, SourceMainFramesV1.Point0012.outputs.2.hi, SourceMainFramesV1.Point0013.outputs.2.hi, SourceMainFramesV1.Point0014.outputs.2.hi, SourceMainFramesV1.Point0015.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=9) domain
     SourceMainFramesV1.Point0009.input_defined SourceMainFramesV1.Point0009.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0009.outputs.2.hi (by
         change SourceMainFramesV1.Point0009.outputs.2.hi ∈ [SourceMainFramesV1.Point0008.outputs.2.hi, SourceMainFramesV1.Point0009.outputs.2.hi, SourceMainFramesV1.Point0010.outputs.2.hi, SourceMainFramesV1.Point0011.outputs.2.hi, SourceMainFramesV1.Point0012.outputs.2.hi, SourceMainFramesV1.Point0013.outputs.2.hi, SourceMainFramesV1.Point0014.outputs.2.hi, SourceMainFramesV1.Point0015.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=10) domain
     SourceMainFramesV1.Point0010.input_defined SourceMainFramesV1.Point0010.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0010.outputs.2.hi (by
         change SourceMainFramesV1.Point0010.outputs.2.hi ∈ [SourceMainFramesV1.Point0008.outputs.2.hi, SourceMainFramesV1.Point0009.outputs.2.hi, SourceMainFramesV1.Point0010.outputs.2.hi, SourceMainFramesV1.Point0011.outputs.2.hi, SourceMainFramesV1.Point0012.outputs.2.hi, SourceMainFramesV1.Point0013.outputs.2.hi, SourceMainFramesV1.Point0014.outputs.2.hi, SourceMainFramesV1.Point0015.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=11) domain
     SourceMainFramesV1.Point0011.input_defined SourceMainFramesV1.Point0011.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0011.outputs.2.hi (by
         change SourceMainFramesV1.Point0011.outputs.2.hi ∈ [SourceMainFramesV1.Point0008.outputs.2.hi, SourceMainFramesV1.Point0009.outputs.2.hi, SourceMainFramesV1.Point0010.outputs.2.hi, SourceMainFramesV1.Point0011.outputs.2.hi, SourceMainFramesV1.Point0012.outputs.2.hi, SourceMainFramesV1.Point0013.outputs.2.hi, SourceMainFramesV1.Point0014.outputs.2.hi, SourceMainFramesV1.Point0015.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=12) domain
     SourceMainFramesV1.Point0012.input_defined SourceMainFramesV1.Point0012.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0012.outputs.2.hi (by
         change SourceMainFramesV1.Point0012.outputs.2.hi ∈ [SourceMainFramesV1.Point0008.outputs.2.hi, SourceMainFramesV1.Point0009.outputs.2.hi, SourceMainFramesV1.Point0010.outputs.2.hi, SourceMainFramesV1.Point0011.outputs.2.hi, SourceMainFramesV1.Point0012.outputs.2.hi, SourceMainFramesV1.Point0013.outputs.2.hi, SourceMainFramesV1.Point0014.outputs.2.hi, SourceMainFramesV1.Point0015.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=13) domain
     SourceMainFramesV1.Point0013.input_defined SourceMainFramesV1.Point0013.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0013.outputs.2.hi (by
         change SourceMainFramesV1.Point0013.outputs.2.hi ∈ [SourceMainFramesV1.Point0008.outputs.2.hi, SourceMainFramesV1.Point0009.outputs.2.hi, SourceMainFramesV1.Point0010.outputs.2.hi, SourceMainFramesV1.Point0011.outputs.2.hi, SourceMainFramesV1.Point0012.outputs.2.hi, SourceMainFramesV1.Point0013.outputs.2.hi, SourceMainFramesV1.Point0014.outputs.2.hi, SourceMainFramesV1.Point0015.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=14) domain
     SourceMainFramesV1.Point0014.input_defined SourceMainFramesV1.Point0014.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0014.outputs.2.hi (by
         change SourceMainFramesV1.Point0014.outputs.2.hi ∈ [SourceMainFramesV1.Point0008.outputs.2.hi, SourceMainFramesV1.Point0009.outputs.2.hi, SourceMainFramesV1.Point0010.outputs.2.hi, SourceMainFramesV1.Point0011.outputs.2.hi, SourceMainFramesV1.Point0012.outputs.2.hi, SourceMainFramesV1.Point0013.outputs.2.hi, SourceMainFramesV1.Point0014.outputs.2.hi, SourceMainFramesV1.Point0015.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=15) domain
     SourceMainFramesV1.Point0015.input_defined SourceMainFramesV1.Point0015.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0015.outputs.2.hi (by
         change SourceMainFramesV1.Point0015.outputs.2.hi ∈ [SourceMainFramesV1.Point0008.outputs.2.hi, SourceMainFramesV1.Point0009.outputs.2.hi, SourceMainFramesV1.Point0010.outputs.2.hi, SourceMainFramesV1.Point0011.outputs.2.hi, SourceMainFramesV1.Point0012.outputs.2.hi, SourceMainFramesV1.Point0013.outputs.2.hi, SourceMainFramesV1.Point0014.outputs.2.hi, SourceMainFramesV1.Point0015.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block01
