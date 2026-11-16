/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0752
import SourceMainFramesV1.Point0753
import SourceMainFramesV1.Point0754
import SourceMainFramesV1.Point0755
import SourceMainFramesV1.Point0756
import SourceMainFramesV1.Point0757
import SourceMainFramesV1.Point0758
import SourceMainFramesV1.Point0759
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block94
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0752.outputs.2.hi,
 SourceMainFramesV1.Point0753.outputs.2.hi,
 SourceMainFramesV1.Point0754.outputs.2.hi,
 SourceMainFramesV1.Point0755.outputs.2.hi,
 SourceMainFramesV1.Point0756.outputs.2.hi,
 SourceMainFramesV1.Point0757.outputs.2.hi,
 SourceMainFramesV1.Point0758.outputs.2.hi,
 SourceMainFramesV1.Point0759.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 752 ≤ i) (high : i < 760)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=752) domain
     SourceMainFramesV1.Point0752.input_defined SourceMainFramesV1.Point0752.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0752.outputs.2.hi (by
         change SourceMainFramesV1.Point0752.outputs.2.hi ∈ [SourceMainFramesV1.Point0752.outputs.2.hi, SourceMainFramesV1.Point0753.outputs.2.hi, SourceMainFramesV1.Point0754.outputs.2.hi, SourceMainFramesV1.Point0755.outputs.2.hi, SourceMainFramesV1.Point0756.outputs.2.hi, SourceMainFramesV1.Point0757.outputs.2.hi, SourceMainFramesV1.Point0758.outputs.2.hi, SourceMainFramesV1.Point0759.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=753) domain
     SourceMainFramesV1.Point0753.input_defined SourceMainFramesV1.Point0753.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0753.outputs.2.hi (by
         change SourceMainFramesV1.Point0753.outputs.2.hi ∈ [SourceMainFramesV1.Point0752.outputs.2.hi, SourceMainFramesV1.Point0753.outputs.2.hi, SourceMainFramesV1.Point0754.outputs.2.hi, SourceMainFramesV1.Point0755.outputs.2.hi, SourceMainFramesV1.Point0756.outputs.2.hi, SourceMainFramesV1.Point0757.outputs.2.hi, SourceMainFramesV1.Point0758.outputs.2.hi, SourceMainFramesV1.Point0759.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=754) domain
     SourceMainFramesV1.Point0754.input_defined SourceMainFramesV1.Point0754.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0754.outputs.2.hi (by
         change SourceMainFramesV1.Point0754.outputs.2.hi ∈ [SourceMainFramesV1.Point0752.outputs.2.hi, SourceMainFramesV1.Point0753.outputs.2.hi, SourceMainFramesV1.Point0754.outputs.2.hi, SourceMainFramesV1.Point0755.outputs.2.hi, SourceMainFramesV1.Point0756.outputs.2.hi, SourceMainFramesV1.Point0757.outputs.2.hi, SourceMainFramesV1.Point0758.outputs.2.hi, SourceMainFramesV1.Point0759.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=755) domain
     SourceMainFramesV1.Point0755.input_defined SourceMainFramesV1.Point0755.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0755.outputs.2.hi (by
         change SourceMainFramesV1.Point0755.outputs.2.hi ∈ [SourceMainFramesV1.Point0752.outputs.2.hi, SourceMainFramesV1.Point0753.outputs.2.hi, SourceMainFramesV1.Point0754.outputs.2.hi, SourceMainFramesV1.Point0755.outputs.2.hi, SourceMainFramesV1.Point0756.outputs.2.hi, SourceMainFramesV1.Point0757.outputs.2.hi, SourceMainFramesV1.Point0758.outputs.2.hi, SourceMainFramesV1.Point0759.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=756) domain
     SourceMainFramesV1.Point0756.input_defined SourceMainFramesV1.Point0756.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0756.outputs.2.hi (by
         change SourceMainFramesV1.Point0756.outputs.2.hi ∈ [SourceMainFramesV1.Point0752.outputs.2.hi, SourceMainFramesV1.Point0753.outputs.2.hi, SourceMainFramesV1.Point0754.outputs.2.hi, SourceMainFramesV1.Point0755.outputs.2.hi, SourceMainFramesV1.Point0756.outputs.2.hi, SourceMainFramesV1.Point0757.outputs.2.hi, SourceMainFramesV1.Point0758.outputs.2.hi, SourceMainFramesV1.Point0759.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=757) domain
     SourceMainFramesV1.Point0757.input_defined SourceMainFramesV1.Point0757.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0757.outputs.2.hi (by
         change SourceMainFramesV1.Point0757.outputs.2.hi ∈ [SourceMainFramesV1.Point0752.outputs.2.hi, SourceMainFramesV1.Point0753.outputs.2.hi, SourceMainFramesV1.Point0754.outputs.2.hi, SourceMainFramesV1.Point0755.outputs.2.hi, SourceMainFramesV1.Point0756.outputs.2.hi, SourceMainFramesV1.Point0757.outputs.2.hi, SourceMainFramesV1.Point0758.outputs.2.hi, SourceMainFramesV1.Point0759.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=758) domain
     SourceMainFramesV1.Point0758.input_defined SourceMainFramesV1.Point0758.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0758.outputs.2.hi (by
         change SourceMainFramesV1.Point0758.outputs.2.hi ∈ [SourceMainFramesV1.Point0752.outputs.2.hi, SourceMainFramesV1.Point0753.outputs.2.hi, SourceMainFramesV1.Point0754.outputs.2.hi, SourceMainFramesV1.Point0755.outputs.2.hi, SourceMainFramesV1.Point0756.outputs.2.hi, SourceMainFramesV1.Point0757.outputs.2.hi, SourceMainFramesV1.Point0758.outputs.2.hi, SourceMainFramesV1.Point0759.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=759) domain
     SourceMainFramesV1.Point0759.input_defined SourceMainFramesV1.Point0759.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0759.outputs.2.hi (by
         change SourceMainFramesV1.Point0759.outputs.2.hi ∈ [SourceMainFramesV1.Point0752.outputs.2.hi, SourceMainFramesV1.Point0753.outputs.2.hi, SourceMainFramesV1.Point0754.outputs.2.hi, SourceMainFramesV1.Point0755.outputs.2.hi, SourceMainFramesV1.Point0756.outputs.2.hi, SourceMainFramesV1.Point0757.outputs.2.hi, SourceMainFramesV1.Point0758.outputs.2.hi, SourceMainFramesV1.Point0759.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block94
