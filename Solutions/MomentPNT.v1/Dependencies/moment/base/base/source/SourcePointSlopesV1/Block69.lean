/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0552
import SourceMainFramesV1.Point0553
import SourceMainFramesV1.Point0554
import SourceMainFramesV1.Point0555
import SourceMainFramesV1.Point0556
import SourceMainFramesV1.Point0557
import SourceMainFramesV1.Point0558
import SourceMainFramesV1.Point0559
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block69
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0552.outputs.2.hi,
 SourceMainFramesV1.Point0553.outputs.2.hi,
 SourceMainFramesV1.Point0554.outputs.2.hi,
 SourceMainFramesV1.Point0555.outputs.2.hi,
 SourceMainFramesV1.Point0556.outputs.2.hi,
 SourceMainFramesV1.Point0557.outputs.2.hi,
 SourceMainFramesV1.Point0558.outputs.2.hi,
 SourceMainFramesV1.Point0559.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 552 ≤ i) (high : i < 560)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=552) domain
     SourceMainFramesV1.Point0552.input_defined SourceMainFramesV1.Point0552.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0552.outputs.2.hi (by
         change SourceMainFramesV1.Point0552.outputs.2.hi ∈ [SourceMainFramesV1.Point0552.outputs.2.hi, SourceMainFramesV1.Point0553.outputs.2.hi, SourceMainFramesV1.Point0554.outputs.2.hi, SourceMainFramesV1.Point0555.outputs.2.hi, SourceMainFramesV1.Point0556.outputs.2.hi, SourceMainFramesV1.Point0557.outputs.2.hi, SourceMainFramesV1.Point0558.outputs.2.hi, SourceMainFramesV1.Point0559.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=553) domain
     SourceMainFramesV1.Point0553.input_defined SourceMainFramesV1.Point0553.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0553.outputs.2.hi (by
         change SourceMainFramesV1.Point0553.outputs.2.hi ∈ [SourceMainFramesV1.Point0552.outputs.2.hi, SourceMainFramesV1.Point0553.outputs.2.hi, SourceMainFramesV1.Point0554.outputs.2.hi, SourceMainFramesV1.Point0555.outputs.2.hi, SourceMainFramesV1.Point0556.outputs.2.hi, SourceMainFramesV1.Point0557.outputs.2.hi, SourceMainFramesV1.Point0558.outputs.2.hi, SourceMainFramesV1.Point0559.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=554) domain
     SourceMainFramesV1.Point0554.input_defined SourceMainFramesV1.Point0554.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0554.outputs.2.hi (by
         change SourceMainFramesV1.Point0554.outputs.2.hi ∈ [SourceMainFramesV1.Point0552.outputs.2.hi, SourceMainFramesV1.Point0553.outputs.2.hi, SourceMainFramesV1.Point0554.outputs.2.hi, SourceMainFramesV1.Point0555.outputs.2.hi, SourceMainFramesV1.Point0556.outputs.2.hi, SourceMainFramesV1.Point0557.outputs.2.hi, SourceMainFramesV1.Point0558.outputs.2.hi, SourceMainFramesV1.Point0559.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=555) domain
     SourceMainFramesV1.Point0555.input_defined SourceMainFramesV1.Point0555.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0555.outputs.2.hi (by
         change SourceMainFramesV1.Point0555.outputs.2.hi ∈ [SourceMainFramesV1.Point0552.outputs.2.hi, SourceMainFramesV1.Point0553.outputs.2.hi, SourceMainFramesV1.Point0554.outputs.2.hi, SourceMainFramesV1.Point0555.outputs.2.hi, SourceMainFramesV1.Point0556.outputs.2.hi, SourceMainFramesV1.Point0557.outputs.2.hi, SourceMainFramesV1.Point0558.outputs.2.hi, SourceMainFramesV1.Point0559.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=556) domain
     SourceMainFramesV1.Point0556.input_defined SourceMainFramesV1.Point0556.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0556.outputs.2.hi (by
         change SourceMainFramesV1.Point0556.outputs.2.hi ∈ [SourceMainFramesV1.Point0552.outputs.2.hi, SourceMainFramesV1.Point0553.outputs.2.hi, SourceMainFramesV1.Point0554.outputs.2.hi, SourceMainFramesV1.Point0555.outputs.2.hi, SourceMainFramesV1.Point0556.outputs.2.hi, SourceMainFramesV1.Point0557.outputs.2.hi, SourceMainFramesV1.Point0558.outputs.2.hi, SourceMainFramesV1.Point0559.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=557) domain
     SourceMainFramesV1.Point0557.input_defined SourceMainFramesV1.Point0557.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0557.outputs.2.hi (by
         change SourceMainFramesV1.Point0557.outputs.2.hi ∈ [SourceMainFramesV1.Point0552.outputs.2.hi, SourceMainFramesV1.Point0553.outputs.2.hi, SourceMainFramesV1.Point0554.outputs.2.hi, SourceMainFramesV1.Point0555.outputs.2.hi, SourceMainFramesV1.Point0556.outputs.2.hi, SourceMainFramesV1.Point0557.outputs.2.hi, SourceMainFramesV1.Point0558.outputs.2.hi, SourceMainFramesV1.Point0559.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=558) domain
     SourceMainFramesV1.Point0558.input_defined SourceMainFramesV1.Point0558.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0558.outputs.2.hi (by
         change SourceMainFramesV1.Point0558.outputs.2.hi ∈ [SourceMainFramesV1.Point0552.outputs.2.hi, SourceMainFramesV1.Point0553.outputs.2.hi, SourceMainFramesV1.Point0554.outputs.2.hi, SourceMainFramesV1.Point0555.outputs.2.hi, SourceMainFramesV1.Point0556.outputs.2.hi, SourceMainFramesV1.Point0557.outputs.2.hi, SourceMainFramesV1.Point0558.outputs.2.hi, SourceMainFramesV1.Point0559.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=559) domain
     SourceMainFramesV1.Point0559.input_defined SourceMainFramesV1.Point0559.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0559.outputs.2.hi (by
         change SourceMainFramesV1.Point0559.outputs.2.hi ∈ [SourceMainFramesV1.Point0552.outputs.2.hi, SourceMainFramesV1.Point0553.outputs.2.hi, SourceMainFramesV1.Point0554.outputs.2.hi, SourceMainFramesV1.Point0555.outputs.2.hi, SourceMainFramesV1.Point0556.outputs.2.hi, SourceMainFramesV1.Point0557.outputs.2.hi, SourceMainFramesV1.Point0558.outputs.2.hi, SourceMainFramesV1.Point0559.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block69
