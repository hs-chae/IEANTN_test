/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0584
import SourceMainFramesV1.Point0585
import SourceMainFramesV1.Point0586
import SourceMainFramesV1.Point0587
import SourceMainFramesV1.Point0588
import SourceMainFramesV1.Point0589
import SourceMainFramesV1.Point0590
import SourceMainFramesV1.Point0591
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block73
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0584.outputs.2.hi,
 SourceMainFramesV1.Point0585.outputs.2.hi,
 SourceMainFramesV1.Point0586.outputs.2.hi,
 SourceMainFramesV1.Point0587.outputs.2.hi,
 SourceMainFramesV1.Point0588.outputs.2.hi,
 SourceMainFramesV1.Point0589.outputs.2.hi,
 SourceMainFramesV1.Point0590.outputs.2.hi,
 SourceMainFramesV1.Point0591.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 584 ≤ i) (high : i < 592)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=584) domain
     SourceMainFramesV1.Point0584.input_defined SourceMainFramesV1.Point0584.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0584.outputs.2.hi (by
         change SourceMainFramesV1.Point0584.outputs.2.hi ∈ [SourceMainFramesV1.Point0584.outputs.2.hi, SourceMainFramesV1.Point0585.outputs.2.hi, SourceMainFramesV1.Point0586.outputs.2.hi, SourceMainFramesV1.Point0587.outputs.2.hi, SourceMainFramesV1.Point0588.outputs.2.hi, SourceMainFramesV1.Point0589.outputs.2.hi, SourceMainFramesV1.Point0590.outputs.2.hi, SourceMainFramesV1.Point0591.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=585) domain
     SourceMainFramesV1.Point0585.input_defined SourceMainFramesV1.Point0585.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0585.outputs.2.hi (by
         change SourceMainFramesV1.Point0585.outputs.2.hi ∈ [SourceMainFramesV1.Point0584.outputs.2.hi, SourceMainFramesV1.Point0585.outputs.2.hi, SourceMainFramesV1.Point0586.outputs.2.hi, SourceMainFramesV1.Point0587.outputs.2.hi, SourceMainFramesV1.Point0588.outputs.2.hi, SourceMainFramesV1.Point0589.outputs.2.hi, SourceMainFramesV1.Point0590.outputs.2.hi, SourceMainFramesV1.Point0591.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=586) domain
     SourceMainFramesV1.Point0586.input_defined SourceMainFramesV1.Point0586.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0586.outputs.2.hi (by
         change SourceMainFramesV1.Point0586.outputs.2.hi ∈ [SourceMainFramesV1.Point0584.outputs.2.hi, SourceMainFramesV1.Point0585.outputs.2.hi, SourceMainFramesV1.Point0586.outputs.2.hi, SourceMainFramesV1.Point0587.outputs.2.hi, SourceMainFramesV1.Point0588.outputs.2.hi, SourceMainFramesV1.Point0589.outputs.2.hi, SourceMainFramesV1.Point0590.outputs.2.hi, SourceMainFramesV1.Point0591.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=587) domain
     SourceMainFramesV1.Point0587.input_defined SourceMainFramesV1.Point0587.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0587.outputs.2.hi (by
         change SourceMainFramesV1.Point0587.outputs.2.hi ∈ [SourceMainFramesV1.Point0584.outputs.2.hi, SourceMainFramesV1.Point0585.outputs.2.hi, SourceMainFramesV1.Point0586.outputs.2.hi, SourceMainFramesV1.Point0587.outputs.2.hi, SourceMainFramesV1.Point0588.outputs.2.hi, SourceMainFramesV1.Point0589.outputs.2.hi, SourceMainFramesV1.Point0590.outputs.2.hi, SourceMainFramesV1.Point0591.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=588) domain
     SourceMainFramesV1.Point0588.input_defined SourceMainFramesV1.Point0588.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0588.outputs.2.hi (by
         change SourceMainFramesV1.Point0588.outputs.2.hi ∈ [SourceMainFramesV1.Point0584.outputs.2.hi, SourceMainFramesV1.Point0585.outputs.2.hi, SourceMainFramesV1.Point0586.outputs.2.hi, SourceMainFramesV1.Point0587.outputs.2.hi, SourceMainFramesV1.Point0588.outputs.2.hi, SourceMainFramesV1.Point0589.outputs.2.hi, SourceMainFramesV1.Point0590.outputs.2.hi, SourceMainFramesV1.Point0591.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=589) domain
     SourceMainFramesV1.Point0589.input_defined SourceMainFramesV1.Point0589.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0589.outputs.2.hi (by
         change SourceMainFramesV1.Point0589.outputs.2.hi ∈ [SourceMainFramesV1.Point0584.outputs.2.hi, SourceMainFramesV1.Point0585.outputs.2.hi, SourceMainFramesV1.Point0586.outputs.2.hi, SourceMainFramesV1.Point0587.outputs.2.hi, SourceMainFramesV1.Point0588.outputs.2.hi, SourceMainFramesV1.Point0589.outputs.2.hi, SourceMainFramesV1.Point0590.outputs.2.hi, SourceMainFramesV1.Point0591.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=590) domain
     SourceMainFramesV1.Point0590.input_defined SourceMainFramesV1.Point0590.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0590.outputs.2.hi (by
         change SourceMainFramesV1.Point0590.outputs.2.hi ∈ [SourceMainFramesV1.Point0584.outputs.2.hi, SourceMainFramesV1.Point0585.outputs.2.hi, SourceMainFramesV1.Point0586.outputs.2.hi, SourceMainFramesV1.Point0587.outputs.2.hi, SourceMainFramesV1.Point0588.outputs.2.hi, SourceMainFramesV1.Point0589.outputs.2.hi, SourceMainFramesV1.Point0590.outputs.2.hi, SourceMainFramesV1.Point0591.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=591) domain
     SourceMainFramesV1.Point0591.input_defined SourceMainFramesV1.Point0591.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0591.outputs.2.hi (by
         change SourceMainFramesV1.Point0591.outputs.2.hi ∈ [SourceMainFramesV1.Point0584.outputs.2.hi, SourceMainFramesV1.Point0585.outputs.2.hi, SourceMainFramesV1.Point0586.outputs.2.hi, SourceMainFramesV1.Point0587.outputs.2.hi, SourceMainFramesV1.Point0588.outputs.2.hi, SourceMainFramesV1.Point0589.outputs.2.hi, SourceMainFramesV1.Point0590.outputs.2.hi, SourceMainFramesV1.Point0591.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block73
