import DecodedOutputs
import RamanujanPV.HighTransitionCount.Data
import RamanujanPV.HighTransitionCount.GapCheck

/-! Conditional only on the still-running full, unchanged entry checker.
The existing accepted prime-gap proof is actually consumed. After Final passes,
its entries_checked will discharge the sole numerical premise. -/
namespace RHOcticPush.HighDecodedOutputs
open RamanujanPV RamanujanPV.QuotientDemandCheck
open RamanujanPV.HighTransitionCount

theorem all_meanings
    (checked : checkEntries nodes gaps gapCount entryCount = true) :
    ∀ i, i < entryCount → Meaning (nodes.get i) :=
  DecodedOutputs.all_meanings gaps_checked checked

theorem finished_pi
    (checked : checkEntries nodes gaps gapCount entryCount = true) :
    ∀ i, i < entryCount → (nodes.get i).kind = 2 →
      Nat.primeCounting (nodes.get i).v = (nodes.get i).value :=
  DecodedOutputs.finished_pi gaps_checked checked

theorem finished_source_function
    (checked : checkEntries nodes gaps gapCount entryCount = true) :
    ∀ i, i < entryCount → (nodes.get i).kind = 2 →
      2 ≤ (nodes.get i).v → (nodes.get i).v ≤ 2000000000000 →
      QuotientCCell.SourceExecution (nodes.get i).v (nodes.get i).value :=
  DecodedOutputs.finished_source_function gaps_checked checked

#print axioms all_meanings
#print axioms finished_pi
#print axioms finished_source_function
end RHOcticPush.HighDecodedOutputs
