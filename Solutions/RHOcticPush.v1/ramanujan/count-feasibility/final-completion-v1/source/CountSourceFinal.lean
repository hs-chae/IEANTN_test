import RamanujanPV.HighTransitionCount.Final
import SourceOutputAdapter
import HighDecodedOutputs

/-! Closed only after exhaustive numerical checking, fresh compilation of the
legacy complement and a fresh unchanged Final. Both actual C source grammars
are consumed through construction of an inhabited source-indexed model run.
Compiler/runtime/ABI/stdio/hardware and C-model interpretation remain external.
-/
namespace RHOcticPush.ColdCount
open RamanujanPV RamanujanPV.QuotientCMachine
open RamanujanPV.QuotientDriverInit RamanujanPV.QuotientDriverExecution
open RamanujanPV.QuotientDemandCheck RamanujanPV.HighTransitionCount

theorem count : Nat.primeCounting 1490000000000 = 55206486339 :=
  RamanujanPV.HighTransitionCount.pi_1490000000000

theorem complete_actual_source_run :
    ∃ final, CounterSyntax.SourceDriverRun QuotientCSourceV2.actualSource
      HighDriverSource.actualSource canonicalLayout 32000000 ⟨[], []⟩ final ∧
      final.world.buffered = [] ∧ final.world.committed = wordBytes 55206486339 :=
  SourceOutputAdapter.canonical_source_output count

theorem every_actual_source_output (layout : Layout) (token : Nat) (world : World)
    {final : DriverState}
    (run : CounterSyntax.SourceDriverRun QuotientCSourceV2.actualSource
      HighDriverSource.actualSource layout token world final) :
    final.world.buffered = [] ∧ final.world.committed =
      world.committed ++ world.buffered ++ wordBytes 55206486339 :=
  SourceOutputAdapter.every_source_output count layout token world run

theorem all_finished_pi :
    ∀ i, i < entryCount → (nodes.get i).kind = 2 →
      Nat.primeCounting (nodes.get i).v = (nodes.get i).value :=
  HighDecodedOutputs.finished_pi entries_checked

theorem all_finished_source_function :
    ∀ i, i < entryCount → (nodes.get i).kind = 2 →
      2 ≤ (nodes.get i).v → (nodes.get i).v ≤ 2000000000000 →
      QuotientCCell.SourceExecution (nodes.get i).v (nodes.get i).value :=
  HighDecodedOutputs.finished_source_function entries_checked

#print axioms count
#print axioms complete_actual_source_run
#print axioms every_actual_source_output
#print axioms all_finished_pi
#print axioms all_finished_source_function
end RHOcticPush.ColdCount
