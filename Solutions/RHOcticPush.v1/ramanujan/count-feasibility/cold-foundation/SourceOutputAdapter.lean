import CounterGrammarConsumer

/-! Connect an independently supplied exact mathematical count to the inhabited
run of both actual source texts. The exact count remains an explicit proof
parameter here; the final closed consumer will supply the completed numerical
Final theorem. This is no claim of physical compiler or ISO-C model adequacy. -/
namespace RHOcticPush.SourceOutputAdapter
open RamanujanPV RamanujanPV.QuotientCMachine
open RamanujanPV.QuotientDriverInit RamanujanPV.QuotientDriverExecution

theorem canonical_source_output
    (count : Nat.primeCounting 1490000000000 = 55206486339) :
    ∃ final, CounterSyntax.SourceDriverRun QuotientCSourceV2.actualSource
      HighDriverSource.actualSource canonicalLayout 32000000 ⟨[], []⟩ final ∧
      final.world.buffered = [] ∧ final.world.committed = wordBytes 55206486339 :=
  CounterSyntax.complete_canonical_source_run.elim fun final facts =>
    ⟨final, facts.1, facts.2.1, facts.2.2.trans (congrArg wordBytes count)⟩

theorem every_source_output
    (count : Nat.primeCounting 1490000000000 = 55206486339)
    (layout : Layout) (token : Nat) (world : World) {final : DriverState}
    (run : CounterSyntax.SourceDriverRun QuotientCSourceV2.actualSource
      HighDriverSource.actualSource layout token world final) :
    final.world.buffered = [] ∧ final.world.committed =
      world.committed ++ world.buffered ++ wordBytes 55206486339 :=
  CounterSyntax.source_output_of_exact_count count layout token world run

#print axioms canonical_source_output
#print axioms every_source_output
end RHOcticPush.SourceOutputAdapter
