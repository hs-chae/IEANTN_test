import CounterSourceSyntax
import HighDriverContract

/-! Source-indexed consumption of independent grammar in the existing finite
counter model. This lifts the preserved AST execution relation through actual
source syntax; it does not assert full ISO-C operational adequacy or physical
compiler/stdio/hardware conformance. No output value is assumed here. -/
namespace RHOcticPush.CounterSyntax
open RamanujanPV RamanujanPV.QuotientCMachine
open RamanujanPV.QuotientDriverInit RamanujanPV.QuotientDriverExecution

structure SourceModelMain : Prop where
  application : HighDriverContract.SourceModelMain
  counterAccepted : checkedCounter QuotientCSourceV2.actualSource QuotientCSourceV2.functions = true
  mainAccepted : checkedDriver HighDriverSource.actualSource HighDriverSource.program = true

/-- The independently checked physical source text is an index of this lifted
model run. Both grammar derivations are required to construct a source run. -/
inductive SourceDriverRun (counterText mainText : String) (layout : Layout)
    (token : Nat) (world : World) (final : DriverState) : Prop where
  | execution : CounterProgram counterText QuotientCSourceV2.functions →
      DriverProgram mainText HighDriverSource.program →
      DriverRun token HighDriverSource.program.main.body (initialDriver layout token world)
        (.returned final (.core (.i32 0))) →
      SourceDriverRun counterText mainText layout token world final

theorem actual_source_model_main : SourceModelMain :=
  ⟨HighDriverContract.actual_source_model_main,actual_counter_accepted,actual_driver_accepted⟩

/-- The final source-aware model claim has an inhabited successful run with the
actual prime count. The generic grammar-soundness theorems occur in its proof. -/
theorem possible_source_success (layout : Layout) (stack : StackLayout layout)
    (token : Nat) (world : World) :
    ∃ final, SourceDriverRun QuotientCSourceV2.actualSource HighDriverSource.actualSource
      layout token world final ∧ final.world.buffered = [] ∧ final.world.committed =
        world.committed ++ world.buffered ++ wordBytes (Nat.primeCounting 1490000000000) := by
  have checked := actual_source_model_main
  obtain ⟨final,run,buffered,committed⟩ :=
    checked.application.possibleSuccess layout stack token world
  exact ⟨final,SourceDriverRun.execution (checkedCounter_sound checked.counterAccepted)
    (checkedDriver_sound checked.mainAccepted) run,buffered,committed⟩

/-- Every source-indexed successful run uses the exact same formal main and
counter AST as the original arithmetic correctness theorem. -/
theorem every_source_success (layout : Layout) (token : Nat) (world : World)
    {final : DriverState}
    (run : SourceDriverRun QuotientCSourceV2.actualSource HighDriverSource.actualSource
      layout token world final) :
    final.world.buffered = [] ∧ final.world.committed =
      world.committed ++ world.buffered ++ wordBytes (Nat.primeCounting 1490000000000) := by
  cases run with
  | execution _ _ run =>
    exact actual_source_model_main.application.everySuccessfulRun layout token world final run

theorem complete_canonical_source_run :
    ∃ final, SourceDriverRun QuotientCSourceV2.actualSource HighDriverSource.actualSource
      canonicalLayout 32000000 ⟨[],[]⟩ final ∧ final.world.buffered = [] ∧
      final.world.committed = wordBytes (Nat.primeCounting 1490000000000) := by
  simpa only [List.nil_append] using possible_source_success canonicalLayout
    HighDriverContract.canonicalStack 32000000 ⟨[],[]⟩

/-- The still-independent exact numerical count, once kernel proved, can be
plugged into this source-aware adapter. No count is invented or hardcoded as a
premise of generic source correspondence or program correctness. -/
theorem source_output_of_exact_count
    (count : Nat.primeCounting 1490000000000 = 55206486339)
    (layout : Layout) (token : Nat) (world : World) {final : DriverState}
    (run : SourceDriverRun QuotientCSourceV2.actualSource HighDriverSource.actualSource
      layout token world final) :
    final.world.buffered = [] ∧ final.world.committed =
      world.committed ++ world.buffered ++ wordBytes 55206486339 := by
  simpa only [count] using every_source_success layout token world run

#print axioms actual_source_model_main
#print axioms possible_source_success
#print axioms every_source_success
#print axioms complete_canonical_source_run
#print axioms source_output_of_exact_count
end RHOcticPush.CounterSyntax
