import HighDriverRuntime

/-! Source-linked high-input application contract. The formal source identity is
the existing restricted rendered-byte contract, not a new independent C parser.
Physical compiler/ABI/stdio/runtime/hardware conformance remains external. -/
namespace RHOcticPush.HighDriverContract
open RamanujanPV RamanujanPV.QuotientCMachine
open RamanujanPV.QuotientDriverInit RamanujanPV.QuotientDriverExecution

structure SourceModelMain : Prop where
  counterBytes : QuotientCSourceV2.render () = some QuotientCSourceV2.actualSource
  counterChecked : LCMSourcePV.RestrictedC.SourceCorresponds
    QuotientCSourceV2.render QuotientCSourceV2.actualSource ()
  mainBytes : QuotientDriverSource.render HighDriverSource.program =
    some HighDriverSource.actualSource
  mainChecked : LCMSourcePV.RestrictedC.SourceCorresponds
    QuotientDriverSource.render HighDriverSource.actualSource HighDriverSource.program
  prototype : HighDriverSource.program.prototype.returnType =
      QuotientCSourceV2.countFunction.returnType ∧
    HighDriverSource.program.prototype.name = QuotientCSourceV2.countFunction.name ∧
    HighDriverSource.program.prototype.parameters = QuotientCSourceV2.countFunction.parameters
  initialization : ∀ layout : Layout,
    StaticInit HighDriverSource.program.globals [layout.smallBase, layout.largeBase]
      emptyHeap (initializedHeap layout)
  possibleSuccess : ∀ (layout : Layout) (stack : StackLayout layout)
      (token : Nat) (world : World),
    ∃ final, DriverRun token HighDriverSource.program.main.body
        (initialDriver layout token world) (.returned final (.core (.i32 0))) ∧
      final.world.buffered = [] ∧ final.world.committed =
        world.committed ++ world.buffered ++ wordBytes (Nat.primeCounting 1490000000000)
  everySuccessfulRun : ∀ (layout : Layout) (token : Nat) (world : World)
      (final : DriverState),
    DriverRun token HighDriverSource.program.main.body (initialDriver layout token world)
      (.returned final (.core (.i32 0))) →
    final.world.buffered = [] ∧ final.world.committed =
      world.committed ++ world.buffered ++ wordBytes (Nat.primeCounting 1490000000000)

/-- All application proof components are supplied, including the source-bound
globals and actual successful/failure branch semantics. No desired count or
successful external-I/O fact is a premise. -/
theorem actual_source_model_main : SourceModelMain :=
  ⟨QuotientCSourceV2.actual_source_bytes, QuotientCSourceV2.actual_source_checked,
    HighDriverSource.actual_source_bytes, HighDriverSource.actual_source_checked,
    HighDriverSource.same_actual_counter_prototype,
    HighDriverRuntime.source_static_initialization,
    HighDriverRuntime.possible_success_source_run,
    fun layout token world final run =>
      HighDriverRuntime.successful_main_output layout token world run⟩

/-- A valid application local-object placement is explicitly constructed;
logical execution is not hidden behind an empty layout hypothesis. -/
def canonicalStack : StackLayout canonicalLayout where
  resultAddress := 24000008
  aligned := by norm_num
  bounded := by norm_num [modulus]
  apartSmall := Or.inr (by norm_num [canonicalLayout, QuotientDriverSource.capacity])
  apartLarge := Or.inr (by norm_num [canonicalLayout, QuotientDriverSource.capacity])

/-- An inhabited full model run, not an assertion about a physical fflush. -/
theorem complete_canonical_model_run :
    ∃ final, DriverRun 32000000 HighDriverSource.program.main.body
        (initialDriver canonicalLayout 32000000 ⟨[], []⟩)
        (.returned final (.core (.i32 0))) ∧
      final.world.buffered = [] ∧
        final.world.committed = wordBytes (Nat.primeCounting 1490000000000) := by
  simpa only [List.nil_append] using
    actual_source_model_main.possibleSuccess canonicalLayout canonicalStack 32000000 ⟨[], []⟩

/-- The exact still-pending numerical count is the sole mathematical parameter
of the fixed output adapter. The live complete certificate will discharge it. -/
theorem output_of_exact_count
    (count : Nat.primeCounting 1490000000000 = 55206486339)
    (layout : Layout) (token : Nat) (world : World) {final : DriverState}
    (run : DriverRun token HighDriverSource.program.main.body
      (initialDriver layout token world) (.returned final (.core (.i32 0)))) :
    final.world.buffered = [] ∧ final.world.committed =
      world.committed ++ world.buffered ++ wordBytes 55206486339 := by
  have h := actual_source_model_main.everySuccessfulRun layout token world final run
  simpa only [count] using h

#print axioms actual_source_model_main
#print axioms complete_canonical_model_run
#print axioms output_of_exact_count
end RHOcticPush.HighDriverContract
