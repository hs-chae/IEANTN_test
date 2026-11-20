/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteGuardedMillion

/-! Explicit source-linked RESULT, combining the independently checked actual
C/AST correspondences with the source-derived mathematical conclusion.
The pure mathematical bound need not mention C bytes. This bundle preserves
both kinds of evidence, using the SAME AST definitions as the execution proofs.
It does not assert physical process/caller association. -/
namespace RamanujanPV.FiniteGuardedResult
set_option autoImplicit false

structure SourceBindings : Prop where
  counter : LCMSourcePV.RestrictedC.SourceCorresponds QuotientCSource.render QuotientCSource.actualSource ()
  driver : LCMSourcePV.RestrictedC.SourceCorresponds QuotientDriverSource.render
    QuotientDriverSource.actualSource QuotientDriverSource.program
  segment : LCMSourcePV.RestrictedC.SourceCorresponds SegmentCheckerSource.render
    SegmentCheckerSource.actualSource SegmentCheckerSource.functions
  exponential : LCMSourcePV.RestrictedC.SourceCorresponds FiniteExpSource.render FiniteExpSource.actualSource ()
  logarithm : LCMSourcePV.RestrictedC.SourceCorresponds FiniteLogSource.render FiniteLogSource.actualSource ()
  cell : LCMSourcePV.RestrictedC.SourceCorresponds FiniteCellSource.render FiniteCellSource.actualSource ()

theorem actual_source_bindings : SourceBindings :=
  ⟨QuotientCSource.actual_source_checked,QuotientDriverSource.actual_source_checked,
    SegmentCheckerSource.actual_source_checked,FiniteExpSource.actual_source_checked,
    FiniteLogSource.actual_source_checked,FiniteCellSource.actual_source_checked⟩

/-- The completed selected source-first result, with all actual program bindings
and the every-real quantitative conclusion retained together. -/
theorem source_linked_uniform_gap : SourceBindings ∧
    ∀x : ℝ,(38358837683:ℝ)≤x→x<38359837684→(501901:ℝ)<gap x :=
  ⟨actual_source_bindings,fun _ lower upper=>FiniteGuardedMillion.uniform_gap lower upper⟩

theorem source_linked_real_interval : SourceBindings ∧
    ∀x : ℝ,(38358837683:ℝ)≤x→x<38359837684→Holds x :=
  ⟨actual_source_bindings,fun _ lower upper=>FiniteGuardedMillion.first_1000001_real_interval lower upper⟩

#print axioms actual_source_bindings
#print axioms source_linked_uniform_gap
#print axioms source_linked_real_interval
end RamanujanPV.FiniteGuardedResult
