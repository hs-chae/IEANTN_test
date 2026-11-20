/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.PrimeBaseCombinedMillion

/-! Package the existing execution proofs and exact byte correspondences with
the alternative numerical provider's real theorem. No physical caller, loader
or process/output association is asserted by this function-level result. -/
namespace RamanujanPV.PrimeBaseCombinedResult
set_option autoImplicit false

structure SourceBindings : Prop where
  counter : LCMSourcePV.RestrictedC.SourceCorresponds QuotientCSourceV2.render
    QuotientCSourceV2.actualSource ()
  driver : LCMSourcePV.RestrictedC.SourceCorresponds QuotientDriverSource.render
    QuotientDriverSource.actualSource QuotientDriverSource.program
  segment : LCMSourcePV.RestrictedC.SourceCorresponds SegmentCheckerSource.render
    SegmentCheckerSource.actualSource SegmentCheckerSource.functions
  exponential : LCMSourcePV.RestrictedC.SourceCorresponds FiniteExpSource.render
    FiniteExpSource.actualSource ()
  logarithm : LCMSourcePV.RestrictedC.SourceCorresponds FiniteLogSource.render
    FiniteLogSource.actualSource ()
  cell : LCMSourcePV.RestrictedC.SourceCorresponds FiniteCellSource.render
    FiniteCellSource.actualSource ()

theorem actual_source_bindings : SourceBindings :=
  ⟨QuotientCSourceV2.actual_source_checked, QuotientDriverSource.actual_source_checked,
    SegmentCheckerSource.actual_source_checked, FiniteExpSource.actual_source_checked,
    FiniteLogSource.actual_source_checked, FiniteCellSource.actual_source_checked⟩

theorem source_linked_uniform_gap : SourceBindings ∧
    ∀ x : ℝ, (38358837683 : ℝ) ≤ x → x < 38359837684 → (501901 : ℝ) < gap x :=
  ⟨actual_source_bindings, fun _ lower upper => PrimeBaseCombinedMillion.uniform_gap lower upper⟩

theorem source_linked_real_interval : SourceBindings ∧
    ∀ x : ℝ, (38358837683 : ℝ) ≤ x → x < 38359837684 → Holds x :=
  ⟨actual_source_bindings, fun _ lower upper => PrimeBaseCombinedMillion.first_1000001_real_interval lower upper⟩

#print axioms actual_source_bindings
#print axioms source_linked_uniform_gap
#print axioms source_linked_real_interval
end RamanujanPV.PrimeBaseCombinedResult
