/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteCellWords
import RamanujanPV.FiniteCellTrace
import RamanujanPV.FinitePredicateBounds

/-! Logical transport from actual typed C observations to mathematical guards.
The full positive-run inverse is a separate theorem, not asserted by these rules. -/
namespace RamanujanPV.FiniteCellSound
open FiniteScalarMachine FiniteCellWords FiniteCellTrace
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

theorem false_test {p : Prototypes} {c : Service} {e : LCMSourcePV.Witness.C.Expr}
    {s t : State} {P : Prop} [Decidable P]
    (known : Eval p c e s s (WideScalar.boolean (decide P)))
    (actual : FalseCondition p c e s t) : t=s ∧ ¬P := by
  obtain ⟨value,evaluated,stop⟩ := actual
  have same : (t,value)=(s,WideScalar.boolean (decide P)) :=
    Option.some.inj (evaluated.symm.trans known)
  obtain ⟨state,valueEq⟩ := Prod.mk.inj same
  rw [valueEq,truth_boolean] at stop
  exact ⟨state,of_decide_eq_false stop⟩

theorem true_return {p : Prototypes} {c : Service} {e : LCMSourcePV.Witness.C.Expr}
    {s t : State} {P : Prop} [Decidable P]
    (known : Eval p c e s s (WideScalar.boolean (decide P)))
    (actual : Eval p c e s t (i32 1)) : t=s ∧ P := by
  have same : (t,i32 1)=(s,WideScalar.boolean (decide P)) :=
    Option.some.inj (actual.symm.trans known)
  obtain ⟨state,valueEq⟩ := Prod.mk.inj same
  have accepted := (boolean_eq_one (decide P)).mp valueEq.symm
  exact ⟨state,of_decide_eq_true accepted⟩

structure NumericPost (r : RawFactoredCell) : Prop where
  step : r.n < r.next
  divisor : 0 < r.Lu
  index : r.j*WindowCells.eHi ≤ r.n*2^60
  factor : r.A=(r.n*WindowCells.eLo)/r.Lu
  strict : 2^20*r.P^2 < r.A*r.Q

/-- Once extracted from source guards, these exact integers imply the unchanged
mathematical predicate; no prime-count or desired-real-positivity premise occurs. -/
theorem numeric_post_fixed {r : RawFactoredCell} (h : NumericPost r) :
    (r.toCell WindowCells.eLo WindowCells.eHi).FixedPredicate :=
  r.toCell_fixedPredicate WindowCells.eLo WindowCells.eHi h.step h.divisor h.index
    (FinitePredicateBounds.floor_relation h.factor) h.strict

#print axioms false_test
#print axioms true_return
#print axioms numeric_post_fixed
end RamanujanPV.FiniteCellSound
