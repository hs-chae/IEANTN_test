/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import Lean.Data.RArray

/-! Representation-only certificate tabulation. The original RArray/record
checker and mathematical soundness are unchanged. Global pivots retain the
original absolute index; padding outside the represented interval is unused. -/
namespace RamanujanPV.PackedCertificateArray
set_option autoImplicit false

def tabulate {α : Type} (reader : Nat → α) : Nat → Nat → Lean.RArray α
  | 0, lo => .leaf (reader lo)
  | depth+1, lo =>
    let mid := lo+2^depth
    .branch mid (tabulate reader depth lo) (tabulate reader depth mid)

theorem getImpl_tabulate {α : Type} (reader : Nat → α) (depth lo i : Nat)
    (lower : lo ≤ i) (upper : i < lo+2^depth) :
    (tabulate reader depth lo).getImpl i=reader i := by
  induction depth generalizing lo with
  | zero =>
    have same : i=lo := by simp only [Nat.pow_zero] at upper;omega
    subst i
    rfl
  | succ depth ih =>
    simp only [tabulate,Lean.RArray.getImpl]
    split
    · exact ih lo lower (by assumption)
    · apply ih (lo+2^depth) (by omega)
      simpa only [Nat.pow_succ,Nat.mul_two,Nat.add_assoc] using upper

theorem get_tabulate {α : Type} (reader : Nat → α) (depth lo i : Nat)
    (lower : lo ≤ i) (upper : i < lo+2^depth) :
    (tabulate reader depth lo).get i=reader i := by
  rw [Lean.RArray.get_eq_getImpl]
  exact getImpl_tabulate reader depth lo i lower upper

theorem size_tabulate {α : Type} (reader : Nat → α) (depth lo : Nat) :
    (tabulate reader depth lo).size=2^depth := by
  induction depth generalizing lo with
  | zero => rfl
  | succ depth ih => simp only [tabulate,Lean.RArray.size,ih,Nat.pow_succ,Nat.mul_two]

#print axioms get_tabulate
#print axioms size_tabulate
end RamanujanPV.PackedCertificateArray
