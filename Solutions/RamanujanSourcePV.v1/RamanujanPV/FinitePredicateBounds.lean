/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! Width and floor applicability for the exact seven-word finite predicate.
These arithmetic lemmas are consumed by its actual C source execution proof;
they are not standalone source-first PV. -/
namespace RamanujanPV.FinitePredicateBounds
set_option autoImplicit false

theorem word_product {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) : a*b < 2^128 := by
  have h := Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega : 0 < (2^64 : Nat))
  norm_num at h ⊢
  exact h

theorem scaled_square {P : Nat} (hP : P ≤ 2000000000000) :
    2^20*P < 2^128 ∧ (2^20*P)*P < 2^128 := by
  have square := Nat.mul_le_mul hP hP
  norm_num at hP square ⊢
  constructor <;> nlinarith

theorem guarded_domains {n next j P Q Lu : Nat}
    (lower : 38358837683 ≤ n) (advance : n < next) (upper : next ≤ 2000000000001)
    (qDomain : j ≤ n) (qCount : Q ≤ j) (pCount : P ≤ next-1) (positive : 0 < Lu) :
    2 ≤ n ∧ n ≤ 2000000000000 ∧ 0 < next ∧ n ≤ next-1 ∧
      next-1 ≤ 2000000000000 ∧ P ≤ 2000000000000 ∧
      j ≤ 2000000000000 ∧ Q ≤ 2000000000000 ∧ 0 < Lu := by omega

/-- Every multiplication in the exact predicate, including both left-associated
scaled-square operations. A general uint64 P alone would not suffice for the
second multiplication; the actual source's P≤next−1 guard is essential. -/
theorem predicate_products {n next j P Q Lu A eLo eHi : Nat}
    (lower : 38358837683 ≤ n) (advance : n < next) (upper : next ≤ 2000000000001)
    (pCount : P ≤ next-1)
    (nWord : n < 2^64) (jWord : j < 2^64) (qWord : Q < 2^64)
    (luWord : Lu < 2^64) (aWord : A < 2^64)
    (loWord : eLo < 2^64) (hiWord : eHi < 2^64) :
    j*eHi < 2^128 ∧ n*(2^60) < 2^128 ∧ n*eLo < 2^128 ∧
    A*Q < 2^128 ∧ A*Lu < 2^128 ∧
    2^20*P < 2^128 ∧ (2^20*P)*P < 2^128 := by
  have hp : P ≤ 2000000000000 := by omega
  exact ⟨word_product jWord hiWord,word_product nWord (by norm_num),
    word_product nWord loWord,word_product aWord qWord,word_product aWord luWord,
    (scaled_square hp).1,(scaled_square hp).2⟩

theorem quotient_u128 {n eLo Lu : Nat} (nWord : n < 2^64) (loWord : eLo < 2^64) :
    (n*eLo)/Lu < 2^128 :=
  (Nat.div_le_self _ _).trans_lt (word_product nWord loWord)

theorem floor_relation {n eLo Lu A : Nat} (equal : A=(n*eLo)/Lu) :
    A*Lu ≤ n*eLo := by
  rw [equal]
  exact Nat.div_mul_le_self _ _

theorem strict_scaled_square {P A Q : Nat}
    (strict : (2^20*P)*P < A*Q) : 2^20*P^2 < A*Q := by
  simpa only [pow_two,Nat.mul_assoc] using strict

#print axioms word_product
#print axioms predicate_products
#print axioms floor_relation
end RamanujanPV.FinitePredicateBounds
