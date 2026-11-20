/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveKernel
import Mathlib.Algebra.Ring.GeomSum

/-! Exact finite geometric bit masks. This is kernel mathematics, not a
source-program execution claim. No primality or prime-count output is assumed. -/
namespace RamanujanPV.PackedSieveGeometric
open Finset PackedSieveKernel
set_option autoImplicit false
set_option maxHeartbeats 0

theorem geometric_sum (p m : Nat) (hp : 0 < p) :
    (2 ^ (m * p) - 1) / (2 ^ p - 1) =
      ∑ k ∈ range m, 2 ^ (k * p) := by
  have hbase : 2 ≤ 2 ^ p := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hp
  simpa [pow_mul, Nat.mul_comm] using (Nat.geomSum_eq hbase m).symm

theorem sum_lt_two_pow (p m : Nat) (hp : 0 < p) :
    (∑ k ∈ range m, 2 ^ (k * p)) < 2 ^ (m * p) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    calc
      (∑ k ∈ range m, 2 ^ (k * p)) + 2 ^ (m * p) <
          2 ^ (m * p) + 2 ^ (m * p) := Nat.add_lt_add_right ih _
      _ = 2 ^ (m * p + 1) := by simp [pow_succ]; omega
      _ ≤ 2 ^ ((m + 1) * p) :=
        Nat.pow_le_pow_right (by decide) (by simp only [Nat.add_mul, Nat.one_mul]; omega)

theorem testBit_sum (p m i : Nat) (hp : 0 < p) :
    (∑ k ∈ range m, 2 ^ (k * p)).testBit i = true ↔
      ∃ k < m, i = k * p := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hsmall := sum_lt_two_pow p m hp
    by_cases hilow : i < m * p
    · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hilow, ih]
      constructor
      · rintro ⟨k, hk, hi⟩
        exact ⟨k, by omega, hi⟩
      · rintro ⟨k, hk, hi⟩
        refine ⟨k, ?_, hi⟩
        by_contra hkm
        have : k = m := by omega
        subst k
        omega
    · by_cases hieq : i = m * p
      · subst i
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq,
          Nat.testBit_lt_two_pow hsmall]
        simp only [Bool.not_false, true_iff]
        exact ⟨m, by omega, rfl⟩
      · have hhigh : m * p + 1 ≤ i := by omega
        have hsum : (∑ k ∈ range m, 2 ^ (k * p)) + 2 ^ (m * p) < 2 ^ i := by
          calc
            _ < 2 ^ (m * p) + 2 ^ (m * p) := Nat.add_lt_add_right hsmall _
            _ = 2 ^ (m * p + 1) := by simp [pow_succ]; omega
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hhigh
        rw [Nat.testBit_lt_two_pow hsum]
        simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
        intro k hk hi
        have : k * p ≤ m * p := Nat.mul_le_mul_right p (by omega)
        omega

theorem geomMask_eq_sum (p m : Nat) (hp : 0 < p) :
    geomMask p m = ∑ k ∈ range m, 2 ^ (k * p) := by
  simpa [geomMask] using geometric_sum p m hp

theorem testBit_geomMask (p m i : Nat) (hp : 0 < p) :
    (geomMask p m).testBit i = true ↔ ∃ k < m, i = k * p := by
  rw [geomMask_eq_sum p m hp]
  exact testBit_sum p m i hp

#print axioms geometric_sum
#print axioms sum_lt_two_pow
#print axioms testBit_sum
#print axioms geomMask_eq_sum
#print axioms testBit_geomMask
end RamanujanPV.PackedSieveGeometric
