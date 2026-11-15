/-
Arithmetic section adapted from Mathlib/NumberTheory/Chebyshev.lean.
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under the Apache 2.0 license.
Authors of upstream file: Alastair Irving, Terry Tao, Ruben Van de Velde.
The remaining transport proof was written for this session.
-/
import Mathlib
namespace ExposureTask
open Real
noncomputable section
noncomputable def Epsi (x : ℝ) : ℝ := |Chebyshev.psi x-x|/x
noncomputable def Etheta (x : ℝ) : ℝ := |Chebyshev.theta x-x|/x
def C : ℝ := 9354674/1000000000

namespace Arithmetic
open Nat hiding log
open Finset Real Chebyshev
open ArithmeticFunction hiding log id
open scoped Nat.Prime Chebyshev

/-- A sum over prime powers may be written as a double sum over exponents and then primes. -/
theorem sum_PrimePow_eq_sum_sum' {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ} (hx : 0 ≤ x)
  {N : ℕ} (hN : ⌊log x / log 2⌋₊ ≤ N) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n
      = ∑ k ∈ Icc 1 N, ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, f (p ^ k) := by
  trans ∑ ⟨k, p⟩ ∈ Icc 1 N ×ˢ (Ioc 0 ⌊x⌋₊).filter Nat.Prime
    with p ≤ ⌊x ^ (k : ℝ)⁻¹⌋₊, f (p ^ k)
  · refine (sum_bij (i := fun ⟨k, p⟩ _ ↦ p ^ k) ?_ ?_ ?_ ?_).symm
    · simp +contextual [hx, rpow_nonneg, le_floor_iff, ← pos_iff_ne_zero, Prime.isPrimePow,
        one_le_iff_ne_zero, le_rpow_inv_iff_of_pos, isPrimePow_pow_iff, prime_iff]
    · simp +contextual only [hx, rpow_nonneg, le_floor_iff, mem_filter, mem_product, mem_Icc,
        one_le_iff_ne_zero, pos_iff_ne_zero, mem_Ioc, and_imp, Prod.forall, Prod.mk.injEq]
      intro k₁ p₁ hk₁ _ _ _ hp₁ _ k₂ p₂ hk₂ _ _ _ hp₂ _ H
      exact (hp₁.pow_inj' hp₂ hk₁ hk₂ H).symm
    · simp +contextual only [mem_filter, mem_Ioc, hx, le_floor_iff, and_assoc, rpow_nonneg,
        mem_product, mem_Icc, succ_le_iff, exists_prop, Prod.exists, exists_and_left, and_imp]
      rintro b _ hbx ⟨p, k, hp, hk₀, rfl⟩
      rw [cast_pow] at hbx
      refine ⟨k, hk₀, (le_floor ?_).trans hN, p, hp.nat_prime.pos, ?_, hp.nat_prime, ?_, rfl⟩
      · rw [le_div_iff₀ (log_pos (by norm_num)), ← Real.log_pow]
        gcongr
        apply (LE.le.trans ?_ hbx)
        exact pow_le_pow_left₀ (by norm_num) (mod_cast hp.nat_prime.two_le) _
      · exact (le_self_pow₀ (mod_cast hp.nat_prime.one_le) hk₀.ne').trans hbx
      · simp_all [le_rpow_inv_iff_of_pos]
    · simp
  · rw [sum_filter, sum_product]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [sum_ite, not_le, sum_const_zero, add_zero]
    congr 1
    ext p
    simp only [mem_filter, mem_Ioc]
    refine ⟨fun _ ↦ (by simp_all), fun h ↦ ?_⟩
    simp_all only [mem_Icc, one_div, true_and, and_true]
    grw [h.1.2, floor_le_floor]
    apply rpow_le_self_of_one_le _ (by bound)
    have := one_le_floor_iff _ |>.mp <| le_trans (one_le_cast.mp h.2.one_le) h.1.2
    contrapose! this
    apply rpow_lt_one hx this (by bound)

theorem sum_PrimePow_eq_sum_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n
      = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, f (p ^ k) :=
  sum_PrimePow_eq_sum_sum' f hx (le_refl _)

theorem psi_eq_sum_theta' {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : ⌊log x / log 2⌋₊ ≤ N) :
    ψ x = ∑ n ∈ Icc 1 N, θ (x ^ ((1 : ℝ) / n)) := by
  simp_rw [psi, vonMangoldt_apply, ← sum_filter, sum_PrimePow_eq_sum_sum' _ hx hN]
  apply sum_congr rfl fun _ hk ↦ sum_congr rfl fun _ _ ↦ ?_
  rw [Prime.pow_minFac _ (by linarith [mem_Icc.mp hk])]
  simp_all

theorem psi_eq_sum_theta {x : ℝ} (hx : 0 ≤ x) :
    ψ x = ∑ n ∈ Icc 1 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) :=
  psi_eq_sum_theta' hx (le_refl _)

theorem psi_eq_theta_add_sum_theta' {x : ℝ} (hx : 2 ≤ x) {N : ℕ} (hN : ⌊log x / log 2⌋₊ ≤ N) :
    ψ x = θ x + ∑ n ∈ Icc 2 N, θ (x ^ ((1 : ℝ) / n)) := by
  rw [psi_eq_sum_theta' (by linarith) hN, ← add_sum_Ioc_eq_sum_Icc]
  · congr
    simp
  · apply le_trans _ hN
    rw [le_floor_iff' one_ne_zero, le_div_iff₀ (by positivity), cast_one, one_mul]
    gcongr

theorem psi_eq_theta_add_sum_theta {x : ℝ} (hx : 2 ≤ x) :
    ψ x = θ x + ∑ n ∈ Icc 2 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) :=
  psi_eq_theta_add_sum_theta' hx (le_refl _)

/-- Chebyshev's upper bound: `θ x ≤ c x` with the constant `c = log 4`. -/
theorem theta_le_log4_mul_x {x : ℝ} (hx : 0 ≤ x) : θ x ≤ log 4 * x := by
  rw [theta_eq_log_primorial]
  trans log (4 ^ ⌊x⌋₊)
  · gcongr <;> norm_cast
    exacts [primorial_pos _, primorial_le_four_pow _]
  rw [Real.log_pow, mul_comm]
  gcongr
  exact floor_le hx


/-- `|ψ x - θ x| ≤ c √ x log x` with an explicit constant c.  To remove the log, see
`psi_sub_theta_le_mul_sqrt`. -/
theorem abs_remainder {x : ℝ} (hx : 1 ≤ x) :
    |ψ x - θ x| ≤ 2 * x.sqrt * x.log := by
  by_cases! hx : x < 2
  · rw [psi_eq_zero_of_lt_two hx, theta_eq_zero_of_lt_two hx, sub_zero, abs_zero]
    bound
  rw [psi_eq_theta_add_sum_theta hx, add_sub_cancel_left]
  apply le_trans <| abs_sum_le_sum_abs ..
  simp_rw [abs_of_nonneg <| theta_nonneg _]
  trans ∑ i ∈ Icc 2 ⌊log x / log 2⌋₊, log 4 * x.sqrt
  · gcongr with i hi
    apply le_trans (theta_le_log4_mul_x (rpow_nonneg (by linarith) _))
    rw [sqrt_eq_rpow]
    gcongr; simp_all
  simp only [sum_const, card_Icc, reduceSubDiff, nsmul_eq_mul]
  calc
  _ ≤ (log x / log 2) * (log 4 * √x) := by
    gcongr
    rw [cast_sub]
    · trans ↑⌊log x / log 2⌋₊
      · linarith
      · exact floor_le (by bound)
    apply le_floor
    norm_cast
    apply one_le_div _ |>.mpr <;> bound
  _ = (log 4 / log 2) * x.sqrt * x.log := by field
  _ = _ := by
    congr
    rw [(by norm_num : (4 : ℝ) = 2 ^ 2), Real.log_pow]
    field


theorem remainder_exact {x : ℝ} (hx : 2 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x =
      ∑ k ∈ Icc 2 ⌊log x / log 2⌋₊, Chebyshev.theta (x ^ ((1 : ℝ) / k)) := by
  rw [psi_eq_theta_add_sum_theta hx, add_sub_cancel_left]

theorem remainder_nonneg (x : ℝ) : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
  exact sub_nonneg.mpr (Chebyshev.theta_le_psi x)

end Arithmetic

 theorem preliminary {x : ℝ} (hx : 1 ≤ x) :
    |Chebyshev.psi x - Chebyshev.theta x| ≤ 16 * x ^ (5/8 : ℝ) := by
  have hp : 0 < x := by linarith
  calc
    _ ≤ 2 * x.sqrt * x.log := Arithmetic.abs_remainder hx
    _ ≤ 2 * x.sqrt * (x ^ (1/8 : ℝ) / (1/8 : ℝ)) := by
      gcongr
      exact Real.log_le_rpow_div hp.le (by norm_num : (0 : ℝ) < 1/8)
    _ = 16 * x ^ (5/8 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hp (1/2 : ℝ) (1/8 : ℝ)
      norm_num at h
      rw [show (5/8 : ℝ) = 1/2 + 1/8 by norm_num, Real.rpow_add hp]
      ring

 theorem exp75_lower : (2 : ℝ)^75 ≤ Real.exp 75 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1
    norm_num at this ⊢
    exact this
  calc
    (2 : ℝ)^75 ≤ (Real.exp 1)^75 := by gcongr
    _ = Real.exp 75 := by rw [← Real.exp_nat_mul]; norm_num

 theorem quarter_lower {x : ℝ} (hx : Real.exp 300 ≤ x) :
    Real.exp 75 ≤ x ^ (1/4 : ℝ) := by
  calc
    Real.exp 75 = (Real.exp 300) ^ (1/4 : ℝ) := by rw [← Real.exp_mul]; norm_num
    _ ≤ x ^ (1/4 : ℝ) := Real.rpow_le_rpow (by positivity) hx (by norm_num)

 theorem normalized_remainder {x : ℝ} (hx : Real.exp 300 ≤ x) :
    |Chebyshev.psi x - Chebyshev.theta x| / x ≤
      (16 / Real.exp 75) * x ^ (-1/8 : ℝ) := by
  have hp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h1 : 1 ≤ x := le_trans (by linarith [Real.add_one_le_exp (300 : ℝ)]) hx
  have hq := quarter_lower hx
  have heq : x ^ (5/8 : ℝ) * x ^ (1/4 : ℝ) = x * x ^ (-1/8 : ℝ) := by
    calc
      _ = x ^ (7/8 : ℝ) := by rw [← Real.rpow_add hp]; norm_num
      _ = x ^ (1 : ℝ) * x ^ (-1/8 : ℝ) := by rw [← Real.rpow_add hp]; norm_num
      _ = _ := by rw [Real.rpow_one]
  apply (div_le_iff₀ hp).mpr
  have hbound := preliminary h1
  have hpos : (0 : ℝ) < Real.exp 75 := by positivity
  have hmul : Real.exp 75 * |Chebyshev.psi x - Chebyshev.theta x| ≤
      16 * (x * x ^ (-1/8 : ℝ)) := by
    calc
      _ ≤ Real.exp 75 * (16 * x ^ (5/8 : ℝ)) := by gcongr
      _ ≤ x ^ (1/4 : ℝ) * (16 * x ^ (5/8 : ℝ)) := by gcongr
      _ = _ := by rw [← heq]; ring
  have hh : |Chebyshev.psi x - Chebyshev.theta x| ≤
      (16 * (x * x ^ (-1/8 : ℝ))) / Real.exp 75 := by
    apply (le_div_iff₀ hpos).mpr
    simpa only [mul_comm] using hmul
  calc
    _ ≤ (16 * (x * x ^ (-1/8 : ℝ))) / Real.exp 75 := hh
    _ = _ := by ring

 theorem theta_transport
    (H : ∀ t : ℝ, Real.exp 300 ≤ t → Epsi t ≤ C * t ^ (-1/8 : ℝ))
    {x : ℝ} (hx : Real.exp 300 ≤ x) :
    Etheta x ≤ (C + 16 / Real.exp 75) * x ^ (-1/8 : ℝ) := by
  have hp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have htri : |Chebyshev.theta x - x| ≤
      |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
    calc
      _ = |(Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  calc
    Etheta x ≤ Epsi x + |Chebyshev.psi x - Chebyshev.theta x| / x := by
      unfold Etheta Epsi
      rw [← add_div]
      exact div_le_div_of_nonneg_right htri hp.le
    _ ≤ C * x ^ (-1/8 : ℝ) + (16 / Real.exp 75) * x ^ (-1/8 : ℝ) :=
      add_le_add (H x hx) (normalized_remainder hx)
    _ = _ := by ring

 theorem theta_two_term
    (H : ∀ t : ℝ, Real.exp 300 ≤ t → Epsi t ≤ C * t ^ (-1/8 : ℝ))
    {x : ℝ} (hx : Real.exp 300 ≤ x) :
    Etheta x ≤ C * x ^ (-1/8 : ℝ) + (2 * x.sqrt * x.log) / x := by
  have hp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h1 : 1 ≤ x := by linarith [Real.add_one_le_exp (300 : ℝ)]
  have htri : |Chebyshev.theta x - x| ≤
      |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
    calc
      _ = |(Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  calc
    Etheta x ≤ Epsi x + |Chebyshev.psi x - Chebyshev.theta x| / x := by
      unfold Etheta Epsi
      rw [← add_div]
      exact div_le_div_of_nonneg_right htri hp.le
    _ ≤ _ := add_le_add (H x hx)
      (div_le_div_of_nonneg_right (Arithmetic.abs_remainder h1) hp.le)

 theorem theta_target
    (H : ∀ t : ℝ, Real.exp 300 ≤ t → Epsi t ≤ C * t ^ (-1/8 : ℝ))
    {x : ℝ} (hx : Real.exp 300 ≤ x) :
    Etheta x ≤ (C + 1/1000000000) * x ^ (-1/8 : ℝ) := by
  apply (theta_transport H hx).trans
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_trans (Real.exp_pos _).le hx) _)
  apply add_le_add_right
  calc
    16 / Real.exp 75 ≤ 16 / (2 : ℝ)^75 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) exp75_lower
    _ ≤ 1/1000000000 := by norm_num
end
end ExposureTask


#print axioms ExposureTask.Arithmetic.sum_PrimePow_eq_sum_sum'
#print axioms ExposureTask.Arithmetic.remainder_exact
#print axioms ExposureTask.Arithmetic.abs_remainder
#print axioms ExposureTask.theta_transport
#print axioms ExposureTask.theta_two_term
#print axioms ExposureTask.theta_target
