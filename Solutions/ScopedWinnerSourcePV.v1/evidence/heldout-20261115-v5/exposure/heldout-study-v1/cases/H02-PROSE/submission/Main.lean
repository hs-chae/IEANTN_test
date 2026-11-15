/-
Portions of ArithmeticBridge reproduced from Mathlib/NumberTheory/Chebyshev.lean.
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Terry Tao, Ruben Van de Velde.
The remaining transport and absorption proof is part of this submission.
-/
import Mathlib
noncomputable section
namespace ExposureTask
open Real
noncomputable def Epsi (x : ℝ) : ℝ := |Chebyshev.psi x-x|/x
noncomputable def Etheta (x : ℝ) : ℝ := |Chebyshev.theta x-x|/x
def C : ℝ := 9354674/1000000000

namespace ArithmeticBridge
open Nat hiding log
open Finset Real Chebyshev
open ArithmeticFunction hiding log id
open scoped Nat.Prime Chebyshev

-- Proofs reproduced from Mathlib/NumberTheory/Chebyshev.lean (see provenance).
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

theorem abs_psi_sub_theta_le_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
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


end ArithmeticBridge

-- The finite prime-power identity is a proved Mathlib theorem, not an input.
theorem exact_prime_powers {x : ℝ} (hx : 2 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x =
      ∑ n ∈ Finset.Icc 2 ⌊log x / log 2⌋₊,
        Chebyshev.theta (x ^ ((1 : ℝ) / n)) := by
  linarith [ArithmeticBridge.psi_eq_theta_add_sum_theta hx]

theorem remainder_bound {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ Chebyshev.psi x - Chebyshev.theta x ∧
    Chebyshev.psi x - Chebyshev.theta x ≤ 16 * x ^ (5 / 8 : ℝ) := by
  have hx0 : 0 < x := by linarith
  constructor
  · exact sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  calc
    _ ≤ |Chebyshev.psi x - Chebyshev.theta x| := le_abs_self _
    _ ≤ 2 * √x * log x := ArithmeticBridge.abs_psi_sub_theta_le_sqrt_mul_log hx
    _ ≤ 2 * √x * (x ^ (1 / 8 : ℝ) / (1 / 8 : ℝ)) := by
      gcongr
      exact log_le_rpow_div hx0.le (by norm_num)
    _ = 16 * x ^ (5 / 8 : ℝ) := by
      rw [sqrt_eq_rpow]
      have h := rpow_add hx0 (1 / 2 : ℝ) (1 / 8 : ℝ)
      norm_num at h
      nlinarith [h]

-- An entirely rational certificate for the large exponential threshold.
theorem exp75_large : (160000000000000 : ℝ) ≤ exp 75 := by
  have h : (4 : ℝ) ≤ exp 3 := by linarith [add_one_le_exp (3 : ℝ)]
  have hp : (4 : ℝ)^25 ≤ (exp 3)^25 := by gcongr
  have he : exp (75 : ℝ) = (exp 3)^25 := by
    convert exp_nat_mul (3 : ℝ) 25 using 1
    norm_num
  rw [he]
  norm_num at hp ⊢
  linarith

theorem quarter_large {x : ℝ} (hx : exp 300 ≤ x) :
    (160000000000000 : ℝ) ≤ x ^ (1 / 4 : ℝ) := by
  calc
    _ ≤ exp 75 := exp75_large
    _ = (exp 300) ^ (1 / 4 : ℝ) := by
      rw [← exp_mul]; norm_num
    _ ≤ x ^ (1 / 4 : ℝ) := rpow_le_rpow (exp_pos _).le hx (by norm_num)

-- No psi hypothesis is used at any of the smaller prime-power arguments.
theorem absorbed_remainder {x : ℝ} (hx : exp 300 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      (1 / 10000000000000 : ℝ) * x ^ (7 / 8 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos _) hx
  have hx1 : 1 ≤ x := by
    have : 1 ≤ exp (300 : ℝ) := one_le_exp (by norm_num)
    exact this.trans hx
  have hq := quarter_large hx
  have hm := mul_le_mul_of_nonneg_left hq (rpow_nonneg hx0.le (5 / 8 : ℝ))
  have he := rpow_add hx0 (5 / 8 : ℝ) (1 / 4 : ℝ)
  norm_num at he
  calc
    _ ≤ 16 * x ^ (5 / 8 : ℝ) := (remainder_bound hx1).2
    _ ≤ (1 / 10000000000000 : ℝ) * x ^ (7 / 8 : ℝ) := by
      rw [he]
      nlinarith [hm]

theorem theta_transport
    (psiInput : ∀ t : ℝ, exp 300 ≤ t → Epsi t ≤ C * t ^ (-1 / 8 : ℝ))
    {x : ℝ} (hx : exp 300 ≤ x) :
    Etheta x ≤ (C + 1 / 10000000000000) * x ^ (-1 / 8 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos _) hx
  have hpsi := (div_le_iff₀ hx0).mp (psiInput x hx)
  have hr := absorbed_remainder hx
  have hnon : 0 ≤ Chebyshev.psi x - Chebyshev.theta x :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  have ht : |Chebyshev.theta x - x| ≤
      |Chebyshev.psi x - x| + (Chebyshev.psi x - Chebyshev.theta x) := by
    calc
      _ = |(Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x)| := by congr 1; ring
      _ ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg hnon]
  have he : x ^ (7 / 8 : ℝ) = x ^ (-1 / 8 : ℝ) * x := by
    have h := rpow_add hx0 (-1 / 8 : ℝ) 1
    norm_num at h
    convert h using 1
    norm_num
  unfold Etheta
  apply (div_le_iff₀ hx0).mpr
  change |Chebyshev.psi x - x| ≤ C * x ^ (-1 / 8 : ℝ) * x at hpsi
  rw [he] at hr
  nlinarith

theorem requested_bound
    (psiInput : ∀ t : ℝ, exp 300 ≤ t → Epsi t ≤ C * t ^ (-1 / 8 : ℝ))
    {x : ℝ} (hx : exp 300 ≤ x) :
    Etheta x ≤ (C + 1 / 1000000000) * x ^ (-1 / 8 : ℝ) := by
  apply (theta_transport psiInput hx).trans
  apply mul_le_mul_of_nonneg_right
  · linarith [show (1 / 10000000000000 : ℝ) ≤ 1 / 1000000000 by norm_num]
  · exact rpow_nonneg (le_trans (exp_pos _).le hx) _

#print axioms theta_transport
#print axioms requested_bound
end ExposureTask
