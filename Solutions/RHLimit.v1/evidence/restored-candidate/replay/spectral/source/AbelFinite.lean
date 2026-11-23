/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Definitions
namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set
noncomputable def thetaCoeff (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

theorem thetaCoeff_sum (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, thetaCoeff n) = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp [thetaCoeff, Finset.sum_filter]

theorem theta_cube_integrable {y M : ℝ} (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => Chebyshev.theta t / t^3) (Set.Ioc y M) := by
  have hi : IntegrableOn (fun t : ℝ => (t^3)⁻¹) (Set.Icc y M) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((continuous_id.pow 3).continuousAt.inv₀ (pow_ne_zero 3 ht0)).continuousWithinAt
  have h := integrableOn_mul_sum_Icc thetaCoeff (m := 0) hy.le hi
  apply (h.mono_set Set.Ioc_subset_Icc_self).congr_fun _ measurableSet_Ioc
  intro t ht
  dsimp only
  rw [thetaCoeff_sum]
  simp [div_eq_mul_inv, mul_comm]

/-- Actual finite Abel summation, including the ordinary endpoints and both boundary terms. -/
theorem squareFinite_abel {y M : ℝ} (hy : 0 < y) (hyM : y ≤ M) :
    squareFinite y M = Chebyshev.theta M / M^2 - Chebyshev.theta y / y^2 +
      2 * ∫ t in Set.Ioc y M, Chebyshev.theta t / t^3 := by
  let f : ℝ → ℝ := fun t => (t^2)⁻¹
  have hd : ∀ t ∈ Set.Icc y M, HasDerivAt f (-(2 / t^3)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h := ((hasDerivAt_id t).pow 2).inv (pow_ne_zero 2 ht0)
    convert h using 1 <;> first | rfl | (dsimp [f]; field_simp [ht0] <;> ring)
  have hi : IntegrableOn (fun t : ℝ => -(2 / t^3)) (Set.Icc y M) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (((continuous_const : Continuous (fun _ : ℝ => (2:ℝ))).continuousAt.div
      (continuous_id.pow 3).continuousAt (pow_ne_zero 3 ht0)).neg).continuousWithinAt
  have hdi : IntegrableOn (deriv f) (Set.Icc y M) := by
    apply hi.congr_fun _ measurableSet_Icc
    intro t ht
    exact (hd t ht).deriv.symm
  have h := sum_mul_eq_sub_sub_integral_mul thetaCoeff hy.le hyM
    (fun t ht => (hd t ht).differentiableAt) hdi
  have hs : squareFinite y M = ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊M⌋₊, f n * thetaCoeff n := by
    unfold squareFinite
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [f,thetaCoeff]
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  rw [hs,h,thetaCoeff_sum,thetaCoeff_sum]
  have he : (∫ t in Set.Ioc y M, deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, thetaCoeff n) =
      -(2 * ∫ t in Set.Ioc y M, Chebyshev.theta t / t^3) := by
    rw [← integral_const_mul,← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t (Set.Ioc_subset_Icc_self ht)).deriv,thetaCoeff_sum]
    ring
  rw [he]
  dsimp [f]
  ring

/-- Elementary definite integral, evaluated without numerical quadrature. -/
theorem integral_theta_lower_model {y M : ℝ} (hy : 0 < y) (hyM : y ≤ M) :
    (∫ t in Set.Ioc y M, (t - 1.95 * Real.sqrt t) / t^3) =
      1/y - 1/M - 1.3/(y*Real.sqrt y) + 1.3/(M*Real.sqrt M) := by
  have hM : 0 < M := hy.trans_le hyM
  have hmodel : ∀ t ∈ Set.Ioc y M, (t - 1.95 * Real.sqrt t) / t^3 =
      t^(-2:ℝ) - 1.95*t^(-(5/2):ℝ) := by
    intro t ht
    have ht0 : 0 < t := hy.trans ht.1
    have hs : t^(-(5/2):ℝ) = Real.sqrt t / t^3 := by
      rw [show (-(5/2):ℝ) = 1/2-3 by norm_num, Real.rpow_sub ht0,
        ← Real.sqrt_eq_rpow]
      norm_num
    rw [hs,show t^(-2:ℝ) = 1/t^2 by simp [Real.rpow_neg ht0.le]]
    field_simp
    <;> ring
  rw [setIntegral_congr_fun measurableSet_Ioc hmodel,
    ← intervalIntegral.integral_of_le hyM]
  have hp : 0 ∉ Set.uIcc y M := by
    rw [Set.uIcc_of_le hyM]
    intro hh
    linarith [hh.1]
  have hi1 : IntervalIntegrable (fun t : ℝ => t^(-2:ℝ)) volume y M := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := by rw [Set.uIcc_of_le hyM] at ht; linarith [ht.1]
    exact (Real.hasDerivAt_rpow_const (p := (-2:ℝ)) (Or.inl ht0)).continuousAt.continuousWithinAt
  have hi2 : IntervalIntegrable (fun t : ℝ => t^(-(5/2):ℝ)) volume y M := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := by rw [Set.uIcc_of_le hyM] at ht; linarith [ht.1]
    exact (Real.hasDerivAt_rpow_const (p := (-(5/2):ℝ)) (Or.inl ht0)).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_sub hi1 (hi2.const_mul _),intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by norm_num,hp⟩),integral_rpow (Or.inr ⟨by norm_num,hp⟩)]
  have he (t : ℝ) (ht : 0 < t) : t^(-(3/2):ℝ) = 1/(t*Real.sqrt t) := by
    rw [show (-(3/2):ℝ) = -(1+1/2) by norm_num,Real.rpow_neg ht.le,
      Real.rpow_add ht,Real.rpow_one,← Real.sqrt_eq_rpow]
    simp only [one_div]
  norm_num
  rw [he y hy,he M hM]
  simp only [Real.rpow_neg_one]
  ring
end MertensPositive

namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set
/-- Finite Abel lower bound. No global theta estimate or improper-integral limit is needed. -/
theorem finite_square_lower {y M : ℝ} (hy : 0 < y) (hyM : y ≤ M)
    (hU : Chebyshev.theta y ≤ y - 0.05 * Real.sqrt y)
    (hL : ∀ t ∈ Set.Ioc y M, t - 1.95 * Real.sqrt t ≤ Chebyshev.theta t) :
    1/y - 2.55/(y*Real.sqrt y) - 2/M ≤ squareFinite y M := by
  have hM : 0 < M := hy.trans_le hyM
  have hsY : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hImodel : IntegrableOn (fun t : ℝ => (t-1.95*Real.sqrt t)/t^3) (Set.Ioc y M) := by
    apply (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((continuousAt_id.sub (continuousAt_const.mul Real.continuous_sqrt.continuousAt)).div
      (continuous_id.pow 3).continuousAt (pow_ne_zero 3 ht0)).continuousWithinAt
  have hi : (∫ t in Set.Ioc y M, (t-1.95*Real.sqrt t)/t^3) ≤
      ∫ t in Set.Ioc y M, Chebyshev.theta t/t^3 := by
    apply integral_mono_ae hImodel (theta_cube_integrable hy)
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    apply Filter.Eventually.of_forall
    intro t ht
    exact div_le_div_of_nonneg_right (hL t ht) (by have := hy.trans ht.1; positivity)
  rw [integral_theta_lower_model hy hyM] at hi
  have hdiv := div_le_div_of_nonneg_right hU (sq_nonneg y)
  have he : (y-0.05*Real.sqrt y)/y^2 = 1/y-0.05/(y*Real.sqrt y) := by
    field_simp [ne_of_gt hy,ne_of_gt hsY]
    nlinarith [Real.sq_sqrt hy.le]
  rw [he] at hdiv
  have hEnd : 0 ≤ Chebyshev.theta M / M^2 :=
    div_nonneg (Chebyshev.theta_nonneg M) (sq_nonneg M)
  have hPos : 0 ≤ (1.3:ℝ)/(M*Real.sqrt M) := by positivity
  have hA := squareFinite_abel hy hyM
  simp only [div_eq_mul_inv] at hi hdiv hEnd hPos hA ⊢
  linarith
end MertensPositive
