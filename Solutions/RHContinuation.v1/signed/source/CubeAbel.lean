/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CubeCorrection
namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set
noncomputable def cubeFinite (w y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊w⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log n/(n:ℝ)^3

theorem theta_fourth_integrable {w y : ℝ} (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => Chebyshev.theta t/t^4) (Set.Ioc w y) := by
  have hi : IntegrableOn (fun t : ℝ => (t^4)⁻¹) (Set.Icc w y) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((continuous_id.pow 4).continuousAt.inv₀ (pow_ne_zero 4 ht0)).continuousWithinAt
  have h := integrableOn_mul_sum_Icc thetaCoeff (m := 0) hw.le hi
  apply (h.mono_set Set.Ioc_subset_Icc_self).congr_fun _ measurableSet_Ioc
  intro t ht
  dsimp only
  rw [thetaCoeff_sum]
  simp [div_eq_mul_inv,mul_comm]

theorem cubeFinite_abel {w y : ℝ} (hw : 0 < w) (hwy : w ≤ y) :
    cubeFinite w y = Chebyshev.theta y/y^3 - Chebyshev.theta w/w^3 +
      3 * ∫ t in Set.Ioc w y, Chebyshev.theta t/t^4 := by
  let f : ℝ → ℝ := fun t => (t^3)⁻¹
  have hd : ∀ t ∈ Set.Icc w y, HasDerivAt f (-(3/t^4)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h := ((hasDerivAt_id t).pow 3).inv (pow_ne_zero 3 ht0)
    convert h using 1 <;> first | rfl | (dsimp [f]; field_simp [ht0] <;> ring)
  have hi : IntegrableOn (fun t : ℝ => -(3/t^4)) (Set.Icc w y) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (((continuous_const : Continuous (fun _ : ℝ => (3:ℝ))).continuousAt.div
      (continuous_id.pow 4).continuousAt (pow_ne_zero 4 ht0)).neg).continuousWithinAt
  have hdi : IntegrableOn (deriv f) (Set.Icc w y) := by
    apply hi.congr_fun _ measurableSet_Icc
    intro t ht
    exact (hd t ht).deriv.symm
  have h := sum_mul_eq_sub_sub_integral_mul thetaCoeff hw.le hwy
    (fun t ht => (hd t ht).differentiableAt) hdi
  have hs : cubeFinite w y = ∑ n ∈ Finset.Ioc ⌊w⌋₊ ⌊y⌋₊, f n*thetaCoeff n := by
    unfold cubeFinite
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [f,thetaCoeff]
    split_ifs <;> simp [div_eq_mul_inv,mul_comm]
  rw [hs,h,thetaCoeff_sum,thetaCoeff_sum]
  have he : (∫ t in Set.Ioc w y, deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊,
      thetaCoeff n) = -(3*∫ t in Set.Ioc w y, Chebyshev.theta t/t^4) := by
    rw [← integral_const_mul,← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t (Set.Ioc_subset_Icc_self ht)).deriv,thetaCoeff_sum]
    ring
  rw [he]
  dsimp [f]
  ring

theorem integral_cube_lower_model {w y : ℝ} (hw : 0 < w) (hwy : w ≤ y) :
    (∫ t in Set.Ioc w y, (t-1.95*Real.sqrt t)/t^4) =
      0.5/w^2-0.5/y^2-0.78/(w^2*Real.sqrt w)+0.78/(y^2*Real.sqrt y) := by
  have hy : 0 < y := hw.trans_le hwy
  have hmodel : ∀ t ∈ Set.Ioc w y, (t-1.95*Real.sqrt t)/t^4 =
      t^(-3:ℝ)-1.95*t^(-(7/2):ℝ) := by
    intro t ht
    have ht0 : 0 < t := hw.trans ht.1
    have hs : t^(-(7/2):ℝ) = Real.sqrt t/t^4 := by
      rw [show (-(7/2):ℝ)=1/2-4 by norm_num,Real.rpow_sub ht0,← Real.sqrt_eq_rpow]
      norm_num
    rw [hs,show t^(-3:ℝ)=1/t^3 by simp [Real.rpow_neg ht0.le]]
    field_simp <;> ring
  rw [setIntegral_congr_fun measurableSet_Ioc hmodel,← intervalIntegral.integral_of_le hwy]
  have hp : 0 ∉ Set.uIcc w y := by
    rw [Set.uIcc_of_le hwy]
    intro hh
    linarith [hh.1]
  have hi1 : IntervalIntegrable (fun t : ℝ => t^(-3:ℝ)) volume w y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := by rw [Set.uIcc_of_le hwy] at ht; linarith [ht.1]
    exact (Real.hasDerivAt_rpow_const (p := (-3:ℝ)) (Or.inl ht0)).continuousAt.continuousWithinAt
  have hi2 : IntervalIntegrable (fun t : ℝ => t^(-(7/2):ℝ)) volume w y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := by rw [Set.uIcc_of_le hwy] at ht; linarith [ht.1]
    exact (Real.hasDerivAt_rpow_const (p := (-(7/2):ℝ))
      (Or.inl ht0)).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_sub hi1 (hi2.const_mul _),intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by norm_num,hp⟩),integral_rpow (Or.inr ⟨by norm_num,hp⟩)]
  have he (t : ℝ) (ht : 0 < t) : t^(-(5/2):ℝ)=1/(t^2*Real.sqrt t) := by
    rw [show (-(5/2):ℝ)=-(2+1/2) by norm_num,Real.rpow_neg ht.le,
      Real.rpow_add ht,← Real.sqrt_eq_rpow]
    norm_num
  norm_num
  rw [he w hw,he y hy]
  simp only [one_div]
  ring

/-- Signed finite endpoints plus the lower theta integral retain the cube main term. -/
theorem finite_cube_lower {w y : ℝ} (hw : 0 < w) (hwy : w ≤ y)
    (hU : Chebyshev.theta w ≤ w-0.05*Real.sqrt w)
    (hLy : y-1.95*Real.sqrt y ≤ Chebyshev.theta y)
    (hL : ∀ t ∈ Set.Ioc w y, t-1.95*Real.sqrt t ≤ Chebyshev.theta t) :
    0.5/w^2-2.29/(w^2*Real.sqrt w)-0.5/y^2 ≤ cubeFinite w y := by
  have hy : 0 < y := hw.trans_le hwy
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hImodel : IntegrableOn (fun t : ℝ => (t-1.95*Real.sqrt t)/t^4) (Set.Ioc w y) := by
    apply (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((continuousAt_id.sub (continuousAt_const.mul Real.continuous_sqrt.continuousAt)).div
      (continuous_id.pow 4).continuousAt (pow_ne_zero 4 ht0)).continuousWithinAt
  have hi : (∫ t in Set.Ioc w y, (t-1.95*Real.sqrt t)/t^4) ≤
      ∫ t in Set.Ioc w y, Chebyshev.theta t/t^4 := by
    apply integral_mono_ae hImodel (theta_fourth_integrable hw)
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Filter.Eventually.of_forall (fun t ht =>
      div_le_div_of_nonneg_right (hL t ht) (by have := hw.trans ht.1; positivity))
  rw [integral_cube_lower_model hw hwy] at hi
  have hdiv := div_le_div_of_nonneg_right hU (by positivity : 0 ≤ w^3)
  have hew : (w-0.05*Real.sqrt w)/w^3 = 1/w^2-0.05/(w^2*Real.sqrt w) := by
    field_simp [ne_of_gt hw,ne_of_gt hsw]
    nlinarith [Real.sq_sqrt hw.le]
  rw [hew] at hdiv
  have hdivy := div_le_div_of_nonneg_right hLy (by positivity : 0 ≤ y^3)
  have hey : (y-1.95*Real.sqrt y)/y^3 = 1/y^2-1.95/(y^2*Real.sqrt y) := by
    field_simp [ne_of_gt hy,ne_of_gt hsy]
    nlinarith [Real.sq_sqrt hy.le]
  rw [hey] at hdivy
  have hPos : 0 ≤ (0.39:ℝ)/(y^2*Real.sqrt y) := by positivity
  have hA := cubeFinite_abel hw hwy
  simp only [div_eq_mul_inv] at hi hdiv hdivy hPos hA ⊢
  linarith

/-- Actual cube-root cut, including p at the square endpoint and excluding the cube root. -/
theorem fullTail_ge_square_add_cubeFinite {x M w : ℝ} (hx : 2 ≤ x)
    (hw : 0 ≤ w) (hw3 : w^3=x) :
    squareFinite (Real.sqrt x) M + cubeFinite w (Real.sqrt x) ≤ fullTail x := by
  let mid := (Finset.Ioc ⌊w⌋₊ ⌊Real.sqrt x⌋₊).filter Nat.Prime
  have hsub : mid ⊆ primes (Real.sqrt x) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpI,hpP⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ioc.mpr ⟨by have := (Finset.mem_Ioc.mp hpI).1; omega,
      (Finset.mem_Ioc.mp hpI).2⟩,hpP⟩
  have hc : ∀ p ∈ mid, x < (p:ℝ)^3 := by
    intro p hp
    have hwp : w < p := Nat.lt_of_floor_lt (Finset.mem_Ioc.mp
      (Finset.mem_filter.mp hp).1).1
    rw [← hw3]
    exact pow_lt_pow_left₀ hwp hw (by norm_num)
  exact fullTail_ge_square_add_cubes hx mid hsub hc

#print axioms finite_cube_lower
#print axioms fullTail_ge_square_add_cubeFinite
end MertensPositive
