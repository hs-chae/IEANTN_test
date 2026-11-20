/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import Mathlib

/-! Primitive integral bounds for the coupled prime-count envelope.
All statements have explicit positive-log domains. No numerical or source
execution premise is introduced here. -/
namespace RamanujanPV.CoupledIntegralBounds
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def phi (t : ℝ) : ℝ := 2 * Real.sqrt t / (Real.log t)^2
noncomputable def kernel (t : ℝ) : ℝ := 1 / (Real.sqrt t * (Real.log t)^2)
noncomputable def phiDerivative (t : ℝ) : ℝ :=
  (1 - 4 / Real.log t) / (Real.sqrt t * (Real.log t)^2)

theorem phi_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt phi (phiDerivative t) t := by
  have ht0 : 0 < t := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht0).ne'
  have hs2 : (Real.sqrt t)^2 = t := Real.sq_sqrt ht0.le
  have hd := ((Real.hasDerivAt_sqrt ht0.ne').const_mul 2).div
    ((Real.hasDerivAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl)
  convert hd using 1
  · rfl
  · dsimp [phiDerivative]
    field_simp
    nlinarith [hs2]

theorem kernel_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn kernel (Icc a b) := by
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.mul Real.continuous_sqrt.continuousOn
    apply ContinuousOn.pow
    exact Real.continuousOn_log.mono (by intro t ht; have : 0 < t := by linarith [ht.1]; exact ne_of_gt this)
  · intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    exact mul_ne_zero (Real.sqrt_pos.2 (by linarith : 0 < t)).ne'
      (pow_ne_zero 2 (Real.log_pos ht1).ne')

theorem phiDerivative_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn phiDerivative (Icc a b) := by
  have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Icc a b) :=
    Real.continuousOn_log.mono (by intro t ht; have : 0 < t := by linarith [ht.1]; exact ne_of_gt this)
  have hn : ContinuousOn (fun t : ℝ => 1 - 4 / Real.log t) (Icc a b) := by
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div continuousOn_const hlog
    intro t ht
    exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  exact hn.div (Real.continuous_sqrt.continuousOn.mul (hlog.pow 2)) (by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    exact mul_ne_zero (Real.sqrt_pos.2 (by linarith : 0 < t)).ne'
      (pow_ne_zero 2 (Real.log_pos ht1).ne'))

theorem kernel_intervalIntegrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable kernel volume a b :=
  (kernel_continuousOn ha).intervalIntegrable_of_Icc hab

theorem phi_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, phiDerivative t) = phi b - phi a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact phi_hasDerivAt (lt_of_lt_of_le ha ht.1)
  · exact (phiDerivative_continuousOn ha).intervalIntegrable_of_Icc hab

theorem integral_upper {a y : ℝ} (ha : 1 < a) (hay : a ≤ y)
    (hloga : 15 ≤ Real.log a) :
    (∫ t in a..y, kernel t) ≤ (15/11:ℝ) * (phi y - phi a) := by
  have hk := kernel_intervalIntegrable ha hay
  have hd := (phiDerivative_continuousOn ha).intervalIntegrable_of_Icc hay
  have h := intervalIntegral.integral_mono_on hay hk (hd.const_mul (15/11:ℝ)) (by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have hl : 15 ≤ Real.log t := hloga.trans (Real.log_le_log (by linarith) ht.1)
    have hl0 : 0 < Real.log t := by linarith
    have hden : 0 < Real.sqrt t * (Real.log t)^2 := by positivity
    dsimp [kernel, phiDerivative]
    rw [mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hden).2
    have hfour : 4 / Real.log t ≤ (4/15:ℝ) :=
      (div_le_iff₀ hl0).2 (by nlinarith)
    linarith)
  simpa only [intervalIntegral.integral_const_mul, phi_integral ha hay] using h

theorem integral_lower {y x : ℝ} (hy : 1 < y) (hyx : y ≤ x) :
    phi x - phi y ≤ (∫ t in y..x, kernel t) := by
  have hk := kernel_intervalIntegrable hy hyx
  have hd := (phiDerivative_continuousOn hy).intervalIntegrable_of_Icc hyx
  have h := intervalIntegral.integral_mono_on hyx hd hk (by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hy ht.1
    have hl0 : 0 < Real.log t := Real.log_pos ht1
    have hden : 0 < Real.sqrt t * (Real.log t)^2 := by positivity
    dsimp [kernel, phiDerivative]
    apply (div_le_div_iff_of_pos_right hden).2
    have : 0 ≤ 4 / Real.log t := by positivity
    linarith)
  simpa only [phi_integral hy hyx] using h

#print axioms phi_hasDerivAt
#print axioms kernel_intervalIntegrable
#print axioms phi_integral
#print axioms integral_upper
#print axioms integral_lower
end RamanujanPV.CoupledIntegralBounds
