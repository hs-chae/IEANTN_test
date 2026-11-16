import Mathlib
namespace SynergyAnalytic
open Real Set MeasureTheory Filter
set_option maxHeartbeats 0

theorem finite_gaussian_cumulative
    {F f : ℝ → ℝ} {q b : ℝ} (hq : 0 < q) (hb : 0 ≤ b)
    (hF : Continuous F) (hf : Continuous f)
    (hFd : ∀ x ∈ Ioo 0 b, HasDerivAt F (f x) x) (hF0 : F 0 = 0)
    (hFb : 0 ≤ F b) :
    (2*q)*(∫ x in (0:ℝ)..b, x*Real.exp (-q*x^2)*F x) ≤
      ∫ x in (0:ℝ)..b, Real.exp (-q*x^2)*f x := by
  have hw : Continuous (fun x : ℝ => Real.exp (-q*x^2)) := by fun_prop
  have hwp : Continuous (fun x : ℝ => Real.exp (-q*x^2)*(-q*(2*x))) := by fun_prop
  have hd : ∀ x : ℝ, HasDerivAt (fun y => Real.exp (-q*y^2))
      (Real.exp (-q*x^2)*(-q*(2*x))) x := by
    intro x
    convert (((hasDerivAt_id x).pow 2).const_mul (-q)).exp using 1 <;>first | rfl | norm_num
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hw.continuousOn hF.continuousOn
    (fun x hx => hd x) (fun x hx => hFd x (by simpa [min_eq_left hb,max_eq_right hb] using hx))
    (hwp.intervalIntegrable 0 b) (hf.intervalIntegrable 0 b)
  have he : (∫ x in (0:ℝ)..b, (Real.exp (-q*x^2)*(-q*(2*x)))*F x) =
      -(2*q)*(∫ x in (0:ℝ)..b, x*Real.exp (-q*x^2)*F x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [he,hF0] at hip
  have hn := mul_nonneg (Real.exp_pos (-q*b^2)).le hFb
  nlinarith

/-- Uniform bounds on every positive finite cutoff prove convergence and the
full improper bound.  There is no separately assumed tail or integrability fact. -/
theorem positive_improper_of_finite
    {g : ℝ → ℝ} {B : ℝ} (hg : Continuous g)
    (hp : ∀ x ≥ 0, 0 ≤ g x)
    (hb : ∀ b ≥ 1, (∫ x in (0:ℝ)..b, g x) ≤ B) :
    IntegrableOn g (Ioi 0) ∧ (∫ x in Ioi (0:ℝ), g x) ≤ B := by
  have hfinite : ∀ b : ℝ, IntegrableOn g (Ioc 0 b) := by
    intro b
    exact (hg.intervalIntegrable 0 b).1
  have hnorm : ∀ᶠ b : ℝ in atTop, (∫ x in (0:ℝ)..b, ‖g x‖) ≤ B := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with b hb1
    have he : (∫ x in (0:ℝ)..b, ‖g x‖) = ∫ x in (0:ℝ)..b, g x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc 0 b := by simpa [uIcc_of_le (by linarith : (0:ℝ)≤b)] using hx
      exact Real.norm_of_nonneg (hp x hx'.1)
    rw [he]
    exact hb b hb1
  have hi : IntegrableOn g (Ioi (0:ℝ)) :=
    integrableOn_Ioi_of_intervalIntegral_norm_bounded B 0 hfinite tendsto_id hnorm
  refine ⟨hi,?_⟩
  have ht := intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id
  exact le_of_tendsto ht (eventually_atTop.2 ⟨1,fun b hb1 => hb b hb1⟩)

theorem gaussian_cumulative_of_uniform_error
    {F f : ℝ → ℝ} {q B : ℝ} (hq : 0 < q)
    (hF : Continuous F) (hf : Continuous f) (hFd : ∀ x : ℝ, HasDerivAt F (f x) x)
    (hF0 : F 0 = 0) (hp : ∀ x ≥ 0, 0 ≤ F x)
    (herr : ∀ b ≥ 1, (∫ x in (0:ℝ)..b, Real.exp (-q*x^2)*f x) ≤ B) :
    IntegrableOn (fun x => x*Real.exp (-q*x^2)*F x) (Ioi 0) ∧
      (2*q)*(∫ x in Ioi (0:ℝ), x*Real.exp (-q*x^2)*F x) ≤ B := by
  have hfin : ∀ b ≥ 1, (∫ x in (0:ℝ)..b, x*Real.exp (-q*x^2)*F x) ≤ B/(2*q) := by
    intro b hb
    have hh := (finite_gaussian_cumulative hq (by linarith : (0:ℝ)≤b) hF hf
      (fun x hx => hFd x) hF0 (hp b (by linarith))).trans (herr b hb)
    exact (le_div_iff₀ (by positivity : (0:ℝ)<2*q)).mpr (by nlinarith)
  have hc : Continuous (fun x => x*Real.exp (-q*x^2)*F x) := by fun_prop
  have hpos : ∀ x ≥ 0, 0 ≤ x*Real.exp (-q*x^2)*F x := by
    intro x hx
    exact mul_nonneg (mul_nonneg hx (Real.exp_pos _).le) (hp x hx)
  have hr := positive_improper_of_finite hc hpos hfin
  refine ⟨hr.1,?_⟩
  have hh := (le_div_iff₀ (by positivity : (0:ℝ)<2*q)).mp hr.2
  nlinarith

#print axioms gaussian_cumulative_of_uniform_error
end SynergyAnalytic
