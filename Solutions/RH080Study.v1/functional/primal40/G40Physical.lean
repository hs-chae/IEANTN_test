/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import G40FullRays
import G40Functions
set_option autoImplicit false
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
namespace RH080.Gaussian40

theorem normSource_even (x : ℝ) : coeffEval normSource (-x) = coeffEval normSource x := by
  norm_num [normSource, coeffEval]

theorem wingSource_even (x : ℝ) : coeffEval wingSource (-x) = coeffEval wingSource x := by
  norm_num [wingSource, coeffEval]

theorem norm_radial_abs (x : ℝ) : radialGaussian true normSource |x| = radialGaussian true normSource x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    simp only [radialGaussian, positivePartOrAbs, ite_true, normSource_even, neg_sq]

/-- The full real-line norm really is the scaled half-line integral. -/
theorem physical_norm_identity :
    (∫ x : ℝ, |physicalF x|) = (2/Real.sqrt Real.pi)*
      (∫ u in Ioi (0 : ℝ), radialGaussian true normSource u) := by
  have hpoint (x : ℝ) : |physicalF x| =
      radialGaussian true normSource (Real.sqrt Real.pi*x) := by
    simp only [physicalF, radialGaussian, positivePartOrAbs, ite_true, abs_mul,
      abs_of_pos (Real.exp_pos _)]
  simp_rw [hpoint]
  rw [Measure.integral_comp_mul_left]
  have habs := integral_comp_abs (f := radialGaussian true normSource)
  simp_rw [norm_radial_abs] at habs
  rw [habs, smul_eq_mul, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr Real.pi_pos))]
  ring

/-- Kernel-only enclosure of the genuine physical Gaussian norm. -/
theorem physical_norm_upper : (∫ x : ℝ, |physicalF x|) ≤ (74901918/100000000 : ℝ) := by
  rw [physical_norm_identity]
  have hs : 0 ≤ (2 : ℝ)/Real.sqrt Real.pi := by positivity
  calc
    _ ≤ (2/Real.sqrt Real.pi)*(6638009580001/10000000000000) :=
      mul_le_mul_of_nonneg_left norm_ray_integral_upper hs
    _ ≤ (1128379167096/1000000000000 : ℝ)*(6638009580001/10000000000000) :=
      mul_le_mul_of_nonneg_right two_div_sqrt_pi_upper (by norm_num)
    _ ≤ (74901918/100000000 : ℝ) := by norm_num

/-- Positivity of the Gaussian factor justifies the actual positive-part semantics. -/
theorem physical_positive_part (x : ℝ) :
    max 0 (physicalG x) = radialGaussian false wingSource (Real.sqrt Real.pi*x) := by
  unfold physicalG radialGaussian positivePartOrAbs
  simp only [Bool.false_eq_true, ite_false]
  by_cases hp : 0 ≤ coeffEval wingSource (Real.sqrt Real.pi*x)
  · rw [max_eq_right hp, max_eq_right (mul_nonneg hp (Real.exp_nonneg _))]
  · have hp' : coeffEval wingSource (Real.sqrt Real.pi*x) ≤ 0 := le_of_not_ge hp
    rw [max_eq_left hp', max_eq_left (mul_nonpos_of_nonpos_of_nonneg hp' (Real.exp_nonneg _))]
    simp

/-- Genuine positive-wing integral enclosure; Fourier association is a separate theorem. -/
theorem physical_positive_wing_upper :
    2*(∫ x in Ioi (1 : ℝ), max 0 (physicalG x)) ≤ (3111791/100000000 : ℝ) := by
  simp_rw [physical_positive_part]
  rw [integral_comp_mul_left_Ioi (radialGaussian false wingSource) 1
    (Real.sqrt_pos.mpr Real.pi_pos)]
  simp only [mul_one, smul_eq_mul]
  have hm : (∫ u in Ioi (Real.sqrt Real.pi), radialGaussian false wingSource u) ≤
      (∫ u in Ioi (1772453850905/1000000000000 : ℝ), radialGaussian false wingSource u) := by
    apply setIntegral_mono_set
      (integrableOn_radialGaussian_ray false wingSource (by decide)
        (1772453850905/1000000000000) (by norm_num))
      (ae_of_all _ (radialGaussian_nonneg _ _))
    exact ae_of_all _ (fun x hx => wing_start_le_sqrt_pi.trans_lt hx)
  have hs : 0 ≤ (2 : ℝ)/Real.sqrt Real.pi := by positivity
  calc
    2*((Real.sqrt Real.pi)⁻¹*∫ u in Ioi (Real.sqrt Real.pi), radialGaussian false wingSource u)
      = (2/Real.sqrt Real.pi)*(∫ u in Ioi (Real.sqrt Real.pi), radialGaussian false wingSource u) := by ring
    _ ≤ (2/Real.sqrt Real.pi)*(275775241001/10000000000000) :=
      mul_le_mul_of_nonneg_left (hm.trans wing_ray_integral_upper) hs
    _ ≤ (1128379167096/1000000000000 : ℝ)*(275775241001/10000000000000) :=
      mul_le_mul_of_nonneg_right two_div_sqrt_pi_upper (by norm_num)
    _ ≤ (3111791/100000000 : ℝ) := by norm_num

theorem physicalF_zero_lower : (999999999/1000000000 : ℝ) ≤ physicalF 0 := by
  norm_num [physicalF, normSource, coeffEval]

/-- Actual integral objective for A=36/11. No extremal or ANT theorem is assumed. -/
noncomputable def gaussianInverseObjective : ℝ :=
  (∫ x : ℝ, |physicalF x|)/
    (physicalF 0-(36/11 : ℝ)*(2*∫ x in Ioi (1 : ℝ), max 0 (physicalG x)))

theorem gaussian_objective_upper : gaussianInverseObjective ≤ (833948898/1000000000 : ℝ) := by
  have hden : 0 < physicalF 0-(36/11 : ℝ)*(2*∫ x in Ioi (1 : ℝ), max 0 (physicalG x)) := by
    nlinarith [physicalF_zero_lower, physical_positive_wing_upper]
  unfold gaussianInverseObjective
  apply (div_le_iff₀ hden).mpr
  nlinarith [physical_norm_upper, physicalF_zero_lower, physical_positive_wing_upper]

theorem gaussian_objective_lt_printed_2026 :
    gaussianInverseObjective < (834050619151/1000000000000 : ℝ) := by
  exact gaussian_objective_upper.trans_lt (by norm_num)

#print axioms physical_norm_upper
#print axioms physical_positive_wing_upper
#print axioms gaussian_objective_lt_printed_2026
end RH080.Gaussian40
