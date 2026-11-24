import BoxZeroKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual complex shift of the Box Fourier integral. -/
namespace RHOcticPush.BoxZero
open Real Complex Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 0

noncomputable def phase (y u : ℝ) : ℂ :=
  Complex.exp (((y : ℂ) * Complex.I) * (u : ℂ))
noncomputable def H (ε y : ℝ) : ℂ :=
  ∫ u in (-1 : ℝ)..1, ((Real.exp (ε*u)/2 : ℝ) : ℂ) * phase y u
noncomputable def amplitude (ε u : ℝ) : ℂ := ((Real.exp (ε*u)-1)/2 : ℝ)
noncomputable def amplitudeD (ε u : ℝ) : ℂ := ((ε * Real.exp (ε*u))/2 : ℝ)

lemma phase_norm (y u : ℝ) : ‖phase y u‖ = 1 := by
  rw [phase, Complex.norm_exp]
  norm_num [Complex.mul_re, Complex.mul_im]

lemma exp_defect (x : ℝ) : |Real.exp x-1| ≤ |x| * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_exp] at h
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

lemma amplitude_bound {ε : ℝ} (hε : 0 ≤ ε) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    ‖amplitude ε u‖ ≤ ε * Real.exp ε * |u| / 2 := by
  have hu1 : |u| ≤ 1 := abs_le.mpr hu
  have he : |ε*u| = ε*|u| := by rw [abs_mul, abs_of_nonneg hε]
  have heu : ε * |u| ≤ ε := by nlinarith
  have hh := exp_defect (ε*u)
  rw [he] at hh
  have hc := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr heu)
    (mul_nonneg hε (abs_nonneg u))
  unfold amplitude
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  have hc' : ε * |u| * Real.exp ε = ε * Real.exp ε * |u| := by ring
  rw [hc'] at hc
  exact div_le_div_of_nonneg_right (hh.trans hc) (by norm_num)

@[fun_prop] lemma phase_continuous (y : ℝ) : Continuous (phase y) := by unfold phase; fun_prop
lemma amplitude_continuous (ε : ℝ) : Continuous (amplitude ε) := by unfold amplitude; fun_prop
lemma amplitudeD_continuous (ε : ℝ) : Continuous (amplitudeD ε) := by
  unfold amplitudeD
  fun_prop

lemma H_zero (y : ℝ) : H 0 y = (F y : ℂ) := by
  by_cases hy : y = 0
  · subst y
    norm_num [H, phase, F_sinc]
  · unfold H
    simp only [zero_mul, Real.exp_zero, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    rw [intervalIntegral.integral_const_mul]
    have hc : (y : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hy) Complex.I_ne_zero
    unfold phase
    rw [integral_exp_mul_complex hc]
    rw [F_eq hy]
    norm_num only [Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg]
    rw [show -((y : ℂ) * Complex.I) = ((-y : ℝ) : ℂ) * Complex.I by push_cast; ring]
    simp only [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    simp only [Complex.cos_neg, Complex.sin_neg]
    field_simp
    <;> ring

lemma shift_as_integral (ε y : ℝ) :
    H ε y - (F y : ℂ) = ∫ u in (-1 : ℝ)..1, amplitude ε u * phase y u := by
  rw [← H_zero y]
  unfold H
  rw [← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro u _
    simp only [zero_mul, Real.exp_zero]
    unfold amplitude
    push_cast
    ring
  · exact (by fun_prop : Continuous (fun u : ℝ =>
      ((Real.exp (ε*u)/2 : ℝ) : ℂ) * phase y u)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun u : ℝ =>
      ((Real.exp (0*u)/2 : ℝ) : ℂ) * phase y u)).intervalIntegrable _ _

lemma abs_integral_unit : (∫ u in (-1 : ℝ)..1, |u|) = 1 := by
  have hi : IntervalIntegrable (fun u : ℝ => |u|) volume (-1) 0 :=
    continuous_abs.intervalIntegrable _ _
  have hj : IntervalIntegrable (fun u : ℝ => |u|) volume 0 1 :=
    continuous_abs.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi hj]
  have hl : (∫ u in (-1 : ℝ)..0, |u|) = ∫ u in (-1 : ℝ)..0, -u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    exact abs_of_nonpos hu.2
  have hr : (∫ u in (0 : ℝ)..1, |u|) = ∫ u in (0 : ℝ)..1, u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    exact abs_of_nonneg hu.1
  rw [hl, hr, intervalIntegral.integral_neg, integral_id, integral_id]
  norm_num

theorem shift_global {ε : ℝ} (hε : 0 ≤ ε) (y : ℝ) :
    ‖H ε y - (F y : ℂ)‖ ≤ ε * Real.exp ε / 2 := by
  rw [shift_as_integral]
  calc
    _ ≤ ∫ u in (-1 : ℝ)..1, ‖amplitude ε u * phase y u‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ u in (-1 : ℝ)..1, (ε * Real.exp ε / 2) * |u| := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (((amplitude_continuous ε).mul (phase_continuous y)).norm.intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun u : ℝ => (ε * Real.exp ε / 2) * |u|)).intervalIntegrable _ _)
      intro u hu
      change ‖amplitude ε u * phase y u‖ ≤ _
      rw [norm_mul, phase_norm, mul_one]
      have h := amplitude_bound hε hu
      nlinarith
    _ = _ := by rw [intervalIntegral.integral_const_mul, abs_integral_unit, mul_one]

lemma amplitude_derivative (ε u : ℝ) :
    HasDerivAt (amplitude ε) (amplitudeD ε u) u := by
  have h := ((((hasDerivAt_id u).const_mul ε).exp.sub_const 1).div_const 2).ofReal_comp
  exact h.congr_deriv (by dsimp [amplitudeD]; push_cast; ring)

noncomputable def phasePrimitive (y u : ℝ) : ℂ := phase y u / ((y : ℂ) * Complex.I)

lemma phase_antiderivative {y : ℝ} (hy : y ≠ 0) (u : ℝ) :
    HasDerivAt (phasePrimitive y) (phase y u) u := by
  have hc : (y : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hy) Complex.I_ne_zero
  have hd := (((hasDerivAt_id u).ofReal_comp.const_mul ((y : ℂ) * Complex.I)).cexp).div_const
    ((y : ℂ) * Complex.I)
  exact hd.congr_deriv (by simp [phase, hc])

lemma phasePrimitive_continuous (y : ℝ) : Continuous (phasePrimitive y) :=
  (phase_continuous y).div_const _

lemma phasePrimitive_norm {y : ℝ} (hy : 0 < y) (u : ℝ) :
    ‖phasePrimitive y u‖ = 1/y := by
  rw [phasePrimitive, norm_div, phase_norm, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos hy]

lemma amplitudeD_bound {ε : ℝ} (hε : 0 ≤ ε) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    ‖amplitudeD ε u‖ ≤ ε * Real.exp ε / 2 := by
  have heu : ε*u ≤ ε := by nlinarith [hu.2]
  unfold amplitudeD
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr

theorem shift_tail {ε y : ℝ} (hε : 0 ≤ ε) (hy : 0 < y) :
    ‖H ε y - (F y : ℂ)‖ ≤ 2 * ε * Real.exp ε / y := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1)
    (amplitude_continuous ε).continuousOn (phasePrimitive_continuous y).continuousOn
    (fun u _ => amplitude_derivative ε u) (fun u _ => phase_antiderivative hy.ne' u)
    ((amplitudeD_continuous ε).intervalIntegrable _ _)
    ((phase_continuous y).intervalIntegrable _ _)
  have ha : ‖amplitude ε 1 * phasePrimitive y 1‖ ≤ (ε * Real.exp ε / 2)/y := by
    rw [norm_mul, phasePrimitive_norm hy]
    have h := amplitude_bound hε (show (1 : ℝ) ∈ Icc (-1) 1 by norm_num)
    norm_num only [abs_one, mul_one] at h
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos.mpr hy))
  have hb : ‖amplitude ε (-1) * phasePrimitive y (-1)‖ ≤ (ε * Real.exp ε / 2)/y := by
    rw [norm_mul, phasePrimitive_norm hy]
    have h := amplitude_bound hε (show (-1 : ℝ) ∈ Icc (-1) 1 by norm_num)
    norm_num only [abs_neg, abs_one, mul_one] at h
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos.mpr hy))
  have hi : ‖∫ u in (-1 : ℝ)..1, amplitudeD ε u * phasePrimitive y u‖ ≤
      ε * Real.exp ε / y := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 1) (C := ε * Real.exp ε / (2*y))
      (f := fun u : ℝ => amplitudeD ε u * phasePrimitive y u) (by
        intro u hu
        rw [uIoc_of_le (by norm_num)] at hu
        have hm := amplitudeD_bound hε (show u ∈ Icc (-1 : ℝ) 1 from ⟨hu.1.le, hu.2⟩)
        rw [norm_mul, phasePrimitive_norm hy]
        have ht := mul_le_mul_of_nonneg_right hm (le_of_lt (one_div_pos.mpr hy))
        calc
          _ ≤ (ε * Real.exp ε / 2) * (1/y) := ht
          _ = _ := by ring)
    have hh' : ‖∫ u in (-1 : ℝ)..1, amplitudeD ε u * phasePrimitive y u‖ ≤
        (ε * Real.exp ε / (2*y))*2 := by norm_num at hh ⊢; exact hh
    calc
      _ ≤ (ε * Real.exp ε / (2*y))*2 := hh'
      _ = _ := by ring
  rw [shift_as_integral, hibp]
  calc
    _ ≤ ‖amplitude ε 1 * phasePrimitive y 1‖ +
        ‖amplitude ε (-1) * phasePrimitive y (-1)‖ +
        ‖∫ u in (-1 : ℝ)..1, amplitudeD ε u * phasePrimitive y u‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (ε * Real.exp ε / 2)/y + (ε * Real.exp ε / 2)/y + ε * Real.exp ε / y :=
      add_le_add (add_le_add ha hb) hi
    _ = _ := by ring

#print axioms H_zero
#print axioms shift_global
#print axioms shift_tail
end RHOcticPush.BoxZero
