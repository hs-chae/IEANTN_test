/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.DirectKernel

open Complex MeasureTheory Set Filter
namespace WinnerDirectKernel

lemma norm_zexp (z : ℂ) (u : ℝ) : ‖zexp z u‖ = Real.exp (z.re*u) := by
  simp [zexp, Complex.norm_exp, Complex.mul_re]

lemma integral_exp_upper {b v L : ℝ} (hb : 0 < b) :
    (∫ u in v..L, Real.exp (b*u)) ≤ Real.exp (b*L)/b := by
  have hder : ∀ u : ℝ, HasDerivAt (fun t : ℝ => Real.exp (b*t)/b) (Real.exp (b*u)) u := by
    intro u
    simpa [hb.ne'] using (((hasDerivAt_id u).const_mul b).exp.div_const b)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hder u) (show IntervalIntegrable (fun u : ℝ => Real.exp (b*u)) volume v L by
      apply Continuous.intervalIntegrable; fun_prop)
  rw [he]
  exact sub_le_self _ (div_nonneg (Real.exp_pos _).le hb.le)

lemma norm_remainder_integral {z : ℂ} {v L : ℝ}
    (hv : 0 < v) (hL : v ≤ L) (hb : 0 < z.re) :
    ‖∫ u in v..L, zexp z u / (u : ℂ)^3‖ ≤
      Real.exp (z.re*L) / (z.re*v^3) := by
  have hbound : ∀ u ∈ Set.Ioc v L,
      ‖zexp z u / (u : ℂ)^3‖ ≤ Real.exp (z.re*u)/v^3 := by
    intro u hu
    have hu0 : 0 < u := hv.trans hu.1
    simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
      norm_zexp]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos hv 3)
      (pow_le_pow_left₀ hv.le hu.1.le 3)
  have hi : IntervalIntegrable (fun u : ℝ => Real.exp (z.re*u)/v^3) volume v L := by
    apply Continuous.intervalIntegrable; fun_prop
  have hn := intervalIntegral.norm_integral_le_of_norm_le hL
    (Eventually.of_forall hbound) hi
  calc
    _ ≤ ∫ u in v..L, Real.exp (z.re*u)/v^3 := hn
    _ = (∫ u in v..L, Real.exp (z.re*u))/v^3 := intervalIntegral.integral_div _ _
    _ ≤ (Real.exp (z.re*L)/z.re)/v^3 :=
      div_le_div_of_nonneg_right (integral_exp_upper hb) (pow_pos hv 3).le
    _ = _ := by ring

noncomputable def piKernel (z : ℂ) (v L : ℝ) : ℂ :=
  zexp z L / (z * (L : ℂ)) + (∫ u in v..L, zexp z u / (z * (u : ℂ)^2))

/-- The direct logarithmic integral kernel keeps the ordinate in its correction denominator. -/
theorem norm_piKernel {z : ℂ} {v L : ℝ} (hz : z ≠ 0)
    (hv : 0 < v) (hL : v ≤ L) (hb : 0 < z.re) :
    ‖piKernel z v L‖ ≤
      Real.exp (z.re*L)/(‖z‖*L) + Real.exp (z.re*L)/(‖z‖^2*L^2) +
        Real.exp (z.re*v)/(‖z‖^2*v^2) +
          2*Real.exp (z.re*L)/(‖z‖^2*z.re*v^3) := by
  have hLp : 0 < L := hv.trans_le hL
  rw [piKernel, integral_kernel_identity z hz hv hL]
  calc
    _ ≤ ‖zexp z L / (z * (L : ℂ))‖ + ‖zexp z L / (z^2 * (L : ℂ)^2)‖ +
        ‖zexp z v / (z^2 * (v : ℂ)^2)‖ +
          ‖(2 / z^2) * (∫ u in v..L, zexp z u / (u : ℂ)^3)‖ := by
      have h0 := norm_add_le
        (zexp z L / (z * (L : ℂ)) + zexp z L / (z^2 * (L : ℂ)^2) -
          zexp z v / (z^2 * (v : ℂ)^2))
        ((2 / z^2) * (∫ u in v..L, zexp z u / (u : ℂ)^3))
      have h1 := norm_sub_le (zexp z L / (z * (L : ℂ)) +
        zexp z L / (z^2 * (L : ℂ)^2)) (zexp z v / (z^2 * (v : ℂ)^2))
      have h2 := norm_add_le (zexp z L / (z * (L : ℂ)))
        (zexp z L / (z^2 * (L : ℂ)^2))
      linarith
    _ = Real.exp (z.re*L)/(‖z‖*L) + Real.exp (z.re*L)/(‖z‖^2*L^2) +
        Real.exp (z.re*v)/(‖z‖^2*v^2) +
          (2/‖z‖^2)*‖∫ u in v..L, zexp z u / (u : ℂ)^3‖ := by
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hLp, abs_of_pos hv, norm_zexp, Complex.norm_ofNat]
    _ ≤ Real.exp (z.re*L)/(‖z‖*L) + Real.exp (z.re*L)/(‖z‖^2*L^2) +
        Real.exp (z.re*v)/(‖z‖^2*v^2) +
          (2/‖z‖^2)*(Real.exp (z.re*L)/(z.re*v^3)) := by
      gcongr
      exact norm_remainder_integral hv hL hb
    _ = _ := by ring

#print axioms norm_remainder_integral
#print axioms norm_piKernel
end WinnerDirectKernel
