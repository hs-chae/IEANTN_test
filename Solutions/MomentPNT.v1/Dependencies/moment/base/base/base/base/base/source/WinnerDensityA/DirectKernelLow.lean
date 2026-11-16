/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.DirectKernelNorm
namespace WinnerDirectKernel
open Complex MeasureTheory Set

/-- A crude but uniform low-real-part estimate; it needs no oscillatory cancellation. -/
theorem norm_piKernel_low {z : ℂ} {a v L : ℝ}
    (hv : 0 < v) (hL : v ≤ L) (hg : 0 < |z.im|)
    (hb : 0 ≤ z.re) (hba : z.re ≤ a) :
    ‖piKernel z v L‖ ≤ Real.exp (a*L)/(|z.im| * L) +
      (Real.exp (a*L)/(|z.im| * v^2))*(L-v) := by
  let g := |z.im|
  let n := ‖z‖
  have hLp : 0 < L := hv.trans_le hL
  have hgn : g ≤ n := Complex.abs_im_le_norm z
  have hnp : 0 < n := hg.trans_le hgn
  have hE : Real.exp (z.re*L) ≤ Real.exp (a*L) := by gcongr
  have hpoint : ∀ u ∈ Set.uIoc v L,
      ‖zexp z u / (z * (u : ℂ)^2)‖ ≤ Real.exp (a*L)/(g*v^2) := by
    intro u hu
    rw [Set.uIoc_of_le hL] at hu
    have hu0 : 0 < u := hv.trans hu.1
    have hexp : Real.exp (z.re*u) ≤ Real.exp (a*L) := by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left hu.2 hb).trans (mul_le_mul_of_nonneg_right hba hLp.le)
    rw [norm_div, norm_mul, norm_pow, norm_zexp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hu0]
    change Real.exp (z.re*u)/(n*u^2) ≤ Real.exp (a*L)/(g*v^2)
    calc _ ≤ Real.exp (a*L)/(n*u^2) := by gcongr
         _ ≤ Real.exp (a*L)/(g*v^2) := by
           apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
           exact mul_le_mul hgn (pow_le_pow_left₀ hv.le hu.1.le 2) (sq_nonneg v) hnp.le
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [abs_of_nonneg (sub_nonneg.mpr hL)] at hint
  have hfirst : ‖zexp z L / (z * (L : ℂ))‖ ≤ Real.exp (a*L)/(g*L) := by
    rw [norm_div, norm_mul, norm_zexp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLp]
    change Real.exp (z.re*L)/(n*L) ≤ Real.exp (a*L)/(g*L)
    calc _ ≤ Real.exp (a*L)/(n*L) := by gcongr
         _ ≤ Real.exp (a*L)/(g*L) := by
           apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
           exact mul_le_mul_of_nonneg_right hgn hLp.le
  unfold piKernel
  have ht := norm_add_le (zexp z L / (z * (L : ℂ)))
    (∫ u in v..L, zexp z u / (z * (u : ℂ)^2))
  dsimp only [g] at hfirst hint
  linarith

#print axioms norm_piKernel_low
end WinnerDirectKernel
