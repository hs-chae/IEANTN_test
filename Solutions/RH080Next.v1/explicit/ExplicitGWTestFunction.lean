/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitBRStripTransfer
import Mathlib.Analysis.SpecialFunctions.Complex.Log

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem horizontal_decay_dilate (H : ℂ → ℂ) (hH : HorizontalQuadraticDecay H)
    (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) :
    HorizontalQuadraticDecay (fun z : ℂ => (a:ℂ)*H ((r:ℂ)*z)) := by
  intro A hA
  obtain ⟨C,R,hC,hR,hbound⟩ := hH (r*A) (mul_nonneg hr.le hA)
  let K : ℝ := 1+r⁻¹
  refine ⟨a*K^2*C,R/r,by positivity,div_nonneg hR hr.le,?_⟩
  intro z hz hzr
  have hzIm : |(((r:ℂ)*z).im)| ≤ r*A := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hz hr.le
  have hzRe : R ≤ |(((r:ℂ)*z).re)| := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      abs_mul, abs_of_pos hr]
    have h := (div_le_iff₀ hr).mp hzr
    nlinarith
  have hb := hbound ((r:ℂ)*z) hzIm hzRe
  have hs : 1+|z.re| ≤ K*(1+|(((r:ℂ)*z).re)|) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      abs_mul, abs_of_pos hr]
    have heq : K*(1+r*|z.re|) = 1+|z.re|+(r⁻¹+r*|z.re|) := by
      dsimp [K]
      field_simp
      <;> ring
    rw [heq]
    exact le_add_of_nonneg_right (add_nonneg (inv_nonneg.mpr hr.le) (mul_nonneg hr.le (abs_nonneg _)))
  have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|z.re|) hs 2
  calc
    ‖(a:ℂ)*H ((r:ℂ)*z)‖*(1+|z.re|)^2 = a*(‖H ((r:ℂ)*z)‖*(1+|z.re|)^2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
      ring
    _ ≤ a*(‖H ((r:ℂ)*z)‖*(K*(1+|(((r:ℂ)*z).re)|))^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs2 (norm_nonneg _)) ha
    _ = (a*K^2)*(‖H ((r:ℂ)*z)‖*(1+|(((r:ℂ)*z).re)|)^2) := by ring
    _ ≤ (a*K^2)*C := mul_le_mul_of_nonneg_left hb (mul_nonneg ha (sq_nonneg _))

private theorem horizontal_decay_phase (H : ℂ → ℂ) (hH : HorizontalQuadraticDecay H)
    (L : ℝ) : HorizontalQuadraticDecay (fun z : ℂ => H z*Complex.exp (Complex.I*(L:ℂ)*z)) := by
  intro A hA
  obtain ⟨C,R,hC,hR,hbound⟩ := hH A hA
  refine ⟨C*exp (A*|L|),R,mul_nonneg hC (exp_pos _).le,hR,?_⟩
  intro z hz hzr
  have he : ‖Complex.exp (Complex.I*(L:ℂ)*z)‖ ≤ exp (A*|L|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_sub,
      one_mul, zero_add]
    calc
      -(L*z.im) ≤ |-(L*z.im)| := le_abs_self _
      _ = |L| *|z.im| := by rw [abs_neg, abs_mul]
      _ ≤ |L| *A := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = A*|L| := by ring
  calc
    ‖H z*Complex.exp (Complex.I*(L:ℂ)*z)‖*(1+|z.re|)^2 =
      (‖H z‖*(1+|z.re|)^2)*‖Complex.exp (Complex.I*(L:ℂ)*z)‖ := by rw [norm_mul]; ring
    _ ≤ C*exp (A*|L|) := mul_le_mul (hbound z hz hzr) he (norm_nonneg _) hC

/-- Actual Guinand--Weil test function from the published Mellin derivation.
The result proves its entire extension and strip decay for any positive d;
the support-seven case is obtained from the preceding mesh-dilation theorem. -/
theorem mellin_test_function_strip (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hdec : HorizontalQuadraticDecay H) (d L : ℝ) (hd : 0 < d) :
    Differentiable ℂ (fun z : ℂ => (d:ℂ)*H (((d/(2*π):ℝ):ℂ)*z)*Complex.exp (Complex.I*(L:ℂ)*z)) ∧
      HorizontalQuadraticDecay (fun z : ℂ => (d:ℂ)*H (((d/(2*π):ℝ):ℂ)*z)*Complex.exp (Complex.I*(L:ℂ)*z)) := by
  constructor
  · fun_prop
  · exact horizontal_decay_phase _ (horizontal_decay_dilate H hdec d (d/(2*π)) hd.le (by positivity)) L

end RH080Next.Explicit
