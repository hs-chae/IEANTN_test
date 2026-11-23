/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib
import EvenKernel

/-! Exact analytic attachment of the numerical octic Fourier expression to its
actual defining kernel integral. The rational formula is used only away fromzero;
the zero value is separately proved. No numerical evaluation or PV claim occurs. -/
namespace RHLimit.OcticFourier
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def primitive (y u : ℝ) : ℝ :=
  (1-u^8)*sin (y*u)/y +
  (-8)*(u^7*cos (y*u))/y^2 +
  56*(u^6*sin (y*u))/y^3 +
  336*(u^5*cos (y*u))/y^4 +
  (-1680)*(u^4*sin (y*u))/y^5 +
  (-6720)*(u^3*cos (y*u))/y^6 +
  20160*(u^2*sin (y*u))/y^7 +
  40320*(u*cos (y*u))/y^8 +
  (-40320)*sin (y*u)/y^9

noncomputable def formula (y : ℝ) : ℝ :=
  (-16)*cos y/y^2 + 112*sin y/y^3 + 672*cos y/y^4 +
  (-3360)*sin y/y^5 + (-13440)*cos y/y^6 + 40320*sin y/y^7 +
  80640*cos y/y^8 + (-80640)*sin y/y^9

lemma primitive_derivative {y : ℝ} (hy : y ≠ 0) (u : ℝ) :
    HasDerivAt (primitive y) ((1-u^8)*cos (y*u)) u := by
  have hi := hasDerivAt_id u
  have hs := (Real.hasDerivAt_sin (y*u)).comp u (hi.const_mul y)
  have hc := (Real.hasDerivAt_cos (y*u)).comp u (hi.const_mul y)
  have h0 := (((hasDerivAt_const u (1:ℝ)).sub (hi.pow 8)).mul hs).div_const y
  have h1 := (((hi.pow 7).mul hc).const_mul (-8)).div_const (y^2)
  have h2 := (((hi.pow 6).mul hs).const_mul 56).div_const (y^3)
  have h3 := (((hi.pow 5).mul hc).const_mul 336).div_const (y^4)
  have h4 := (((hi.pow 4).mul hs).const_mul (-1680)).div_const (y^5)
  have h5 := (((hi.pow 3).mul hc).const_mul (-6720)).div_const (y^6)
  have h6 := (((hi.pow 2).mul hs).const_mul 20160).div_const (y^7)
  have h7 := ((hi.mul hc).const_mul 40320).div_const (y^8)
  have h8 := (hs.const_mul (-40320)).div_const (y^9)
  apply ((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).congr_deriv
  dsimp
  norm_num
  field_simp [hy]
  ring

/-- Exact Fourier formula for the actual octic kernel, on its source domain. -/
theorem transform_eq {y : ℝ} (hy : y ≠ 0) :
    EvenKernel.transform 4 y = formula y := by
  have he : EvenKernel.transform 4 y = ∫ u in (-1:ℝ)..1, (1-u^8)*cos (y*u) := by
    unfold EvenKernel.transform
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [EvenKernel.kernel_eq_raw 4 (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hu)]
  rw [he]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => primitive_derivative hy u)]
  · simp [primitive,formula]
    field_simp [hy]
    ring
  · exact (by fun_prop : Continuous (fun u:ℝ => (1-u^8)*cos (y*u))).intervalIntegrable _ _

theorem transform_zero : EvenKernel.transform 4 0 = 16/9 := by
  have h := EvenKernel.kernel_mass 4
  norm_num [EvenKernel.mass] at h
  simpa [EvenKernel.transform] using h

noncomputable def formulaDerivative (y : ℝ) : ℝ :=
  16 * sin y / y ^ 2 + 144 * cos y / y ^ 3 + (-1008) * sin y / y ^ 4 +
  (-6048) * cos y / y ^ 5 + 30240 * sin y / y ^ 6 +
  120960 * cos y / y ^ 7 + (-362880) * sin y / y ^ 8 +
  (-725760) * cos y / y ^ 9 + 725760 * sin y / y ^ 10

/-- The expression differentiated by the numerical code is the actual Fourier derivative. -/
lemma formula_hasDerivAt {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt formula (formulaDerivative y) y := by
  have hi := hasDerivAt_id y
  have hs := Real.hasDerivAt_sin y
  have hc := Real.hasDerivAt_cos y
  have h0 := (hc.const_mul (-16)).div (hi.pow 2) (pow_ne_zero 2 hy)
  have h1 := (hs.const_mul 112).div (hi.pow 3) (pow_ne_zero 3 hy)
  have h2 := (hc.const_mul 672).div (hi.pow 4) (pow_ne_zero 4 hy)
  have h3 := (hs.const_mul (-3360)).div (hi.pow 5) (pow_ne_zero 5 hy)
  have h4 := (hc.const_mul (-13440)).div (hi.pow 6) (pow_ne_zero 6 hy)
  have h5 := (hs.const_mul 40320).div (hi.pow 7) (pow_ne_zero 7 hy)
  have h6 := (hc.const_mul 80640).div (hi.pow 8) (pow_ne_zero 8 hy)
  have h7 := (hs.const_mul (-80640)).div (hi.pow 9) (pow_ne_zero 9 hy)
  apply (((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).congr_deriv
  dsimp [formulaDerivative]
  norm_num
  field_simp [hy]
  ring

/-- Analytic attachment at every nonzero ordinate, without numerical assumptions. -/
theorem transform_hasDerivAt {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (EvenKernel.transform 4) (formulaDerivative y) y := by
  apply (formula_hasDerivAt hy).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hy] with z hz
  exact transform_eq hz

#print axioms transform_eq
#print axioms transform_zero
#print axioms transform_hasDerivAt
end RHLimit.OcticFourier
