/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FourierWeakDuality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Complex Module Real
open scoped Topology FourierTransform RealInnerProductSpace Complex
namespace RH080Next.Dual

/-- Gaussian-regularized inversion does not require the Fourier transform to be
integrable. This is the class bridge needed for unrestricted CMS weak duality. -/
theorem abel_fourier_inversion
    (f : ℝ → ℂ) (hf : Integrable f) {v : ℝ} (hcont : ContinuousAt f v) :
    Tendsto (fun c : ℝ => ∫ w : ℝ,
      cexp (- (c : ℂ)⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫) * (𝓕 f) w)
      atTop (𝓝 (f v)) := by
  have A := Real.tendsto_integral_gaussian_smul' hf hcont
  apply A.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  have J : Integrable (fun w : ℝ =>
      cexp (- (c : ℂ)⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)) :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa) _ _
  have H := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner J hf
  calc
    _ = ∫ w : ℝ, 𝓕 (fun y : ℝ =>
        cexp (- (c : ℂ)⁻¹ * ‖y‖ ^ 2 + 2 * π * I * ⟪v, y⟫)) w • f w := by
      congr with w
      rw [fourier_gaussian_innerProductSpace' (by simpa)]
      simp only [div_inv_eq_mul]
      congr 3 <;> ring
    _ = _ := by simpa using! H

def abelWeight (c x : ℝ) : ℝ := Real.exp (-c⁻¹ * x ^ 2)

lemma abelWeight_nonneg (c x : ℝ) : 0 ≤ abelWeight c x := (Real.exp_pos _).le

lemma abelWeight_le_one (c x : ℝ) (hc : 0 ≤ c) : abelWeight c x ≤ 1 := by
  unfold abelWeight
  rw [Real.exp_le_one_iff]
  have : 0 ≤ c⁻¹ * x ^ 2 := mul_nonneg (inv_nonneg.mpr hc) (sq_nonneg x)
  linarith

lemma abelWeight_continuous (c : ℝ) : Continuous (abelWeight c) := by
  unfold abelWeight
  fun_prop

lemma tendsto_abelWeight (x : ℝ) :
    Tendsto (fun c : ℝ => abelWeight c x) atTop (𝓝 1) := by
  unfold abelWeight
  have ht : Tendsto (fun c : ℝ => -c⁻¹ * x ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.neg.mul_const (x ^ 2)
  simpa [Function.comp_def] using! (Real.continuous_exp.tendsto 0).comp ht

lemma integrable_abelWeight (c : ℝ) (hc : 0 < c) : Integrable (abelWeight c) := by
  exact integrable_exp_neg_mul_sq (inv_pos.mpr hc)

lemma continuous_real_fourier (F G : ℝ → ℝ) (hF : Integrable F)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ)) :
    Continuous G := by
  have hh : Continuous (𝓕 (fun x : ℝ => (F x : ℂ))) := by
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hF.ofReal
  rw [hfourier] at hh
  simpa only [Function.comp_def, Complex.ofReal_re] using! Complex.continuous_re.comp hh

lemma bound_real_fourier (F G : ℝ → ℝ)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ)) (v : ℝ) :
    |G v| ≤ ∫ x : ℝ, |F x| := by
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) (fun x : ℝ => (F x : ℂ)) v
  change ‖𝓕 (fun x : ℝ => (F x : ℂ)) v‖ ≤ _ at h
  simpa [hfourier, Complex.norm_real, Real.norm_eq_abs] using h

lemma integrable_abel_fourier (F G : ℝ → ℝ) (hF : Integrable F)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ))
    (c : ℝ) (hc : 0 < c) : Integrable (fun v : ℝ => abelWeight c v * G v) := by
  apply (integrable_abelWeight c hc).mul_bdd
    (continuous_real_fourier F G hF hfourier).aestronglyMeasurable
  exact ae_of_all _ (fun v => by simpa only [Real.norm_eq_abs] using bound_real_fourier F G hfourier v)

/-- Real Abel inversion at zero for the true Fourier transform; no assumption
that G is integrable is present. -/
theorem abel_real_inversion_zero (F G : ℝ → ℝ) (hF : Integrable F)
    (hcont : ContinuousAt F 0)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ)) :
    Tendsto (fun c : ℝ => ∫ v : ℝ, abelWeight c v * G v) atTop (𝓝 (F 0)) := by
  have H := abel_fourier_inversion (fun x : ℝ => (F x : ℂ)) hF.ofReal
    (Complex.continuous_ofReal.continuousAt.comp hcont)
  have Hr := (Complex.continuous_re.tendsto (F 0 : ℂ)).comp H
  apply Hr.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  have hi : Integrable (fun w : ℝ => ((abelWeight c w * G w : ℝ) : ℂ)) :=
    (integrable_abel_fourier F G hF hfourier c hc).ofReal
  have he : (fun w : ℝ =>
      cexp (- (c : ℂ)⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪(0 : ℝ), w⟫) *
        (𝓕 (fun x : ℝ => (F x : ℂ))) w) =
      fun w : ℝ => ((abelWeight c w * G w : ℝ) : ℂ) := by
    funext w
    rw [hfourier]
    simp only [inner_zero_left, ofReal_zero, mul_zero, add_zero]
    have hearg : - (c : ℂ)⁻¹ * (‖w‖ : ℂ) ^ 2 =
        ((-c⁻¹ * w ^ 2 : ℝ) : ℂ) := by
      simp only [ofReal_mul, ofReal_neg, ofReal_inv, ofReal_pow]
      rw [Real.norm_eq_abs, ← ofReal_pow, sq_abs, ofReal_pow]
    rw [hearg, ← Complex.ofReal_exp]
    simp only [abelWeight, ofReal_mul]
  simp only [Function.comp_apply]
  rw [he]
  have hre := integral_re hi
  change (∫ w : ℝ, ((abelWeight c w * G w : ℝ) : ℂ).re) =
    (∫ w : ℝ, ((abelWeight c w * G w : ℝ) : ℂ)).re at hre
  rw [← hre]
  simp

#print axioms abel_fourier_inversion
#print axioms abel_real_inversion_zero
end RH080Next.Dual
