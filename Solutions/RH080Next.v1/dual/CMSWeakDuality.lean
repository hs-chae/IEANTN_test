/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AbelFourierInversion
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Real Set
open scoped Topology FourierTransform
namespace RH080Next.Dual
open RH080.Dual

lemma integrable_abel_mul (f : ℝ → ℝ) (hf : Integrable f) (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun x : ℝ => abelWeight c x * f x) := by
  apply hf.bdd_mul (c := 1) (abelWeight_continuous c).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (abelWeight_nonneg c x)] using
      abelWeight_le_one c x hc)

lemma tendsto_integral_abel (f : ℝ → ℝ) (hf : Integrable f) :
    Tendsto (fun c : ℝ => ∫ x : ℝ, abelWeight c x * f x) atTop (𝓝 (∫ x : ℝ, f x)) := by
  apply tendsto_integral_filter_of_dominated_convergence _ _ _ hf.norm
  · filter_upwards with x
    simpa using! (tendsto_abelWeight x).mul_const (f x)
  · filter_upwards with c
    exact (abelWeight_continuous c).aestronglyMeasurable.mul hf.1
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with c (hc : 0 ≤ c)
    filter_upwards with x
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abelWeight_nonneg c x)]
    exact mul_le_of_le_one_left (abs_nonneg _) (abelWeight_le_one c x hc)

/-- Full CMS-class weak duality. Only F is assumed L1; the positive exterior
part of its actual Fourier transform is integrable. G need not be L1.
Gaussian regularization, inversion and dominated convergence are kernel-proved. -/
theorem weak_duality_cms (F G V : ℝ → ℝ) (A M : ℝ)
    (hF : Integrable F) (hV : Integrable V)
    (hcont : ContinuousAt F 0)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ))
    (hpen : Integrable (exteriorPositive G))
    (hcenter : ∀ v : ℝ, ¬ (1 < |v|) → V v = 1)
    (hlower : ∀ v : ℝ, 1 < |v| → 1 - A ≤ V v)
    (hupper : ∀ v : ℝ, 1 < |v| → V v ≤ 1)
    (hkernel : ∀ x : ℝ, |cosineTransform V x| ≤ M) :
    F 0 - A * (∫ v in exterior, max 0 (G v)) ≤ M * (∫ x : ℝ, |F x|) := by
  have hcos : cosineTransform F = G := by
    funext v
    rw [cosineTransform_eq_re_fourier F hF v, hfourier]
    rfl
  have hGV : Integrable (fun v : ℝ => G v * V v) := by
    have hp := (integrable_cosine_product F V hF hV).integral_prod_right
    convert hp using 1
    funext v
    rw [← hcos]
    unfold cosineTransform
    rw [← integral_mul_const]
    congr 1
    funext x
    ring
  have hleft := (abel_real_inversion_zero F G hF hcont hfourier).sub
    ((tendsto_integral_abel (exteriorPositive G) hpen).const_mul A)
  have hright := tendsto_integral_abel (fun v : ℝ => G v * V v) hGV
  have hlim : F 0 - A * (∫ v : ℝ, exteriorPositive G v) ≤ ∫ v : ℝ, G v * V v := by
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c (hc : 0 < c)
    have hiG := integrable_abel_fourier F G hF hfourier c hc
    have hiP := integrable_abel_mul (exteriorPositive G) hpen c hc.le
    have hiV := integrable_abel_mul (fun v : ℝ => G v * V v) hGV c hc.le
    have hi := integral_mono (hiG.sub (hiP.const_mul A)) hiV (fun v => by
      change abelWeight c v * G v - A * (abelWeight c v * exteriorPositive G v) ≤
        abelWeight c v * (G v * V v)
      have hd := dual_pointwise G V A hcenter hlower hupper v
      nlinarith [mul_nonneg (abelWeight_nonneg c v) (sub_nonneg.mpr hd)])
    change (∫ v : ℝ, abelWeight c v * G v - A * (abelWeight c v * exteriorPositive G v)) ≤
      (∫ v : ℝ, abelWeight c v * (G v * V v)) at hi
    rw [integral_sub hiG (hiP.const_mul A), integral_const_mul] at hi
    exact hi
  rw [exteriorPositive, integral_indicator exterior_measurable] at hlim
  have hpair := cosine_pairing F V hF hV
  rw [hcos] at hpair
  rw [hpair] at hlim
  have hFK : Integrable (fun x : ℝ => F x * cosineTransform V x) := by
    have hp := (integrable_cosine_product F V hF hV).integral_prod_left
    convert hp using 1
    funext x
    unfold cosineTransform
    rw [← integral_const_mul]
    congr 1
    funext v
    ring_nf
  have hFM : Integrable (fun x : ℝ => |F x| * M) := by
    simpa only [Real.norm_eq_abs] using hF.norm.mul_const M
  have hu := integral_mono hFK hFM (fun x => calc
    F x * cosineTransform V x ≤ |F x * cosineTransform V x| := le_abs_self _
    _ = |F x| * |cosineTransform V x| := abs_mul _ _
    _ ≤ |F x| * M := mul_le_mul_of_nonneg_left (hkernel x) (abs_nonneg _))
  rw [integral_mul_const] at hu
  nlinarith

private theorem even_sine_integral_zero (W : ℝ → ℝ) (heven : Function.Even W) (t : ℝ) :
    (∫ v : ℝ, W v*sin (t*v)) = 0 := by
  have h := integral_neg_eq_self (fun v : ℝ => W v*sin (t*v)) volume
  have heq : (fun v : ℝ => W (-v)*sin (t*(-v))) = (fun v : ℝ => -(W v*sin (t*v))) := by
    funext v
    simp [heven v]
  rw [heq, integral_neg] at h
  linarith

/-- The cosine integral is the actual complex Fourier transform for an even
integrable real window; its imaginary part vanishes by parity. -/
theorem fourier_even_real_eq_cosine (W : ℝ → ℝ) (hW : Integrable W)
    (heven : Function.Even W) :
    𝓕 (fun v : ℝ => (W v : ℂ)) = fun u : ℝ => (cosineTransform W u : ℂ) := by
  funext u
  have hi : Integrable (fun v : ℝ =>
      Complex.exp ((-2*π*v*u:ℝ)*Complex.I)*(W v:ℂ)) := by
    apply hW.ofReal.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards with v
      rw [Complex.norm_exp]
      simp [Complex.mul_re]
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ v : ℝ, Complex.exp ((-2*π*v*u:ℝ)*Complex.I)*(W v:ℂ)) = _
  apply Complex.ext
  · have hre := integral_re hi
    change (∫ v : ℝ, (Complex.exp ((-2*π*v*u:ℝ)*Complex.I)*(W v:ℂ)).re) =
      (∫ v : ℝ, Complex.exp ((-2*π*v*u:ℝ)*Complex.I)*(W v:ℂ)).re at hre
    rw [← hre]
    simp only [Complex.ofReal_re]
    unfold cosineTransform
    apply integral_congr_ae
    filter_upwards with v
    simp [Complex.mul_re, Complex.exp_re]
    ring_nf
  · have him := integral_im hi
    change (∫ v : ℝ, (Complex.exp ((-2*π*v*u:ℝ)*Complex.I)*(W v:ℂ)).im) =
      (∫ v : ℝ, Complex.exp ((-2*π*v*u:ℝ)*Complex.I)*(W v:ℂ)).im at him
    rw [← him]
    simp only [Complex.ofReal_im]
    have heq : (fun v : ℝ => (Complex.exp ((-2*π*v*u:ℝ)*Complex.I)*(W v:ℂ)).im) =
        (fun v : ℝ => -(W v*sin ((2*π*u)*v))) := by
      funext v
      simp [Complex.mul_im, Complex.exp_im]
      ring_nf
    rw [heq, integral_neg, even_sine_integral_zero W heven (2*π*u), neg_zero]


/-- Weak duality on the exact real-even CMS class, with the Fourier transform
constructed from F rather than supplied as an independent numerical function. -/
theorem weak_duality_even_cms (F V : ℝ → ℝ) (A M : ℝ)
    (hF : Integrable F) (hV : Integrable V) (hcont : ContinuousAt F 0)
    (heven : Function.Even F)
    (hpen : Integrable (exteriorPositive (cosineTransform F)))
    (hcenter : ∀ v : ℝ, ¬ (1 < |v|) → V v = 1)
    (hlower : ∀ v : ℝ, 1 < |v| → 1 - A ≤ V v)
    (hupper : ∀ v : ℝ, 1 < |v| → V v ≤ 1)
    (hkernel : ∀ x : ℝ, |cosineTransform V x| ≤ M) :
    F 0 - A * (∫ v in exterior, max 0 (cosineTransform F v)) ≤
      M * (∫ x : ℝ, |F x|) :=
  weak_duality_cms F (cosineTransform F) V A M hF hV hcont
    (fourier_even_real_eq_cosine F hF heven) hpen hcenter hlower hupper hkernel

/-- A certified inverse-transform cap supplies the correctly directed lower
bound on the CMS primal quotient. No claim about prime gaps is inferred. -/
theorem functional_lower_bound_even_cms (F V : ℝ → ℝ) (A M : ℝ)
    (hF : Integrable F) (hV : Integrable V) (hcont : ContinuousAt F 0)
    (heven : Function.Even F)
    (hpen : Integrable (exteriorPositive (cosineTransform F)))
    (hcenter : ∀ v : ℝ, ¬ (1 < |v|) → V v = 1)
    (hlower : ∀ v : ℝ, 1 < |v| → 1 - A ≤ V v)
    (hupper : ∀ v : ℝ, 1 < |v| → V v ≤ 1)
    (hkernel : ∀ x : ℝ, |cosineTransform V x| ≤ M) (hM : 0 < M)
    (hden : 0 < F 0 - A * (∫ v in exterior, max 0 (cosineTransform F v))) :
    1 / M ≤ (∫ x : ℝ, |F x|) /
      (F 0 - A * (∫ v in exterior, max 0 (cosineTransform F v))) := by
  apply (div_le_div_iff₀ hM hden).2
  have hw := weak_duality_even_cms F V A M hF hV hcont heven hpen
    hcenter hlower hupper hkernel
  nlinarith

#print axioms weak_duality_cms
#print axioms weak_duality_even_cms
#print axioms functional_lower_bound_even_cms
end RH080Next.Dual
