/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFiniteDifference

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped FourierTransform Topology
namespace RH080Next.Explicit

private theorem integrable_inv_sq_tail : IntegrableOn (fun u : ℝ => 1/u^2) (Ioi 1) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := fun u : ℝ => -(u⁻¹)) (a := 1) (l := 0)
  · intro u hu
    have hu0 : u ≠ 0 := by have : (1:ℝ) ≤ u := hu; linarith
    have h := (hasDerivAt_const u (-1:ℝ)).div (hasDerivAt_id u) hu0
    have heq : ((fun x : ℝ => (-1:ℝ))/id) = (fun x : ℝ => -x⁻¹) := by
      funext x
      simp [div_eq_mul_inv]
    rw [heq] at h
    simpa only [id_eq, zero_mul, neg_mul, one_mul, sub_neg_eq_add, zero_add, neg_div, one_div] using h
  · intro u hu
    exact div_nonneg (by norm_num) (sq_nonneg u)
  · simpa only [neg_zero] using (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0)).neg

private theorem integrable_of_even_continuous_tail (F : ℝ → ℝ) (hF : Continuous F)
    (heven : Function.Even F) (c : ℝ)
    (htail : ∀ u : ℝ, 1 < u → |F u| ≤ c/u^2) : Integrable F := by
  have h01 : IntegrableOn F (Ioc (0:ℝ) 1) := hF.integrableOn_Ioc
  have h1 : IntegrableOn F (Ioi 1) := by
    apply (integrable_inv_sq_tail.const_mul c).mono'
    · exact hF.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simpa [Real.norm_eq_abs, div_eq_mul_inv] using htail u hu
  have hs : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext u
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h|h) <;> linarith
    · intro h
      by_cases h1 : u ≤ 1
      · exact Or.inl ⟨h,h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  have hp : IntegrableOn F (Ioi 0) := by simpa only [hs] using h01.union h1
  have hi := integrable_comp_abs_of_integrableOn_positive F hp
  apply hi.congr
  filter_upwards with u
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg (lt_of_not_ge hu), heven u]

theorem integrable_inverseCosine_affineSpectrum (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) :
    Integrable (inverseCosine (affineSpectrum nodes m)) := by
  apply integrable_of_even_continuous_tail _
    (continuous_inverseCosine _ (integrable_affineSpectrum nodes m hlen hm))
    (inverseCosine_even _) (nodalV1 nodes m/(4*π^2))
  intro u hu
  have h := inverseCosine_affineSpectrum_variation_bound nodes m hlen hm hlast u (by linarith)
  convert h using 1 <;> field_simp <;> ring

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
theorem fourier_even_real_eq_inverseCosine (W : ℝ → ℝ) (hW : Integrable W)
    (heven : Function.Even W) :
    𝓕 (fun v : ℝ => (W v : ℂ)) = fun u : ℝ => (inverseCosine W u : ℂ) := by
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
    unfold inverseCosine
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

/-- Complete pointwise Fourier correspondence for every actual affine window,
including the outer zero and arbitrary finite support radius. -/
theorem fourier_affine_inverse_eq_window (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) :
    𝓕 (fun u : ℝ => (inverseCosine (affineSpectrum nodes m) u : ℂ)) =
      fun v : ℝ => (affineSpectrum nodes m v : ℂ) := by
  have hW := integrable_affineSpectrum nodes m hlen hm
  have hF := integrable_inverseCosine_affineSpectrum nodes m hlen hm hlast
  have hWF := fourier_even_real_eq_inverseCosine _ hW (affineSpectrum_even nodes m)
  have hFi : Integrable (𝓕 (fun v : ℝ => (affineSpectrum nodes m v : ℂ))) := by
    rw [hWF]
    exact hF.ofReal
  funext v
  have h := hW.ofReal.fourierInv_fourier_eq hFi
    ((Complex.continuous_ofReal.comp (continuous_affineSpectrum nodes m)).continuousAt (x := -v))
  rw [Real.fourierInv_eq_fourier_neg, hWF, neg_neg] at h
  simpa only [affineSpectrum_even nodes m v] using h

end RH080Next.Explicit
