/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFourierPair
import ExplicitEntireUniqueness
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology FourierTransform
namespace RH080Next.Explicit

private def laplaceCoefficient (v : ℝ) : ℂ := ((2*π*v:ℝ):ℂ)*Complex.I

def compactLaplace (W : ℝ → ℝ) (R : ℝ) (z : ℂ) : ℂ :=
  ∫ v in Icc (-R) R, (W v:ℂ)*Complex.exp (laplaceCoefficient v*z)

private theorem laplace_exp_bound (v R A : ℝ) (z : ℂ)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hv : |v| ≤ R) (hz : |z.im| ≤ A) :
    ‖Complex.exp (laplaceCoefficient v*z)‖ ≤ exp (2*π*R*A) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have heq : (laplaceCoefficient v*z).re = -(2*π*v*z.im) := by
    simp [laplaceCoefficient,Complex.mul_re,Complex.mul_im]
  rw [heq]
  calc
    -(2*π*v*z.im) ≤ |2*π*v*z.im| := by simpa only [abs_neg] using le_abs_self (-(2*π*v*z.im))
    _ = 2*π*(|v| *|z.im|) := by rw [abs_mul,abs_mul,abs_mul,abs_of_pos Real.pi_pos]; norm_num; ring
    _ ≤ 2*π*(R*A) := mul_le_mul_of_nonneg_left (mul_le_mul hv hz (abs_nonneg _) hR) (by positivity)
    _ = 2*π*R*A := by ring

/-- The actual compact Fourier-Laplace integral is entire, by differentiation
under the integral with a proved uniform compact-strip bound. -/
theorem differentiable_compactLaplace (W : ℝ → ℝ) (hW : Continuous W)
    (hWi : Integrable W) (R : ℝ) (hR : 0 ≤ R) :
    Differentiable ℂ (compactLaplace W R) := by
  intro z0
  let A : ℝ := |z0.im|+1
  let B : ℝ := 2*π*R*exp (2*π*R*A)
  let F : ℂ → ℝ → ℂ := fun z v => (W v:ℂ)*Complex.exp (laplaceCoefficient v*z)
  let F' : ℂ → ℝ → ℂ := fun z v => (W v:ℂ)*
    (Complex.exp (laplaceCoefficient v*z)*laplaceCoefficient v)
  have hder (z : ℂ) (v : ℝ) : HasDerivAt (fun w : ℂ => F w v) (F' z v) z := by
    simpa only [F,F',id_eq,mul_one] using
      (((hasDerivAt_id z).const_mul (laplaceCoefficient v)).cexp).const_mul (W v:ℂ)
  have hnormc (v : ℝ) : ‖laplaceCoefficient v‖ = 2*π*|v| := by
    simp [laplaceCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos]
  have hbound : ∀ᵐ v ∂(volume.restrict (Icc (-R) R)),
      ∀ z ∈ Metric.ball z0 1, ‖F' z v‖ ≤ B*|W v| := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    intro z hz
    have hvR : |v| ≤ R := abs_le.mpr hv
    have hzdist : ‖z-z0‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
    have hzi := Complex.abs_im_le_norm (z-z0)
    have hzA : |z.im| ≤ A := by
      have ht := abs_add_le (z.im-z0.im) z0.im
      simp only [Complex.sub_im] at hzi
      dsimp [A]
      rw [sub_add_cancel] at ht
      linarith
    have he := laplace_exp_bound v R A z hR (by dsimp [A]; positivity) hvR hzA
    dsimp only [F']
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,hnormc]
    calc
      |W v| *(‖Complex.exp (laplaceCoefficient v*z)‖*(2*π*|v|)) ≤
          |W v| *(exp (2*π*R*A)*(2*π*R)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact mul_le_mul he (mul_le_mul_of_nonneg_left hvR (by positivity))
          (by positivity) (exp_pos _).le
      _ = B*|W v| := by dsimp [B]; ring
  have hint : Integrable (F z0) (volume.restrict (Icc (-R) R)) := by
    exact (by dsimp [F,laplaceCoefficient]; fun_prop : Continuous (F z0)).integrableOn_Icc
  have hmeas : ∀ᶠ z in 𝓝 z0, AEStronglyMeasurable (F z) (volume.restrict (Icc (-R) R)) := by
    filter_upwards with z
    exact (by dsimp [F,laplaceCoefficient]; fun_prop : Continuous (F z)).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (F' z0) (volume.restrict (Icc (-R) R)) := by
    exact (by dsimp [F',laplaceCoefficient]; fun_prop : Continuous (F' z0)).aestronglyMeasurable
  have hbi : Integrable (fun v : ℝ => B*|W v|) (volume.restrict (Icc (-R) R)) :=
    (hWi.abs.const_mul B).integrableOn
  have hdint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc (-R) R)) (F := F) (F' := F')
    (bound := fun v : ℝ => B*|W v|) (Metric.ball_mem_nhds z0 (by norm_num))
    hmeas hint hdmeas hbound hbi (by filter_upwards with v; intro z hz; exact hder z v)
  exact hdint.2.differentiableAt

private theorem compactLaplace_eq_integral (W : ℝ → ℝ) (R : ℝ)
    (hs : Function.support W ⊆ Icc (-R) R) (z : ℂ) :
    compactLaplace W R z = ∫ v : ℝ, (W v:ℂ)*Complex.exp (laplaceCoefficient v*z) := by
  unfold compactLaplace
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  have hw : W v = 0 := by
    by_contra h
    exact hv (hs h)
  rw [hw,Complex.ofReal_zero,zero_mul]

theorem compactLaplace_affine_real (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (u : ℝ) :
    compactLaplace (affineSpectrum nodes m) (radius nodes m) (u:ℂ) =
      (inverseCosine (affineSpectrum nodes m) u:ℂ) := by
  have hw := integrable_affineSpectrum nodes m hlen hm
  have hf := fourier_even_real_eq_inverseCosine _ hw (affineSpectrum_even nodes m)
  calc
    _ = 𝓕 (fun v : ℝ => (affineSpectrum nodes m v:ℂ)) (-u) := by
      rw [compactLaplace_eq_integral _ _ (affineSpectrum_support_subset nodes m hlen hm),
        Real.fourier_real_eq_integral_exp_smul]
      change (∫ v : ℝ, (affineSpectrum nodes m v:ℂ)*Complex.exp (laplaceCoefficient v*(u:ℂ))) =
        ∫ v : ℝ, Complex.exp ((-2*π*v*(-u):ℝ)*Complex.I)*(affineSpectrum nodes m v:ℂ)
      apply integral_congr_ae
      filter_upwards with v
      have heq : laplaceCoefficient v*(u:ℂ) = ((-2*π*v*(-u):ℝ):ℂ)*Complex.I := by
        dsimp [laplaceCoefficient]
        push_cast
        ring
      rw [heq]
      ring
    _ = (inverseCosine (affineSpectrum nodes m) (-u):ℂ) := congrFun hf (-u)
    _ = _ := by rw [inverseCosine_even]

/-- The entire extension used in the general source theorem equals the actual
compact integral at every complex point, not merely on the real axis. -/
theorem entire_extension_eq_compactLaplace (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ)) :
    H = compactLaplace (affineSpectrum nodes m) (radius nodes m) := by
  apply entire_eq_of_real_eq H _ hH
    (differentiable_compactLaplace _ (continuous_affineSpectrum nodes m)
      (integrable_affineSpectrum nodes m hlen hm) _ (by unfold radius; positivity))
  intro u
  exact (hreal u).trans (compactLaplace_affine_real nodes m hlen hm u).symm

theorem compactLaplace_negative_imag (W : ℝ → ℝ) (R y : ℝ) :
    compactLaplace W R (-(y:ℂ)*Complex.I) =
      ((∫ v in Icc (-R) R, W v*exp (2*π*y*v)):ℝ) := by
  unfold compactLaplace
  calc
    _ = ∫ v in Icc (-R) R, ((W v*exp (2*π*y*v):ℝ):ℂ) := by
      apply integral_congr_ae
      filter_upwards with v
      have heq : laplaceCoefficient v*(-(y:ℂ)*Complex.I) = ((2*π*y*v:ℝ):ℂ) := by
        dsimp [laplaceCoefficient]
        push_cast
        ring_nf
        simp [Complex.I_sq]
      rw [heq,← Complex.ofReal_exp,← Complex.ofReal_mul]
    _ = _ := integral_ofReal

end RH080Next.Explicit
