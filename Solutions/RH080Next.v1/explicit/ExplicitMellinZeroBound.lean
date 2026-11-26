/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSZeroSource

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

theorem realZeroFamily_norm (nodes : List ℚ) (m : ℕ) (d L : ℝ) (ρ : CMSZeroIndex) :
    ‖realZeroFamily nodes m d L ρ‖ =
      |inverseCosine (affineSpectrum nodes m) ((d/(2*π))*(ρ:ℂ).im)| *cmsMultiplicity ρ := by
  unfold realZeroFamily cmsMultiplicity
  rw [norm_mul,norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_add,mul_zero,sub_zero,
    zero_sub,one_mul,exp_zero,one_mul,Complex.norm_real,Real.norm_eq_abs]
  norm_cast

/-- The actual spectral term of the proved Mellin identity is bounded by
actual two-sign zero sums. The general partial-summation source and all its
admissibility fields remain explicit; no final zero-error cap is assumed. -/
theorem mellin_zero_norm_bound (hsource : SourceCMSZeroPartialSummationProofScheme)
    (hcount : SourceCMSZeroCounting) (hRH : RiemannHypothesis)
    (hD : SourceDLMFRealEtaIntegral)
    (nodes : List ℚ) (m : ℕ) (d L T0 : ℝ) (hd : 0 < d)
    (hT0e : exp 1 ≤ T0) (hT010 : T0 < 10) (hQ : cmsQ T0 = 0)
    (hadm : CMSZeroAdmissible (inverseCosine (affineSpectrum nodes m))
      (deriv (inverseCosine (affineSpectrum nodes m))) (d/(2*π)) T0) :
    Summable (realZeroFamily nodes m d L) ∧
    ‖(d:ℂ)*(∑' ρ : CMSZeroIndex, realZeroFamily nodes m d L ρ)‖ ≤
      4*π*cmsZeroMain (inverseCosine (affineSpectrum nodes m)) (d/(2*π)) T0+
      2*d*cmsZeroRemainder (deriv (inverseCosine (affineSpectrum nodes m))) (d/(2*π)) T0 := by
  let Δ : ℝ := d/(2*π)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  obtain ⟨hA,hbound⟩ := cms_full_zero_bound_from_sources hsource hcount hRH hD T0 hT0e hT010 hQ
    (inverseCosine (affineSpectrum nodes m)) (deriv (inverseCosine (affineSpectrum nodes m))) Δ hΔ hadm
  have hnorm : Summable (fun ρ : CMSZeroIndex => ‖realZeroFamily nodes m d L ρ‖) := by
    apply (hA.mul_left Δ⁻¹).congr
    intro ρ
    rw [realZeroFamily_norm]
    unfold cmsAmplitude
    change Δ⁻¹*(Δ*|inverseCosine (affineSpectrum nodes m) (Δ*(ρ:ℂ).im)| *cmsMultiplicity ρ) = _
    rw [←mul_assoc,←mul_assoc,inv_mul_cancel₀ hΔ.ne',one_mul]
  have hsum : Summable (realZeroFamily nodes m d L) := hnorm.of_norm
  have heq : d*(∑' ρ : CMSZeroIndex, ‖realZeroFamily nodes m d L ρ‖) =
      2*π*(∑' ρ : CMSZeroIndex, cmsAmplitude (inverseCosine (affineSpectrum nodes m)) Δ ρ) := by
    rw [←tsum_mul_left,←tsum_mul_left]
    apply tsum_congr
    intro ρ
    rw [realZeroFamily_norm]
    unfold cmsAmplitude Δ
    field_simp
    <;> ring
  refine ⟨hsum,?_⟩
  calc
    ‖(d:ℂ)*(∑' ρ : CMSZeroIndex, realZeroFamily nodes m d L ρ)‖ =
        d*‖∑' ρ : CMSZeroIndex, realZeroFamily nodes m d L ρ‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    _ ≤ d*(∑' ρ : CMSZeroIndex, ‖realZeroFamily nodes m d L ρ‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) hd.le
    _ = 2*π*(∑' ρ : CMSZeroIndex, cmsAmplitude (inverseCosine (affineSpectrum nodes m)) Δ ρ) := heq
    _ ≤ 2*π*(2*cmsZeroMain (inverseCosine (affineSpectrum nodes m)) Δ T0+
        2*Δ*cmsZeroRemainder (deriv (inverseCosine (affineSpectrum nodes m))) Δ T0) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by dsimp [Δ]; field_simp; ring

#print axioms mellin_zero_norm_bound
end RH080Next.Explicit
