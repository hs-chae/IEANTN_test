import OcticMollifier
import Mathlib.Analysis.Fourier.Convolution

/-! Fourier normalization and the actual convolution, not only a postulated
spectral multiplier. The negative frequency compensates Mathlib's 2pi convention. -/
namespace RHOcticPush.FourierMollifier
open Real Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution FourierTransform
set_option maxHeartbeats 0

noncomputable def cosine (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ u : ℝ, f u * Real.cos (y * u)

lemma odd_sine_integral {f : ℝ → ℝ} (heven : ∀ u, f (-u) = f u) (y : ℝ) :
    (∫ u : ℝ, f u * Real.sin (y * u)) = 0 := by
  have h := integral_neg_eq_self (fun u : ℝ => f u * Real.sin (y * u)) volume
  simp_rw [heven, mul_neg, Real.sin_neg, mul_neg] at h
  rw [integral_neg] at h
  linarith

theorem fourier_of_even {f : ℝ → ℝ} (hf : Integrable f)
    (heven : ∀ u, f (-u) = f u) (y : ℝ) :
    𝓕 (fun u : ℝ => (f u : ℂ)) (-y / (2 * Real.pi)) = (cosine f y : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hphase (u : ℝ) : -2 * Real.pi * u * (-y / (2 * Real.pi)) = y * u := by
    field_simp
  simp_rw [hphase, smul_eq_mul]
  have hfc : Integrable (fun u : ℝ => (f u : ℂ)) := hf.ofReal
  have hi : Integrable (fun u : ℝ => Complex.exp ((y * u : ℝ) * Complex.I) * (f u : ℂ)) := by
    apply hf.norm.mono'
    · exact (by fun_prop : Continuous (fun u : ℝ => Complex.exp ((y * u : ℝ) * Complex.I))).aestronglyMeasurable.mul hfc.aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul, Complex.norm_exp]
      simp
  have hexp (u : ℝ) : Complex.exp ((y * u : ℝ) * Complex.I) =
      (Real.cos (y * u) : ℂ) + (Real.sin (y * u) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hre (u : ℝ) : (Complex.exp ((y * u : ℝ) * Complex.I) * (f u : ℂ)).re =
      f u * Real.cos (y * u) := by
    rw [hexp]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him (u : ℝ) : (Complex.exp ((y * u : ℝ) * Complex.I) * (f u : ℂ)).im =
      f u * Real.sin (y * u) := by
    rw [hexp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re hi]
    simp only [RCLike.re_eq_complex_re, hre, Complex.ofReal_re, cosine]
  · rw [← RCLike.im_eq_complex_im, ← integral_im hi]
    simpa only [RCLike.im_eq_complex_im, him, Complex.ofReal_im] using odd_sine_integral heven y

theorem kernel_zero_of_one_le_abs {u : ℝ} (hu : 1 ≤ |u|) : EvenKernel.kernel 4 u = 0 := by
  have hp : (1 : ℝ) ≤ |u| ^ 8 := one_le_pow₀ hu
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ u ^ 8)] at hp
  unfold EvenKernel.kernel
  norm_num only [Nat.reduceMul]
  exact max_eq_left (by linarith)

theorem kernel_support : Function.support (EvenKernel.kernel 4) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  intro u hu
  by_contra h
  have ha : 1 ≤ |u| := by
    change ¬(-1 < u ∧ u < 1) at h
    rw [not_and_or] at h
    rcases h with h | h
    · exact (neg_le_abs u).trans' (by linarith)
    · exact (le_abs_self u).trans' (by linarith)
  exact hu (kernel_zero_of_one_le_abs ha)

theorem kernel_compact : HasCompactSupport (EvenKernel.kernel 4) := by
  apply exists_compact_iff_hasCompactSupport.mp
  refine ⟨Set.Icc (-1 : ℝ) 1, isCompact_Icc, ?_⟩
  intro u hu
  by_contra h
  exact hu (Set.Ioo_subset_Icc_self (kernel_support h))

theorem kernel_integrable : Integrable (EvenKernel.kernel 4) :=
  (EvenKernel.kernel_continuous 4).integrable_of_hasCompactSupport kernel_compact

theorem cosine_kernel (y : ℝ) : cosine (EvenKernel.kernel 4) y = EvenKernel.transform 4 y := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  have hk : EvenKernel.kernel 4 u ≠ 0 := by
    intro h
    exact hu (by simp [h])
  exact Set.Ioo_subset_Ioc_self (kernel_support hk)

theorem kernel_even (u : ℝ) : EvenKernel.kernel 4 (-u) = EvenKernel.kernel 4 u := by
  have hp : (-u) ^ (8 : ℕ) = u ^ 8 := by ring
  simpa only [EvenKernel.kernel, Nat.reduceMul, hp]

theorem smoothKernel_fourier (n : ℕ) (y : ℝ) :
    𝓕 (fun u : ℝ => (RHOcticPush.Mollifier.smoothKernel n u : ℂ)) (-y / (2 * Real.pi)) =
      ((RHOcticPush.Mollifier.multiplier n y * EvenKernel.transform 4 y : ℝ) : ℂ) := by
  have he : (fun u : ℝ => (RHOcticPush.Mollifier.smoothKernel n u : ℂ)) =
      (fun u : ℝ => ((RHOcticPush.Mollifier.bump n).normed volume u : ℂ)) ⋆[mul ℂ ℂ]
        (fun u : ℝ => (EvenKernel.kernel 4 u : ℂ)) := by
    funext u
    simp only [RHOcticPush.Mollifier.smoothKernel, convolution_def,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul, ContinuousLinearMap.mul_apply']
    rw [← integral_complex_ofReal]
    congr 1
    funext t
    norm_cast
  rw [he]
  have hc := Real.fourier_mul_convolution_eq (R := ℂ)
    (f₁ := fun u : ℝ => ((RHOcticPush.Mollifier.bump n).normed volume u : ℂ))
    (f₂ := fun u : ℝ => (EvenKernel.kernel 4 u : ℂ))
    ((RHOcticPush.Mollifier.bump n).integrable_normed.ofReal) kernel_integrable.ofReal
    (-y / (2 * Real.pi))
  rw [hc]
  rw [fourier_of_even (RHOcticPush.Mollifier.bump n).integrable_normed
    (fun u => (RHOcticPush.Mollifier.bump n).normed_neg u) y]
  rw [fourier_of_even kernel_integrable kernel_even y, cosine_kernel]
  simp only [cosine, RHOcticPush.Mollifier.multiplier, Complex.ofReal_mul]

noncomputable def actualSmoothZeroPacket (j : ℕ) (C L : ℝ)
    (z : PsiSmoothing.Zero) : ℂ :=
  Complex.exp (Complex.I * (z.val.im * L : ℝ)) * (EvenKernel.δ C L : ℂ) *
    𝓕 (fun u : ℝ => (RHOcticPush.Mollifier.smoothKernel j u : ℂ))
      (-(EvenKernel.δ C L * z.val.im) / (2 * Real.pi)) *
    (IEANTN.zetaOrder z : ℂ)

theorem actualSmoothZeroPacket_eq_regularized (j : ℕ) (C L : ℝ) (z : PsiSmoothing.Zero) :
    actualSmoothZeroPacket j C L z = RHOcticPush.Mollifier.regularizedPacket j C L z := by
  unfold actualSmoothZeroPacket
  rw [smoothKernel_fourier]
  unfold RHOcticPush.Mollifier.regularizedPacket EvenKernel.zeroPacket
  push_cast
  ring

/-- Full-zero limit for the actual smooth convolution Fourier transform, with
its exact frequency scale and multiplicity, not an abstract proposed multiplier. -/
theorem actualSmoothFullZeroLimit (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) :
    Tendsto (fun j : ℕ => ∑' z : PsiSmoothing.Zero, actualSmoothZeroPacket j C L z)
      atTop (𝓝 (EvenKernel.zeroTerm 4 C L)) := by
  simpa only [actualSmoothZeroPacket_eq_regularized] using
    RHOcticPush.Mollifier.regularized_full_zero_limit rh hN hδ

#print axioms fourier_of_even
#print axioms kernel_integrable
#print axioms smoothKernel_fourier
#print axioms actualSmoothZeroPacket_eq_regularized
#print axioms actualSmoothFullZeroLimit
end RHOcticPush.FourierMollifier
