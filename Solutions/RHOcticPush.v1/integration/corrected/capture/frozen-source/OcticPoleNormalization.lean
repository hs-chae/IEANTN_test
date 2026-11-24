import OcticIntegralLimits
import OcticMellinNormalize

/-! Exact source pole/main-term normalization. This consumes the independent
entire Mellin change of variables, the actual convolution's evenness, and D=delta exp(L/2). -/
namespace RHOcticPush.PoleNormalization
open Real Set Filter MeasureTheory
open scoped Topology
open RHOcticPush.Mollifier RHOcticPush.PopulationLimit RHOcticPush.PhysicalWeight
open RHOcticPush.IntegralLimits RHOcticPush.GreenSource RHOcticPush.MellinNormalize
set_option maxHeartbeats 0

lemma mellin_one_eq_integral (j : ℕ) (C L : ℝ) :
    RHOcticPush.GreenSource.mellin (logWeight j C L) 1 =
      ((∫ t : ℝ, logWeight j C L t : ℝ) : ℂ) := by
  unfold RHOcticPush.GreenSource.mellin
  have he : (∫ t in Set.Ioi (0 : ℝ), (logWeight j C L t : ℂ) * (t : ℂ) ^ (1 : ℂ) / t) =
      ∫ t in Set.Ioi (0 : ℝ), (logWeight j C L t : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
    dsimp only
    rw [Complex.cpow_one, mul_div_cancel_right₀ _ htne]
  rw [he, integral_complex_ofReal]
  congr 1
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : 0 < t
  · simp [ht]
  · simp [logWeight, ht]

theorem source_pole_eq_smoothMain (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) :
    2 * (∫ t : ℝ, greenWeight j C L t) = smoothMain j C L := by
  rw [source_pole_eq_physical_integral]
  have h := actual_mellin j hδ (1 : ℂ)
  have heL : Complex.exp (((1 : ℂ) - 1 / 2) * (L : ℂ)) =
      (Real.exp (L / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have heU (u : ℝ) : (smoothKernel j u : ℂ) *
      Complex.exp (((1 : ℂ) - 1 / 2) * (EvenKernel.δ C L : ℂ) * (u : ℂ)) =
        ((smoothKernel j u * Real.exp (EvenKernel.δ C L * u / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [mellin_one_eq_integral, heL] at h
  simp_rw [heU] at h
  rw [integral_complex_ofReal, ← Complex.ofReal_mul, delta_exp_half] at h
  have hs : Function.support (fun u : ℝ => smoothKernel j u *
      Real.exp (EvenKernel.δ C L * u / 2)) ⊆ Set.Ioc (-2 : ℝ) 2 := by
    intro u hu
    have hk : smoothKernel j u ≠ 0 := by intro hk; exact hu (by simp [hk])
    exact Set.Ioo_subset_Ioc_self (smoothKernel_support j hk)
  have hi := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hs
  have hcosh := even_exp_integral_eq_cosh (smoothKernel_contDiff j).continuous
    (smoothKernel_even j) 2 (EvenKernel.δ C L / 2)
  have hcosh' : (∫ u in (-2 : ℝ)..2, smoothKernel j u *
      Real.exp (EvenKernel.δ C L * u / 2)) =
      ∫ u in (-2 : ℝ)..2, smoothKernel j u * Real.cosh (EvenKernel.δ C L * u / 2) := by
    simpa only [div_mul_eq_mul_div] using hcosh
  rw [← hi, hcosh'] at h
  unfold smoothMain
  exact_mod_cast h

theorem source_pole_tends {C L : ℝ} (hδ : 0 < EvenKernel.δ C L) :
    Tendsto (fun j : ℕ => 2 * ∫ t : ℝ, greenWeight j C L t)
      atTop (𝓝 (EvenKernel.mainTerm 4 C L)) := by
  simpa only [source_pole_eq_smoothMain _ hδ] using smoothMain_tends C L

#print axioms source_pole_eq_smoothMain
#print axioms source_pole_tends
end RHOcticPush.PoleNormalization
