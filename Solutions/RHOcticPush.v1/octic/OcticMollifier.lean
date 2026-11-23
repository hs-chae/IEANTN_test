import OcticConvergence
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Group.Tannery

/-! Actual smooth normalized bump approximations to the octic kernel, and the
dominated limit for its full zero family. This supplies specific pieces of an
explicit-formula regularization argument, not an assumed explicit formula. -/
namespace RHOcticPush.Mollifier
open Real Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ContDiff
set_option maxHeartbeats 0

noncomputable def bump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

noncomputable def smoothKernel (n : ℕ) : ℝ → ℝ :=
  (bump n).normed volume ⋆[lsmul ℝ ℝ, volume] EvenKernel.kernel 4

theorem smoothKernel_contDiff (n : ℕ) : ContDiff ℝ ∞ (smoothKernel n) := by
  unfold smoothKernel
  exact ((bump n).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left (lsmul ℝ ℝ)
    ((bump n).contDiff_normed (μ := volume))
      ((EvenKernel.kernel_continuous 4).locallyIntegrable (μ := volume))

theorem radius_tends_zero : Tendsto (fun n : ℕ => (bump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem smoothKernel_tends (u : ℝ) :
    Tendsto (fun n : ℕ => smoothKernel n u) atTop (𝓝 (EvenKernel.kernel 4 u)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous radius_tends_zero
    (EvenKernel.kernel_continuous 4) u

theorem smoothKernel_nonneg (n : ℕ) (u : ℝ) : 0 ≤ smoothKernel n u := by
  unfold smoothKernel
  rw [convolution_def]
  apply integral_nonneg
  intro t
  change 0 ≤ (bump n).normed volume t * EvenKernel.kernel 4 (u - t)
  exact mul_nonneg ((bump n).nonneg_normed t) (EvenKernel.kernel_nonneg 4 _)

theorem smoothKernel_le_one (n : ℕ) (u : ℝ) : smoothKernel n u ≤ 1 := by
  have he : ConvolutionExistsAt ((bump n).normed volume) (fun _ : ℝ => (1 : ℝ))
      u (lsmul ℝ ℝ) volume := by
    simpa [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      ((bump n).integrable_normed (μ := volume))
  calc
    _ ≤ (((bump n).normed volume) ⋆[lsmul ℝ ℝ, volume] (fun _ : ℝ => (1 : ℝ))) u :=
      convolution_mono_right_of_nonneg he (fun t => (bump n).nonneg_normed t)
        (EvenKernel.kernel_le_one 4) (by intro _; norm_num)
    _ = 1 := (bump n).normed_convolution_eq_right (by intro _ _; rfl)

/-- All finite weighted populations have the required real limit. In particular,
this applies to the fixed larger prime-power population used in regularization. -/
theorem finite_population_limit (s : Finset ℕ) (C L : ℝ) (w : ℕ → ℝ) :
    Tendsto
      (fun j : ℕ => ∑ k ∈ s, smoothKernel j ((Real.log k - L) / EvenKernel.δ C L) * w k)
      atTop
      (𝓝 (∑ k ∈ s, EvenKernel.kernel 4 ((Real.log k - L) / EvenKernel.δ C L) * w k)) := by
  apply tendsto_finset_sum
  intro k _
  exact (smoothKernel_tends _).mul_const _

/-- Dominated convergence for actual mollified kernel integrals on any fixed
compact interval. It covers the main term and, after the log change of variable,
the nonsingular trivial-zero integral with its original normalization. -/
theorem weighted_interval_limit {a b : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.uIcc a b)) :
    Tendsto (fun j : ℕ => ∫ u in a..b, smoothKernel j u * g u)
      atTop (𝓝 (∫ u in a..b, EvenKernel.kernel 4 u * g u)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun u => |g u|)
  · exact Eventually.of_forall fun j =>
      (((smoothKernel_contDiff j).continuous.continuousOn.mul hg).mono
        uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact Eventually.of_forall fun j => Filter.Eventually.of_forall fun u _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (smoothKernel_nonneg j u)]
      simpa using mul_le_mul_of_nonneg_right (smoothKernel_le_one j u) (abs_nonneg (g u))
  · exact hg.abs.intervalIntegrable
  · exact Filter.Eventually.of_forall fun u _ => (smoothKernel_tends u).mul_const (g u)

theorem weighted_composed_interval_limit {a b : ℝ} {s g : ℝ → ℝ}
    (hs : ContinuousOn s (Set.uIcc a b)) (hg : ContinuousOn g (Set.uIcc a b)) :
    Tendsto (fun j : ℕ => ∫ u in a..b, smoothKernel j (s u) * g u)
      atTop (𝓝 (∫ u in a..b, EvenKernel.kernel 4 (s u) * g u)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun u => |g u|)
  · exact Eventually.of_forall fun j =>
      ((((smoothKernel_contDiff j).continuous.comp_continuousOn hs).mul hg).mono
        uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact Eventually.of_forall fun j => Filter.Eventually.of_forall fun u _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (smoothKernel_nonneg j (s u))]
      simpa using mul_le_mul_of_nonneg_right (smoothKernel_le_one j (s u)) (abs_nonneg (g u))
  · exact hg.abs.intervalIntegrable
  · exact Filter.Eventually.of_forall fun u _ => (smoothKernel_tends (s u)).mul_const (g u)

noncomputable def multiplier (n : ℕ) (y : ℝ) : ℝ :=
  ∫ t : ℝ, (bump n).normed volume t * Real.cos (y * t)

lemma multiplier_integrable (n : ℕ) (y : ℝ) :
    Integrable (fun t : ℝ => (bump n).normed volume t * Real.cos (y * t)) := by
  apply (bump n).integrable_normed.mono'
  · exact ((bump n).continuous_normed.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((bump n).nonneg_normed t)]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) ((bump n).nonneg_normed t)

theorem multiplier_abs_le_one (n : ℕ) (y : ℝ) : |multiplier n y| ≤ 1 := by
  calc
    _ ≤ ∫ t : ℝ, |(bump n).normed volume t * Real.cos (y * t)| := by
      simpa only [multiplier, Real.norm_eq_abs] using
        norm_integral_le_integral_norm
          (fun t : ℝ => (bump n).normed volume t * Real.cos (y * t))
    _ ≤ ∫ t : ℝ, (bump n).normed volume t := by
      apply integral_mono (multiplier_integrable n y).norm (bump n).integrable_normed
      intro t
      dsimp only
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((bump n).nonneg_normed t)]
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) ((bump n).nonneg_normed t)
    _ = 1 := (bump n).integral_normed

theorem multiplier_tends_one (y : ℝ) :
    Tendsto (fun n : ℕ => multiplier n y) atTop (𝓝 1) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (φ := bump) radius_tends_zero
    (show Continuous (fun t : ℝ => Real.cos (y * t)) by fun_prop) 0
  simpa [multiplier, convolution, mul_neg, Real.cos_neg] using h

noncomputable def regularizedPacket (n : ℕ) (C L : ℝ) (z : PsiSmoothing.Zero) : ℂ :=
  EvenKernel.zeroPacket 4 C L z * (multiplier n (EvenKernel.δ C L * z.val.im) : ℝ)

/-- The actual all-zero sum survives this specific normalized-bump Fourier
regularization. No cutoff or unproved tail statement occurs in this limit. -/
theorem regularized_full_zero_limit (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) :
    Tendsto (fun n : ℕ => ∑' z : PsiSmoothing.Zero, regularizedPacket n C L z)
      atTop (𝓝 (EvenKernel.zeroTerm 4 C L)) := by
  apply tendsto_tsum_of_dominated_convergence
    (RHOcticPush.Convergence.packet_norm_summable rh hN hδ)
  · intro z
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (multiplier_tends_one (EvenKernel.δ C L * z.val.im))
    simpa [regularizedPacket] using tendsto_const_nhds.mul h
  · exact Eventually.of_forall fun n z => by
      unfold regularizedPacket
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa using mul_le_mul_of_nonneg_left
        (multiplier_abs_le_one n (EvenKernel.δ C L * z.val.im)) (norm_nonneg _)

#print axioms smoothKernel_contDiff
#print axioms smoothKernel_tends
#print axioms smoothKernel_nonneg
#print axioms smoothKernel_le_one
#print axioms finite_population_limit
#print axioms weighted_interval_limit
#print axioms weighted_composed_interval_limit
#print axioms multiplier_abs_le_one
#print axioms regularized_full_zero_limit
end RHOcticPush.Mollifier
