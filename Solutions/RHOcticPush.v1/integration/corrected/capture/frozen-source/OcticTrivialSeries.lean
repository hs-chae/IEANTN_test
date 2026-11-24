import OcticIntegralLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A genuine all-trivial-zero geometric-series integral. Summability is an
explicit *derived* input at the generic interchange theorem, not an asserted
value of an infinite sum. The complete source adapter supplies that input. -/
namespace RHOcticPush.TrivialSeries
open Real Set Filter MeasureTheory
open RHOcticPush.Mollifier RHOcticPush.PhysicalWeight RHOcticPush.IntegralLimits
set_option maxHeartbeats 0

noncomputable def term (j : ℕ) (C L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  logWeight j C L t / t * (1 / t ^ 2) ^ (n + 1)

lemma weight_nonneg (j : ℕ) (C L t : ℝ) : 0 ≤ logWeight j C L t := by
  unfold logWeight
  split_ifs
  · exact div_nonneg (smoothKernel_nonneg _ _) (Real.sqrt_nonneg _)
  · rfl

lemma support_gt_one (j : ℕ) {C L t : ℝ} (hδ : 0 < EvenKernel.δ C L)
    (hgap : 0 < L - 2 * EvenKernel.δ C L) (ht : logWeight j C L t ≠ 0) : 1 < t :=
  (Real.one_lt_exp_iff.mpr hgap).trans (logWeight_support j hδ ht).1

lemma term_nonneg (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L)
    (hgap : 0 < L - 2 * EvenKernel.δ C L) (n : ℕ) (t : ℝ) : 0 ≤ term j C L n t := by
  by_cases hw : logWeight j C L t = 0
  · simp [term, hw]
  · have ht : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) (support_gt_one j hδ hgap hw)
    exact mul_nonneg (div_nonneg (weight_nonneg _ _ _ _) ht.le) (by positivity)

lemma term_le_weight (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L)
    (hgap : 0 < L - 2 * EvenKernel.δ C L) (n : ℕ) (t : ℝ) :
    term j C L n t ≤ logWeight j C L t := by
  by_cases hw : logWeight j C L t = 0
  · simp [term, hw]
  · have ht1 := support_gt_one j hδ hgap hw
    have ht : 0 < t := by linarith
    have hr0 : 0 ≤ 1 / t ^ 2 := by positivity
    have hr1 : 1 / t ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos ht)).mpr (by nlinarith)
    have hp : (1 / t ^ 2) ^ (n + 1) ≤ 1 := pow_le_one₀ hr0 hr1
    have hw0 := weight_nonneg j C L t
    unfold term
    calc _ ≤ (logWeight j C L t / t) * 1 :=
           mul_le_mul_of_nonneg_left hp (div_nonneg hw0 ht.le)
         _ ≤ logWeight j C L t := by
           rw [mul_one]
           apply (div_le_iff₀ ht).mpr
           nlinarith

theorem term_integrable (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L)
    (hgap : 0 < L - 2 * EvenKernel.δ C L) (n : ℕ) :
    Integrable (term j C L n) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hw : Integrable (logWeight j C L) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((logWeight_contDiff j hδ).continuous.integrable_of_hasCompactSupport
      (logWeight_compact j hδ)).integrableOn
  have hwm : Measurable (logWeight j C L) := (logWeight_contDiff j hδ).continuous.measurable
  apply hw.mono'
  · have hm : Measurable (term j C L n) := by unfold term; fun_prop
    exact hm.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg j hδ hgap n t)]
      exact term_le_weight j hδ hgap n t

theorem pointwise_geometric_sum (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L)
    (hgap : 0 < L - 2 * EvenKernel.δ C L) (t : ℝ) :
    (∑' n : ℕ, term j C L n t) = logWeight j C L t / (t * (t ^ 2 - 1)) := by
  by_cases hw : logWeight j C L t = 0
  · simp [term, hw]
  · have ht1 := support_gt_one j hδ hgap hw
    have ht : 0 < t := by linarith
    have hr0 : 0 ≤ 1 / t ^ 2 := by positivity
    have hr1 : 1 / t ^ 2 < 1 := (div_lt_one (sq_pos_of_pos ht)).mpr (by nlinarith)
    have hs : (∑' n : ℕ, (1 / t ^ 2) ^ n) = (1 - 1 / t ^ 2)⁻¹ := tsum_geometric_of_norm_lt_one
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
    have he : (fun n : ℕ => term j C L n t) = fun n =>
        (logWeight j C L t / t * (1 / t ^ 2)) * (1 / t ^ 2) ^ n := by
      funext n
      unfold term
      rw [pow_succ]
      ring
    rw [he, tsum_mul_left, hs]
    have hsq : t ^ 2 - 1 ≠ 0 := by nlinarith
    have hr : 1 - 1 / t ^ 2 ≠ 0 := by linarith
    field_simp [ht.ne', hsq, hr]

theorem integrated_geometric_sum (j : ℕ) {C L : ℝ} (hδ : 0 < EvenKernel.δ C L)
    (hgap : 0 < L - 2 * EvenKernel.δ C L)
    (hs : Summable (fun n : ℕ => ∫ t in Set.Ioi (0 : ℝ), term j C L n t)) :
    (∑' n : ℕ, ∫ t in Set.Ioi (0 : ℝ), term j C L n t) = smoothTrivial j C L := by
  have hnorm (n : ℕ) : (∫ t in Set.Ioi (0 : ℝ), ‖term j C L n t‖) =
      ∫ t in Set.Ioi (0 : ℝ), term j C L n t := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => Real.norm_of_nonneg (term_nonneg j hδ hgap n t)
  have hn : Summable (fun n : ℕ => ∫ t in Set.Ioi (0 : ℝ), ‖term j C L n t‖) :=
    hs.congr (fun n => (hnorm n).symm)
  rw [integral_tsum_of_summable_integral_norm (fun n => term_integrable j hδ hgap n) hn]
  simp_rw [pointwise_geometric_sum j hδ hgap]
  let g : ℝ → ℝ := fun t => logWeight j C L t / (t * (t ^ 2 - 1))
  have hg : Function.support g ⊆ Set.Ioo (Real.exp (L - 2 * EvenKernel.δ C L))
      (Real.exp (L + 2 * EvenKernel.δ C L)) := by
    intro t ht
    have hw : logWeight j C L t ≠ 0 := by intro hw; exact ht (by simp [g, hw])
    exact logWeight_support j hδ hw
  have hpos : (∫ t in Set.Ioi (0 : ℝ), g t) = ∫ t : ℝ, g t := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1
    apply Set.indicator_eq_self.mpr
    intro t ht
    exact (Real.exp_pos _).trans (hg ht).1
  have hwide := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume)
    (show Function.support g ⊆ Set.Ioc (Real.exp (L - 2 * EvenKernel.δ C L))
      (Real.exp (L + 2 * EvenKernel.δ C L)) from
      fun t ht => Set.Ioo_subset_Ioc_self (hg ht))
  change (∫ t in Set.Ioi (0 : ℝ), g t) = _
  rw [hpos, ← hwide]
  apply intervalIntegral.integral_congr
  intro t ht
  have hAB : Real.exp (L - 2 * EvenKernel.δ C L) ≤
      Real.exp (L + 2 * EvenKernel.δ C L) := Real.exp_le_exp.mpr (by linarith)
  rw [Set.uIcc_of_le hAB] at ht
  have ht0 : 0 < t := (Real.exp_pos _).trans_le ht.1
  dsimp [g, logWeight]
  rw [if_pos ht0, div_div]
  congr 1
  ring

#print axioms term_integrable
#print axioms pointwise_geometric_sum
#print axioms integrated_geometric_sum
end RHOcticPush.TrivialSeries
