import OcticBPTInfinite
import OcticConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace RHOcticPush.BPTSpecialization
open Real Set MeasureTheory Filter
open RHOcticPush.DerivativeBounds RHLimit.BPTZeroCount
set_option maxHeartbeats 0

lemma log_inverse_primitive_derivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => -(log t + 1) / t) (log t / t ^ 2) t := by
  apply ((((Real.hasDerivAt_log ht.ne').add_const 1).neg).div
    (hasDerivAt_id t) ht.ne').congr_deriv
  dsimp
  field_simp
  ring

lemma log_inverse_primitive_limit :
    Tendsto (fun t : ℝ => -(log t + 1) / t) atTop (nhds 0) := by
  have hlog : Tendsto (fun t : ℝ => log t / t) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hi : Tendsto (fun t : ℝ => 1 / t) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  simpa only [neg_div, add_div, neg_zero, add_zero] using (hlog.add hi).neg

lemma log_sq_integrable {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn (fun t : ℝ => log t / t ^ 2) (Ioi a) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := fun t : ℝ => -(log t + 1) / t)
    (l := 0) _ _ log_inverse_primitive_limit
  · intro t ht
    exact log_inverse_primitive_derivative (by linarith [ht.out])
  · intro t ht
    exact div_nonneg (log_nonneg (ha.trans ht.le)) (sq_nonneg t)

lemma log_sq_tends_zero :
    Tendsto (fun t : ℝ => log t / t ^ 2) atTop (nhds 0) := by
  have hlog : Tendsto (fun t : ℝ => log t / t) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hi : Tendsto (fun t : ℝ => 1 / t) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  convert hlog.mul hi using 1 <;> simp [div_eq_mul_inv, pow_two, mul_assoc]

lemma integrable_abs_mul_log_of_decay {a K : ℝ} (ha : 1 ≤ a)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi a))
    (hbound : ∀ t ∈ Ioi a, |f t| ≤ K / t ^ 2) :
    IntegrableOn (fun t : ℝ => |f t| * log t) (Ioi a) := by
  have hm := (log_sq_integrable ha).const_mul K
  have hlog : ContinuousOn log (Ioi a) := by
    intro t ht
    exact (continuousAt_log (by linarith [ht.out])).continuousWithinAt
  apply hm.mono' ((hf.abs.mul hlog).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hlog0 : 0 ≤ log t := log_nonneg (ha.trans ht.le)
  change |(|f t| * log t)| ≤ _
  rw [abs_mul, abs_abs, abs_of_nonneg hlog0]
  calc
    |f t| * log t ≤ (K / t ^ 2) * log t :=
      mul_le_mul_of_nonneg_right (hbound t ht) hlog0
    _ = K * (log t / t ^ 2) := by ring

lemma abs_mul_log_tends_zero_of_decay {K : ℝ} {f : ℝ → ℝ}
    (hbound : ∀ᶠ t : ℝ in atTop, |f t| ≤ K / t ^ 2) :
    Tendsto (fun t : ℝ => |f t| * log t) atTop (nhds 0) := by
  apply squeeze_zero' _ _ (by simpa using log_sq_tends_zero.const_mul K)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact mul_nonneg (abs_nonneg _) (log_nonneg ht)
  · filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with t h ht
    calc
      |f t| * log t ≤ (K / t ^ 2) * log t :=
        mul_le_mul_of_nonneg_right h (log_nonneg ht)
      _ = K * (log t / t ^ 2) := by ring

lemma density_le_log {t : ℝ} (ht : 2 * Real.pi ≤ t) :
    0 ≤ density t ∧ density t ≤ log t / (2 * Real.pi) := by
  have hp : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 * Real.pi) ht
  refine ⟨RHLimit.AbsoluteStieltjes.density_nonneg ht, ?_⟩
  unfold density
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [log_div ht0.ne' (by positivity : (2 * Real.pi) ≠ 0)]
  linarith [log_nonneg hp]

lemma density_integrable {a : ℝ} (ha : 2 * Real.pi ≤ a)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi a))
    (hlog : IntegrableOn (fun t => |f t| * log t) (Ioi a)) :
    IntegrableOn (fun t => |f t| * density t) (Ioi a) := by
  have hm := hlog.div_const (2 * Real.pi)
  have hd : ContinuousOn density (Ioi a) := by
    intro t ht
    unfold density
    have ht0 : 0 < t := by linarith [ht.out, Real.pi_pos]
    exact (((continuousAt_id.div_const (2 * Real.pi)).log
      (div_ne_zero ht0.ne' (by positivity))).div_const _).continuousWithinAt
  apply hm.mono' ((hf.abs.mul hd).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hden := density_le_log (ha.trans ht.le)
  change |(|f t| * density t)| ≤ _
  rw [abs_mul, abs_abs, abs_of_nonneg hden.1]
  calc
    |f t| * density t ≤ |f t| * (log t / (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hden.2 (abs_nonneg _)
    _ = (|f t| * log t) / (2 * Real.pi) := by ring

noncomputable def packet (δ t : ℝ) := δ * EvenKernel.transform 4 (δ * t)
noncomputable def packetDeriv (δ t : ℝ) := δ ^ 2 * first (δ * t)

lemma packet_derivative (δ t : ℝ) : HasDerivAt (packet δ) (packetDeriv δ t) t := by
  apply (((transform_hasDerivAt (δ * t)).comp t
    ((hasDerivAt_id t).const_mul δ)).const_mul δ).congr_deriv
  dsimp [packetDeriv]
  ring

lemma packet_continuous (δ : ℝ) : Continuous (packet δ) :=
  continuous_iff_continuousAt.mpr (fun t => (packet_derivative δ t).continuousAt)

lemma packetDeriv_continuous (δ : ℝ) : Continuous (packetDeriv δ) := by
  have hc : Continuous first :=
    continuous_iff_continuousAt.mpr (fun t => (first_hasDerivAt t).continuousAt)
  exact continuous_const.mul (hc.comp (continuous_const.mul continuous_id))

lemma packet_decay {δ t : ℝ} (hδ : 0 < δ) (ht : t ≠ 0) :
    |packet δ t| ≤ (32 / δ) / t ^ 2 := by
  rw [packet, abs_mul, abs_of_pos hδ]
  calc
    _ ≤ δ * (32 / (δ * t) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (RHOcticPush.Decay.transform_abs_le_decay (mul_ne_zero hδ.ne' ht)) hδ.le
    _ = _ := by field_simp <;> ring

lemma packetDeriv_decay {δ t : ℝ} (hδ : 0 < δ) (ht : t ≠ 0) :
    |packetDeriv δ t| ≤ 34 / t ^ 2 := by
  rw [packetDeriv, abs_mul, abs_of_nonneg (sq_nonneg δ)]
  calc
    _ ≤ δ ^ 2 * (34 / (δ * t) ^ 2) :=
      mul_le_mul_of_nonneg_left (first_abs_le_decay (mul_ne_zero hδ.ne' ht)) (sq_nonneg δ)
    _ = _ := by field_simp <;> ring

/-- Actual infinite scaled-octic BPT estimate. Every convergence, regularity and
boundary premise of the general infinite transport is proved here, for all δ>0. -/
theorem octic_infinite_bound (h : PublishedBound) {δ a : ℝ}
    (hδ : 0 < δ) (ha : 2 * Real.pi ≤ a) :
    Summable (fun z : RHOcticPush.BPTInfinite.PositiveZero a =>
      |packet δ z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ∧
    (∑' z : RHOcticPush.BPTInfinite.PositiveZero a,
      |packet δ z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ≤
      (∫ t in Ioi a, |packet δ t| * density t) +
      (7 / 25) * (|packet δ a| * log a +
        ∫ t in Ioi a, |packetDeriv δ t| * log t) := by
  have ha1 : 1 ≤ a := by linarith [Real.pi_gt_three]
  have hnone (t : ℝ) (ht : t ∈ Ioi a) : t ≠ 0 := by linarith [ht.out]
  apply RHOcticPush.BPTInfinite.infinite_absolute_bound h ha
    (fun t _ => packet_derivative δ t) (packetDeriv_continuous δ).continuousOn
  · apply density_integrable ha (packet_continuous δ).continuousOn
    exact integrable_abs_mul_log_of_decay ha1 (packet_continuous δ).continuousOn
      (fun t ht => packet_decay hδ (hnone t ht))
  · exact integrable_abs_mul_log_of_decay ha1 (packetDeriv_continuous δ).continuousOn
      (fun t ht => packetDeriv_decay hδ (hnone t ht))
  · apply abs_mul_log_tends_zero_of_decay
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact packet_decay hδ ht.ne'

#print axioms log_sq_integrable
#print axioms octic_infinite_bound
end RHOcticPush.BPTSpecialization
