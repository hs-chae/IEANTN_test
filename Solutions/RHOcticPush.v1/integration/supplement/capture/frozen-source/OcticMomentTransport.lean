import OcticDerivativeMoments
import OcticFourierMoments
import OcticZeroPairing
import OcticZeroAllowance

/-! Exact scaling and logarithmic transport for the infinite octic zero bound. -/
namespace RHOcticPush.MomentTransport
open Real Set MeasureTheory
open RHOcticPush.DerivativeBounds RHOcticPush.DerivativeMoments
open RHOcticPush.BPTSpecialization
set_option maxHeartbeats 0

lemma first_log_integrable_small {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    IntegrableOn (fun y : ℝ => |first y| * log y) (Ioi c) := by
  have hlog : ContinuousOn log (uIcc c 1) := by
    rw [uIcc_of_le hc1]
    intro y hy
    exact (continuousAt_log (ne_of_gt (hc.trans_le hy.1))).continuousWithinAt
  have hlo : IntegrableOn (fun y : ℝ => |first y| * log y) (Ioc c 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc1).mp
      ((first_continuous.abs.continuousOn.mul hlog).intervalIntegrable)
  rw [← Ioc_union_Ioi_eq_Ioi hc1, integrableOn_union]
  exact ⟨hlo, first_log_integrable⟩

lemma first_log_integral_small_lt {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ y in Ioi c, |first y| * log y) < 24 := by
  have hs := first_log_integrable_small hc hc1
  have hlo : IntegrableOn (fun y : ℝ => |first y| * log y) (Ioc c 1) :=
    hs.mono_set Ioc_subset_Ioi_self
  have he : (∫ y in Ioi c, |first y| * log y) =
      (∫ y in Ioc c 1, |first y| * log y) +
        ∫ y in Ioi (1 : ℝ), |first y| * log y := by
    rw [← Ioc_union_Ioi_eq_Ioi hc1]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hlo first_log_integrable
  have hneg : (∫ y in Ioc c 1, |first y| * log y) ≤ 0 := by
    apply setIntegral_nonpos measurableSet_Ioc
    intro y hy
    exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      (Real.log_nonpos (hc.trans hy.1).le hy.2)
  rw [he]
  linarith [first_log_integral_lt]

lemma first_integral_small_le {c : ℝ} (hc : 0 ≤ c) :
    (∫ y in Ioi c, |first y|) ≤ 117 / 10 := by
  apply le_trans _ first_integral_le
  exact setIntegral_mono_set first_integrable (by filter_upwards with y; positivity)
    (Filter.Eventually.of_forall (fun y hy => hc.trans_lt hy))

lemma derivative_log_moment_bound {δ : ℝ} (hδ : 0 < δ) (hsmall : 12 * δ ≤ 1) :
    (∫ y in Ioi (12 * δ), |first y| * log (y / δ)) ≤
      12 * log (1 / δ) + 24 := by
  have hc : 0 < 12 * δ := by positivity
  have hδ1 : δ ≤ 1 := by linarith
  have hlogδ : 0 ≤ log (1 / δ) := Real.log_nonneg
    ((le_div_iff₀ hδ).mpr (by simpa using hδ1))
  have hfirst := first_integrable.mono_set (Ioi_subset_Ioi hc.le)
  have hlog := first_log_integrable_small hc hsmall
  have he : (∫ y in Ioi (12 * δ), |first y| * log (y / δ)) =
      log (1 / δ) * (∫ y in Ioi (12 * δ), |first y|) +
        ∫ y in Ioi (12 * δ), |first y| * log y := by
    calc
      _ = ∫ y in Ioi (12 * δ), log (1 / δ) * |first y| + |first y| * log y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        have hy0 : y ≠ 0 := ne_of_gt (hc.trans hy)
        dsimp only
        rw [Real.log_div hy0 hδ.ne', Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hδ.ne',
          Real.log_one]
        ring
      _ = _ := by rw [integral_add (hfirst.const_mul _) hlog, integral_const_mul]
  rw [he]
  have h0 := mul_le_mul_of_nonneg_left (first_integral_small_le hc.le) hlogδ
  have h1 := first_log_integral_small_lt hc hsmall
  nlinarith

lemma scaled_derivative_log_eq {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in Ioi (12 : ℝ), |packetDeriv δ t| * log t) =
      δ * ∫ y in Ioi (12 * δ), |first y| * log (y / δ) := by
  have he : (fun t : ℝ => |packetDeriv δ t| * log t) =
      fun t => δ ^ 2 * (|first (δ * t)| * log ((δ * t) / δ)) := by
    funext t
    rw [packetDeriv, abs_mul, abs_of_nonneg (sq_nonneg δ), mul_div_cancel_left₀ _ hδ.ne']
    ring
  rw [he, integral_const_mul, integral_comp_mul_left_Ioi
    (fun y : ℝ => |first y| * log (y / δ)) 12 hδ]
  simp only [smul_eq_mul]
  rw [mul_comm δ 12]
  field_simp

theorem scaled_derivative_log_le {δ : ℝ} (hδ : 0 < δ) (hsmall : 12 * δ ≤ 1) :
    (∫ t in Ioi (12 : ℝ), |packetDeriv δ t| * log t) ≤
      δ * (12 * log (1 / δ) + 24) := by
  rw [scaled_derivative_log_eq hδ]
  exact mul_le_mul_of_nonneg_left (derivative_log_moment_bound hδ hsmall) hδ.le

lemma scaled_density_integral_eq {δ : ℝ} (hδ : 0 < δ) :
    2 * (∫ t in Ioi (12 : ℝ), |packet δ t| * RHLimit.BPTZeroCount.density t) =
      (1 / Real.pi) * ∫ y in Ioi (12 * δ),
        RHOcticPush.FourierMoments.F y * log (y / (2 * Real.pi * δ)) := by
  let g := fun y : ℝ => RHOcticPush.FourierMoments.F y * log (y / (2 * Real.pi * δ))
  have he : (fun t : ℝ => |packet δ t| * RHLimit.BPTZeroCount.density t) =
      fun t : ℝ => (δ / (2 * Real.pi)) * g (δ * t) := by
    funext t
    have hr : (δ * t) / (2 * Real.pi * δ) = t / (2 * Real.pi) := by
      field_simp
    simp only [packet, abs_mul, abs_of_pos hδ, RHLimit.BPTZeroCount.density,
      g, RHOcticPush.FourierMoments.F, hr]
    ring
  rw [he, integral_const_mul, integral_comp_mul_left_Ioi g 12 hδ]
  simp only [smul_eq_mul]
  rw [mul_comm δ 12]
  dsimp [g]
  field_simp

lemma scaled_density_integral_le {δ : ℝ} (hδ : 0 < δ) :
    2 * (∫ t in Ioi (12 : ℝ), |packet δ t| * RHLimit.BPTZeroCount.density t) ≤
      (RHOcticPush.FourierMoments.M0 * log (1 / (2 * Real.pi * δ)) +
        RHOcticPush.FourierMoments.M1) / Real.pi + (64 / 9) * δ := by
  have hq : 0 < 2 * Real.pi * δ := by positivity
  have hqc : 2 * Real.pi * δ ≤ 12 * δ :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) hδ.le
  have h := RHOcticPush.FourierMoments.truncated_ratio_integral_le
    (show 0 < 12 * δ by positivity) hq hqc
  rw [scaled_density_integral_eq hδ]
  calc
    _ ≤ (1 / Real.pi) * (RHOcticPush.FourierMoments.M0 *
          log (1 / (2 * Real.pi * δ)) + RHOcticPush.FourierMoments.M1 +
            (16 / 9) * (12 * δ)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (RHOcticPush.FourierMoments.M0 * log (1 / (2 * Real.pi * δ)) +
        RHOcticPush.FourierMoments.M1) / Real.pi + ((64 / 3) * δ) / Real.pi := by ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply (div_le_iff₀ Real.pi_pos).mpr
      nlinarith [mul_nonneg hδ.le (show 0 ≤ Real.pi - 3 by linarith [Real.pi_gt_three])]

lemma boundary_packet_le {δ : ℝ} (hδ : 0 < δ) :
    |packet δ 12| * log 12 ≤ ((16 / 9) * δ) * log 12 := by
  have hm := RHOcticPush.Decay.transform_abs_le_mass 4 (δ * 12)
  norm_num [EvenKernel.mass] at hm
  rw [packet, abs_mul, abs_of_pos hδ]
  exact mul_le_mul_of_nonneg_right (by nlinarith)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 12))

/-- Every infinite zero and analytic transport is proved. The two moment caps
are explicit actual integral conditions, to be supplied by separate kernel proofs. -/
theorem full_zero_bound_in_terms_of_moments (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound) {C L : ℝ}
    (hδ : 0 < EvenKernel.δ C L) (hsmall : 12 * EvenKernel.δ C L ≤ 1) :
    ‖EvenKernel.zeroTerm 4 C L‖ ≤
      (RHOcticPush.FourierMoments.M0 * log (1 / (2 * Real.pi * EvenKernel.δ C L)) +
        RHOcticPush.FourierMoments.M1) / Real.pi +
      RHOcticPush.ZeroAllowance.residual (EvenKernel.δ C L) +
        32 * EvenKernel.δ C L / 9 := by
  have hz := RHOcticPush.ZeroPairing.zeroTerm_norm_le_BPT_integrals rh hN hB hδ
  have hm := scaled_density_integral_le hδ
  have hd := scaled_derivative_log_le hδ hsmall
  have hb := boundary_packet_le hδ
  unfold RHOcticPush.ZeroAllowance.residual
  nlinarith

lemma augmented_residual_lt {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / 6000) :
    RHOcticPush.ZeroAllowance.residual δ + 32 * δ / 9 < 3 / 125 := by
  have h := RHOcticPush.ZeroAllowance.residual_lt_fourteen_thousandths hδ hsmall
  linarith

lemma log_scale_identity {C L : ℝ} (hD : 0 < EvenKernel.D C L) :
    log (1 / (2 * Real.pi * EvenKernel.δ C L)) =
      L / 2 - log (2 * Real.pi * EvenKernel.D C L) := by
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (by unfold EvenKernel.δ; positivity), Real.log_one,
    Real.log_mul (by positivity : (2 * Real.pi) ≠ 0)
      (by unfold EvenKernel.δ; positivity)]
  unfold EvenKernel.δ
  rw [Real.log_mul hD.ne' (by positivity : Real.exp (-L / 2) ≠ 0), Real.log_exp,
    Real.log_mul (by positivity : (2 * Real.pi) ≠ 0) hD.ne']
  ring

/-- The original sharp infinite ZeroEstimate follows from two actual moment caps.
No analytically equivalent zero estimate is reintroduced as a premise. -/
theorem sharp_zero_estimate_from_moments
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ (911 / 500) * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi) :
    EvenKernel.ZeroEstimate 4 (43 / 20) (911 / 500) (3 / 2) (3 / 125) := by
  intro rh L hL
  have hs := RHOcticPush.ZeroAllowance.fixed_delta_small hL
  have hsmall : 12 * EvenKernel.δ (43 / 20) L ≤ 1 := by linarith [hs.2]
  have hbound := full_zero_bound_in_terms_of_moments rh hN hB hs.1 hsmall
  have hres := augmented_residual_lt hs.1 hs.2
  have hqsmall : 2 * Real.pi * EvenKernel.δ (43 / 20) L ≤ 1 := by
    nlinarith [Real.pi_lt_four, mul_nonneg hs.1.le (show 0 ≤ 4 - Real.pi by linarith [Real.pi_lt_four])]
  have hlog : 0 ≤ log (1 / (2 * Real.pi * EvenKernel.δ (43 / 20) L)) :=
    Real.log_nonneg ((le_div_iff₀
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hs.1)).mpr
        (by simpa using hqsmall))
  have hcap : (RHOcticPush.FourierMoments.M0 *
        log (1 / (2 * Real.pi * EvenKernel.δ (43 / 20) L)) +
          RHOcticPush.FourierMoments.M1) / Real.pi ≤
      (911 / 500) * log (1 / (2 * Real.pi * EvenKernel.δ (43 / 20) L)) + 3 / 2 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_right h0 hlog]
  have hD : 0 < EvenKernel.D (43 / 20) L := by unfold EvenKernel.D; linarith
  rw [log_scale_identity hD] at hbound hcap
  linarith

#print axioms scaled_density_integral_le
#print axioms full_zero_bound_in_terms_of_moments
#print axioms sharp_zero_estimate_from_moments
end RHOcticPush.MomentTransport
