import OcticFamilyMoments
import OcticStrict
import OcticBPTSourceEndpoint

/-! A separate stronger frontier. The original2.15 target remains unchanged.
The sharper coefficient1.8208 uses the same rational M0≤5.72 certificate output. -/
namespace RHOcticPush.StrongerFrontier
open Real Set
open RHOcticPush.MomentTransport RHLimit.OcticGeometry RHLimit.OcticPrimePowers
set_option maxHeartbeats 0

theorem zero_estimate_family_A (A : ℝ)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ A * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi)
    {C : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) :
    EvenKernel.ZeroEstimate 4 C A (3 / 2) (3 / 20) := by
  intro rh L hL
  have hD : 0 < EvenKernel.D C L := by
    unfold EvenKernel.D
    nlinarith [hC.1, mul_nonneg (show 0 ≤ C - 103 / 100 by linarith [hC.1])
      (show 0 ≤ L - 24 by linarith)]
  have hδ : 0 < EvenKernel.δ C L := by unfold EvenKernel.δ; positivity
  have hs := RHLimit.OcticGeometry.delta_small hC hL
  have hsmall : 12 * EvenKernel.δ C L ≤ 1 := by linarith
  have hbound := full_zero_bound_in_terms_of_moments rh hN hB hδ hsmall
  have hres := RHOcticPush.FamilyMoments.family_augmented_residual_lt hδ hs
  have hqsmall : 2 * Real.pi * EvenKernel.δ C L ≤ 1 := by
    nlinarith [Real.pi_lt_four, mul_nonneg hδ.le (show 0 ≤ 4 - Real.pi by linarith [Real.pi_lt_four])]
  have hlog : 0 ≤ log (1 / (2 * Real.pi * EvenKernel.δ C L)) :=
    Real.log_nonneg ((le_div_iff₀
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hδ)).mpr
        (by simpa using hqsmall))
  have hcap : (RHOcticPush.FourierMoments.M0 *
        log (1 / (2 * Real.pi * EvenKernel.δ C L)) +
          RHOcticPush.FourierMoments.M1) / Real.pi ≤
      A * log (1 / (2 * Real.pi * EvenKernel.δ C L)) + 3 / 2 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_right h0 hlog]
  rw [log_scale_identity hD] at hbound hcap
  linarith

theorem zero_estimate_fixed_A (A : ℝ)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ A * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi) :
    EvenKernel.ZeroEstimate 4 (43 / 20) A (3 / 2) (3 / 125) := by
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
      A * log (1 / (2 * Real.pi * EvenKernel.δ (43 / 20) L)) + 3 / 2 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_right h0 hlog]
  have hD : 0 < EvenKernel.D (43 / 20) L := by unfold EvenKernel.D; linarith
  rw [log_scale_identity hD] at hbound hcap
  linarith

lemma scalar_geometry_stronger {C : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) :
    EvenKernel.ScalarGeometry 4 C (1138 / 625) (3 / 2)
      (3 / 20) (29 / 500) (1 / 1000) (21 / 5) := by
  intro L hL
  obtain ⟨ha, hla, hab, hlog, hδ, hd, _, hη, _⟩ := scalar_geometry_family hC L hL
  refine ⟨ha, hla, hab, hlog, hδ, hd, ?_, hη, ?_⟩
  · norm_num [EvenKernel.countCoefficient, EvenKernel.mass]
    linarith [hC.1]
  · have hd' := D_family_lower hC.1 hL
    have hπ : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
    have hm := mul_le_mul hπ hd' (by norm_num : (0 : ℝ) ≤ 284 / 25) Real.pi_pos.le
    have harg : (71 : ℝ) ≤ 2 * Real.pi * EvenKernel.D C L := by nlinarith
    have hlo : (17 / 4 : ℝ) ≤ log (2 * Real.pi * EvenKernel.D C L) := by
      apply (Real.le_log_iff_exp_le (by linarith : 0 < 2 * Real.pi * EvenKernel.D C L)).mpr
      exact exp_seventeen_quarters_upper.le.trans harg
    norm_num [EvenKernel.mass]
    linarith

/-- Separate all-real stronger frontier, with both interval endpoints strictly
excluded. The two rational moment caps are the very same numerical workload. -/
theorem strict_count_family_18208
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ 143 / 25)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ 23 / 5)
    (rh : RiemannHypothesis) :
    ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
      (8 / 9 * C - 569 / 625 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ) := by
  have h0' : RHOcticPush.FourierMoments.M0 ≤ (1138 / 625) * Real.pi := by
    linarith [Real.pi_gt_d4]
  have h1' : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi := by
    linarith [Real.pi_gt_three, Real.pi_gt_d2]
  intro C hC
  have h := RHLimit.OcticStrict.open_count_from_kernel 4 C (1138 / 625) (3 / 2)
    (3 / 20) (29 / 500) (1 / 1000) (21 / 5) rh
    (RHOcticPush.ExplicitFormula.explicit_formula_from_general_sources hGreen hN hC)
    (zero_estimate_family_A (1138 / 625) hN
      (RHOcticPush.BPTSourceEndpoint.publishedBound_of_offOrdinate hB) h0' h1' hC)
    (primepower_cost_family 4 hC) (trivial_cost_family 4 hC)
    (scalar_geometry_stronger hC) (forward_coverage_family hC)
  norm_num [EvenKernel.countCoefficient, EvenKernel.mass] at h
  convert h using 1 <;> ring

/-- Width2.1492 supports the same positive4.2/log(u) excess above sqrt(u).
This is a separate rigorous improvement, conditional on the independent moment gate. -/
theorem strict_count_21492
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ 143 / 25)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ 23 / 5)
    (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (1 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u
          (u + 5373 / 2500 * sqrt u * log u)).card : ℝ) := by
  have h := strict_count_family_18208 hGreen hN hB h0 h1 rh
    (5373 / 2500) (by norm_num)
  norm_num at h
  exact h

lemma scalar_geometry_fixed_stronger :
    EvenKernel.ScalarGeometry 4 (43 / 20) (1138 / 625) (3 / 2)
      (3 / 125) (31 / 2000) (1 / 1000) (29 / 5) := by
  intro L hL
  obtain ⟨ha, hla, hab, hlog, hδ, hd, _, hη, _⟩ := scalar_geometry_215 L hL
  refine ⟨ha, hla, hab, hlog, hδ, hd, ?_, hη, ?_⟩
  · norm_num [EvenKernel.countCoefficient, EvenKernel.mass]
  · have hd' : (124 / 5 : ℝ) ≤ EvenKernel.D (43 / 20) L := by
      unfold EvenKernel.D
      linarith
    have hπ : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
    have hm := mul_le_mul hπ hd' (by norm_num : (0 : ℝ) ≤ 124 / 5) Real.pi_pos.le
    have harg : (154 : ℝ) ≤ 2 * Real.pi * EvenKernel.D (43 / 20) L := by nlinarith
    have hlo : (161 / 32 : ℝ) ≤ log (2 * Real.pi * EvenKernel.D (43 / 20) L) := by
      apply (Real.le_log_iff_exp_le
        (by linarith : 0 < 2 * Real.pi * EvenKernel.D (43 / 20) L)).mpr
      exact exp_161_32_upper.le.trans harg
    norm_num [EvenKernel.mass]
    linarith

/-- At the original width and onset, a strictly larger uniform prime population:
the leading coefficient grows by exactly3/5000, with the same5.8/log(u) term. -/
theorem strict_count_215_stronger
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ 143 / 25)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ 23 / 5)
    (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (5629 / 5625 + (29 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 43 / 20 * sqrt u * log u)).card : ℝ) := by
  have h0' : RHOcticPush.FourierMoments.M0 ≤ (1138 / 625) * Real.pi := by
    linarith [Real.pi_gt_d4]
  have h1' : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi := by
    linarith [Real.pi_gt_d2]
  have h := RHLimit.OcticStrict.open_count_from_kernel 4 (43 / 20) (1138 / 625) (3 / 2)
    (3 / 125) (31 / 2000) (1 / 1000) (29 / 5) rh
    (RHOcticPush.ExplicitFormula.explicit_formula_from_general_sources hGreen hN (by norm_num))
    (zero_estimate_fixed_A (1138 / 625) hN
      (RHOcticPush.BPTSourceEndpoint.publishedBound_of_offOrdinate hB) h0' h1')
    primepower_cost_215 trivial_cost_215 scalar_geometry_fixed_stronger forward_coverage_215
  norm_num [EvenKernel.countCoefficient, EvenKernel.mass] at h
  exact h

/-- A narrower2.1493 interval with a uniform positive leading excess1/11250;
this supports a liminf strictly greater than1, unlike an excess only of order1/log(u). -/
theorem strict_count_21493_uniform_excess
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ 143 / 25)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ 23 / 5)
    (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (11251 / 11250 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u
          (u + 21493 / 10000 * sqrt u * log u)).card : ℝ) := by
  have h := strict_count_family_18208 hGreen hN hB h0 h1 rh
    (21493 / 10000) (by norm_num)
  norm_num at h
  exact h

theorem prime_count_215_stronger
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ 143 / 25)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ 23 / 5)
    (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (5629 / 5625 + (29 / 5) / log u) * sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * sqrt u * log u) -
          QuarticWindow.primeCounting u := by
  intro u hu
  have hu0 : 0 ≤ u := (Real.exp_pos 24).le.trans hu
  have hu1 : 1 ≤ u := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 24)).trans hu
  have hlog : 0 ≤ log u := Real.log_nonneg hu1
  have hab : u ≤ u + (43 / 20) * sqrt u * log u :=
    le_add_of_nonneg_right (by positivity)
  exact (strict_count_215_stronger hGreen hN hB h0 h1 rh u hu).trans_le
    (QuarticWindow.count_le_primeCounting_difference hu0 hab)

#print axioms zero_estimate_family_A
#print axioms strict_count_family_18208
#print axioms strict_count_21492
#print axioms strict_count_21493_uniform_excess
#print axioms prime_count_215_stronger
end RHOcticPush.StrongerFrontier
