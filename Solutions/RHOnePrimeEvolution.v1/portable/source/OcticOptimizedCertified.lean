import OcticStrongMomentCaps
import OcticFamilyMoments
import OcticStrict
import OcticBPTSourceEndpoint
import OcticExplicitFormula
import GoldbachTripleCount

/-! Bounded final stronger frontier from the SAME fixed7301-row kernel certificate.
The actual numerical caps are no-argument theorems; all analytic inputs, full real
rays and finite Goldbach verification remain explicit. No optimality is asserted. -/
namespace RHOcticPush.OptimizedFinal
open Real Set
open RHOcticPush RHOcticPush.MomentTransport RHLimit.OcticGeometry RHLimit.OcticPrimePowers
set_option maxHeartbeats 0

lemma optimized_moment_caps :
    FourierMoments.M0 ≤ (18203 / 10000) * Real.pi ∧
    FourierMoments.M1 ≤ (1457 / 1000) * Real.pi := by
  constructor
  · have h := Moments.Endpoint.actual_M0_strong
    linarith [Real.pi_gt_d4]
  · have h := Moments.Endpoint.actual_M1_strong
    linarith [Real.pi_gt_d4]

theorem zero_estimate_family (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate)
    {C : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) :
    EvenKernel.ZeroEstimate 4 C (18203 / 10000) (1457 / 1000) (3 / 20) := by
  obtain ⟨h0, h1⟩ := optimized_moment_caps
  have hB' := BPTSourceEndpoint.publishedBound_of_offOrdinate hB
  intro rh L hL
  have hD : 0 < EvenKernel.D C L := by
    unfold EvenKernel.D
    nlinarith [hC.1, mul_nonneg (show 0 ≤ C - 103 / 100 by linarith [hC.1])
      (show 0 ≤ L - 24 by linarith)]
  have hδ : 0 < EvenKernel.δ C L := by unfold EvenKernel.δ; positivity
  have hs := RHLimit.OcticGeometry.delta_small hC hL
  have hsmall : 12 * EvenKernel.δ C L ≤ 1 := by linarith
  have hbound := full_zero_bound_in_terms_of_moments rh hN hB' hδ hsmall
  have hres := FamilyMoments.family_augmented_residual_lt hδ hs
  have hqsmall : 2 * Real.pi * EvenKernel.δ C L ≤ 1 := by
    nlinarith [Real.pi_lt_four, mul_nonneg hδ.le (show 0 ≤ 4 - Real.pi by linarith [Real.pi_lt_four])]
  have hlog : 0 ≤ log (1 / (2 * Real.pi * EvenKernel.δ C L)) :=
    Real.log_nonneg ((le_div_iff₀
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hδ)).mpr
        (by simpa using hqsmall))
  have hcap : (RHOcticPush.FourierMoments.M0 *
        log (1 / (2 * Real.pi * EvenKernel.δ C L)) +
          RHOcticPush.FourierMoments.M1) / Real.pi ≤
      (18203 / 10000) * log (1 / (2 * Real.pi * EvenKernel.δ C L)) + 1457 / 1000 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_right h0 hlog]
  rw [log_scale_identity hD] at hbound hcap
  linarith

theorem zero_estimate_215 (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) :
    EvenKernel.ZeroEstimate 4 (43 / 20) (18203 / 10000) (1457 / 1000) (3 / 125) := by
  obtain ⟨h0, h1⟩ := optimized_moment_caps
  have hB' := BPTSourceEndpoint.publishedBound_of_offOrdinate hB
  intro rh L hL
  have hs := RHOcticPush.ZeroAllowance.fixed_delta_small hL
  have hsmall : 12 * EvenKernel.δ (43 / 20) L ≤ 1 := by linarith [hs.2]
  have hbound := full_zero_bound_in_terms_of_moments rh hN hB' hs.1 hsmall
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
      (18203 / 10000) * log (1 / (2 * Real.pi * EvenKernel.δ (43 / 20) L)) + 1457 / 1000 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_right h0 hlog]
  have hD : 0 < EvenKernel.D (43 / 20) L := by unfold EvenKernel.D; linarith
  rw [log_scale_identity hD] at hbound hcap
  linarith

lemma scalar_geometry_family {C : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) :
    EvenKernel.ScalarGeometry 4 C (18203 / 10000) (1457 / 1000)
      (3 / 20) (29 / 500) (1 / 1000) (21 / 5) := by
  intro L hL
  obtain ⟨ha, hla, hab, hlog, hδ, hd, _, hη, _⟩ := RHLimit.OcticGeometry.scalar_geometry_family hC L hL
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

lemma scalar_geometry_215 :
    EvenKernel.ScalarGeometry 4 (43 / 20) (18203 / 10000) (1457 / 1000)
      (3 / 125) (31 / 2000) (1 / 1000) (29 / 5) := by
  intro L hL
  obtain ⟨ha, hla, hab, hlog, hδ, hd, _, hη, _⟩ := RHLimit.OcticGeometry.scalar_geometry_215 L hL
  refine ⟨ha, hla, hab, hlog, hδ, hd, ?_, hη, ?_⟩
  · norm_num [EvenKernel.countCoefficient, EvenKernel.mass]
  · have hd' : (124 / 5 : ℝ) ≤ EvenKernel.D (43 / 20) L := by unfold EvenKernel.D; linarith
    have hπ : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
    have hm := mul_le_mul hπ hd' (by norm_num : (0 : ℝ) ≤ 124 / 5) Real.pi_pos.le
    have harg : (154 : ℝ) ≤ 2 * Real.pi * EvenKernel.D (43 / 20) L := by nlinarith
    have hlo : (161 / 32 : ℝ) ≤ log (2 * Real.pi * EvenKernel.D (43 / 20) L) := by
      apply (Real.le_log_iff_exp_le
        (by linarith : 0 < 2 * Real.pi * EvenKernel.D (43 / 20) L)).mpr
      exact exp_161_32_upper.le.trans harg
    norm_num [EvenKernel.mass]
    linarith

theorem strict_count_family (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ C ∈ Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
      (8 / 9 * C - 18203 / 20000 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ) := by
  intro C hC
  have h := RHLimit.OcticStrict.open_count_from_kernel 4 C (18203 / 10000) (1457 / 1000)
    (3 / 20) (29 / 500) (1 / 1000) (21 / 5) rh
    (ExplicitFormula.explicit_formula_from_general_sources hGreen hN hC)
    (zero_estimate_family hN hB hC) (primepower_cost_family 4 hC)
    (trivial_cost_family 4 hC) (scalar_geometry_family hC) (forward_coverage_family hC)
  norm_num [EvenKernel.countCoefficient, EvenKernel.mass] at h
  convert h using 1 <;> ring

theorem strict_count_214891875 (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (1 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 343827 / 160000 * sqrt u * log u)).card : ℝ) := by
  have h := strict_count_family hGreen hN hB rh (343827 / 160000) (by norm_num)
  norm_num at h
  exact h

theorem strict_count_2149_uniform (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (180013 / 180000 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 2149 / 1000 * sqrt u * log u)).card : ℝ) := by
  have h := strict_count_family hGreen hN hB rh (2149 / 1000) (by norm_num)
  norm_num at h
  exact h

theorem strict_count_215 (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (180173 / 180000 + (29 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 43 / 20 * sqrt u * log u)).card : ℝ) := by
  have h := RHLimit.OcticStrict.open_count_from_kernel 4 (43 / 20) (18203 / 10000) (1457 / 1000)
    (3 / 125) (31 / 2000) (1 / 1000) (29 / 5) rh
    (ExplicitFormula.explicit_formula_from_general_sources hGreen hN (by norm_num))
    (zero_estimate_215 hN hB) primepower_cost_215 trivial_cost_215
    scalar_geometry_215 forward_coverage_215
  norm_num [EvenKernel.countCoefficient, EvenKernel.mass] at h
  exact h

theorem prime_count_215 (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (180173 / 180000 + (29 / 5) / log u) * sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * sqrt u * log u) -
          QuarticWindow.primeCounting u := by
  intro u hu
  have hu0 : 0 ≤ u := (Real.exp_pos 24).le.trans hu
  have hu1 : 1 ≤ u := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 24)).trans hu
  have hlog : 0 ≤ log u := Real.log_nonneg hu1
  have hab : u ≤ u + (43 / 20) * sqrt u * log u := le_add_of_nonneg_right (by positivity)
  exact (strict_count_215 hGreen hN hB rh u hu).trans_le
    (QuarticWindow.count_le_primeCounting_difference hu0 hab)

theorem triples_above_n_minus_H (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) (hnH : 2 * H < n)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    (1 + (21 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
      ((Goldbach.sortedTriples n).card : ℝ) := by
  have hnH' : 2 * (H : ℝ) < n := by exact_mod_cast hnH
  have hcount := strict_count_214891875 hGreen hN hB rh _ hu
  have hcard := Goldbach.window_card_le_sortedTriples hEven hn
    (u := (n : ℝ) - H)
    (v := (n : ℝ) - H + (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))
    (by linarith [Real.add_one_le_exp (24 : ℝ)]) (by linarith) (by linarith) (by linarith)
  exact hcount.trans_le (by exact_mod_cast hcard)

#print axioms optimized_moment_caps
#print axioms zero_estimate_family
#print axioms zero_estimate_215
#print axioms strict_count_family
#print axioms strict_count_214891875
#print axioms strict_count_2149_uniform
#print axioms prime_count_215
#print axioms triples_above_n_minus_H
#check @prime_count_215
end RHOcticPush.OptimizedFinal
