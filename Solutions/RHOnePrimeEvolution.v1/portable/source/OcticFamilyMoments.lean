import OcticMomentTransport
import OcticExplicitFormula

/-! The original full real-parameter octic frontier from the same two moments.
The parameter C ranges over every real value in[1.03,16], not a sample grid. -/
namespace RHOcticPush.FamilyMoments
open Real Set
open RHOcticPush.MomentTransport
set_option maxHeartbeats 0

lemma log_five_hundred_bounds : 1 < Real.log 500 ∧ Real.log 500 < 7 := by
  constructor
  · apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 500)).mpr
    linarith [Real.exp_one_lt_three]
  · apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 500)).mpr
    have he : (8 / 3 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 8 / 3)
      (by norm_num : (7 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hp
    have hp' : (8 / 3 : ℝ) ^ 7 < Real.exp 7 := by
      simpa only [Nat.cast_ofNat, mul_one] using hp
    exact (by norm_num : (500 : ℝ) < (8 / 3 : ℝ) ^ 7).trans hp'

lemma delta_log_bound_500 {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / 500) :
    δ * Real.log (1 / δ) ≤ Real.log 500 / 500 := by
  have hp : 0 < 1 / ((500 : ℝ) * δ) := by positivity
  have hj := Real.log_le_sub_one_of_pos hp
  have hm : δ * Real.log (1 / (500 * δ)) ≤ 1 / 500 - δ := by
    calc
      _ ≤ δ * (1 / (500 * δ) - 1) :=
        mul_le_mul_of_nonneg_left hj hδ.le
      _ = _ := by field_simp
  have he : Real.log (1 / δ) =
      Real.log 500 + Real.log (1 / (500 * δ)) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hδ.ne', Real.log_one,
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by positivity : (500 : ℝ) * δ ≠ 0),
      Real.log_one, Real.log_mul (by norm_num : (500 : ℝ) ≠ 0) hδ.ne']
    ring
  have hpos := mul_nonneg (show 0 ≤ 1 / 500 - δ by linarith)
    (show 0 ≤ Real.log 500 - 1 by linarith [log_five_hundred_bounds.1])
  rw [he]
  nlinarith

lemma family_augmented_residual_lt {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 3 / 2500) :
    RHOcticPush.ZeroAllowance.residual δ + 32 * δ / 9 < 3 / 20 := by
  have hs : δ ≤ 1 / 500 := by linarith
  have hlog := delta_log_bound_500 hδ hs
  have hlog' : δ * Real.log (1 / δ) < 7 / 500 := by
    nlinarith [log_five_hundred_bounds.2]
  have h12 := RHLimit.BPTZeroCount.log_twelve_lt
  have hprod : δ * Real.log 12 ≤ (5 / 2) * δ := by
    nlinarith [mul_nonneg hδ.le (show 0 ≤ 5 / 2 - Real.log 12 by linarith)]
  unfold RHOcticPush.ZeroAllowance.residual
  nlinarith

/-- The complete original real-parameter ZeroEstimate family, conditional only
on the two actual Fourier moment caps and the named general literature inputs. -/
theorem sharp_zero_estimate_family_from_moments
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ (911 / 500) * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi)
    {C : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) :
    EvenKernel.ZeroEstimate 4 C (911 / 500) (3 / 2) (3 / 20) := by
  intro rh L hL
  have hD : 0 < EvenKernel.D C L := by
    unfold EvenKernel.D
    nlinarith [hC.1, mul_nonneg (show 0 ≤ C - 103 / 100 by linarith [hC.1])
      (show 0 ≤ L - 24 by linarith)]
  have hδ : 0 < EvenKernel.δ C L := by unfold EvenKernel.δ; positivity
  have hs := RHLimit.OcticGeometry.delta_small hC hL
  have hsmall : 12 * EvenKernel.δ C L ≤ 1 := by linarith
  have hbound := full_zero_bound_in_terms_of_moments rh hN hB hδ hsmall
  have hres := family_augmented_residual_lt hδ hs
  have hqsmall : 2 * Real.pi * EvenKernel.δ C L ≤ 1 := by
    nlinarith [Real.pi_lt_four, mul_nonneg hδ.le (show 0 ≤ 4 - Real.pi by linarith [Real.pi_lt_four])]
  have hlog : 0 ≤ log (1 / (2 * Real.pi * EvenKernel.δ C L)) :=
    Real.log_nonneg ((le_div_iff₀
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hδ)).mpr
        (by simpa using hqsmall))
  have hcap : (RHOcticPush.FourierMoments.M0 *
        log (1 / (2 * Real.pi * EvenKernel.δ C L)) +
          RHOcticPush.FourierMoments.M1) / Real.pi ≤
      (911 / 500) * log (1 / (2 * Real.pi * EvenKernel.δ C L)) + 3 / 2 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_right h0 hlog]
  rw [log_scale_identity hD] at hbound hcap
  linarith

theorem prime_count_family_from_general_sources_and_moments
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ (911 / 500) * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi)
    (rh : RiemannHypothesis) :
    ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, Real.exp 24 ≤ u →
      (8 / 9 * C - 911 / 1000 + (21 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + C * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u :=
  RHLimit.OcticTwoInputs.prime_count_family rh
    (fun C hC => RHOcticPush.ExplicitFormula.explicit_formula_from_general_sources hGreen hN hC)
    (fun C hC => sharp_zero_estimate_family_from_moments hN hB h0 h1 hC)

#print axioms family_augmented_residual_lt
#print axioms sharp_zero_estimate_family_from_moments
#print axioms prime_count_family_from_general_sources_and_moments
end RHOcticPush.FamilyMoments
