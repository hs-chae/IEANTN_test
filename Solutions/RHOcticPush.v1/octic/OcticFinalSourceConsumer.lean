import OcticCertifiedMoments
import OcticEndpointSourceConsumer
import OcticStrongerFrontier

/-! Final actual octic consumers: the two complete Fourier moments are now
proved by independent kernel-checked quadrature, including all endpoints and tails.
No numerical or octic-specific analytic hypothesis remains. RH and the three
independently audited general literature inputs remain explicit. -/
namespace RHOcticPush.Final
open Real Set

lemma actual_M0_original : FourierMoments.M0 ≤ (911 / 500) * Real.pi := by
  have h := Moments.Endpoint.actual_M0
  linarith [Real.pi_gt_d2]
lemma actual_M1_original : FourierMoments.M1 ≤ (3 / 2) * Real.pi := by
  have h := Moments.Endpoint.actual_M1
  linarith [Real.pi_gt_d2]

theorem zero_estimate_215
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) :
    EvenKernel.ZeroEstimate 4 (43 / 20) (911 / 500) (3 / 2) (3 / 125) :=
  MomentTransport.sharp_zero_estimate_from_moments hN
    (BPTSourceEndpoint.publishedBound_of_offOrdinate hB) actual_M0_original actual_M1_original

theorem zero_estimate_family
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) :
    ∀ C ∈ Icc (103 / 100 : ℝ) 16,
      EvenKernel.ZeroEstimate 4 C (911 / 500) (3 / 2) (3 / 20) :=
  fun _ hC => FamilyMoments.sharp_zero_estimate_family_from_moments hN
    (BPTSourceEndpoint.publishedBound_of_offOrdinate hB) actual_M0_original actual_M1_original hC

theorem prime_count_215 (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / log u) * sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * sqrt u * log u) -
          QuarticWindow.primeCounting u :=
  EndpointSourceConsumer.prime_count_215 hGreen hN hB actual_M0_original actual_M1_original rh

theorem strict_count_215 (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 43 / 20 * sqrt u * log u)).card : ℝ) :=
  EndpointSourceConsumer.strict_count_215 hGreen hN hB actual_M0_original actual_M1_original rh

theorem strict_count_family (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ C ∈ Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
      (8 / 9 * C - 911 / 1000 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ) :=
  EndpointSourceConsumer.strict_count_family hGreen hN hB actual_M0_original actual_M1_original rh

theorem strict_count_family_stronger (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ C ∈ Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
      (8 / 9 * C - 569 / 625 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ) :=
  StrongerFrontier.strict_count_family_18208 hGreen hN hB
    Moments.Endpoint.actual_M0 Moments.Endpoint.actual_M1 rh

theorem strict_count_21492 (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (1 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 5373 / 2500 * sqrt u * log u)).card : ℝ) :=
  StrongerFrontier.strict_count_21492 hGreen hN hB
    Moments.Endpoint.actual_M0 Moments.Endpoint.actual_M1 rh

theorem strict_count_21493_uniform_excess (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (11251 / 11250 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 21493 / 10000 * sqrt u * log u)).card : ℝ) :=
  StrongerFrontier.strict_count_21493_uniform_excess hGreen hN hB
    Moments.Endpoint.actual_M0 Moments.Endpoint.actual_M1 rh

theorem strict_count_215_stronger (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (5629 / 5625 + (29 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 43 / 20 * sqrt u * log u)).card : ℝ) :=
  StrongerFrontier.strict_count_215_stronger hGreen hN hB
    Moments.Endpoint.actual_M0 Moments.Endpoint.actual_M1 rh

theorem prime_count_215_stronger (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (5629 / 5625 + (29 / 5) / log u) * sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * sqrt u * log u) -
          QuarticWindow.primeCounting u :=
  StrongerFrontier.prime_count_215_stronger hGreen hN hB
    Moments.Endpoint.actual_M0 Moments.Endpoint.actual_M1 rh

theorem prime_count_family (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ C ∈ Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
      (8 / 9 * C - 911 / 1000 + (21 / 5) / log u) * sqrt u <
        QuarticWindow.primeCounting (u + C * sqrt u * log u) -
          QuarticWindow.primeCounting u :=
  FamilyMoments.prime_count_family_from_general_sources_and_moments hGreen hN
    (BPTSourceEndpoint.publishedBound_of_offOrdinate hB) actual_M0_original actual_M1_original rh

theorem prime_count_family_stronger (hGreen : GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : BPTSourceEndpoint.SourceBPTOffOrdinate) (rh : RiemannHypothesis) :
    ∀ C ∈ Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
      (8 / 9 * C - 569 / 625 + (21 / 5) / log u) * sqrt u <
        QuarticWindow.primeCounting (u + C * sqrt u * log u) -
          QuarticWindow.primeCounting u := by
  intro C hC u hu
  have hu0 : 0 ≤ u := (Real.exp_pos 24).le.trans hu
  have hu1 : 1 ≤ u := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 24)).trans hu
  have hlog : 0 ≤ log u := Real.log_nonneg hu1
  have hC0 : 0 ≤ C := by linarith [hC.1]
  have hab : u ≤ u + C * sqrt u * log u := le_add_of_nonneg_right (by positivity)
  exact (strict_count_family_stronger hGreen hN hB rh C hC u hu).trans_le
    (QuarticWindow.count_le_primeCounting_difference hu0 hab)

#print axioms zero_estimate_215
#print axioms zero_estimate_family
#print axioms prime_count_215
#print axioms strict_count_215
#print axioms prime_count_family
#print axioms strict_count_family
#print axioms strict_count_family_stronger
#print axioms prime_count_family_stronger
#print axioms strict_count_21492
#print axioms strict_count_21493_uniform_excess
#print axioms strict_count_215_stronger
#print axioms prime_count_215_stronger
#check @strict_count_215
end RHOcticPush.Final
