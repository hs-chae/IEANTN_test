import OcticStrictMoments
import OcticTwoMomentsConsumer
import OcticBPTSourceEndpoint

/-! Actual final source path consumes the proved non-ordinate-to-closed BPT
adapter. Numerical moments remain explicit until their independent kernel gate. -/
namespace RHOcticPush.EndpointSourceConsumer
open Real Set

theorem strict_count_215
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ (911 / 500) * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi)
    (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 43 / 20 * sqrt u * log u)).card : ℝ) :=
  RHOcticPush.StrictMoments.count_215_from_general_sources_and_moments hGreen hN
    (RHOcticPush.BPTSourceEndpoint.publishedBound_of_offOrdinate hB) h0 h1 rh

theorem strict_count_family
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ (911 / 500) * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi)
    (rh : RiemannHypothesis) :
    ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
      (8 / 9 * C - 911 / 1000 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ) :=
  RHOcticPush.StrictMoments.count_family_from_general_sources_and_moments hGreen hN
    (RHOcticPush.BPTSourceEndpoint.publishedBound_of_offOrdinate hB) h0 h1 rh

theorem prime_count_215
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ (911 / 500) * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi)
    (rh : RiemannHypothesis) :
    ∀ u : ℝ, Real.exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u :=
  RHOcticPush.TwoMomentsConsumer.prime_count_215_from_general_sources_and_moments hGreen hN
    (RHOcticPush.BPTSourceEndpoint.publishedBound_of_offOrdinate hB) h0 h1 rh

#print axioms strict_count_215
#print axioms strict_count_family
#print axioms prime_count_215
end RHOcticPush.EndpointSourceConsumer
