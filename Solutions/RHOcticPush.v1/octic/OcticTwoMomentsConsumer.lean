import OcticMomentTransport
import OcticExplicitFormula

/-! The original2.15 prime-count conclusion with every octic-specific analytic
bridge discharged. Only two explicit actual numerical moment caps remain. The
three general literature inputs stay visible; this is not an RH-only theorem. -/
namespace RHOcticPush.TwoMomentsConsumer
open Real

theorem prime_count_215_from_general_sources_and_moments
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ (911 / 500) * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi)
    (rh : RiemannHypothesis) :
    ∀ u : ℝ, Real.exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u :=
  RHOcticPush.ExplicitFormula.prime_count_215_one_open_analytic_input hGreen hN rh
    (RHOcticPush.MomentTransport.sharp_zero_estimate_from_moments hN hB h0 h1)

#print axioms prime_count_215_from_general_sources_and_moments
#check @prime_count_215_from_general_sources_and_moments
end RHOcticPush.TwoMomentsConsumer
