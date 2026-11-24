import OcticFamilyMoments
import OcticStrict

/-! Actual finite strictly-between-prime sets: both endpoints are excluded.
These are source-to-consumer theorems, with only the two moment caps pending. -/
namespace RHOcticPush.StrictMoments
open Real Set

theorem count_215_from_general_sources_and_moments
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ (911 / 500) * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi)
    (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 43 / 20 * sqrt u * log u)).card : ℝ) :=
  RHLimit.OcticStrict.count_215 rh
    (RHOcticPush.ExplicitFormula.explicit_formula_from_general_sources hGreen hN (by norm_num))
    (RHOcticPush.MomentTransport.sharp_zero_estimate_from_moments hN hB h0 h1)

theorem count_family_from_general_sources_and_moments
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ (911 / 500) * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi)
    (rh : RiemannHypothesis) :
    ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
      (8 / 9 * C - 911 / 1000 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ) :=
  RHLimit.OcticStrict.count_family rh
    (fun C hC => RHOcticPush.ExplicitFormula.explicit_formula_from_general_sources hGreen hN hC)
    (fun C hC => RHOcticPush.FamilyMoments.sharp_zero_estimate_family_from_moments hN hB h0 h1 hC)

/-- A separate below2.15 consequence at the same proved moment target:
2.149875 rather than2.15, with the explicit positive4.2/log(u) excess. -/
theorem count_2149875_from_general_sources_and_moments
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHLimit.BPTZeroCount.PublishedBound)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ (911 / 500) * Real.pi)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ (3 / 2) * Real.pi)
    (rh : RiemannHypothesis) :
    ∀ u : ℝ, exp 24 ≤ u →
      (1 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 17199 / 8000 * sqrt u * log u)).card : ℝ) := by
  have h := count_family_from_general_sources_and_moments hGreen hN hB h0 h1 rh
    (17199 / 8000) (by norm_num)
  norm_num at h
  exact h

#print axioms count_215_from_general_sources_and_moments
#print axioms count_family_from_general_sources_and_moments
#print axioms count_2149875_from_general_sources_and_moments
end RHOcticPush.StrictMoments
