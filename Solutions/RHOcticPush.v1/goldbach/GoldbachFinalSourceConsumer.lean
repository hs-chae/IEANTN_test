/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticGoldbachTripleCount
import OcticCertifiedMoments

/-! Final actual sorted ternary counts. The two complete Fourier moments are
consumed from their no-argument kernel proofs. Finite binary Goldbach verification,
RH, genuine general literature inputs, and exact scalar geometry stay explicit. -/
namespace RHOcticPush.Goldbach.Final
open Real Set

theorem triple_count_family
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    {C u : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) (hu : exp 24 ≤ u)
    (hhalf : (n : ℝ) / 2 < u)
    (hupper : u + C * sqrt u * log u ≤ (n : ℝ) - 4)
    (hres : (n : ℝ) - u ≤ (H : ℝ)) :
    (8 / 9 * C - 569 / 625 + (21 / 5) / log u) * sqrt u <
      ((RHOcticPush.Goldbach.sortedTriples n).card : ℝ) :=
  RHOcticPush.Goldbach.octic_triple_count_family hGreen hN hB
    RHOcticPush.Moments.Endpoint.actual_M0 RHOcticPush.Moments.Endpoint.actual_M1
    rh hEven hn hC hu hhalf hupper hres

theorem triples_above_n_minus_H
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) (hnH : 2 * H < n)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : (5373 / 2500) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    (1 + (21 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
      ((RHOcticPush.Goldbach.sortedTriples n).card : ℝ) :=
  RHOcticPush.Goldbach.triples_above_n_minus_H hGreen hN hB
    RHOcticPush.Moments.Endpoint.actual_M0 RHOcticPush.Moments.Endpoint.actual_M1
    rh hEven hn hnH hu hwidth

theorem triples_fixed_width_stronger
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) (hnH : 2 * H < n)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : (43 / 20) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    (5629 / 5625 + (29 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
      ((RHOcticPush.Goldbach.sortedTriples n).card : ℝ) :=
  RHOcticPush.Goldbach.triples_fixed_width_stronger hGreen hN hB
    RHOcticPush.Moments.Endpoint.actual_M0 RHOcticPush.Moments.Endpoint.actual_M1
    rh hEven hn hnH hu hwidth

#print axioms triple_count_family
#print axioms triples_above_n_minus_H
#print axioms triples_fixed_width_stronger
#check @triples_above_n_minus_H
end RHOcticPush.Goldbach.Final
