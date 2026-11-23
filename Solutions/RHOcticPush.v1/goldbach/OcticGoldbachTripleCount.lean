/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GoldbachTripleCount
import OcticStrongerFrontier

/-! Whole-network propagation of the actual rich octic prime count to sorted
ternary Goldbach multiplicity. Finite binary verification is a separate explicit
input. All interval geometry is proved or explicitly stated as scalar conditions;
no global binary theorem or ternary record is claimed. -/
namespace RHOcticPush.Goldbach
open Real Set
set_option maxHeartbeats 0

lemma rich_window_to_triples {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) {u v K : ℝ}
    (hu2 : 2 ≤ u) (hhalf : (n : ℝ) / 2 < u)
    (hupper : v ≤ (n : ℝ) - 4) (hres : (n : ℝ) - u ≤ (H : ℝ))
    (hcount : K < ((QuarticWindow.primesBetween u v).card : ℝ)) :
    K < ((sortedTriples n).card : ℝ) := by
  have h := window_card_le_sortedTriples hEven hn hu2 hhalf hupper hres
  exact hcount.trans_le (by exact_mod_cast h)

/-- Every prime population in the stronger full octic family propagates to
at least as many actual sorted triples whenever the explicit window fits the
available finite binary Goldbach range. -/
theorem octic_triple_count_family
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ 143 / 25)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ 23 / 5)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    {C u : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) (hu : exp 24 ≤ u)
    (hhalf : (n : ℝ) / 2 < u)
    (hupper : u + C * sqrt u * log u ≤ (n : ℝ) - 4)
    (hres : (n : ℝ) - u ≤ (H : ℝ)) :
    (8 / 9 * C - 569 / 625 + (21 / 5) / log u) * sqrt u <
      ((sortedTriples n).card : ℝ) := by
  apply rich_window_to_triples hEven hn (by linarith [Real.add_one_le_exp (24 : ℝ)])
    hhalf hupper hres
  exact RHOcticPush.StrongerFrontier.strict_count_family_18208 hGreen hN hB h0 h1 rh C hC u hu

/-- A concrete center determined by n and the verified binary height H.
The only remaining geometry condition is the displayed real scalar width budget. -/
theorem triples_above_n_minus_H
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ 143 / 25)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ 23 / 5)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) (hnH : 2 * H < n)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : (5373 / 2500) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    (1 + (21 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
      ((sortedTriples n).card : ℝ) := by
  have hnH' : 2 * (H : ℝ) < n := by exact_mod_cast hnH
  have h := octic_triple_count_family hGreen hN hB h0 h1 rh hEven hn
    (C := 5373 / 2500) (u := (n : ℝ) - H) (by norm_num) hu
    (by linarith) (by linarith) (by linarith)
  norm_num at h
  exact h

/-- The original2.15-width stronger population also yields a uniformly larger
sorted ternary representation count, at the same finite binary height H. -/
theorem triples_fixed_width_stronger
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (h0 : RHOcticPush.FourierMoments.M0 ≤ 143 / 25)
    (h1 : RHOcticPush.FourierMoments.M1 ≤ 23 / 5)
    (rh : RiemannHypothesis) {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) (hnH : 2 * H < n)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : (43 / 20) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    (5629 / 5625 + (29 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
      ((sortedTriples n).card : ℝ) := by
  have hnH' : 2 * (H : ℝ) < n := by exact_mod_cast hnH
  apply rich_window_to_triples hEven hn (by linarith [Real.add_one_le_exp (24 : ℝ)])
    (u := (n : ℝ) - H)
    (v := (n : ℝ) - H + (43 / 20) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))
    (by linarith) (by linarith) (by linarith)
  exact RHOcticPush.StrongerFrontier.strict_count_215_stronger hGreen hN hB h0 h1 rh _ hu

#print axioms octic_triple_count_family
#print axioms triples_above_n_minus_H
#print axioms triples_fixed_width_stronger
end RHOcticPush.Goldbach
