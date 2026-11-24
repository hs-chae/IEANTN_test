/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GoldbachExtendedRange

/-! A completely explicit nonempty newly covered band. This module assumes,
and does not establish or relabel as PV, finite binary Goldbach up to4e18.
All numerical geometry and count losses are kernel proofs. -/
namespace RHOnePrime.Goldbach
open Real Set
set_option maxHeartbeats 0

lemma exp24_lt_two_quintillion : exp (24 : ℝ) < 2000000000000000000 := by
  have hpow : (exp (1 : ℝ)) ^ 24 < (3 : ℝ) ^ 24 :=
    pow_lt_pow_left₀ Real.exp_one_lt_three (exp_pos 1).le (by norm_num)
  have he : exp (24 : ℝ) = (exp (1 : ℝ)) ^ 24 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 24
  rw [he]
  norm_num at hpow ⊢
  linarith

lemma four_quintillion_lt_exp50 : (4000000000000000000 : ℝ) < exp 50 := by
  have he : (5 / 2 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow : (5 / 2 : ℝ) ^ 50 < (exp (1 : ℝ)) ^ 50 :=
    pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  have h50 : exp (50 : ℝ) = (exp (1 : ℝ)) ^ 50 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 50
  rw [h50]
  norm_num at hpow ⊢
  linarith

/-- Every odd n in [6e18,8e18] has more than750 million actual sorted ternary
representations under the same RH/source package and finite binary hypothesis.
The old largest-prime injection required n>8e18 and covered none of this band. -/
theorem triples_750_million_new_band
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis)
    (hEven : IEANTN.GoldbachEvenUpTo 4000000000000000000)
    {n : ℕ} (hn : Odd n)
    (hnlow : 6000000000000000000 ≤ n)
    (hnupper : n ≤ 8000000000000000000) :
    (750000000 : ℝ) < ((RHOcticPush.Goldbach.sortedTriples n).card : ℝ) := by
  let u : ℝ := (n : ℝ) - 4000000000000000000
  have hnl : (6000000000000000000 : ℝ) ≤ n := by exact_mod_cast hnlow
  have hnu : (n : ℝ) ≤ 8000000000000000000 := by exact_mod_cast hnupper
  have hul : (2000000000000000000 : ℝ) ≤ u := by dsimp [u]; linarith
  have huu : u ≤ 4000000000000000000 := by dsimp [u]; linarith
  have hu0 : 0 ≤ u := by linarith
  have hupos : 0 < u := by linarith
  have hu : exp 24 ≤ u := exp24_lt_two_quintillion.le.trans hul
  have hs : (sqrt u) ^ 2 = u := sq_sqrt hu0
  have hs0 : 0 ≤ sqrt u := sqrt_nonneg u
  have hsl : (1400000000 : ℝ) ≤ sqrt u := by nlinarith
  have hsu : sqrt u ≤ 2000000000 := by nlinarith
  have hl : 24 ≤ log u := by simpa using log_le_log (exp_pos 24) hu
  have hlu : log u ≤ 50 := by
    have h := log_le_log hupos (huu.trans four_quintillion_lt_exp50.le)
    simpa using h
  have hwidth : (343827 / 160000) * sqrt u * log u ≤
      (4000000000000000000 : ℝ) - 4 := by
    have hfirst : (343827 / 160000 : ℝ) * sqrt u ≤ 6000000000 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hfirst (show 0 ≤ log u by linarith)
    nlinarith
  have h := triples_extended_214891875 hG hN hB rh hEven hn
    (by omega : 3 * 4000000000000000000 ≤ 2 * n) hu hwidth
  change (1 / 2 + (21 / 10) / log u) * sqrt u < _ at h
  have hquot : (21 / 500 : ℝ) ≤ (21 / 10) / log u :=
    (le_div_iff₀ (show 0 < log u by linarith)).mpr (by nlinarith)
  have hm := mul_le_mul
    (show (271 / 500 : ℝ) ≤ 1 / 2 + (21 / 10) / log u by linarith)
    hsl (by norm_num : (0 : ℝ) ≤ 1400000000)
    (by linarith : 0 ≤ 1 / 2 + (21 / 10) / log u)
  linarith

#print axioms triples_750_million_new_band
end RHOnePrime.Goldbach
