/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GoldbachNumericalBand
import IEANTN.Nodes.PrimeInterval.v4.Conclusions

/-! Adapters consume the existing canonical count statement, allowing actual
typed graph composition instead of adding RH/source assumptions downstream.
No Challenge import or copied proof-acceptance flag is used.
-/
namespace RHOnePrime.Canonical
open Real Set
open RHOnePrime.Frontier RHOnePrime.Goldbach RHOcticPush.Goldbach
set_option maxHeartbeats 0

theorem generic_block_from_family (hf : PrimeInterval.v4.optimized_strict_family)
    {C x : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) (hx : exp 24 ≤ x)
    {m : ℕ} (hm : (m : ℝ) ≤ allowance C x) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
        x + C * sqrt x * log x := by
  apply quantile_open_of_card ((exp_pos 24).le.trans hx)
  exact hm.trans_lt (hf C hC x hx)

theorem shifted_block_from_family (hf : PrimeInterval.v4.optimized_strict_family)
    {x : ℝ} (hx : exp 24 ≤ x) {m : ℕ} (hm : (m : ℝ) ≤ sqrt x) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
        x + (343827 / 160000) * sqrt x * log x - (189 / 40) * sqrt x := by
  have h := hf (populationWidth 1 x) (population_one_width_domain hx) x hx
  have hc : 8 / 9 * populationWidth 1 x - 18203 / 20000 + (21 / 5) / log x = 1 := by
    unfold populationWidth widthFor
    ring
  change (8 / 9 * populationWidth 1 x - 18203 / 20000 + (21 / 5) / log x) * sqrt x <
    ((QuarticWindow.primesBetween x (x + populationWidth 1 x * sqrt x * log x)).card : ℝ) at h
  rw [hc, one_mul, population_one_window_identity hx] at h
  exact quantile_open_of_card ((exp_pos 24).le.trans hx) (hm.trans_lt h)

theorem extended_from_family (hf : PrimeInterval.v4.optimized_strict_family)
    {H n : ℕ} (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    (hnH : 3 * H ≤ 2 * n) (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    (1 / 2 + (21 / 10) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
      ((sortedTriples n).card : ℝ) := by
  have hnH' : 3 * (H : ℝ) ≤ 2 * n := by exact_mod_cast hnH
  have hcount := hf (343827 / 160000) (by norm_num) ((n : ℝ) - H) hu
  norm_num at hcount
  have hcard := window_card_le_two_sortedTriples hEven hn
    (u := (n : ℝ) - H)
    (v := (n : ℝ) - H + (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))
    (by linarith [Real.add_one_le_exp (24 : ℝ)]) (by linarith) (by linarith) (by linarith)
  have hcard' : ((QuarticWindow.primesBetween ((n : ℝ) - H)
      ((n : ℝ) - H + (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))).card : ℝ) ≤
      2 * ((sortedTriples n).card : ℝ) := by exact_mod_cast hcard
  change (1 + (21 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
    ((QuarticWindow.primesBetween ((n : ℝ) - H)
      ((n : ℝ) - H + (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))).card : ℝ) at hcount
  have hdiv : ((1 + (21 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H)) / 2 <
      ((sortedTriples n).card : ℝ) := by linarith
  convert hdiv using 1 <;> ring

theorem full_range_from_family (hf : PrimeInterval.v4.optimized_strict_family)
    {H n : ℕ} (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n)
    (hu : exp 24 ≤ (n : ℝ) - H)
    (hwidth : (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4) :
    (1 / 3 + (7 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
      ((sortedTriples n).card : ℝ) := by
  have hcount := hf (343827 / 160000) (by norm_num) ((n : ℝ) - H) hu
  norm_num at hcount
  have hcard := window_card_le_three_sortedTriples hEven hn
    (u := (n : ℝ) - H)
    (v := (n : ℝ) - H + (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))
    (by linarith [Real.add_one_le_exp (24 : ℝ)]) (by linarith) (by linarith)
  have hcard' : ((QuarticWindow.primesBetween ((n : ℝ) - H)
      ((n : ℝ) - H + (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))).card : ℝ) ≤
      3 * ((sortedTriples n).card : ℝ) := by exact_mod_cast hcard
  change (1 + (21 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
    ((QuarticWindow.primesBetween ((n : ℝ) - H)
      ((n : ℝ) - H + (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H))).card : ℝ) at hcount
  have hdiv : ((1 + (21 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H)) / 3 <
      ((sortedTriples n).card : ℝ) := by linarith
  convert hdiv using 1 <;> ring

theorem numeric_band_from_family (hf : PrimeInterval.v4.optimized_strict_family)
    (hEven : IEANTN.GoldbachEvenUpTo 4000000000000000000)
    {n : ℕ} (hn : Odd n) (hnlow : 6000000000000000000 ≤ n)
    (hnupper : n ≤ 8000000000000000000) :
    (750000000 : ℝ) < ((sortedTriples n).card : ℝ) := by
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
  have h := extended_from_family hf hEven hn
    (by omega : 3 * 4000000000000000000 ≤ 2 * n) hu hwidth
  change (1 / 2 + (21 / 10) / log u) * sqrt u < _ at h
  have hquot : (21 / 500 : ℝ) ≤ (21 / 10) / log u :=
    (le_div_iff₀ (show 0 < log u by linarith)).mpr (by nlinarith)
  have hm := mul_le_mul
    (show (271 / 500 : ℝ) ≤ 1 / 2 + (21 / 10) / log u by linarith)
    hsl (by norm_num : (0 : ℝ) ≤ 1400000000)
    (by linarith : 0 ≤ 1 / 2 + (21 / 10) / log u)
  linarith

#print axioms generic_block_from_family
#print axioms shifted_block_from_family
#print axioms extended_from_family
#print axioms full_range_from_family
#print axioms numeric_band_from_family
end RHOnePrime.Canonical
