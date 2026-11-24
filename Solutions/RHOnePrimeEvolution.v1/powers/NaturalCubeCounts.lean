/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CubeDensityEarlier
import Mathlib.Analysis.Complex.ExponentialBounds
namespace RHOnePrime.PowerPopulation
open Real Set
set_option maxHeartbeats 0

lemma exp_eight_lt_2981 : exp 8 < 2981 := by
  have h := pow_lt_pow_left₀ exp_one_lt_d9 (exp_nonneg 1) (by decide : (8 : ℕ) ≠ 0)
  have he : exp (8 : ℝ) = (exp 1) ^ (8 : ℕ) := by simpa using exp_nat_mul 1 8
  rw [he]
  exact h.trans (by norm_num)

lemma exp_thirteen_lt_442414 : exp 13 < 442414 := by
  have h := pow_lt_pow_left₀ exp_one_lt_d9 (exp_nonneg 1) (by decide : (13 : ℕ) ≠ 0)
  have he : exp (13 : ℝ) = (exp 1) ^ (13 : ℕ) := by simpa using exp_nat_mul 1 13
  rw [he]
  exact h.trans (by norm_num)

/-- Actual natural-variable count; both cube endpoints are excluded. -/
theorem cube_count_natural (hf : OcticFamily) {n : ℕ} (hn : 2981 ≤ n) :
    ((101797 / 20000 : ℝ) + (7 / 5) / log (n : ℝ)) * n * sqrt n <
      ((QuarticWindow.primesBetween ((n : ℝ) ^ 3) (((n : ℝ) + 1) ^ 3)).card : ℝ) := by
  have hn' : (2981 : ℝ) ≤ n := by exact_mod_cast hn
  exact cube_population hf (exp_eight_lt_2981.le.trans hn')

/-- A disjoint collection of actual short windows, at a concrete integer onset. -/
theorem cube_density_natural (hf : OcticFamily) {n : ℕ} (hn : 442414 ≤ n) :
    (n : ℝ) ^ 2 / (2 * log n) <
      ((QuarticWindow.primesBetween ((n : ℝ) ^ 3) (((n : ℝ) + 1) ^ 3)).card : ℝ) := by
  have hn' : (442414 : ℝ) ≤ n := by exact_mod_cast hn
  exact cube_density_half_13 hf (exp_thirteen_lt_442414.le.trans hn')

theorem cube_count_natural_from_sources
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {n : ℕ} (hn : 2981 ≤ n) :
    ((101797 / 20000 : ℝ) + (7 / 5) / log (n : ℝ)) * n * sqrt n <
      ((QuarticWindow.primesBetween ((n : ℝ) ^ 3) (((n : ℝ) + 1) ^ 3)).card : ℝ) :=
  cube_count_natural (RHOcticPush.OptimizedFinal.strict_count_family hGreen hN hB rh) hn

theorem cube_density_natural_from_sources
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {n : ℕ} (hn : 442414 ≤ n) :
    (n : ℝ) ^ 2 / (2 * log n) <
      ((QuarticWindow.primesBetween ((n : ℝ) ^ 3) (((n : ℝ) + 1) ^ 3)).card : ℝ) :=
  cube_density_natural (RHOcticPush.OptimizedFinal.strict_count_family hGreen hN hB rh) hn

#print axioms exp_eight_lt_2981
#print axioms exp_thirteen_lt_442414
#print axioms cube_count_natural_from_sources
#print axioms cube_density_natural_from_sources
#check @cube_count_natural_from_sources
#check @cube_density_natural_from_sources
end RHOnePrime.PowerPopulation
