/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PowerPopulation
namespace RHOnePrime.PowerPopulation
open Real Set
set_option maxHeartbeats 0

lemma binomial_first_order {n : ℝ} (hn : 0 < n) (k : ℕ) :
    n ^ (k + 3) + (k + 3 : ℝ) * n ^ (k + 2) ≤ (n + 1) ^ (k + 3) := by
  have hneg : (-2 : ℝ) ≤ 1 / n := by
    have h0 : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h := one_add_mul_le_pow hneg (k + 3)
  have hm := mul_le_mul_of_nonneg_left h (pow_nonneg hn.le (k + 3))
  have he : n ^ (k + 3) * (1 + (k + 3 : ℝ) * (1 / n)) =
      n ^ (k + 3) + (k + 3 : ℝ) * n ^ (k + 2) := by
    rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
    field_simp
  have he' : n ^ (k + 3) * (1 + 1 / n) ^ (k + 3) = (n + 1) ^ (k + 3) := by
    rw [← mul_pow]
    congr 1
    field_simp
  simpa only [Nat.cast_add, Nat.cast_ofNat, he, he'] using hm

lemma higher_power_window_fits {n : ℝ} (hn : exp 8 ≤ n) (k : ℕ) :
    n ^ (k + 3) + (27 / 4 : ℝ) * sqrt (n ^ (k + 3)) * log (n ^ (k + 3)) <
      (n + 1) ^ (k + 3) := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hn1 : 1 ≤ n := (one_le_exp (by norm_num : (0 : ℝ) ≤ 8)).trans hn
  have hL : 8 ≤ log n := by simpa using log_le_log (exp_pos 8) hn
  have hbudget := log_sqrt_cube_budget hn
  have hnk : 1 ≤ n ^ k := one_le_pow₀ hn1
  have hsk : sqrt (n ^ k) ≤ n ^ k := by
    apply sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith⟩
  have hs : sqrt (n ^ (k + 3)) ≤ n * sqrt n * n ^ k := by
    rw [show n ^ (k + 3) = n ^ 3 * n ^ k by rw [pow_add]; ring,
      sqrt_mul (by positivity : 0 ≤ n ^ 3),
      show n ^ 3 = n ^ 2 * n by ring, sqrt_mul (sq_nonneg _), sqrt_sq hn0.le]
    exact mul_le_mul_of_nonneg_left hsk (by positivity)
  have hr : 0 < (k + 3 : ℝ) := by positivity
  have hm := mul_lt_mul_of_pos_left hbudget
    (by positivity : 0 < (k + 3 : ℝ) * n * sqrt n * n ^ k)
  have heq : ((k + 3 : ℝ) * n * sqrt n * n ^ k) * sqrt n =
      (k + 3 : ℝ) * n ^ (k + 2) := by
    calc
      _ = (k + 3 : ℝ) * n * (sqrt n) ^ 2 * n ^ k := by ring
      _ = (k + 3 : ℝ) * n * n * n ^ k := by rw [sq_sqrt hn0.le]
      _ = _ := by rw [pow_add]; ring
  rw [heq] at hm
  have hm' : (27 / 4 : ℝ) * (n * sqrt n * n ^ k) * ((k + 3 : ℝ) * log n) <
      (k + 3 : ℝ) * n ^ (k + 2) := by nlinarith
  have hsmall := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ (27 / 4 : ℝ) * ((k + 3 : ℝ) * log n))
  have hb := binomial_first_order hn0 k
  rw [log_pow]
  push_cast
  nlinarith

/-- All integer powers at least three, with a quantitative count, not just existence. -/
theorem higher_power_population (hf : OcticFamily) {n : ℝ} (hn : exp 8 ≤ n) (k : ℕ) :
    ((101797 / 20000 : ℝ) + (21 / 5) / ((k + 3 : ℝ) * log n)) * sqrt (n ^ (k + 3)) <
      ((QuarticWindow.primesBetween (n ^ (k + 3)) ((n + 1) ^ (k + 3))).card : ℝ) := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hn1 : 1 ≤ n := (one_le_exp (by norm_num : (0 : ℝ) ≤ 8)).trans hn
  have hn3 : exp 24 ≤ n ^ 3 := by
    have h := pow_le_pow_left₀ (exp_nonneg 8) hn 3
    simpa only [← exp_nat_mul, show (3 : ℕ) * (8 : ℝ) = 24 by norm_num] using h
  have hu : exp 24 ≤ n ^ (k + 3) := by
    have hnk : 1 ≤ n ^ k := one_le_pow₀ hn1
    rw [show n ^ (k + 3) = n ^ 3 * n ^ k by rw [pow_add]; ring]
    exact hn3.trans (le_mul_of_one_le_right (by positivity) hnk)
  have hc := hf (27 / 4) (by norm_num) (n ^ (k + 3)) hu
  rw [log_pow] at hc
  push_cast at hc
  norm_num at hc
  have hmono : ((QuarticWindow.primesBetween (n ^ (k + 3))
      (n ^ (k + 3) + (27 / 4 : ℝ) * sqrt (n ^ (k + 3)) * log (n ^ (k + 3)))).card : ℝ) ≤
      ((QuarticWindow.primesBetween (n ^ (k + 3)) ((n + 1) ^ (k + 3))).card : ℝ) := by
    exact_mod_cast open_count_mono le_rfl (higher_power_window_fits hn k).le
  rw [log_pow] at hmono
  push_cast at hmono
  exact hc.trans_le hmono

theorem higher_power_population_from_sources
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {n : ℝ} (hn : exp 8 ≤ n) (k : ℕ) :
    ((101797 / 20000 : ℝ) + (21 / 5) / ((k + 3 : ℝ) * log n)) * sqrt (n ^ (k + 3)) <
      ((QuarticWindow.primesBetween (n ^ (k + 3)) ((n + 1) ^ (k + 3))).card : ℝ) :=
  higher_power_population (RHOcticPush.OptimizedFinal.strict_count_family hGreen hN hB rh) hn k

#print axioms higher_power_window_fits
#print axioms higher_power_population
#print axioms higher_power_population_from_sources
end RHOnePrime.PowerPopulation
