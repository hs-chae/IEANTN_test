/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticOptimizedCertified
import Mathlib.Analysis.Complex.Exponential

namespace RHOnePrime.PowerPopulation
open Real Set
set_option maxHeartbeats 0

/-- Actual inherited count contract; no new analytic premise is introduced. -/
def OcticFamily : Prop := ∀ C ∈ Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
  (8 / 9 * C - 18203 / 20000 + (21 / 5) / log u) * sqrt u <
    ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ)

lemma open_count_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    (QuarticWindow.primesBetween a b).card ≤
      (QuarticWindow.primesBetween c d).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpB, hap, hpb⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨?_, hca.trans_lt hap, hpb.trans_le hbd⟩
  exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hpB).1.trans
    (Nat.floor_le_floor hbd), (Nat.mem_primesLE.mp hpB).2⟩

/-- Whole-ray logarithm estimate; the Taylor sum is checked in Lean's kernel. -/
lemma log_sqrt_cube_budget {x : ℝ} (hx : exp 8 ≤ x) :
    (27 / 4 : ℝ) * log x < sqrt x := by
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hL : 8 ≤ log x := by simpa using log_le_log (exp_pos 8) hx
  let v := log x - 8
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have he4 : (217 / 4 : ℝ) ≤ exp 4 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 12
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have hev : 1 + v / 2 ≤ exp (v / 2) := by linarith [Real.add_one_le_exp (v / 2)]
  have he : exp (log x / 2) = exp 4 * exp (v / 2) := by
    rw [← exp_add]
    dsimp [v]
    congr 1
    ring
  have hs : sqrt x = exp (log x / 2) := by
    rw [sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  rw [hs, he]
  have hprod := mul_le_mul he4 hev (by linarith : 0 ≤ 1 + v / 2) (exp_nonneg 4)
  dsimp [v] at hprod
  linarith

lemma cube_window_fits {n : ℝ} (hn : exp 8 ≤ n) :
    n ^ 3 + (27 / 4 : ℝ) * sqrt (n ^ 3) * log (n ^ 3) < (n + 1) ^ 3 := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hlog := log_sqrt_cube_budget hn
  have hs : sqrt (n ^ 3) = n * sqrt n := by
    rw [show n ^ 3 = n ^ 2 * n by ring, sqrt_mul (sq_nonneg _), sqrt_sq hn0.le]
  rw [hs, log_pow]
  have hsq := sq_sqrt hn0.le
  have hmul := mul_lt_mul_of_pos_left hlog (by positivity : 0 < 3 * n * sqrt n)
  nlinarith [sq_nonneg n]

/-- A quantitative cube theorem, strengthening the inherited existence-only
consumer at exactly the same all-real onset and under the same analytic inputs. -/
theorem cube_population (hf : OcticFamily) {n : ℝ} (hn : exp 8 ≤ n) :
    ((101797 / 20000 : ℝ) + (7 / 5) / log n) * n * sqrt n <
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hu : exp 24 ≤ n ^ 3 := by
    have h := pow_le_pow_left₀ (exp_nonneg 8) hn 3
    simpa only [← exp_nat_mul, show (3 : ℕ) * (8 : ℝ) = 24 by norm_num] using h
  have hcount := hf (27 / 4) (by norm_num) (n ^ 3) hu
  have hs : sqrt (n ^ 3) = n * sqrt n := by
    rw [show n ^ 3 = n ^ 2 * n by ring, sqrt_mul (sq_nonneg _), sqrt_sq hn0.le]
  have hcount' : ((101797 / 20000 : ℝ) + (7 / 5) / log n) * n * sqrt n <
      ((QuarticWindow.primesBetween (n ^ 3)
        (n ^ 3 + (27 / 4 : ℝ) * sqrt (n ^ 3) * log (n ^ 3))).card : ℝ) := by
    convert hcount using 1
    rw [hs, log_pow]
    norm_num
    ring
  exact hcount'.trans_le (by exact_mod_cast open_count_mono le_rfl (cube_window_fits hn).le)

theorem cube_population_five (hf : OcticFamily) {n : ℝ} (hn : exp 8 ≤ n) :
    5 * n * sqrt n <
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hl : 0 < log n := by
    have h := log_le_log (exp_pos 8) hn
    simp only [log_exp] at h
    linarith
  have h := cube_population hf hn
  have hh : 5 * n * sqrt n <
      ((101797 / 20000 : ℝ) + (7 / 5) / log n) * n * sqrt n := by
    have hp : 0 < n * sqrt n := mul_pos hn0 (sqrt_pos.mpr hn0)
    have hd : 0 < (7 / 5 : ℝ) / log n := div_pos (by norm_num) hl
    nlinarith
  exact hh.trans h

theorem cube_population_from_sources
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {n : ℝ} (hn : exp 8 ≤ n) :
    ((101797 / 20000 : ℝ) + (7 / 5) / log n) * n * sqrt n <
      ((QuarticWindow.primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ) :=
  cube_population (RHOcticPush.OptimizedFinal.strict_count_family hGreen hN hB rh) hn

#print axioms cube_population
#print axioms cube_population_five
#print axioms cube_population_from_sources
end RHOnePrime.PowerPopulation
