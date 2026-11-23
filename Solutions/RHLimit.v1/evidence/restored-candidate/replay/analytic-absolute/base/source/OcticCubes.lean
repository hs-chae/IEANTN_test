/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticQuantiles
import Mathlib.Analysis.Complex.Exponential

/-! A genuine cross-family consumer of the new quantitative short-window theorem.
The count result is the main export; existence is also linked to the existing
`PrimesBetweenCubes` family from the inspected upstream source.
These are conditional adapters, not a proof of the analytic kernel input. -/
namespace RHContinuation.OcticCubes
open Real

/-- An elementary whole-ray estimate, with no sample grid. -/
theorem three_log_le_sqrt {x : ℝ} (hx : Real.exp 8 ≤ x) :
    3 * Real.log x < Real.sqrt x := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hL : 8 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 8) hx
    simpa using h
  let v := Real.log x - 8
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have he2 : (5 : ℝ) ≤ Real.exp 2 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h ⊢
    linarith
  have he4 : (25 : ℝ) ≤ Real.exp 4 := by
    rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 2]
  have hev : 1 + v / 2 ≤ Real.exp (v / 2) := by
    have h := Real.add_one_le_exp (v / 2)
    linarith
  have he : Real.exp (Real.log x / 2) = Real.exp 4 * Real.exp (v / 2) := by
    rw [← Real.exp_add]
    dsimp [v]
    congr 1
    ring
  have hsq : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  rw [hsq, he]
  have hprod := mul_le_mul he4 hev (by linarith : 0 ≤ 1 + v / 2)
    (Real.exp_nonneg 4)
  dsimp [v] at hprod
  linarith

/-- The new direct interval fits strictly inside each successive-cube interval. -/
theorem octic_fits_cube {n : ℝ} (hn : Real.exp 8 ≤ n) :
    n ^ 3 + (43 / 20 : ℝ) * Real.sqrt (n ^ 3) * Real.log (n ^ 3) <
      (n + 1) ^ 3 := by
  have hn0 : 0 < n := (Real.exp_pos _).trans_le hn
  have hlog := three_log_le_sqrt hn
  have hs : Real.sqrt (n ^ 3) = n * Real.sqrt n := by
    rw [show n ^ 3 = n ^ 2 * n by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hn0.le]
  rw [hs, Real.log_pow]
  have hsq := Real.sq_sqrt hn0.le
  have hmul := mul_lt_mul_of_pos_left hlog
    (by positivity : 0 < (43 / 20 : ℝ) * n * Real.sqrt n)
  nlinarith [sq_nonneg n]

/-- The new whole-ray prime-count provider gives a block of actual primes in every
successive-cube interval, and in particular a strict-interior prime. -/
theorem prime_between_cubes
    (hinterval : ∀ u : ℝ, Real.exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + (43 / 20) * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u)
    (n : ℕ) (hn : Real.exp 8 ≤ (n : ℝ)) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3 := by
  have hn0 : 0 < (n : ℝ) := (Real.exp_pos _).trans_le hn
  have hu : Real.exp 24 ≤ (n : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (Real.exp_nonneg 8) hn 3
    simpa only [← Real.exp_nat_mul, show (3 : ℕ) * (8 : ℝ) = 24 by norm_num] using h
  have hlog : 0 < Real.log ((n : ℝ) ^ 3) := by
    apply Real.log_pos
    have he := Real.add_one_le_exp (24 : ℝ)
    linarith
  obtain ⟨hl, hu'⟩ := RHContinuation.PrimeQuantiles.octic_quantiles
    hinterval hu (m := 0) (by
      norm_num only [Nat.cast_zero]
      positivity)
  refine ⟨Nat.nth Nat.Prime (Nat.primeCounting ⌊(n : ℝ) ^ 3⌋₊),
    Nat.prime_nth_prime _, ?_, ?_⟩
  · exact_mod_cast hl
  · have h := hu'.trans_lt (octic_fits_cube hn)
    exact_mod_cast h

#print axioms prime_between_cubes
end RHContinuation.OcticCubes
