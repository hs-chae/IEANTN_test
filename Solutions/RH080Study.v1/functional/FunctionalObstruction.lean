/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Algebraic consumers for Fourier dual and sensitivity bounds

These are unconditional mathematical lemmas. They do not assert that an external
Arb computation was kernel verified, and they do not assert a prime-gap theorem.
The full weak-duality estimate `D ≤ M * mass` must be supplied by a separate
analytic argument. Its intended application is Blanquer Robles v2, Theorem 4,
proof in subsection "Certified dual bounds", to the general CMS functional.
-/

set_option autoImplicit false
namespace RH080.Functional

/-- Generic exact reciprocal transport from an actual weak-duality inequality. -/
theorem ratio_lower_of_dual {mass D M : ℝ}
    (_hmass : 0 < mass) (hD : 0 < D) (hM : 0 < M)
    (hdual : D ≤ M * mass) : 1 / M ≤ mass / D := by
  apply (div_le_div_iff₀ hM hD).2
  nlinarith

/-- A source-verified bound of 1.23 for the dual transform excludes coefficient
0.8 within this functional. This is not an obstruction to prime-gap theorems
obtained by other analytic methods. -/
theorem compact_dual_excludes_four_fifths {mass D : ℝ}
    (hmass : 0 < mass) (hD : 0 < D)
    (hdual : D ≤ (123 / 100 : ℝ) * mass) :
    (4 / 5 : ℝ) < mass / D := by
  have h := ratio_lower_of_dual hmass hD (by norm_num : (0 : ℝ) < 123 / 100) hdual
  norm_num at h ⊢
  linarith

/-- The tighter original dual certificate has the stronger floor 50000/60393.
Its numerical verification is external until a separate kernel/source proof
actually supplies this inequality. -/
theorem original_dual_floor {mass D : ℝ}
    (hmass : 0 < mass) (hD : 0 < D)
    (hdual : D ≤ (60393 / 50000 : ℝ) * mass) :
    (50000 / 60393 : ℝ) ≤ mass / D := by
  have h := ratio_lower_of_dual hmass hD
    (by norm_num : (0 : ℝ) < 60393 / 50000) hdual
  norm_num at h
  exact h

/-- A new independently computed reduced-penalty dual, when its analytic
weak-dual inequality is supplied, still excludes 0.8 at A=5/2. Feasibility
persists at every larger A; the numerical certificate remains external E until
a separate verified source/kernel proof supplies it. -/
theorem reduced_penalty_dual_floor {mass D : ℝ}
    (hmass : 0 < mass) (hD : 0 < D)
    (hdual : D ≤ (2499 / 2000 : ℝ) * mass) :
    (2000 / 2499 : ℝ) ≤ mass / D ∧ (4 / 5 : ℝ) < mass / D := by
  have h := ratio_lower_of_dual hmass hD
    (by norm_num : (0 : ℝ) < 2499 / 2000) hdual
  norm_num at h
  constructor
  · exact h
  · linarith

/-- Exact moment/interpolation budget for the twenty-step candidate, using
π² < 10 separately in the analytic derivative estimate. -/
theorem compact_interpolation_budget :
    (10 : ℝ) * (134917 / 16384) * (1 / 128) ^ 2 = 674585 / 134217728 := by
  norm_num

/-- The numerical program may return any grid bound at most 1.2249; the exact
analytic interpolation allowance then stays strictly below 1.23. -/
theorem compact_grid_margin {grid : ℝ} (hgrid : grid ≤ (12249 / 10000 : ℝ)) :
    grid + 674585 / 134217728 < (123 / 100 : ℝ) := by
  linarith

/-- The stronger intended source-program grid target leaves more margin. -/
theorem compact_grid_target :
    (611 / 500 : ℝ) + 674585 / 134217728 < 123 / 100 := by
  norm_num

/-- Scalar sensitivity of an arbitrary Fourier witness to its exterior-prime
penalty. This lemma neither asserts nor introduces a smaller Brun--Titchmarsh
constant; an analytically valid penalty is needed by the prime adapter. -/
theorem ratio_at_most_iff {mass value leak A target : ℝ}
    (hden : 0 < value - A * leak) :
    mass / (value - A * leak) ≤ target ↔
      mass ≤ target * (value - A * leak) := by
  exact div_le_iff₀ hden

/-- Quantitative sufficient penalty for the previously kernel-proved degree24
Gaussian budgets. The target 0.8 is obtained only if a separate valid analytic
argument allows A≤2.046. Such a source theorem is NOT supplied here. -/
theorem prior_gaussian_four_fifths_if_penalty {mass value leak A : ℝ}
    (hmass : mass ≤ (74899 / 100000 : ℝ))
    (hvalue : (999999999 / 1000000000 : ℝ) ≤ value)
    (hleak0 : 0 ≤ leak) (hleak : leak ≤ (1947 / 62500 : ℝ))
    (_hA0 : 0 ≤ A) (hA : A ≤ (1023 / 500 : ℝ)) :
    0 < value - A * leak ∧ mass / (value - A * leak) < (4 / 5 : ℝ) := by
  have hprod : A * leak ≤ (1023 / 500 : ℝ) * (1947 / 62500 : ℝ) := by
    exact mul_le_mul hA hleak hleak0 (by norm_num)
  constructor
  · nlinarith
  · apply (div_lt_iff₀ (by nlinarith : 0 < value - A * leak)).2
    nlinarith

/-- Exact threshold of the conservative prior numerical budgets, stated as a
rational identity so it cannot be confused with a newly proved analytic input. -/
theorem prior_gaussian_critical_penalty :
    (((999999999 / 1000000000 : ℝ) - (5 / 4) * (74899 / 100000)) /
      (1947 / 62500)) = 63762499 / 31152000 := by
  norm_num

end RH080.Functional

#print axioms RH080.Functional.compact_dual_excludes_four_fifths
#print axioms RH080.Functional.original_dual_floor
#print axioms RH080.Functional.compact_grid_margin
#print axioms RH080.Functional.prior_gaussian_four_fifths_if_penalty
