/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Sixteenth

/-!
# Short intervals from Agent A's θ coefficient

Agent A's committed solution proves `Eθ ≤ (0.009782 + 10⁻¹²)·x^{-1/8}` on `x ≥ e^300`
(`WinnerDensityA.revers_source_theta300`, under its own named inputs). Taken as a hypothesis, the
same criterion as `global_interval` gives a prime in `(x, x + 0.0196·x^{7/8}]` for every
`x ≥ e^300`, against `0.0264·x^{7/8}` in the network (`QRHPropagation.v2.prime_intervals_300`). The
improvement is the input's, not this file's.
-/

namespace QRHGlobal

open Real IEANTN

theorem intervals_from_agentA_theta (hcrit : PrimeInterval.v1.eTheta_criterion)
    (hθ : HasPowerLogBound Eθ (0.009782 + 1 / 10 ^ 12) 0 (7 / 8) (exp 300)) :
    ∀ x ≥ exp 300, HasPrimeInInterval x (0.0196 * x ^ ((7 : ℝ) / 8)) := by
  refine interval_of_theta_power hcrit hθ (by norm_num) (by norm_num) ?_
  have he : exp (-300 / 8 : ℝ) ≤ 1 / 10 ^ 6 := by
    rw [show (-300 / 8 : ℝ) = -(300 / 8) by norm_num, exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
    calc ((1 / 10 ^ 6 : ℝ))⁻¹ ≤ 2.7182818283 ^ 37 := by norm_num
      _ ≤ exp ((37 : ℕ) : ℝ) := exp_nat_ge 37
      _ ≤ exp (300 / 8) := exp_le_exp.mpr (by norm_num)
  nlinarith

end QRHGlobal
