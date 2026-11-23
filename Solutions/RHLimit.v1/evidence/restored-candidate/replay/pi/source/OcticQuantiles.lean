/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PrimeQuantiles
namespace RHContinuation.PrimeQuantiles
open Real Nat
theorem octic_quantiles
    (hinterval : ∀ u : ℝ, Real.exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + (43 / 20) * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u)
    {u : ℝ} (hu : Real.exp 24 ≤ u) {m : ℕ}
    (hm : (m : ℝ) ≤ (9001 / 9000 + (29 / 5) / Real.log u) * Real.sqrt u) :
    u < (Nat.nth Nat.Prime (Nat.primeCounting ⌊u⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊u⌋₊ + m) : ℝ) ≤
        u + (43 / 20) * Real.sqrt u * Real.log u := by
  have hup : 0 < u := (Real.exp_pos _).trans_le hu
  have hul : 0 ≤ Real.log u := Real.log_nonneg (by
    have h := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 24)
    exact h.trans hu)
  apply quantile_from_count hup.le
    (by nlinarith [Real.sqrt_nonneg u])
  exact hm.trans_lt (hinterval u hu)


#print axioms octic_quantiles
end RHContinuation.PrimeQuantiles
