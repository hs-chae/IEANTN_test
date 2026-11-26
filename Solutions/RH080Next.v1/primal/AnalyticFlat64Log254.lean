/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators
namespace RH080Next.AnalyticFlat64

/-- A kernel proof by a finite positive exponential sum. No native execution
or external interval result is used, and this mathematical lemma is not PV. -/
theorem log254_lt : Real.log (254:ℝ)<277/50 := by
  have series := Real.sum_le_exp_of_nonneg (show (0:ℝ)≤277/50 by norm_num) 15
  have finite : (254:ℝ)<∑i∈Finset.range 15,(277/50:ℝ)^i/(Nat.factorial i:ℝ) := by
    norm_num [Finset.sum_range_succ,Nat.factorial]
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<254)).2 (finite.trans_le series)

#print axioms log254_lt
end RH080Next.AnalyticFlat64
