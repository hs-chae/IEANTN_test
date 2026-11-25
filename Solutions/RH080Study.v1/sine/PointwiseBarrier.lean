/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
namespace RH080.PointwiseBarrier
open Real

/-- Even before paying the second endpoint error, subtracting the full
Schoenfeld6.1 theta allowance cannot certify an interval of coefficient0.8
on the campaign's late range. This is an obstruction to this particular
pointwise subtraction budget, not an assertion that the interval lacks primes. -/
theorem schoenfeld_single_endpoint_budget_negative (x : ℝ)
    (hx : 1 < x) (hlog : 24 ≤ log x) :
    (4/5 : ℝ)*sqrt x*log x - sqrt x*(log x-2)*log x/(8*π) < 0 := by
  have hs : 0 < sqrt x := sqrt_pos.2 (by linarith)
  have hl : 0 < log x := log_pos hx
  have hp : 0 < 8*π := by positivity
  have hcoef : (4/5 : ℝ) < (log x-2)/(8*π) := by
    apply (lt_div_iff₀ hp).mpr
    nlinarith [pi_lt_d6]
  have hm := mul_lt_mul_of_pos_right hcoef (mul_pos hs hl)
  have heq : ((log x-2)/(8*π))*(sqrt x*log x) =
      sqrt x*(log x-2)*log x/(8*π) := by ring
  rw [heq] at hm
  nlinarith

end RH080.PointwiseBarrier
#print axioms RH080.PointwiseBarrier.schoenfeld_single_endpoint_budget_negative
