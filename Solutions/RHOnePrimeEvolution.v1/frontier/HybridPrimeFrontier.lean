/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FiniteGapRefined
import CMSOpenTransfer

/-! Actual all-real combination of separate source predicates. The finite
historical gap computation is B-tier and is NOT claimed source-first PV.
The late analytic package is kept explicit; RH-only Mathlib derivation is not
asserted. Early and late inputs are consumed, not conjoined to an unrelated proof.
-/
namespace RHOnePrime.Hybrid
open Real
open RHOnePrime.CMSOpen RHOnePrime.CMSPrime RHOnePrime.FiniteGap
set_option maxHeartbeats 0

theorem hybrid_from_late_open (hgap : SourceGapB) {c : ℝ}
    (hc : (1 / 2500 : ℝ) ≤ c)
    (hlate : ∀ x : ℝ, exp 44 ≤ x →
      HasPrimeOpen x (x + c * sqrt x * log x)) :
    ∀ x : ℝ, exp 24 ≤ x → HasPrimeOpen x (x + c * sqrt x * log x) := by
  intro x hx
  by_cases h : x < exp 44
  · exact finite_coefficient_0004 hgap hc hx h
  · exact hlate x (le_of_not_gt h)

theorem all_real_open_08771 (hgap : SourceGapB) (hCMS : SourceCMS616)
    (rh : RiemannHypothesis) :
    ∀ x : ℝ, exp 24 ≤ x →
      HasPrimeOpen x (x + (8771 / 10000) * sqrt x * log x) := by
  apply hybrid_from_late_open hgap (by norm_num)
  intro x hx
  exact open_prime_08771 hCMS rh hx

/-- Pointwise absolute finite-gap frontier. This keeps the actual1551 length
instead of replacing finite information by a needlessly wide RH-scale window. -/
theorem piecewise_absolute_08771 (hgap : SourceGapB) (hCMS : SourceCMS616)
    (rh : RiemannHypothesis) :
    ∀ x : ℝ, exp 24 ≤ x → HasPrimeOpen x
      (x + if x < exp 44 then 1551 else (8771 / 10000) * sqrt x * log x) := by
  intro x hx
  split_ifs with h
  · exact finite_constant_window hgap hx h
  · exact open_prime_08771 hCMS rh (le_of_not_gt h)

#print axioms hybrid_from_late_open
#print axioms all_real_open_08771
#print axioms piecewise_absolute_08771
end RHOnePrime.Hybrid
