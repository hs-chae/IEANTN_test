/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HybridPrimeFrontier
import CMSSharperUniform

namespace RHOnePrime.Hybrid
open Real
open RHOnePrime.CMSOpen RHOnePrime.CMSPrime RHOnePrime.FiniteGap
set_option maxHeartbeats 0

theorem all_real_open_08768 (hgap : SourceGapB) (hCMS : SourceCMS616)
    (rh : RiemannHypothesis) :
    ∀ x : ℝ, exp 24 ≤ x →
      HasPrimeOpen x (x + (548 / 625) * sqrt x * log x) := by
  apply hybrid_from_late_open hgap (by norm_num)
  intro x hx
  exact RHOnePrime.CMSSharper.open_prime_08768 hCMS rh hx

noncomputable def piecewiseWidth (x : ℝ) : ℝ :=
  if x < exp 44 then 1551 else
  if x ≤ exp 59 then (8301 / 10000) * sqrt x * log x else
    (548 / 625) * sqrt x * log x

/-- Preserve the substantially shorter bounded coefficient below.8358 and the
absolute finite-gap interval instead of publishing only the uniform constant.
The bounded improvement is not promoted to an asymptotic coefficient. -/
theorem piecewise_open_frontier (hgap : SourceGapB) (hCMS : SourceCMS616)
    (rh : RiemannHypothesis) :
    ∀ x : ℝ, exp 24 ≤ x → HasPrimeOpen x (x + piecewiseWidth x) := by
  intro x hx
  unfold piecewiseWidth
  split_ifs with h1 h2
  · exact finite_constant_window hgap hx h1
  · exact open_prime_08301 hCMS rh (le_of_not_gt h1) h2
  · exact RHOnePrime.CMSSharper.open_prime_08768 hCMS rh (le_of_not_gt h1)

lemma finite_constant_shorter_than_cms {x : ℝ} (hx : exp 24 ≤ x) :
    (1551 : ℝ) < (22 / 25) * sqrt x * log x := by
  have hxlarge : (1000000 : ℝ) < x := exp24_large.trans_le hx
  have hx0 : 0 ≤ x := by linarith
  have hs : (1000 : ℝ) < sqrt x := by nlinarith [sq_sqrt hx0, sqrt_nonneg x]
  have hl : 24 ≤ log x := by simpa using log_le_log (exp_pos 24) hx
  nlinarith

theorem piecewise_strictly_shorter_than_088 {x : ℝ} (hx : exp 24 ≤ x) :
    piecewiseWidth x < (22 / 25) * sqrt x * log x := by
  have hs : 0 < sqrt x := sqrt_pos.mpr ((exp_pos 24).trans_le hx)
  have hl : 0 < log x := by
    have h : 24 ≤ log x := by simpa using log_le_log (exp_pos 24) hx
    linarith
  unfold piecewiseWidth
  split_ifs
  · exact finite_constant_shorter_than_cms hx
  · nlinarith [mul_pos hs hl]
  · nlinarith [mul_pos hs hl]

#print axioms all_real_open_08768
#print axioms piecewise_open_frontier
#print axioms piecewise_strictly_shorter_than_088
end RHOnePrime.Hybrid
