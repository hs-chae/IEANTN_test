/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ThetaWindows
import Mathlib.NumberTheory.LSeries.RiemannZeta
namespace SchoenfeldRHTheta.v1
/-- **Schoenfeld1976 Theorem10, equation(6.1), theta component, printedp337.**
Ordinary RH gives the strict error estimate for every realx>=23*10^8.
Theta includes primes at its endpoint; the threshold is inclusive.
This is a primary analytic source claim, not a claimed Lean proof of that paper. -/
def refined_theta : Prop := RiemannHypothesis → ∀ x : ℝ, 2300000000 ≤ x →
  |Chebyshev.theta x-x| < IEANTN.ThetaWindows.schoenfeldError x
end SchoenfeldRHTheta.v1
