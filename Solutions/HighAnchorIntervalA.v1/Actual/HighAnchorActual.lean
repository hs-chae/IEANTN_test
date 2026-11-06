/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalA.UnionComparison
import IEANTNQRHBridge

namespace HighAnchorActual

/-- The actual pinned OpenAI QRH proof supplies the zero-free hypothesis.
CHJ-II, eight density-source assertions, finite RH and RVM remain explicit. -/
theorem prime_interval_ray
    (hsource : DirectIntervalA.CHJII_Theorem1_3_Row40)
    (h8 : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm : ZeroCount.v1.rvm_error_bound) :
    ∀ x : ℝ, Real.exp 330 ≤ x →
      IEANTN.HasPrimeInInterval x ((23/25 : ℝ) * x^(79/100 : ℝ)) :=
  HighAnchorIntervalA.prime_interval_ray hsource h8 hRH hrvm
    OpenAIQRH.v1.local_pinned_replay

end HighAnchorActual

#print axioms HighAnchorActual.prime_interval_ray
