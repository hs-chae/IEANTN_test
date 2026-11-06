/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalA.Result
import DirectIntervalA.EvolvedResult

namespace HighAnchorIntervalA

/-- Both actual prime conclusions and a strict width comparison under their
honest union of source premises. The old uniform FKS assumption is retained;
it is not silently inferred from the new higher-anchor source package. -/
theorem strict_intervals_under_union
    (hsource:DirectIntervalA.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    (hFKS:FKS.v3.density_0618) :
    ∀x:ℝ,Real.exp 330≤x→
      IEANTN.HasPrimeInInterval x ((23/25:ℝ)*x^(79/100:ℝ)) ∧
      IEANTN.HasPrimeInInterval x (x^(4/5:ℝ)) ∧
      (23/25:ℝ)*x^(79/100:ℝ)<x^(4/5:ℝ) := by
  intro x hx
  exact ⟨prime_interval_ray hsource h8 hRH hrvm hQRH x hx,
    DirectIntervalA.evolved_prime_interval_ray hsource hFKS hrvm hQRH x hx,
    interval_width_strict hx⟩

end HighAnchorIntervalA
#print axioms HighAnchorIntervalA.strict_intervals_under_union
