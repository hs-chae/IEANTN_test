/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.Result
import IEANTNQRHBridge

namespace DirectIntervalActual

theorem prime_interval_ray
    (hCHJ : DirectIntervalA.CHJII_Theorem1_3_Row40)
    (hFKS : FKS.v3.density_0618)
    (hRvM : ZeroCount.v1.rvm_error_bound) :
    ∀ x : ℝ, Real.exp 330 ≤ x → IEANTN.HasPrimeInInterval x (x^(4/5:ℝ)) :=
  DirectIntervalA.prime_interval_ray hCHJ hFKS hRvM OpenAIQRH.v1.local_pinned_replay

end DirectIntervalActual
#print axioms DirectIntervalActual.prime_interval_ray
