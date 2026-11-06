/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.EvolvedResult
import IEANTNQRHBridge

namespace DirectIntervalActual

theorem evolved_prime_interval_ray
    (hCHJ : DirectIntervalA.CHJII_Theorem1_3_Row40)
    (hFKS : FKS.v3.density_0618) (hRvM : ZeroCount.v1.rvm_error_bound) :
    ∀ x : ℝ, Real.exp 330 ≤ x → IEANTN.HasPrimeInInterval x (x^(4/5:ℝ)) :=
  DirectIntervalA.evolved_prime_interval_ray hCHJ hFKS hRvM OpenAIQRH.v1.local_pinned_replay

theorem psi_increment_error_64
    (hCHJ : DirectIntervalA.CHJII_Theorem1_3_Row40)
    (hFKS : FKS.v3.density_0618) (hRvM : ZeroCount.v1.rvm_error_bound)
    {L : ℝ} (hL : (330 : ℝ)≤L) :
    |Chebyshev.psi (Real.exp L+Real.exp (4*L/5))-Chebyshev.psi (Real.exp L)-
      Real.exp (4*L/5)| ≤ (405513/1000000 : ℝ)*Real.exp (4*L/5) :=
  DirectIntervalA.psi_increment_error_64 hCHJ hFKS hRvM OpenAIQRH.v1.local_pinned_replay hL

end DirectIntervalActual
#print axioms DirectIntervalActual.evolved_prime_interval_ray
#print axioms DirectIntervalActual.psi_increment_error_64
