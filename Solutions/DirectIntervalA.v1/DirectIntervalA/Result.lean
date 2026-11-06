/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.Assembly
import DirectIntervalA.HighRay
import DirectIntervalA.LowRay

namespace DirectIntervalA

/-- A prime in every stated real interval. The numerical allowances are proved
from the actual two-program output chain and its one-row low-strip companion.
The three literature inputs remain explicit, as does QRH in this generic root. -/
theorem prime_interval_ray
    (hCHJ : CHJII_Theorem1_3_Row40)
    (hFKS : FKS.v3.density_0618)
    (hRvM : ZeroCount.v1.rvm_error_bound)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8)) :
    ∀ x : ℝ, Real.exp 330 ≤ x → IEANTN.HasPrimeInInterval x (x^(4/5:ℝ)) :=
  prime_ray_of_budgets hCHJ hFKS hRvM hQRH
    (fun _ hL ↦ high_ray_036 hL) (fun _ hL ↦ low_le hL)

end DirectIntervalA
#print axioms DirectIntervalA.prime_interval_ray
