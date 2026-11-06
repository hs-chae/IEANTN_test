/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.Assembly
import DirectIntervalA.EvolvedRay
import DirectIntervalA.LowRay

namespace DirectIntervalA

theorem evolved_prime_interval_ray
    (hCHJ : CHJII_Theorem1_3_Row40) (hFKS : FKS.v3.density_0618)
    (hRvM : ZeroCount.v1.rvm_error_bound) (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8)) :
    ∀ x : ℝ, Real.exp 330 ≤ x → IEANTN.HasPrimeInInterval x (x^(4/5:ℝ)) :=
  prime_ray_of_budgets hCHJ hFKS hRvM hQRH
    (fun _ hL ↦ (evolved_high_ray hL).trans (by norm_num))
    (fun _ hL ↦ low_le hL)

theorem psi_increment_error_64
    (hCHJ : CHJII_Theorem1_3_Row40) (hFKS : FKS.v3.density_0618)
    (hRvM : ZeroCount.v1.rvm_error_bound) (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L : ℝ} (hL : (330 : ℝ)≤L) :
    |Chebyshev.psi (Real.exp L+Real.exp (4*L/5))-Chebyshev.psi (Real.exp L)-
      Real.exp (4*L/5)| ≤ (405513/1000000 : ℝ)*Real.exp (4*L/5) := by
  have h:=psi_increment_error_profile hCHJ hFKS hRvM hQRH hL
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  linarith [evolved_high_ray hL,low_le hL]

/-- The two displayed scalar caps improve on the entire real ray. This compares
those caps only; the exact analytic profile and conventional alternatives remain. -/
theorem scalar_allowance_strict (L : ℝ) :
    (405513/1000000 : ℝ)*Real.exp (4*L/5) <
      (408514/1000000 : ℝ)*Real.exp (4*L/5) := by
  exact mul_lt_mul_of_pos_right (by norm_num) (Real.exp_pos _)

end DirectIntervalA
#print axioms DirectIntervalA.evolved_prime_interval_ray
#print axioms DirectIntervalA.psi_increment_error_64
#print axioms DirectIntervalA.scalar_allowance_strict
