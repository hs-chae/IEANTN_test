/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.Result

namespace DirectIntervalA

/-- A certified scalar enclosure for the interval error, normalized by its length.
The sharper symbolic profile theorem is retained, not replaced by this cap. -/
theorem psi_increment_error_512
    (hCHJ : CHJII_Theorem1_3_Row40) (hFKS : FKS.v3.density_0618)
    (hRvM : ZeroCount.v1.rvm_error_bound) (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L : ℝ} (hL : (330 : ℝ)≤L) :
    |Chebyshev.psi (Real.exp L+Real.exp (4*L/5))-Chebyshev.psi (Real.exp L)-
      Real.exp (4*L/5)| ≤ (408514/1000000 : ℝ)*Real.exp (4*L/5) := by
  have h:=psi_increment_error_profile hCHJ hFKS hRvM hQRH hL
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  linarith [high_ray hL,low_le hL]

end DirectIntervalA
#print axioms DirectIntervalA.psi_increment_error_512
