/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalB.Assembly
import HighAnchorIntervalB.MomentCertificate
import HighAnchorIntervalB.LowRay

namespace HighAnchorIntervalB
open Real Set

theorem high_le {L:ℝ} (hL:330≤L) : high L≤(94/100:ℝ) :=
  (high_antitone (by simp : (330:ℝ)∈Ici 330) hL hL).trans Numerical.high330_le

theorem psi_increment_error_ray
    (hsource:DirectIntervalA.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L:ℝ} (hL:330≤L) :
    |Chebyshev.psi (exp L+gap L)-Chebyshev.psi (exp L)-gap L|≤
      (1989/2000:ℝ)*gap L := by
  apply (psi_increment_error_profile hsource h8 hRH hrvm hQRH hL).trans
  apply mul_le_mul_of_nonneg_right _ (gap_pos L).le
  linarith [low_le hL,high_le hL]

theorem theta_increment_lower_ray
    (hsource:DirectIntervalA.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L:ℝ} (hL:330≤L) :
    (9/2000:ℝ)*gap L≤Chebyshev.theta (exp L+gap L)-Chebyshev.theta (exp L) := by
  apply le_trans _ (theta_increment_lower_profile hsource h8 hRH hrvm hQRH hL)
  apply mul_le_mul_of_nonneg_right _ (gap_pos L).le
  linarith [low_le hL,high_le hL]

/-- Full real ray, with the original source package and actual numerical
execution facts consumed. No density-budget or prime-interval oracle remains. -/
theorem prime_interval_ray
    (hsource:DirectIntervalA.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8)) :
    ∀x:ℝ,exp 330≤x→IEANTN.HasPrimeInInterval x ((22/25:ℝ)*x^(79/100:ℝ)) := by
  apply real_ray_of_log_ray
  intro L hL
  exact hasPrime_exp_of_psi_error hL (psi_increment_error_ray hsource h8 hRH hrvm hQRH hL)
    (by norm_num)

end HighAnchorIntervalB
#print axioms HighAnchorIntervalB.prime_interval_ray
#print axioms HighAnchorIntervalB.psi_increment_error_ray
#print axioms HighAnchorIntervalB.interval_width_strict
