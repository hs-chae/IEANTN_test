/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.Assembly
import E1NPlus.HighRay
import E1NPlus.LowRay
namespace E1NPlus
open Real

theorem psi_increment_error_ray
    (hsource:E1FrozenN.Interval.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L:ℝ} (hL:330 ≤ L) :
    |Chebyshev.psi (exp L+gap L)-Chebyshev.psi (exp L)-gap L| ≤
      (99939/100000:ℝ)*gap L := by
  apply (psi_increment_error_profile hsource h8 hRH hrvm hQRH hL).trans
  apply mul_le_mul_of_nonneg_right _ (gap_pos L).le
  linarith [low_le hL,high_le hL]

theorem theta_increment_lower_ray
    (hsource:E1FrozenN.Interval.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L:ℝ} (hL:330 ≤ L) :
    (609/1000000:ℝ)*gap L ≤ Chebyshev.theta (exp L+gap L)-Chebyshev.theta (exp L) := by
  apply le_trans _ (theta_increment_lower_profile hsource h8 hRH hrvm hQRH hL)
  apply mul_le_mul_of_nonneg_right _ (gap_pos L).le
  linarith [low_le hL,high_le hL]

/-- Every real x in the ray, using only frozen numerical leaves and new analysis. -/
theorem prime_interval_ray
    (hsource:E1FrozenN.Interval.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8)) :
    ∀x:ℝ,exp 330 ≤ x → IEANTN.HasPrimeInInterval x ((43/50:ℝ)*x^(79/100:ℝ)) := by
  apply real_ray_of_log_ray
  intro L hL
  exact hasPrime_exp_of_psi_error hL (psi_increment_error_ray hsource h8 hRH hrvm hQRH hL)
    (by norm_num)

theorem width_strict_against_E {x:ℝ} (hx:0<x) :
    (43/50:ℝ)*x^(79/100:ℝ)<(22/25:ℝ)*x^(79/100:ℝ) :=
  mul_lt_mul_of_pos_right (by norm_num) (rpow_pos_of_pos hx _)
#print axioms prime_interval_ray
#print axioms psi_increment_error_ray
#print axioms theta_increment_lower_ray
#print axioms width_strict_against_E
end E1NPlus
