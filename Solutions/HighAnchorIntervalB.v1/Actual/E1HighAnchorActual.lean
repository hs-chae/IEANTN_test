/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalB.Result
import IEANTNQRHBridge
namespace E1HighAnchorActual
 theorem prime_interval_ray
    (hsource : DirectIntervalA.CHJII_Theorem1_3_Row40)
    (h8 : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm : ZeroCount.v1.rvm_error_bound) :
    ∀x:ℝ,Real.exp 330≤x→IEANTN.HasPrimeInInterval x ((22/25:ℝ)*x^(79/100:ℝ)) :=
  HighAnchorIntervalB.prime_interval_ray hsource h8 hRH hrvm
    OpenAIQRH.v1.local_pinned_replay
theorem psi_increment_error_ray
    (hsource : DirectIntervalA.CHJII_Theorem1_3_Row40)
    (h8 : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm : ZeroCount.v1.rvm_error_bound) {L:ℝ} (hL:330≤L) :
    |Chebyshev.psi (Real.exp L+HighAnchorIntervalB.gap L)-Chebyshev.psi (Real.exp L)-
      HighAnchorIntervalB.gap L|≤(1989/2000:ℝ)*HighAnchorIntervalB.gap L :=
  HighAnchorIntervalB.psi_increment_error_ray hsource h8 hRH hrvm
    OpenAIQRH.v1.local_pinned_replay hL
 theorem theta_increment_lower_ray
    (hsource : DirectIntervalA.CHJII_Theorem1_3_Row40)
    (h8 : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm : ZeroCount.v1.rvm_error_bound) {L:ℝ} (hL:330≤L) :
    (9/2000:ℝ)*HighAnchorIntervalB.gap L≤
      Chebyshev.theta (Real.exp L+HighAnchorIntervalB.gap L)-Chebyshev.theta (Real.exp L) :=
  HighAnchorIntervalB.theta_increment_lower_ray hsource h8 hRH hrvm
    OpenAIQRH.v1.local_pinned_replay hL
#print axioms prime_interval_ray
#print axioms psi_increment_error_ray
#print axioms theta_increment_lower_ray
#print axioms OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
end E1HighAnchorActual
