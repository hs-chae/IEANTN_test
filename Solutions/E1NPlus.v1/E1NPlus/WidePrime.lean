/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.Result
namespace E1NPlus
open Real

theorem wide_prime_ray
    (hsource:E1FrozenN.Interval.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8)) :
    ∀x:ℝ,exp 330 ≤ x → IEANTN.HasPrimeInInterval x (x^(4/5:ℝ)) := by
  intro x hx
  have hx1:1 ≤ x:=(one_le_exp (by norm_num : (0:ℝ) ≤ 330)).trans hx
  have hx0:0<x:=lt_of_lt_of_le zero_lt_one hx1
  have hw:(43/50:ℝ)*x^(79/100:ℝ) ≤ x^(4/5:ℝ):=by
    have hc:(43/50:ℝ)*x^(79/100:ℝ) ≤ x^(79/100:ℝ):=by
      nlinarith [rpow_pos_of_pos hx0 (79/100:ℝ)]
    exact hc.trans (rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  obtain ⟨p,hp,hpx,hpr⟩:=prime_interval_ray hsource h8 hRH hrvm hQRH x hx
  exact ⟨p,hp,hpx,by linarith⟩
#print axioms wide_prime_ray
end E1NPlus
