/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.MomentPNT.v1.Conclusions
import SynergyAnalytic.PrimeRich
namespace MomentPNTDerived
open Real Set MeasureTheory IEANTN SynergyAnalytic
set_option maxHeartbeats 300000

/-- Exact rational specialization of the reusable source-moment profile. -/
theorem moment_profile_330 (h : MomentPNT.v1.moment_future_pi) :
    HasPowerLogBound Eπ (8522322 / 1000000000) 0 (7 / 8) (Real.exp 330) := by
  have bound := h 330 (by norm_num)
  norm_num [HasPowerLogBound] at bound ⊢
  intro x hx
  have positive : 0 < x := (Real.exp_pos 330).trans_le hx
  exact (bound x hx).trans (mul_le_mul_of_nonneg_right (by norm_num)
    (Real.rpow_nonneg positive.le _))

/-- The unchanged interval width now has a stronger guaranteed prime count:
0.00095363 in place of the historical 0.00079, without another source input. -/
theorem moment_prime_rich (h : MomentPNT.v1.moment_future_pi)
    {x : ℝ} (hx : Real.exp 330 ≤ x) :
    (95363 / 100000000 : ℝ) * x ^ ((7 : ℝ) / 8) / Real.log x ≤
      primeCounting (x + (9 / 500 : ℝ) * x ^ ((7 : ℝ) / 8)) - primeCounting x := by
  have base := prime_rich_parameter
    (by norm_num : (0 : ℝ) ≤ 8522322 / 1000000000) (moment_profile_330 h) hx hx
  have positive : 0 < x := (Real.exp_pos 330).trans_le hx
  have log_positive : 0 < Real.log x := by
    have lower := Real.log_le_log (Real.exp_pos 330) hx
    rw [Real.log_exp] at lower
    linarith
  have coefficient : (95363 / 100000000 : ℝ) ≤
      (9 / 500) / (1000001 / 1000000) -
        (8522322 / 1000000000) * (5001 / 5000 + 1) := by norm_num
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right coefficient (Real.rpow_nonneg positive.le _))
    log_positive.le).trans base

#print axioms moment_profile_330
#print axioms moment_prime_rich

end MomentPNTDerived
